/*
 * Copyright (c) 2003, 2007-14 Matteo Frigo
 * Copyright (c) 2003, 2007-14 Massachusetts Institute of Technology
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */



/* Plans for handling vector transform loops.  These are *just* the
   loops, and rely on child plans for the actual DFTs.
 
   They form a wrapper around solvers that don't have apply functions
   for non-null vectors.
 
   vrank-geq1 plans also recursively handle the case of multi-dimensional
   vectors, obviating the need for most solvers to deal with this.  We
   can also play games here, such as reordering the vector loops.
 
   Each vrank-geq1 plan reduces the vector rank by 1, picking out a
   dimension determined by the vecloop_dim field of the solver. */

#include "dft.h"

#include <stdbool.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

// copied from trig.c begin
#if defined(TRIGREAL_IS_LONG_DOUBLE)
#  define COS cosl
#  define SIN sinl
#  define KTRIG(x) (x##L)
#  if defined(HAVE_DECL_SINL) && !HAVE_DECL_SINL
     extern long double sinl(long double x);
#  endif
#  if defined(HAVE_DECL_COSL) && !HAVE_DECL_COSL
     extern long double cosl(long double x);
#  endif
#elif defined(TRIGREAL_IS_QUAD)
#  define COS cosq
#  define SIN sinq
#  define KTRIG(x) (x##Q)
   extern __float128 sinq(__float128 x);
   extern __float128 cosq(__float128 x);
#else
#  define COS cos
#  define SIN sin
#  define KTRIG(x) (x)
#endif

static const trigreal K2PI =
    KTRIG(6.2831853071795864769252867665590057683943388);
#define by2pi(m, n) ((K2PI * (m)) / (n))

/*
 * Improve accuracy by reducing x to range [0..1/8]
 * before multiplication by 2 * PI.
 */

static void real_cexp(INT m, INT n, trigreal *out)
{
     trigreal theta, c, s, t;
     unsigned octant = 0;
     INT quarter_n = n;

     n += n; n += n;
     m += m; m += m;

     if (m < 0) m += n;
     if (m > n - m) { m = n - m; octant |= 4; }
     if (m - quarter_n > 0) { m = m - quarter_n; octant |= 2; }
     if (m > quarter_n - m) { m = quarter_n - m; octant |= 1; }

     theta = by2pi(m, n);
     register trigreal dmr = by2pi(m, n);
     if(theta!=dmr) 
     {
        printf("vrank-geq1 real_cexp error! theta\n");
        theta = by2pi(m, n);
     }
     c = COS(theta); s = SIN(theta);
     dmr = c*c + s*s - 1;
     if(dmr>0.00000001 || dmr <-0.00000001 ) 
     {
        printf("vrank-geq1 real_cexp error! c,s\n");
        c = COS(theta); s = SIN(theta);
     }
     if (octant & 1) { t = c; c = s; s = t; }
     if (octant & 2) { t = c; c = -s; s = t; }
     if (octant & 4) { s = -s; }

     out[0] = c; 
     out[1] = s; 
}
// modified from trig.c end

extern int fftSize;

bool start = true;
int radix;
R * simpleCoeff;    // 1/i, coefficients of memory checksum
R * outChecksum1;   // sum(a_i), intermediate checksum for FFT_2
R * outChecksum2;   // sum(1/i a_i), 2nd intermediate checksums for FFT_2
R * inAddr;



double flipBit1(double input, int flippedBit)
{
  char copy[8];
  memcpy(&copy, &input, sizeof(input));

  int index = flippedBit/8;
  int offset = flippedBit % 8;
  char tmp = 1 << offset;
  copy[index]= copy[index]^tmp;

  memcpy(&input, &copy, sizeof(copy));
  return input;
}

// checksum vector generation with DMR
void checksumVectorRAGeneration(int m, R * rA)
{
    R * rA0;
    R sumrA0 = 0, sumrA1 = 0;

     {
          int res = m % 3;
          register R c1 = 0.866025403784438818632906986749731004238128662;
          register R numeratorIm;
          if(res == 1) 
          {
               numeratorIm = - c1;
               rA[0] = 1, rA[1] = 0;
          }
          else 
          {
               numeratorIm = c1;
               rA[0] = 0.5, rA[1] = c1;  
          }
          rA0 = rA;
          rA0 += 2;
           for(int i=1; i<m; i++) // dmr
           {   
               R wi[2];
               real_cexp(i, m, wi);

               register R temp0, temp1, res0, res1, denom;
               register R w0, w1;
               register R dmr;
               w0 = wi[0], w1 = wi[1];
               // rA[m]
               temp0 = 1 + 0.5 * w0 - c1 * w1;
               dmr = 1 + 0.5 * w0 - c1 * w1;
               if(temp0!=dmr) 
                {
                    printf("rA error first part! temp0\n");
                    temp0 = 1 + 0.5 * w0 - c1 * w1;
                }
               
               temp1 = 0.5 * w1 + c1 * w0;
               dmr = 0.5 * w1 + c1 * w0;

               if(temp1!=dmr) 
                {
                    printf("rA error first part! temp1\n");
                    temp1 = 0.5 * w1 + c1 * w0;
                }
               // if(i==100)
               //      printf("temp: %f %f\n", temp0, temp1);

               res0 = 1.5 * temp0 - numeratorIm * temp1;
               dmr = 1.5 * temp0 - numeratorIm * temp1;
               if(res0!=dmr) 
                {
                    printf("rA error first part! res0\n");
                    res0 = 1.5 * temp0 - numeratorIm * temp1;
                }

                res1 = 1.5 * temp1 + numeratorIm * temp0;
                dmr = 1.5 * temp1 + numeratorIm * temp0;

               if(res1!=dmr) 
                {
                    printf("rA error first part! res1\n");
                    dmr = 1.5 * temp1 + numeratorIm * temp0;
                }

               denom = temp0 * temp0 + temp1 * temp1;
               dmr = temp0 * temp0 + temp1 * temp1;

               if(denom!=dmr) 
                {
                    printf("rA error first part! denom\n");
                   denom = temp0 * temp0 + temp1 * temp1;
                }

               w0 = res0 / denom;
               dmr = res0 / denom;
               if(w0!=dmr) 
                {
                    printf("rA error first part! w0\n");
                    w0 = res0 / denom;
                }

               w1 = res1 / denom;
               dmr = res1 / denom;
               if(w1!=dmr) 
                {
                    printf("rA error first part! w1:\n");                   
                    w1 = res1 / denom;
                }

               rA0[0] = w0;
               rA0[1] = w1;

               sumrA0 += w0;
               sumrA1 += w1;

               rA0 += 2;
           }
     }

     // checksum for rA
     rA0[0] = sumrA0;
     rA0[1] = sumrA1;

     return ;
}

void checksumsInit(int m, int r, R * checksum1, R * checksum2, R * outChecksum1, R * outChecksum2)
{
    for(int i=0; i<r*2; i++)
      checksum1[i] = 0;
    for(int i=0; i<r*2; i++)
      checksum2[i] = 0;

    for(int i=0; i<m*2; i++)
      outChecksum1[i] = 0;
    for(int i=0; i<m*2; i++)
      outChecksum2[i] = 0;

    return ;
}

void simpleCoefficientGeneration(int size)
{
    R * sc = simpleCoeff;
    for(int i=1; i<size+1; i++)
    {
      sc[0] = 1.0 / i;
      sc ++;
    }
}

// checksum rearrangement, coeff[2*i] = 1/i * rA[i]
void coefficientGeneration(int m, R * rA, R * coeff)
{
    R * cof = coeff;
    R * posrA = rA;
    register R c;
    for(int i=1; i<m+1; i++)
    {
        c = 1.0 / i; 
        cof[0] = posrA[0] * c;
        cof[1] = posrA[1] * c;
        cof += 2, posrA += 2;
    }
    return ;
}

// m: m-FFT, r: radix, coeff: memory checksum coefficients
void checksumGeneration1(int m, int r, R * ri, R * ii, R * rA, R * coeff, R * checksum1, R * checksum2)
{
      R * posR; 
      R * posI;
      R * pos1;
      R * pos2;
      posR = ri, posI = ii;// pos1 = checksum1, pos2 = checksum2;

      R * posrA = rA;      
      R * cof = coeff;

      register R temp0, temp1;
      for(int i=0; i<m; i++)
      {
          register R c0 = cof[0];
          register R c1 = cof[1];
          register R rAc0 = posrA[0];
          register R rAc1 = posrA[1];
          pos1 = checksum1, pos2 = checksum2;
          for(int j=0; j<r; j++)
          {
            temp0 = posR[0], temp1 = posI[0];
            pos1[0] += temp0 * rAc0 - temp1 * rAc1;
            pos1[1] += temp0 * rAc1 + temp1 * rAc0;
            pos2[0] += c0 * temp0;
            pos2[1] += c1 * temp1;

            posR += 2, posI += 2;
            pos1 += 2, pos2 += 2; 
          }   
          cof += 2;
          posrA += 2;
      }

      return ;
}

bool outputVerification(R * ro0, R * io0, int cn, R * cks1, R * diff, R delta)
{
    R or00, or01, or10, or11, or20, or21;
    or00 = 0, or01 = 0, or10 = 0, or11 = 0, or20 = 0, or21 = 0; 

    int j;
    for(j=0; j<cn - 3; j+=3)
    {
        or00 += ro0[0], or01 += io0[0];
        or10 += ro0[2], or11 += io0[2];
        or20 += ro0[4], or21 += io0[4];
        ro0 += 6, io0 += 6;  
    }
    if((j+1) < cn )
    {
        or00 += ro0[0], or01 += io0[0];
        or10 += ro0[2], or11 += io0[2];
    }
    else
    {
        or00 += ro0[0], or01 += io0[0];
    }                      

    R r1 = 0.866025403784438818632906986749731004238128662;

    diff[0] = cks1[0] - or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
    diff[1] = cks1[1] - or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20; 

    return (diff[0]>delta || diff[0]<-delta || diff[1]>delta || diff[1]<-delta);

}
R delta1;

void errorCorrection(R * ri0, R * ii0, int m, int r, R * coeff, R * rA, R * cks2, R * diff, R * lastResult, int offset)
{
    //recalc 2 times, correct memory here
    // printf("memory error! ivs: %d\tovs: %d\n", ivs, ovs);
    R * in1;
    R * in2;
    R * cof;
    in1 = ri0, in2 = ii0;
    cof = coeff;

    // current memory checksums
    R cksMR = 0, cksMI = 0;
    int step = 2 * r;

    for(int j=0; j<m; j++)
    {
        cksMR += cof[0] * in1[0];
        cksMI += cof[1] * in2[0];
        in1 += step, in2 += step;
        cof += 2;
    }

    R diffReal = diff[0];
    R diffIm = diff[1];

    R diffReal2 = cks2[0] - cksMR;
    R diffIm2 = cks2[1] - cksMI;

    printf("diff2 : %f %f\n", diffReal2, diffIm2);
    
    if(diffReal2 == 0 && diffIm2 == 0)  
    {
      printf("computational error or x[1] corruption!\n");
      if(diffReal == lastResult[0] && diffIm == lastResult[1])
      {
        printf("x[1] corruption, %f\n", ii0[0]);
        ii0[0] += diffIm;
      }
      return ;
    }
    printf("memory error!\n");
    if(diffReal2 == 0)
    {
        printf("imaginary part error!");
        int index =(int) (-diffReal / diffIm2 - 0.5); // -1 for index
        int pos = index * r * 2;
        printf("memory error ocurrs imaginary part, pos -- val: %d -- %f\n", offset+pos+1, ii0[pos]);
        // if(offset+pos+1 != corruptedIndex) 
        // {
        //   printf("uncorrected error!\n true pos: %d, current pos: %d\n", corruptedIndex, pos);
        //   exit(1);
        // }
        ii0[pos] -= diffReal / rA[2*index+1]; 
        printf("index %d diff: %f\n", index, diffReal / rA[2*index+1]);
    }
    else if(diffIm2 == 0)
    {
        printf("real part error!");
        int index =(int) (diffReal / diffReal2 - 0.5); // -1 for index
        int pos = index * r * 2; // real part
        printf("memory error ocurrs real part, pos -- val: %d -- %f\n", offset+pos, ri0[pos]);
        // if(offset+pos != corruptedIndex) 
        // {
        //   printf("uncorrected error!\n true pos: %d, current pos: %d\n", corruptedIndex, pos);
        //   exit(1);
        // }        
        ri0[pos] -= -diffReal / rA[2*index]; 
        printf("index %d diff: %f\n", index, -diffReal / rA[2*index]);
    }
    else
    {
        printf("multiplie memory error, restart is needed.\n");
        exit(1);
    }
    return ;
}

void outChecksumIncrease(int m, R * ro0, R * io0, R * outChecksum1, R * outChecksum2, R coeffMem)
{
    R * pos1 = outChecksum1;
    R * pos2 = outChecksum2;

    R temp0, temp1;
    for(int j=0; j<m; j++)
    {
        temp0 = ro0[0], temp1 = io0[0];
        pos1[0] += temp0, pos2[0] += temp0 * coeffMem;
        pos1[1] += temp1, pos2[1] += temp1 * coeffMem;
        ro0 += 2, io0 += 2;  
        pos1 += 2, pos2 += 2;
    }

    return ;    
}

typedef struct {
     solver super;
     int vecloop_dim;
     const int *buddies;
     size_t nbuddies;
} S;

typedef struct {
     plan_dft super;

     plan *cld;
     INT vl;
     INT ivs, ovs;
     const S *solver;
} P;

// static void apply(const plan *ego_, R *ri, R *ii, R *ro, R *io)
// {
//      const P *ego = (const P *) ego_;
//      INT i, vl = ego->vl;
//      INT ivs = ego->ivs, ovs = ego->ovs;
//      dftapply cldapply = ((plan_dft *) ego->cld)->apply;

//      for (i = 0; i < vl; ++i) {
//           cldapply(ego->cld,
//                    ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
//      }
// }

static void apply(const plan *ego_, R *ri, R *ii, R *ro, R *io)
{
     const P *ego = (const P *) ego_;
     INT i, vl = ego->vl;
     INT ivs = ego->ivs, ovs = ego->ovs;
     dftapply cldapply = ((plan_dft *) ego->cld)->apply;

     // checksums for FFT_1
     R * checksum1;
     R * checksum2;

     // checksum vector rA1
     R * rA1;

     // memory checksum coefficients
     R * coeff_rA1;

     int m;

     // identify radix, initialize checksums and coefficients
     if(start == true)
     {
        start = false;
        radix = vl;
        m = fftSize / radix;

        rA1 = (R *) malloc(m*2*sizeof(R) + 2);
        checksumVectorRAGeneration(m, rA1);
        // printf("rA1 generation done, rA1[0]: %f\n", rA1[0]);
        
        checksum1 = (R *) malloc(radix*2*sizeof(R));
        checksum2 = (R *) malloc(radix*2*sizeof(R));
        outChecksum1 = (R *) malloc(m*2*sizeof(R));
        outChecksum2 = (R *) malloc(m*2*sizeof(R));
        checksumsInit(m, radix, checksum1, checksum2, outChecksum1, outChecksum2);
        // printf("checksum init done, checksum1[0] and outChecksum1[0]: %f %f\n", checksum1[0], outChecksum1[0]);

        int simpleCoeffSize = radix > m ? radix : m;
        simpleCoeff = (R *) malloc(simpleCoeffSize*sizeof(R));
        simpleCoefficientGeneration(simpleCoeffSize);
        // printf("simple coefficient generation done, simpleCoeff[0]: %f\n", simpleCoeff[0]);

        coeff_rA1 = (R *) malloc( m*2*sizeof(R));
        coefficientGeneration(m, rA1, coeff_rA1);
        // printf("coefficient generation done, coeff_rA1[0]: %f\n", coeff_rA1[0]);

        checksumGeneration1(m, radix, ri, ii, rA1, coeff_rA1, checksum1, checksum2);
        // printf("checksum generation done\n");
     }

     if(vl == radix) // enter the first FFT
     {
        R * cofSimple = simpleCoeff;
        R * cksPos = checksum1;
        R diff[2];

        R delta1 = 1e-4; // first threshold
        // delta1 = 3.48*1e-8; // first threshold
        
        // bool inject = false; // inject computational error
        // inject memory error~~~
        // ri[456345] += 20000;
        // ii[20] += 40000;

        R * posRo;
        R * posIo;
        posRo = ro;
        posIo = io;
        for (i = 0; i < vl; ++i) {


            // printf("%d-th FFT: \n", i);
            bool recalc = true; // recalculation flag
            R lastResult[2] = {0};
            while(recalc)
            {
                cldapply(ego->cld,
                           ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);

              // if(!inject && i==24){
              //     printf("injected!");
              //     (ro + i*ovs)[0]+=10000;
              //     inject =true;
              // }

                recalc = outputVerification(posRo, posIo, m, cksPos, diff, delta1);

                if(recalc) 
                {
                    printf("%d-th diff: %.15f %.15f, pos offset: %lld\n", i, diff[0], diff[1], (long long)i*ivs);
                    errorCorrection(ri + i * ivs, ii + i * ivs, m, radix, coeff_rA1, rA1, checksum2+2*i, diff, lastResult, i*ivs);
                    lastResult[0] = diff[0];
                    lastResult[1] = diff[1];
                    continue;
                }
                else
                {
                    outChecksumIncrease(m, posRo, posIo, outChecksum1, outChecksum2, cofSimple[0]);
                    cofSimple ++;
                    cksPos += 2;
                    posRo += ovs;
                    posIo += ovs;
                }
            }
        }

        free(checksum1);
        free(checksum2);
        free(rA1);
        free(coeff_rA1);

        // copy intermediate output into input for later correction
        memcpy(ri, ro, 2*vl*m*sizeof(R));
        inAddr = ri;

     } 
     else
     {
         for (i = 0; i < vl; ++i) {
              cldapply(ego->cld,
                       ri + i * ivs, ii + i * ivs, ro + i * ovs, io + i * ovs);
         }
     }
}

static void awake(plan *ego_, enum wakefulness wakefulness)
{
     P *ego = (P *) ego_;
     X(plan_awake)(ego->cld, wakefulness);
}

static void destroy(plan *ego_)
{
     P *ego = (P *) ego_;
     X(plan_destroy_internal)(ego->cld);
}

static void print(const plan *ego_, printer *p)
{
     const P *ego = (const P *) ego_;
     const S *s = ego->solver;
     p->print(p, "(dft-vrank>=1-x%D/%d%(%p%))",
 	      ego->vl, s->vecloop_dim, ego->cld);
}

static int pickdim(const S *ego, const tensor *vecsz, int oop, int *dp)
{
     return X(pickdim)(ego->vecloop_dim, ego->buddies, ego->nbuddies,
		       vecsz, oop, dp);
}

static int applicable0(const solver *ego_, const problem *p_, int *dp)
{
     const S *ego = (const S *) ego_;
     const problem_dft *p = (const problem_dft *) p_;

     return (1
	     && FINITE_RNK(p->vecsz->rnk)
	     && p->vecsz->rnk > 0

	     /* do not bother looping over rank-0 problems,
		since they are handled via rdft */
	     && p->sz->rnk > 0

	     && pickdim(ego, p->vecsz, p->ri != p->ro, dp)
	  );
}

static int applicable(const solver *ego_, const problem *p_, 
		      const planner *plnr, int *dp)
{
     const S *ego = (const S *)ego_;
     const problem_dft *p;

     if (!applicable0(ego_, p_, dp)) return 0;

     /* fftw2 behavior */
     if (NO_VRANK_SPLITSP(plnr) && (ego->vecloop_dim != ego->buddies[0]))
	  return 0;

     p = (const problem_dft *) p_;

     if (NO_UGLYP(plnr)) {
	  /* Heuristic: if the transform is multi-dimensional, and the
	     vector stride is less than the transform size, then we
	     probably want to use a rank>=2 plan first in order to combine
	     this vector with the transform-dimension vectors. */
	  {
	       iodim *d = p->vecsz->dims + *dp;
	       if (1
		   && p->sz->rnk > 1 
		   && X(imin)(X(iabs)(d->is), X(iabs)(d->os)) 
		   < X(tensor_max_index)(p->sz)
		    )
		    return 0;
	  }

	  if (NO_NONTHREADEDP(plnr)) return 0; /* prefer threaded version */
     }

     return 1;
}

static plan *mkplan(const solver *ego_, const problem *p_, planner *plnr)
{
     const S *ego = (const S *) ego_;
     const problem_dft *p;
     P *pln;
     plan *cld;
     int vdim;
     iodim *d;

     static const plan_adt padt = {
	  X(dft_solve), awake, print, destroy
     };

     if (!applicable(ego_, p_, plnr, &vdim))
          return (plan *) 0;
     p = (const problem_dft *) p_;

     d = p->vecsz->dims + vdim;

     // if(d->n == 4096) printf("first FFT, problem size: %d\n", 5);
     // if(ego->vecloop_dim == 4096 || d->n == 4096) printf("vecloop_dim: %d, d->n, %d\n", ego->vecloop_dim, d->n);
     // if(d->n == 4096) 
     // {
     //    printf("d->n: %d, p->sz->dims: %d, p->vecsz->dims: %d\n", d->n, p->sz->dims[0].n, p->vecsz->dims[0].n);
        
     // }
     A(d->n > 1);
     cld = X(mkplan_d)(plnr,
		       X(mkproblem_dft_d)(
			    X(tensor_copy)(p->sz),
			    X(tensor_copy_except)(p->vecsz, vdim),
			    TAINT(p->ri, d->is), TAINT(p->ii, d->is),
			    TAINT(p->ro, d->os), TAINT(p->io, d->os)));
     if (!cld) return (plan *) 0;

     pln = MKPLAN_DFT(P, &padt, apply);

     pln->cld = cld;
     pln->vl = d->n;
     pln->ivs = d->is;
     pln->ovs = d->os;

     pln->solver = ego;
     X(ops_zero)(&pln->super.super.ops);
     pln->super.super.ops.other = 3.14159; /* magic to prefer codelet loops */
     X(ops_madd2)(pln->vl, &cld->ops, &pln->super.super.ops);

     if (p->sz->rnk != 1 || (p->sz->dims[0].n > 64))
	  pln->super.super.pcost = pln->vl * cld->pcost;

     return &(pln->super.super);
}

static solver *mksolver(int vecloop_dim, const int *buddies, size_t nbuddies)
{
     static const solver_adt sadt = { PROBLEM_DFT, mkplan, 0 };
     S *slv = MKSOLVER(S, &sadt);
     slv->vecloop_dim = vecloop_dim;
     slv->buddies = buddies;
     slv->nbuddies = nbuddies;
     return &(slv->super);
}

void X(dft_vrank_geq1_register)(planner *p)
{
     /* FIXME: Should we try other vecloop_dim values? */
     static const int buddies[] = { 1, -1 };
     size_t i;
     
     for (i = 0; i < NELEM(buddies); ++i)
          REGISTER_SOLVER(p, mksolver(buddies[i], buddies, NELEM(buddies)));
}
