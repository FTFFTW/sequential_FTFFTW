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

/* express a twiddle problem in terms of dft + multiplication by
   twiddle factors */

#include "ct.h"

#include <math.h>
#include <stdio.h>
#include <stdbool.h>
#include <time.h>
#include <string.h>

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
       printf("dftw-genericbuf real_cexp error! theta\n");
       theta = by2pi(m, n);
     }
     c = COS(theta); s = SIN(theta);
     dmr = c*c + s*s - 1;
     if(dmr>0.00000001 || dmr <-0.00000001 ) 
     {
        printf("dftw-genericbuf real_cexp error! c,s\n");
        c = COS(theta); s = SIN(theta);
     }
     if (octant & 1) { t = c; c = s; s = t; }
     if (octant & 2) { t = c; c = -s; s = t; }
     if (octant & 4) { s = -s; }

     out[0] = c; 
     out[1] = s; 
}
// modified from trig.c end

extern R * outChecksum1; // sum(a_i), intermediate checksums
extern R * outChecksum2; // sum(1/i a_i), intermediate checksums
extern R * simpleCoeff;  // 1/i, coefficients of memory checksum
extern R * inAddr;

//only one checksum is needed for final output since both computational and memory fault
// can be corrected by re-computation from stored intermediate result.
R * outputChecksum;      // final output checksum
R * memoryChecksum1;
R * memoryChecksum2;
R * rA2;
int count;               // index for final output


typedef struct {
     ct_solver super;
     INT batchsz;
} S;

typedef struct {
     plan_dftw super;

     INT r, rs, m, ms, v, vs, mb, me;
     INT batchsz;
     plan *cld;

     triggen *t;
     const S *slv;
} P;


#define BATCHDIST(r) ((r) + 16)

// copied from trig.c end
double flipBit2(double input, int flippedBit)
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
void checksumVectorRAGeneration2(int m, R * rA)
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

// R maxDiff0 = 0;
// R maxDiff1 = 0;
R delta2;
/**************************************************************/
static void bytwiddle(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
{
     INT j, k;
     INT r = ego->r, rs = ego->rs, ms = ego->ms;
     triggen *t = ego->t;
     bool recalc = true;

     delta2 = 2*1e-10;

     while(recalc)
     {
       R ipcReal_2 = 0, ipcIm_2 = 0;
       
       R sumReal, sumIm;
       for( k = mb; k< me; k++)
       {
         int coffset = 2*(k - mb);
         memoryChecksum1[coffset] = 0;
         memoryChecksum1[coffset+1] = 0;
       }

       R * rA0 = rA2;
       int index;
       R temp0, temp1;

       for (j = 0; j < r; ++j) {
         sumReal = 0, sumIm = 0;
         
         for (k = mb; k < me; ++k)
         {
              index = j * rs + k * ms;
              temp0 = rio[index];
              temp1 = iio[index];

              int coffset = 2*(k-mb);
              memoryChecksum1[coffset] += temp0, memoryChecksum1[coffset+1] += temp1;

              index = j * 2 + 2 * BATCHDIST(r) * (k - mb) + 0;
              t->rotate(t, j * k,
                  temp0,
                  temp1,
                  &buf[index]);

              sumReal += buf[index], sumIm += buf[index+1];
         }

         ipcReal_2 += rA0[0]*sumReal - rA0[1]*sumIm;
         ipcIm_2 += rA0[0]*sumIm + rA0[1]*sumReal;
         rA0 += 2;
       }

       outputChecksum[count] = ipcReal_2;
       outputChecksum[count+1] = ipcIm_2;

       recalc = false;
       for(k=mb; k<me; ++k)
       {
         R diff10 = memoryChecksum1[2*(k-mb)] - outChecksum1[2*k];
         R diff20 = memoryChecksum1[2*(k-mb)+1] - outChecksum1[2*k+1];

         // if(fabs(diff10) > maxDiff0) maxDiff0 = fabs(diff10);
         // if(fabs(diff20) > maxDiff1) maxDiff1 = fabs(diff20);

         if (diff10 < -delta2 || diff10 > delta2)        
         {
            printf("error detected\n");
            R * cof0;
            cof0 = simpleCoeff;
            R sumReal = 0;
            R * pos1 = rio + k*ms;
            for (j = 0; j < r; ++j)
            {
              sumReal += pos1[0] * cof0[0];// sumIm += rio[1] * cof0[0];
              cof0 ++;
              pos1 += rs;
            }
            int coffset = 2*(k-mb);
            R diff11 = sumReal - outChecksum2[2*k];

            recalc = true;
            printf("%d-th memoryChecksums: %.16lf %.16lf %.16lf\n", k, diff10, diff20, diff11);
            int index =(int) (diff10 / diff11 - 0.5); // -1 for index
            int pos = index * rs + k * ms;
            printf("dftw-genericbuf bytwiddle real part error, index %d pos %d ~ val %f\n", index, pos, rio[pos]);
            
            // if(pos != corruptedIndex) 
            // {
            //   printf("uncorrected error!\n true pos: %d, current pos: %d\n", corruptedIndex, pos);
            //   exit(1);
            // }
            
            printf("original value: %f\n", inAddr[pos]);
            rio[pos] -= diff10;
            // rio[pos] = inAddr[pos];
            inAddr[pos] = rio[pos];
            printf("corrected value: %f\n", inAddr[pos]);
            // exit(0);
         }
         if (diff20 < -delta2 || diff20 > delta2)
         {
            printf("error detected\n");
            R * cof0;
            cof0 = simpleCoeff;
            R sumIm = 0;
            R * pos1 = iio + k*ms;
            for (j = 0; j < r; ++j)
            {
              //sumReal += rio[0] * cof0[0], 
              sumIm += pos1[0] * cof0[0];
              cof0 ++;
              pos1 += rs;
            }
            int coffset = 2*(k-mb);
            R diff21 = sumIm - outChecksum2[2*k+1];

            recalc = true;
            printf("%d-th memoryChecksums: %.16lf %.16lf %.16lf\n", k, diff10, diff20, diff21);
            int index =(int) (diff20 / diff21 - 0.5); // -1 for index
            int pos = index * rs + k * ms;
            printf("dftw-genericbuf bytwiddle imaginary part error, index %d pos %d ~ val %f\n", index, pos+1, iio[pos]);
            
            // if(pos+1 != corruptedIndex) 
            // {
            //   printf("uncorrected error!\n true pos: %d, current pos: %d\n", corruptedIndex, pos);
            //   exit(1);
            // }

            printf("original value: %f\n", (inAddr+1)[pos]);
            iio[pos] -= diff20;
            // printf("diff: %f %f\n", (inAddr+1)[pos], iio[pos] - memoryChecksum1[2*(k-mb)+1]);
            // iio[pos] = (inAddr+1)[pos];
            (inAddr+1)[pos] = iio[pos];
            printf("corrected value: %f\n", (inAddr+1)[pos]);
         }
       }
      }
     count += 2;
}

static int applicable0(const S *ego,
		       INT r, INT irs, INT ors,
		       INT m, INT v,
		       INT mcount)
{
     return (1
	     && v == 1
	     && irs == ors
	     && mcount >= ego->batchsz
	     && mcount % ego->batchsz == 0
	     && r >= 64 
	     && m >= r
	  );
}

static int applicable(const S *ego,
		      INT r, INT irs, INT ors,
		      INT m, INT v,
		      INT mcount,
		      const planner *plnr)
{
     if (!applicable0(ego, r, irs, ors, m, v, mcount))
	  return 0;
     if (NO_UGLYP(plnr) && m * r < 65536)
	  return 0;

     return 1;
}

// int injectIndex = -1;
// int diceDiff;

static void dobatch(const P *ego, INT mb, INT me, R *buf, R *rio, R *iio)
{
     plan_dft *cld;
     INT ms = ego->ms;

     bytwiddle(ego, mb, me, buf, rio, iio);

     cld = (plan_dft *) ego->cld;

     cld->apply(ego->cld, buf, buf + 1, buf, buf + 1);
     X(cpy2d_pair_co)(buf, buf + 1,
		      rio + ms * mb, iio + ms * mb,
		      me-mb, 2 * BATCHDIST(ego->r), ms,
		      ego->r, 2, ego->rs);
}

/*************/
void finalOutputCorrection(int i, R * rio, R * iio, R delta3, R * buf, const P * ego)
{
     printf("%d~%d error detected\n", 4*i, 4*i+3); //exit(0);
     // must be calculational error since memory error is corrected in bytwiddle;
     // if memory error, interval is too short. However, it can still be handled by recovery from backup
     // exit(0);
     bool recalc = true;
     INT ms = ego->ms;
     INT mb = 4*i;
     INT me = 4*i + ego->batchsz;
     while(recalc)
     {

          // dobatch(ego, 4*i, 4*i + ego->batchsz, buf, inAddr, inAddr+1);
          // decompose dobatch

          // modify the i-th checksum
          count = 2*i;
          bytwiddle(ego, mb, me, buf, inAddr, inAddr+1);

          plan_dft * cld = (plan_dft *) ego->cld;
          cld->apply(ego->cld, buf, buf + 1, buf, buf + 1);

          INT r = ego->r;
          int cn = r;
          R or00 = 0, or01 = 0, or10 = 0, or11 = 0, or20 = 0, or21 = 0; 
          R * rio0;
          for(int k=0; k<4; k++)
          {
               rio0 = buf + 2 * BATCHDIST(r) * k + 0;
               int i;
               for(i=0; i<cn - 3; i+=3)
               {
                    or00 += rio0[0], or01 += rio0[1];
                    or10 += rio0[2], or11 += rio0[3];
                    or20 += rio0[4], or21 += rio0[5];
                    rio0 += 6;  
               }
               or00 += rio0[0], or01 += rio0[1];
               if((i+1)<cn) 
               {
                    or10 += rio0[2], or11 += rio0[3];
               }
          }

          R r1 = 0.866025403784438818632906986749731004238128662;
          
          R cksReal = outputChecksum[2*i] -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21;
          R cksIm = outputChecksum[2*i+1] -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20;
          // printf("%d output: %f %f\n", k, -or00 + 0.5*or10 + r1*or11 + 0.5*or20 - r1*or21, -or01 + 0.5*or11 - r1*or10 + 0.5*or21 + r1*or20);
          recalc = (cksReal>delta3 || cksReal<-delta3 || cksIm>delta3 || cksIm<-delta3);
          if(recalc) printf("error found in correction: %f %f\n", cksReal, cksIm); //exit(0);
     }
     // result verified, copy
     X(cpy2d_pair_co)(buf, buf + 1,
       rio + ms * mb, iio + ms * mb,
       me-mb, 2 * BATCHDIST(ego->r), ms,
       ego->r, 2, ego->rs);          
}

void finalOutputVerification(int cn, int size, R * rio, R * iio, R * buf, R delta3, const P * ego)
{
     int outSumSize = size * 2; //2*(vl/4); // vl/4, 4 fft as a group
     // int outSumSize = (ego->me - ego->mb) * 2 / ego->batchsz;
     R * outSum1 = (R *) malloc(outSumSize *sizeof(R));
     R * outSum2 = (R *) malloc(outSumSize *sizeof(R));
     R * outSum3 = (R *) malloc(outSumSize *sizeof(R));
     for(int i=0; i<outSumSize; i++)
          outSum1[i] = 0;
     for(int i=0; i<outSumSize; i++)
          outSum2[i] = 0;
     for(int i=0; i<outSumSize; i++)
          outSum3[i] = 0;

     R * posos1;    // pos of grouped output
     R * posos2;
     R * posos3;

     R * posR; // pos of real part
     R * posI; // pos of im part
     // R * pos1; 
     // R * pos2; 

     posR = rio, posI = iio;

     int i;
     for(i=0; i<cn-3; i+=3)
     {
          posos1 = outSum1;
          posos2 = outSum2;
          posos3 = outSum3;
          for(int j=0; j<size; j++)
          {
               posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos1 += 2, posR += 8;
          }
          for(int j=0; j<size; j++)
          {
               posos2[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos2[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos2 += 2, posR += 8;
          }
          for(int j=0; j<size; j++)
          {
               posos3[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos3[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos3 += 2, posR += 8;
          }
     }
     if(i+1 < cn)
     {
          posos1 = outSum1;
          posos2 = outSum2;
          for(int j=0; j<size; j++)
          {
               posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos1 += 2, posR += 8;
          }
          for(int j=0; j<size; j++)
          {
               posos2[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos2[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos2 += 2, posR += 8;
          }
     }
     else
     {
          posos1 = outSum1;
          for(int j=0; j<size; j++)
          {
               posos1[0] += posR[0] + posR[2] + posR[4] + posR[6];
               posos1[1] += posR[1] + posR[3] + posR[5] + posR[7];
               posos1 += 2, posR += 8;
          }
     }
     // printf("calculation done\n");

     R diffReal;
     R diffIm;
     R r1 = 0.866025403784438818632906986749731004238128662;

     R o00, o10, o20, o01, o11, o21;

    R setRoe = 5.67 * 1e-7;

     bool error;
     for(int i=0; i<size; i++)
     {
          o00 = outSum1[2*i], o01 = outSum1[2*i+1];
          o10 = outSum2[2*i], o11 = outSum2[2*i+1];
          o20 = outSum3[2*i], o21 = outSum3[2*i+1];

          diffReal = outputChecksum[2*i] - o00 + 0.5*o10 + r1*o11 + 0.5*o20 - r1*o21;
          diffIm = outputChecksum[2*i+1] - o01 + 0.5*o11 - r1*o10 + 0.5*o21 + r1*o20;

          error = (diffReal>delta3 || diffReal<-delta3 || diffIm>delta3 || diffIm<-delta3);
          if(error) finalOutputCorrection(i, rio, iio, delta3, buf, ego);
     }// end for

}

/*************/


static void apply(const plan *ego_, R *rio, R *iio)
{
     const P *ego = (const P *) ego_;

     int cn = ego->r; // current FFT_2 size, cn = r
     rA2 = (R *) malloc(cn*2*sizeof(R) + 2);
     checksumVectorRAGeneration2(cn, rA2);
     // printf("rA generation done\n");

     int checkNum = ego->batchsz;
     int size = (ego->me - ego->mb) / checkNum; // number of FFTs after group
     outputChecksum = (R *) malloc(size*2*sizeof(R));

     memoryChecksum1 = (R *) malloc(checkNum*2*sizeof(R));
     memoryChecksum2 = (R *) malloc(checkNum*2*sizeof(R));
     // inject memory error ~~~
     // rio[243522] += 20000;
     count = 0;

     R *buf = (R *) MALLOC(sizeof(R) * 2 * BATCHDIST(ego->r) * ego->batchsz,
			   BUFFERS);

     // srand(6666);
     // {
     //      int n = (ego->me - ego->mb) / ego->batchsz;
     //      injectIndex = (rand() % n) * ego->batchsz;
     // }

     // diceDiff = dice - ego->r;

     INT m;

     for (m = ego->mb; m < ego->me; m += ego->batchsz)
          dobatch(ego, m, m + ego->batchsz, buf, rio, iio);

     // {
     //    srand(6666);
     //    int num = rand() % (33554432*2);
     //    rio[num] += 1e-7;
     // }     

        R delta3 = 1e-5;
     // R delta3 = 5.7*1e-7;

     // inject memory error  ~~~
     // rio[3425634] += 40000;

     finalOutputVerification(cn, size, rio, iio, buf, delta3, ego);

     A(m == ego->me);

     X(ifree)(buf);
}

static void awake(plan *ego_, enum wakefulness wakefulness)
{
     P *ego = (P *) ego_;
     X(plan_awake)(ego->cld, wakefulness);

     switch (wakefulness) {
	 case SLEEPY:
	      X(triggen_destroy)(ego->t); ego->t = 0;
	      break;
	 default:
	      ego->t = X(mktriggen)(AWAKE_SQRTN_TABLE, ego->r * ego->m);
	      break;
     }
}

static void destroy(plan *ego_)
{
     P *ego = (P *) ego_;
     X(plan_destroy_internal)(ego->cld);
}

static void print(const plan *ego_, printer *p)
{
     const P *ego = (const P *) ego_;
     p->print(p, "(dftw-genericbuf/%D-%D-%D%(%p%))",
	      ego->batchsz, ego->r, ego->m, ego->cld);
}

static plan *mkcldw(const ct_solver *ego_,
		    INT r, INT irs, INT ors,
		    INT m, INT ms,
		    INT v, INT ivs, INT ovs,
		    INT mstart, INT mcount,
		    R *rio, R *iio,
		    planner *plnr)
{
     const S *ego = (const S *)ego_;
     P *pln;
     plan *cld = 0;
     R *buf;

     static const plan_adt padt = {
	  0, awake, print, destroy
     };
     
     UNUSED(ivs); UNUSED(ovs); UNUSED(rio); UNUSED(iio);

     A(mstart >= 0 && mstart + mcount <= m);
     if (!applicable(ego, r, irs, ors, m, v, mcount, plnr))
          return (plan *)0;

     buf = (R *) MALLOC(sizeof(R) * 2 * BATCHDIST(r) * ego->batchsz, BUFFERS);
     cld = X(mkplan_d)(plnr,
			X(mkproblem_dft_d)(
			     X(mktensor_1d)(r, 2, 2),
			     X(mktensor_1d)(ego->batchsz,
					    2 * BATCHDIST(r),
					    2 * BATCHDIST(r)),
			     buf, buf + 1, buf, buf + 1
			     )
			);
     X(ifree)(buf);
     if (!cld) goto nada;

     pln = MKPLAN_DFTW(P, &padt, apply);
     pln->slv = ego;
     pln->cld = cld;
     pln->r = r;
     pln->m = m;
     pln->ms = ms;
     pln->rs = irs;
     pln->batchsz = ego->batchsz;
     pln->mb = mstart;
     pln->me = mstart + mcount;

     {
	  double n0 = (r - 1) * (mcount - 1);
	  pln->super.super.ops = cld->ops;
	  pln->super.super.ops.mul += 8 * n0;
	  pln->super.super.ops.add += 4 * n0;
	  pln->super.super.ops.other += 8 * n0;
     }
     return &(pln->super.super);

 nada:
     X(plan_destroy_internal)(cld);
     return (plan *) 0;
}

static void regsolver(planner *plnr, INT r, INT batchsz)
{
     S *slv = (S *)X(mksolver_ct)(sizeof(S), r, DECDIT, mkcldw, 0);
     slv->batchsz = batchsz;
     REGISTER_SOLVER(plnr, &(slv->super.super));

     if (X(mksolver_ct_hook)) {
	  slv = (S *)X(mksolver_ct_hook)(sizeof(S), r, DECDIT, mkcldw, 0);
	  slv->batchsz = batchsz;
	  REGISTER_SOLVER(plnr, &(slv->super.super));
     }

}

void X(ct_genericbuf_register)(planner *p)
{
     static const INT radices[] = { -1, -2, -4, -8, -16, -32, -64 };
     static const INT batchsizes[] = { 4, 8, 16, 32, 64 };
     unsigned i, j;

     for (i = 0; i < sizeof(radices) / sizeof(radices[0]); ++i)
	  for (j = 0; j < sizeof(batchsizes) / sizeof(batchsizes[0]); ++j)
	       regsolver(p, radices[i], batchsizes[j]);
}
