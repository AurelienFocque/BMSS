
#include "pari/pari.h"
#include "pari/paripriv.h"
#include <time.h>
#define BMSSPREC 1
static clock_t temps_total;
static clock_t temps_kernel;
static clock_t temps_equadiff;
static clock_t temps_euclide;
static clock_t temps_comp;

//THESE TWO FONCTIONS ARE USEFULL FOR NEWTON ITERATIONS
static long find_size(long l)
{   
  long ret=1;
  long tmp=l;
  while(tmp>1)
  {
      tmp=tmp>>1;
      ret++;
  }
  if(l==(1<<(ret-1))){ret--;}
  return ret;
}
static void find_list(long *list,long l)
{   long *tmp=(list)+(find_size(l));
    *tmp=l;
    while(l>1)
    {
      l=(l%2)*((l+1)>>1)+(l%2==0)*(l>>1);
      tmp--;
      *tmp=l;
    }
    return;
}
static 
GEN Fq_ui(long k,GEN T,GEN p)
{
  if(T==NULL)
    return mkintn(1,k);
  else 
    return mkpoln(1,mkintn(1,k));
}
static long 
get_size(long l)
{
  long res=0;
  while(l>0)
  {
    l=l>>1;	
    res++;
  }
  return res;
}
static GEN
Zq_inv(GEN b, GEN T, GEN q, GEN p, long e)
{
  return e==1 ? Fq_inv(b, T, p):
         typ(b)==t_INT ? Fp_inv(b, q):  ZpXQ_inv(b, T, p, e);
}



static GEN
Zq_sqrt(GEN b, GEN T, GEN q, GEN p, long e)
{
  return e==1 ? Fq_sqrt(b, T, q):
         typ(b)==t_INT ? Zp_sqrt(b, p, e):  ZpXQ_sqrt(b, T, p, e);
}

static GEN
Zq_divexact(GEN a, GEN b)
{
  return typ(a)==t_INT ? diviiexact(a, b): ZX_Z_divexact(a, b);
}

static long
Zq_pval(GEN a, GEN p)
{
  return typ(a)==t_INT ? Z_pval(a, p): ZX_pval(a, p);
}

static GEN
Zq_Z_div_safe(GEN a, GEN b, GEN T, GEN q, GEN p, long e)
{
  if(gcmp0(a)==1){return Fq_ui(0,T,p);}
  long v;
  if (e==1) return Fq_div(a, b, T, q);
  v = Z_pvalrem(b, p, &b);
  if (v>0)
  {
    long w = Z_pval(Q_content(a), p);
    if (v>w) {return NULL;}// if curves it may happen
    a = Zq_divexact(a, powiu(p,v));
  }
  return Fq_Fp_mul(a, Fp_inv(b, q), T, q);
}

static GEN
Zq_div_safe(GEN a, GEN b, GEN T, GEN q, GEN p, long e)
{
  if (e==1) return Fq_div(a, b, T, q);
  if(typ(b)==t_INT){return Zq_Z_div_safe(a, b, T, q, p, e);}
  GEN Q=Q_content(b);
  GEN at=Zq_Z_div_safe(a, Q, T, q, p, e);
  GEN bt=Zq_Z_div_safe(b, Q, T, q, p, e);
  if(at==NULL){gerepileupto(avma,0);return NULL;}
  Q=Fq_div(at, bt, T, q);
  gerepileupto(avma,Q);
  return Q;
}

static GEN
ZqX_liftroot(GEN f, GEN a, GEN T, GEN p, long e)
{
  return T ? ZpXQX_liftroot(f, a,T , p, e): ZpX_liftroot(f, a, p, e);
}

static GEN FqX_mul2(GEN P,GEN T,GEN p)
{
  if(T!=NULL)
  {
	  return FqX_mulu(P,2,T,p);
  }
  long d=lg(P)-3;
  long k=0;
  GEN ret=cgetg(lg(P),t_POL);
  for(k=0;k<=d;k++)
    gel(ret,2+k)=Fp_red(shifti(gel(P,2+k),1),p);
  return ret;
}

static GEN FqX_modXn(GEN P,long n,GEN T,GEN p)// works in Fq
{	
  if(T!=NULL)
  {
    GEN ret=RgX_copy(P);
    long k =n;
    while(k<lg(P)-2)
    {	
      gel(ret,2+k)=mkpoln(1,gen_0);
      k++;
    }
    gerepileupto(avma,ret);
    return FqX_red(ret,T,p);
  }
  GEN ret=RgX_copy(P);
  long k =n;
  while(k<lg(P)-2)
  {	
    gel(ret,2+k)=mkintn(1,0);
    k++;
  }
  gerepileupto(avma,ret);
  return RgX_to_FpX(ret,p);
}
static 
GEN RgXn_mul_basecase(GEN P,GEN Q,long n)
{
  long d =lg(P)+lg(Q)-3;
  long min =(d>n+2)*(n+2)+(d<=n+2)*d;
  GEN ret=cgetg(min,t_POL);
  long k=0;
  long j;
  d=min-3;


  while(k<=d)
  {
    gel(ret,2+k)=gen_0;
    k++;
  }
  k=0;
  while(k<=lg(P)-3)
  {	
    j=0;
    while(j+k<n)
    {
      if(j>lg(Q)-3){break;}
      gel(ret,2+j+k)=gadd(gel(ret,2+j+k),gmul(gel(P,2+k),gel(Q,2+j)));
      j++;
    }
    k++;
  }

  return ret;
}
static 
GEN RgXn_sqr_basecase(GEN P,long n)
{
  long d =2*lg(P)-3;
  long min =(d>n+2)*(n+2)+(d<=n+2)*d;
  GEN ret=cgetg(min,t_POL);
  long k=0;
  long j;
  d=min-3;

	
  while(k<=d)
  {
    gel(ret,2+k)=gen_0;
    k++;
  }
  k=0;
  while(k<=lg(P)-3)
  {	
    j=k;
    if(j+k<n)
    {
      gel(ret,2+j+k)=gadd(gel(ret,2+j+k),gsqr(gel(P,2+k)));
      j++;
    }
    while(j+k<n)
    {
      if(j>lg(P)-3){break;}

      gel(ret,2+j+k)=gadd(gel(ret,2+j+k),gmulgs(gmul(gel(P,2+k),gel(P,2+j)),2));
      j++;
    }
    k++;
  }

  return ret;
}

static GEN FqXn_mul_karatsuba(GEN P,GEN Q,long n,GEN T,GEN p)
//doesn't reduce coefficients to be faster, they will be reduced in FqXn_mul
{	
  long s=RgX_equal(P,mkpoln(1,gen_0))||RgX_equal(Q,mkpoln(1,gen_0));
  if(T==NULL)
  {
    if(s){return mkpoln(1,gen_0);}
    if (degpol(P) + degpol(Q) < n) return RgX_mul(P,Q);
    if(n<35)
      return RgXn_mul_basecase(P,Q,n);
  }
  else
  {
    if(s){return mkpoln(1,mkpoln(1,gen_0));}
    if (degpol(P) + degpol(Q) < n) return RgX_mul(P,Q);
    if(n<35)
      return RgXn_mul_basecase(P,Q,n);
  }
  long B=(7*n)/10;
  GEN ret;
  GEN P1=RgX_shift(FqX_modXn(P,n,T,p),-B);
  GEN Q1=RgX_shift(FqX_modXn(Q,n,T,p),-B);
  GEN P2=FqX_modXn(P,B,T,p);
  GEN Q2=FqX_modXn(Q,B,T,p);
  GEN tmp;
  tmp=FqX_mul(P2,Q2,T,p);
  tmp=FqX_modXn(tmp,n,T,p);
  GEN tmp2=FqXn_mul_karatsuba(P1,FqX_modXn(Q2,n-B,T,p),n-B,T,p);
  GEN tmp3=FqXn_mul_karatsuba(FqX_modXn(P2,n-B,T,p),Q1,n-B,T,p);
  ret=RgX_add(tmp,RgX_add(RgX_shift(tmp2,B),RgX_shift(tmp3,B)));
  gerepileupto(avma,ret);
  return ret;
}
static GEN FqXn_sqr_karatsuba(GEN P,long n,GEN T,GEN p)
//doesn't reduce coefficients to be faster, they will be reduced in FqXn_mul
{	
  long s=RgX_equal(P,mkpoln(1,gen_0));
  if(T==NULL)
  {
    if(s){return mkpoln(1,gen_0);}
    if (2*degpol(P)  < n) return RgX_sqr(P);
    if(n<35)
      return RgXn_sqr_basecase(P,n);
  }
  else
  {
    if(s){return mkpoln(1,mkpoln(1,gen_0));}
    if (2*degpol(P)  < n) return RgX_sqr(P);
    if(n<35)
      return RgXn_sqr_basecase(P,n);
  }
  long B=(7*n)/10;
  GEN ret;
  GEN P1=RgX_shift(FqX_modXn(P,n,T,p),-B);
  GEN P2=FqX_modXn(P,B,T,p);
  GEN tmp;
  tmp=FqX_sqr(P2,T,p);
  tmp=FqX_modXn(tmp,n,T,p);
  GEN tmp2=FqXn_mul_karatsuba(P1,FqX_modXn(P2,n-B,T,p),n-B,T,p);
  ret=RgX_add(tmp,RgX_muls(RgX_shift(tmp2,B),2));
  gerepileupto(avma,ret);
  return ret;
}
static 
GEN FqXn_mul(GEN f, GEN g, long n,GEN T,GEN p)
{
  GEN ret;
  if(n<35){ret=FqX_red(RgXn_mul_basecase(f,g,n),T,p);setvarn(ret,0);return ret;}
  else if(n<80){ret=FqX_red(FqXn_mul_karatsuba(f,g,n,T,p),T,p);setvarn(ret,0);return ret;}
  else{return FqX_modXn(FqX_mul(f,g,T,p),n,T,p);}
}
static 
GEN FqXn_sqr(GEN f, long n,GEN T,GEN p)
{
  GEN ret;
  if(n<35){ret=FqX_red(RgXn_sqr_basecase(f,n),T,p);setvarn(ret,0);return ret;}
  else if(n<80){ret=FqX_red(FqXn_sqr_karatsuba(f,n,T,p),T,p);setvarn(ret,0);return ret;}
  else{return FqX_modXn(FqX_sqr(f,T,p),n,T,p);}
}
static GEN FqX_mulup(GEN P,GEN Q,long n,GEN T,GEN p)//works in Fq
// calculate P*Q/x^n (without the low degree coefficients)
{
	
  long d=lg(P)+lg(Q)-5-n;
  if(d<=2||d>=110)
  {
    return RgX_shift(FqX_mul(P,Q,T,p),-n);
  }
  GEN ret=FqX_red(RgX_recip(FqXn_mul(RgX_recip(P),RgX_recip(Q),d,T,p)),T,p);
  // Now we need to fix the eventual loss of a 0 in high degree terms
  d=d-1-(lg(ret)-3);
  ret=RgX_shift(ret,d);
  return ret;
}
static GEN FqX_sqrup(GEN P,long n,GEN T,GEN p)
{
  long d=2*lg(P)-5-n;
  if(d<=2||d>=110)
  {
    return RgX_shift(FqX_sqr(P,T,p),-n);
  }

  GEN ret=FqX_red(RgX_recip(FqXn_sqr(RgX_recip(P),d,T,p)),T,p);
  // Now we need to fix the eventual loss of a 0 in high degree terms
  d=d-1-(lg(ret)-3);
  ret=RgX_shift(ret,d);
  return ret;
}
static GEN FqX_mulup_modxn(GEN P,GEN Q,long t1,long t2,GEN T,GEN p)
// calculate (P*Q/x^t1) mod x^t2 (without the low degree coefficients) 
{	
  if(t2>110)
    return RgX_shift(FqX_modXn(FqX_mul(P,Q,T,p),t2,T,p),-t1);
  else if(2*t1>t2)
    return FqX_add(FqX_mulup(FqX_modXn(Q,t1,T,p),FqX_modXn(P,t1,T,p),t1,T,p),FqX_add(FqXn_mul(RgX_shift(P,-t1),FqX_modXn(Q,t1,T,p),t2-t1,T,p),FqXn_mul(RgX_shift(Q,-t1),FqX_modXn(P,t1,T,p),t2-t1,T,p),T,p),T,p);
  else
    return FqX_add(FqX_add(FqX_mulup(FqX_modXn(Q,t1,T,p),FqX_modXn(P,t1,T,p),t1,T,p),FqX_add(FqXn_mul(RgX_shift(P,-t1),FqX_modXn(Q,t1,T,p),t2-t1,T,p),FqXn_mul(RgX_shift(Q,-t1),FqX_modXn(P,t1,T,p),t2-t1,T,p),T,p),T,p),RgX_shift(FqXn_mul(RgX_shift(P,-t1),RgX_shift(Q,-t1),t2-2*t1,T,p),t1),T,p);
}
static GEN FqX_Newton_iteration_inv(GEN I,GEN P,long t1,long t2,GEN T,GEN p)
//given I=1/P mod x^t1 returns 1/P mod x^t2
{	
  return FqX_sub(I,RgX_shift(FqXn_mul(FqX_mulup_modxn(I,P,t1,t2,T,p),I,t2-t1,T,p),t1),T,p);
}
static GEN comp_modxn(GEN H,GEN S,long n,GEN T,GEN p)// HoS=1+a'S(x)^2+b'S(x)^3 
{	
  clock_t tmp2=clock();	
  GEN ret;
  GEN tmpol;
  if(lg(H)==6)
  {	
    tmpol=FqX_sqr(S,T,p);
    ret=FqXn_mul(tmpol,S,n,T,p);	
    ret=FqX_add(FqX_Fq_add(FqX_Fq_mul(tmpol,gel(H,4),T,p),gen_1,T,p),FqX_Fq_mul(ret,gel(H,5),T,p),T,p);
    ret=FqXn_mul(ret,RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);temps_comp+=clock()-tmp2;
    return ret;
  }
  if(lg(H)==5)
  {
    tmpol=FqX_sqr(S,T,p);
    ret=FqX_Fq_add(FqX_Fq_mul(tmpol,gel(H,4),T,p),gen_1,T,p);
    ret=FqXn_mul(ret,RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);temps_comp+=clock()-tmp2;
    return ret;
  }
  else
  {
    ret=FqXn_mul(ret,RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);temps_comp+=clock()-tmp2;
    return ret;
  }
}

static GEN FqX_div2(GEN P,GEN T,GEN p)
{	
  if(T!=NULL)
  {
    return FqX_Fq_mul(P,Fq_inv(mkpoln(1,gen_2),T,p),T,p);
  }
  long d=lg(P)-3;
  if(d==-1){return mkpoln(1,gen_0);}
  GEN ret=cgetg(lg(P),t_POL);
  long k =0;
  GEN tmp;
  for(k=0;k<=d;k++)
  {
    tmp=gel(P,k+2);
    if(mod2(tmp)==0)
    {
      gel(ret,k+2)=shifti(tmp,-1);
    }
    else
    {
      gel(ret,k+2)=shifti(addii(tmp,p),-1);
    }

  }
  gerepileupto(avma,ret);
  return ret;
}
static GEN FqXn_sqrt(GEN P,long n, GEN T,GEN p)
// requires find_list,find_size and FqX_Newton_iteration_inv
{
  if(Fq_issquare(gel(P,2),T,p)==0)
    return NULL;
  GEN ret;
  GEN k,i;
  ret=mkpoln(1,Fq_sqrt(gel(P,2),T,p));
  i=mkpoln(1,Fq_inv(Fq_mulu(gel(ret,2),2,T,p),T,p));
  long t=find_size(n)+1;
  long tab[t];
  find_list(tab,n);
  long j=0;
  while(j<t-1)
  {	//we compute the inverse and the sqrt at the same time, ret denotes the sqrt and i the inverse        
    k=FqX_sub(RgX_shift(FqX_modXn(P,tab[j+1],T,p),tab[j]-tab[j+1]),FqX_sqrup(ret,tab[j+1]-tab[j],T,p),T,p);
    if(j>0)
      i=FqX_Newton_iteration_inv(i,FqX_mul2(ret,T,p),tab[j-1],tab[j],T, p);	
    ret=FqX_add(ret,RgX_shift(FqXn_mul(i,k,tab[j],T,p),tab[j+1]-tab[j]),T,p);
    j++;
  }
  gerepileupto(avma,ret);
  return ret;  
}
static GEN FqXn_inv(GEN P, long n,GEN T,GEN p)
{  
  GEN ret=mkpoln(1,Fq_inv(gel(P,2),T,p));
  long t=find_size(n)+1;
  long tab[t];
  find_list(tab,n);
  long k=0;
  while(k<t-1)
  {	
    ret=FqX_Newton_iteration_inv(ret,P,tab[k],tab[k+1],T,p);
    k++;
  }
  return ret;
    
}
static GEN poly_integrale(GEN P,GEN T,GEN p,GEN pp,long e)
//return sum(P[i]x^(i+1)/2*i+1)
{	
  long d=lg(P)-3;
  if(d==-1)
  {
    return mkpoln(1,Fq_ui(0,T,p));
  }
  GEN ret=cgetg(lg(P)+1,t_POL);
  gel(ret,2)=Fq_ui(0,T,p);
  long k =0;
 
  while(k<=d)
  {	
    gel(ret,2+k+1)=Zq_div_safe(gel(P,2+k),Fq_ui(2*k+1,T,p),T,p,pp,e);
    if(gel(ret,2+k+1)==NULL){return NULL;}
    k++;
  }

  //pari_printf("ret=%Ps\n",ret);
  return ret;
}
static GEN find_S(long m,GEN G,GEN H,GEN T,GEN p,GEN pp,long e)
//inspired of Luka De Feo thesis.
// requires p<2*m+1
//returns the approximation of the taylor serie solution of G*(S'^2)=(S/x)*(HoS) mod x^m
{   
  clock_t tmp=clock();	
  GEN S;
  GEN ki;
  GEN K;
  long t=find_size(m)+1;
  long tab[t];
  find_list(tab,m);
  long k=1;
  //INITIALISATION
  // GS'^2 
  GEN Dn;
  // 1/S'^2G 
  GEN D=mkpoln(1,Fq_ui(1,T,p));
  //Sqrt(G) and sqrt(1/G) 
  //pari_printf("g0=%Ps\n",gel(G,2));exit(0);
  GEN sG=mkpoln(1,Fq_ui(1,T,p));
  GEN isG=mkpoln(1,Fq_ui(1,T,p));
  S=mkpoln(2,Fq_ui(1,T,p),Fq_ui(0,T,p));
  while(k<t-2)
  {	
    Dn=FqXn_mul(G,FqX_sqr(FqX_deriv(S,T,p),T,p),tab[k+1],T,p);	
    //Dn=(G*S'^2) 

    D=FqX_Newton_iteration_inv(D,FqX_modXn(Dn,tab[k],T,p),tab[k-1],tab[k],T,p);
    // D=1/(G*S'^2) to the precision tab[k]
	
    sG=FqX_add(sG,RgX_shift(FqXn_mul(FqX_div2(isG,T,p),FqX_sub(RgX_shift(G,tab[k-1]-tab[k]),FqX_sqrup(sG,tab[k]-tab[k-1],T,p),T,p),tab[k-1],T,p),tab[k]-tab[k-1]),T,p);
    //computes sqrt(G) to the precision tab[k]

    isG=FqX_Newton_iteration_inv(isG,sG,tab[k-1],tab[k],T,p);

    //computes 1/sqrt(G) to the precision tab[k]
    ki=RgX_shift(FqXn_mul(RgX_shift(FqX_sub(comp_modxn(H,S,tab[k+1],T,p),Dn,T,p),-tab[k]+1),FqXn_mul(D,isG,tab[k+1]-tab[k]+1,T,p),tab[k+1]-tab[k]+1,T,p),tab[k]-1);

    //ki=((S/x)*HoS-*GS'^2)*D*isG using the fact that x^tab[k]-1 | (S/x)*HoS-*GS'^2
    // NB: there may be a way to calculate ki quicker computing only the high degree terms
    K=poly_integrale(ki,T,p,pp,e);
    if (K==NULL){return NULL;}
    S=FqX_add(S,RgX_shift(FqXn_mul(FqXn_mul(RgX_shift(K,-tab[k]),sG,tab[k+1]+1-tab[k],T,p),FqX_deriv(S,T,p),tab[k+1]+1-tab[k],T,p),tab[k]),T,p);

    //S=S+K*sG*S' since K=x^tab[k]*B via a shift we can compute mod x^tab[k+1]-tab[k]
    k++;

  }

  // we need to compute S one step forward each time but the last time.

  Dn=FqXn_mul(G,FqX_sqr(FqX_deriv(S,T,p),T,p),tab[k+1]-1,T,p);
	

  D=FqX_Newton_iteration_inv(D,FqX_modXn(Dn,tab[k],T,p),tab[k-1],tab[k],T,p);	

  sG=FqX_add(sG,RgX_shift(FqXn_mul(FqX_div2(isG,T,p),FqX_sub(RgX_shift(G,tab[k-1]-tab[k]),FqX_sqrup(sG,tab[k]-tab[k-1],T,p),T,p),tab[k-1],T,p),tab[k]-tab[k-1]),T,p);
  isG=FqX_Newton_iteration_inv(isG,sG,tab[k-1],tab[k],T,p);
  //

  ki=RgX_shift(FqXn_mul(RgX_shift(FqX_sub(comp_modxn(H,S,tab[k+1]-1,T,p),Dn,T,p),-tab[k]+1),FqXn_mul(D,isG,tab[k+1]-tab[k],T,p),tab[k+1]-tab[k],T,p),tab[k]-1);

  K=poly_integrale(ki,T,p,pp,e);
  if (K==NULL){return NULL;}
  S=FqX_add(S,RgX_shift(FqXn_mul(FqXn_mul(RgX_shift(K,-tab[k]),sG,tab[k+1]-tab[k],T,p),FqX_deriv(S,T,p),tab[k+1]-tab[k],T,p),tab[k]),T,p);
    
  gerepileupto(avma,S);
  temps_equadiff+=clock()-tmp;

  return S;
}
static GEN D_from_euclide_truncated(GEN R,long l,GEN T, GEN p)
//suitable for Fq
// given R=D.reverse()/N.reverse() mod x^2l return D
{	
  clock_t tmpt=clock();
  pari_sp ltop=avma;
  GEN r1=R;
  GEN r0;
  if(T==NULL)
    r0=RgX_shift(mkpoln(1,gen_1),2*l);
  else
    r0=RgX_shift(mkpoln(1,mkpoln(1,gen_1)),2*l);
  GEN tmp;
  while(lg(r1)-3>=l)
  {	
    tmp=r1;
    r1=FqX_rem(r0,r1,T,p);
    r0=tmp;
  }
  r1=FqX_normalize(RgX_recip(r1),T,p);
  if(Fq_issquare(gel(r1,2),T,p)==0){temps_euclide+=clock()-tmpt;gerepileall(ltop,0);return NULL;}
  gerepileupto(avma,r1);
  temps_euclide+=clock()-tmpt;
  return r1;
}

static GEN D_from_HGCD(GEN R,long l,GEN T, GEN p)
// given R=D.reverse()/N.reverse() mod x^2l return D
// not suitable for Fq
{
  clock_t tmpt=clock();
  GEN ret;
  GEN r1=R;
  GEN r0=RgX_shift(mkpoln(1,gen_1),2*l);
  GEN M=FpXQX_halfgcd(r0,r1,T, p);
  ret=gel( row(M,2),2);
  //ret stands for N.reverse() atm
  ret=FqXn_mul(FqX_red(ret,T,p),FqX_modXn(R,l,T,p),l,T,p);
  ret=FqX_normalize(RgX_recip(ret),T,p);
  if(Fq_issquare(gel(ret,2),T,p)==0)
  {
    gerepileupto(avma,0);
    temps_euclide+=clock()-tmpt;
    return NULL;
  }
  gerepileupto(avma,ret);
  temps_euclide+=clock()-tmpt;
  return ret;
}
GEN find_kernel_LS(GEN a4,GEN a6,long l,GEN b4,GEN b6,GEN pp1,GEN T,GEN p,GEN pp,long e)
//requires both the isogeny to be normalized and separable.
//suitable for padics when l+2*BMSSPREC>pp.
//doesn't require sigma known.
//returns the kernelpolynomial.
{   
  pari_sp ltop=avma;
  GEN G,H;
  G=mkpoln(4,a6,a4,Fq_ui(0,T,p),Fq_ui(1,T,p));
  H=mkpoln(4,b6,b4,Fq_ui(0,T,p),Fq_ui(1,T,p));
  GEN S=find_S(2*l+1,G,H,T,p,pp,e);
  if(S==NULL){return NULL;}
  GEN R=RgX_shift(S,-1);
  R=FqX_red(R,T,pp);
  GEN D;
  if(l<120)
    D=D_from_euclide_truncated(R,l,T,pp);
  if(l>=120)
    D=D_from_HGCD(R,l,T,pp);	
  if(D==NULL){return NULL;}
  D=FqXn_sqrt(D,l,T,pp);
  D=FqX_normalize(D,T,pp);	
  if(degree(D)!=(l-1)/2){gerepileupto(ltop,0);return NULL;}
  gerepileupto(avma,D);
  return D;
}
static
GEN FqX_NewtonGen(GEN S,long l,GEN a4,GEN a6,GEN pp1,GEN T,GEN p)
{
  long d =lg(S)-3;
  GEN Ge=cgetg(3+d,t_POL);
  gel(Ge,2)=Fq_ui((l-1)/2,T,p);
  long k =2;
  gel(Ge,3)=pp1;	
  gel(Ge,2+k)=Fq_mul(Fq_inv(Fq_ui(4*k-2,T,p),T,p),Fq_sub(gel(S,4+k-2),Fq_mul(a4,Fq_mul(Fq_ui(4*k-6,T,p),gel(Ge,k),T,p),T,p),T,p),T,p);
  k++;
  while(k<=d)
  {	
    gel(Ge,2+k)=Fq_mul(Fq_inv(Fq_ui(4*k-2,T,p),T,p),Fq_sub(Fq_sub(gel(S,4+k-2),Fq_mul(a4,Fq_mul(Fq_ui(4*k-6,T,p),gel(Ge,k),T,p),T,p),T,p),Fq_mul(a6,Fq_mul(Fq_ui(4*k-8,T,p),gel(Ge,k-1),T,p),T,p),T,p),T,p);
    k++;
  }
  gel(Ge,2)=Fq_ui(0,T,p);
  k=2;
  while(k<=d)
  {	
    gel(Ge,2+k)=Fq_mul(gel(Ge,2+k),Fq_inv(Fq_ui(k,T,p),T,p),T,p);		
    k++;
  }
	
  return Ge;
}
static 
GEN FqX_primitive(GEN P,GEN T,GEN p)
{

  long d=lg(P)-3;
  if(d==-1)
  {
    return mkpoln(1,Fq_ui(0,T,p));
  }
  GEN ret=cgetg(lg(P)+1,t_POL);
  gel(ret,2)=Fq_ui(0,T,p);
  long k=1;
  while(k<=lg(P)-2)
  {
    gel(ret,2+k)=Fq_mul(Fq_inv(Fq_ui(k,T,p),T,p),gel(P,2+k-1),T,p);
    k++;
  }
  return ret;
	
}
static
GEN FqXn_log(GEN g,long n,GEN T,GEN p)
{
  GEN res;
  res=FqXn_mul(FqX_deriv(g,T,p),FqXn_inv(g,n-1,T,p),n-1,T,p);
  res=FqX_primitive(res,T,p);
  return res;
}
static
GEN FqX_Newton_log_iteration(GEN g,GEN ginv,long t1,long t2,GEN T,GEN p)
{
  GEN res;	
  res=FqXn_mul(FqX_deriv(g,T,p),ginv,t2-1,T,p);
  res=FqX_primitive(res,T,p);
  return res;
}
static
GEN FqX_Newton_iteration_exp(GEN g,GEN ginv,GEN f,long t1,long t2,GEN T,GEN p)
//assumes the inverse of g is known as ginv=1/g mod x^(t2-1) and g=exp(f) mod x^t1 
//returns exp(f) mod x^t2
{
  return FqX_add(g,RgX_shift(FqXn_mul(g,RgX_shift(FqX_sub(f,FqX_Newton_log_iteration(g,ginv,t1,t2,T,p),T,p),-t1),t2-t1,T,p),t1),T,p);
}
static
GEN FqXn_exp(GEN f,long n,GEN T,GEN p)
{
  GEN ret;
  GEN i;
  ret=mkpoln(1,Fq_ui(1,T,p));
  i=mkpoln(1,Fq_ui(1,T,p));
  long t=find_size(n)+1;
  long tab[t];
  find_list(tab,n);
  long j=0;
  while(j<t-1)
  {	
  //we only have about (>=) 1/4 of the precision of the inverse at each step.(One could expect 1/2)
  //However this is quicker to calculate only 2 inverse iterations than the whole thing.
    if(j>0)
    {
      i=FqX_modXn(i,tab[j-1],T,p);
      i=FqX_Newton_iteration_inv(i,ret,tab[j-1],tab[j],T,p);
      i=FqX_Newton_iteration_inv(i,ret,tab[j],tab[j+1]-1,T,p);
    }
    ret=FqX_Newton_iteration_exp(ret,i,f,tab[j],tab[j+1],T,p);
    j++;
  }
  return ret;
}


GEN find_kernel_BMSS(GEN a4,GEN a6,long l,GEN b4,GEN b6,GEN pp1,GEN T,GEN p)
// requires the isogeny to be separable normalized.
// assumes l is odd and pp1 is the sum of the kernel abscissaes.
//requires p>ell+2*BMSSPREC.
{	
  //BMSSPREC denotes the number of extra coefficients calculated to check the result.
  clock_t tmp=clock();
  if(l==3)
  { 
    temps_kernel+=clock()-tmp;
    return FqX_sub(mkpoln(2,Fq_ui(1,T,p),Fq_ui(0,T,p)),mkpoln(1,pp1),T,p);
  }
  GEN Ge;
  GEN G=mkpoln(4,a6,a4,Fq_ui(0,T,p),Fq_ui(1,T,p));
  GEN H=mkpoln(4,b6,b4,Fq_ui(0,T,p),Fq_ui(1,T,p));
  GEN S=find_S((l+1)/2+1+BMSSPREC,G,H,T,p,p,1);
  GEN Sd;
  S=RgX_shift(S,-1);
  Sd=FqXn_inv(S,(l-1)/2+1+BMSSPREC,T,p);
  Ge=FqX_NewtonGen(Sd,l,a4,a6,pp1,T,p);	
  Ge=FqX_neg(Ge,T,p);
  Ge=FqXn_exp(Ge,(l+1)/2+BMSSPREC,T,p);
  Ge=RgX_recip(Ge);
  Ge=normalizepol(Ge);
  temps_kernel+=clock()-tmp;
  printf("[%d,%f],",l,(double)(clock()-tmp)/CLOCKS_PER_SEC);
  if(lg(Ge)==(l-1)/2+3){return Ge;}
  else{return NULL;}
	
}


static GEN global_modular_eqn;
static THREAD GEN modular_eqn;

void
pari_init_seadata(void)  { global_modular_eqn = NULL; }
void
pari_thread_init_seadata(void)  { modular_eqn = global_modular_eqn; }
void
pari_pthread_init_seadata(void)  { global_modular_eqn = modular_eqn; }

static char *
seadata_filename(ulong ell)
{ return stack_sprintf("%s/seadata/sea%ld", pari_datadir, ell); }

static GEN
get_seadata(ulong ell)
{
  pari_sp av=avma;
  GEN eqn;
  char *s = seadata_filename(ell);
  pariFILE *F = pari_fopengz(s);
  if (!F) return NULL;
  if (ell==0)
  {
    eqn = gp_readvec_stream(F->file);
    pari_fclose(F);
    modular_eqn = gclone(eqn);
    avma=av;
    return gen_0;
  } else {
    eqn = gp_read_stream(F->file);
    pari_fclose(F);
    return eqn;
  }
}

/*Builds the modular equation corresponding to the vector list. Shallow */
static GEN
list_to_pol(GEN list, long vx, long vy)
{
  long i, l = lg(list);
  GEN P = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN L = gel(list,i);
    if (typ(L) == t_VEC) L = RgV_to_RgX_reverse(L, vy);
    gel(P, i) = L;
  }
  return RgV_to_RgX_reverse(P, vx);
}

struct meqn {
  char type;
  GEN eq, eval;
  long vx,vy;
};

static int
get_modular_eqn(struct meqn *M, ulong ell, long vx, long vy)
{
  GEN eqn;
  long idx = uprimepi(ell)-1;
  if (!modular_eqn && !get_seadata(0))
    eqn = NULL;
  else if (idx && idx<lg(modular_eqn))
    eqn = gel(modular_eqn, idx);
  else
    eqn = get_seadata(ell);
  M->vx = vx;
  M->vy = vy;
  M->eval = gen_0;
  if (!eqn)
  {

    M->type = 'J';
    M->eq = polmodular_ZXX(ell, ell==3? 0: 5, vx, vy);
    return 0;
  }
  else
  {
    M->type = *GSTR(gel(eqn, 2));
    M->eq = list_to_pol(gel(eqn, 3), vx, vy);
    return 1;
  }
}

static void
err_modular_eqn(long ell)
{ pari_err_FILE("seadata file", seadata_filename(ell)); }

GEN
ellmodulareqn(long ell, long vx, long vy)
{
  pari_sp av = avma;
  struct meqn meqn;
  if (vx<0) vx=0;
  if (vy<0) vy=1;
  if (varncmp(vx,vy)>=0)
    pari_err_PRIORITY("ellmodulareqn", pol_x(vx), ">=", vy);
  if (ell < 0 || !uisprime(ell))
    pari_err_PRIME("ellmodulareqn (level)", stoi(ell));

  if (!get_modular_eqn(&meqn, ell, vx, vy))
    err_modular_eqn(ell);
  return gerepilecopy(av,mkvec2(meqn.eq, stoi(meqn.type=='A')));
}

/***********************************************************************/
/**                                                                   **/
/**                      n-division polynomial                        **/
/**                                                                   **/
/***********************************************************************/

static GEN divpol(GEN t, GEN r2, long n, void *E, const struct bb_algebra *ff);

static GEN
divpol_f2(GEN t, GEN r2, long n, void *E, const struct bb_algebra *ff)
{
  if (n==0) return ff->zero(E);
  if (n<=2) return ff->one(E);
  if (gmael(t,2,n)) return gmael(t,2,n);
  gmael(t,2,n) = gclone(ff->sqr(E,divpol(t,r2,n,E,ff)));
  return gmael(t,2,n);
}

static GEN
divpol_ff(GEN t, GEN r2, long n, void *E, const struct bb_algebra *ff)
{
  if (n<=2) return ff->zero(E);
  if (gmael(t,3,n)) return gmael(t,3,n);
  if (n<=4) return divpol(t,r2,n,E,ff);
  gmael(t,3,n) = gclone(ff->mul(E,divpol(t,r2,n,E,ff), divpol(t,r2,n-2,E,ff)));
  return gmael(t,3,n);
}

static GEN
divpol(GEN t, GEN r2, long n, void *E, const struct bb_algebra *ff)
{
  long m = n/2;
  pari_sp av = avma;
  GEN res;
  if (n==0) return ff->zero(E);
  if (gmael(t,1,n)) return gmael(t,1,n);
  switch(n)
  {
  case 1:
  case 2:
    res = ff->one(E);
    break;
  default:
    if (odd(n))
      if (odd(m))
        res = ff->sub(E, ff->mul(E, divpol_ff(t,r2,m+2,E,ff),
                                    divpol_f2(t,r2,m,E,ff)),
                         ff->mul(E, r2,
                                    ff->mul(E,divpol_ff(t,r2,m+1,E,ff),
                                              divpol_f2(t,r2,m+1,E,ff))));
      else
        res = ff->sub(E, ff->mul(E, r2,
                                    ff->mul(E, divpol_ff(t,r2,m+2,E,ff),
                                               divpol_f2(t,r2,m,E,ff))),
                         ff->mul(E, divpol_ff(t,r2,m+1,E,ff),
                                    divpol_f2(t,r2,m+1,E,ff)));
    else
      res = ff->sub(E, ff->mul(E, divpol_ff(t,r2,m+2,E,ff),
                                  divpol_f2(t,r2,m-1,E,ff)),
                       ff->mul(E, divpol_ff(t,r2,m,E,ff),
                                  divpol_f2(t,r2,m+1,E,ff)));
  }
  res = ff->red(E, res);
  gmael(t,1,n) = gclone(res);
  avma = av;
  return gmael(t,1,n);
}

static void
divpol_free(GEN t)
{
  long i, l = lg(t);
  for (i=1; i<l; i++)
  {
    if (gmael(t,1,i)) gunclone(gmael(t,1,i));
    if (gmael(t,2,i)) gunclone(gmael(t,2,i));
    if (gmael(t,3,i)) gunclone(gmael(t,3,i));
  }
}

static GEN
Flxq_elldivpol34(long n, GEN a4, GEN a6, GEN S, GEN T, ulong p)
{
  GEN res;
  long vs = T[1];
  switch(n)
  {
  case 3:
    res = mkpoln(5, Fl_to_Flx(3%p,vs), pol0_Flx(vs), Flx_mulu(a4, 6, p),
                    Flx_mulu(a6, 12, p), Flx_neg(Flxq_sqr(a4, T, p), p));
    break;
  case 4:
    {
      GEN a42 = Flxq_sqr(a4, T, p);
      res = mkpoln(7, pol1_Flx(vs), pol0_Flx(vs), Flx_mulu(a4, 5, p),
          Flx_mulu(a6, 20, p), Flx_mulu(a42,p-5, p),
          Flx_mulu(Flxq_mul(a4, a6, T, p), p-4, p),
          Flx_sub(Flx_mulu(Flxq_sqr(a6, T, p), p-8%p, p),
            Flxq_mul(a4, a42, T, p), p));
      res = FlxX_double(res, p);
    }
    break;
    default:
      pari_err_BUG("Flxq_elldivpol34"); return NULL;
  }
  setvarn(res, get_FlxqX_var(S));
  return FlxqX_rem(res, S, T, p);
}

static GEN
Fq_elldivpol34(long n, GEN a4, GEN a6, GEN S, GEN T, GEN p)
{
  GEN res;
  switch(n)
  {
  case 3:
    res = mkpoln(5, utoi(3), gen_0, Fq_mulu(a4, 6, T, p),
        Fq_mulu(a6, 12, T, p), Fq_neg(Fq_sqr(a4, T, p), T, p));
    break;
  case 4:
    {
      GEN a42 = Fq_sqr(a4, T, p);
      res = mkpoln(7, gen_1, gen_0, Fq_mulu(a4, 5, T, p),
          Fq_mulu(a6, 20, T, p), Fq_Fp_mul(a42,stoi(-5), T, p),
          Fq_Fp_mul(Fq_mul(a4, a6, T, p), stoi(-4), T, p),
          Fq_sub(Fq_Fp_mul(Fq_sqr(a6, T, p), stoi(-8), T, p),
            Fq_mul(a4,a42, T, p), T, p));
      res = FqX_mulu(res, 2, T, p);
    }
    break;
    default:
      pari_err_BUG("Fq_elldivpol34"); return NULL;
  }
  if (S)
  {
    setvarn(res, get_FpXQX_var(S));
    res = FqX_rem(res, S, T, p);
  }
  return res;
}

static GEN
rhs(GEN a4, GEN a6, long v)
{
  GEN RHS = mkpoln(4, gen_1, gen_0, a4, a6);
  setvarn(RHS, v);
  return RHS;
}

struct divpolmod_red
{
  const struct bb_algebra *ff;
  void *E;
  GEN t, r2;
};

static void
divpolmod_init(struct divpolmod_red *d, GEN D3, GEN D4, GEN RHS, long n,
               void *E, const struct bb_algebra *ff)
{
  long k = n+2;
  d->ff = ff; d->E = E;
  d->t  = mkvec3(const_vec(k, NULL),const_vec(k, NULL),const_vec(k, NULL));
  if (k>=3) gmael(d->t,1,3) = gclone(D3);
  if (k>=4) gmael(d->t,1,4) = gclone(D4);
  d->r2 = ff->sqr(E, RHS);
}

static void
Fq_elldivpolmod_init(struct divpolmod_red *d, GEN a4, GEN a6, long n, GEN h, GEN T, GEN p)
{
  void *E;
  const struct bb_algebra *ff;
  GEN RHS, D3 = NULL, D4 = NULL;
  long v = h ? get_FpXQX_var(h): 0;
  D3 = n>=0 ? Fq_elldivpol34(3, a4, a6, h, T, p): NULL;
  D4 = n>=1 ? Fq_elldivpol34(4, a4, a6, h, T, p): NULL;
  RHS = rhs(a4, a6, v);
  RHS = h ? FqX_rem(RHS, h, T, p): RHS;
  RHS = FqX_mulu(RHS, 4, T, p);
  ff = h ? T ? get_FpXQXQ_algebra(&E, h, T, p): get_FpXQ_algebra(&E, h, p):
           T ? get_FpXQX_algebra(&E, T, p, v): get_FpX_algebra(&E, p, v);
  divpolmod_init(d, D3, D4, RHS, n, E, ff);
}

static void
Flxq_elldivpolmod_init(struct divpolmod_red *d, GEN a4, GEN a6, long n, GEN h, GEN T, ulong p)
{
  void *E;
  const struct bb_algebra *ff;
  GEN RHS, D3 = NULL, D4 = NULL;
  D3 = n>=0 ? Flxq_elldivpol34(3, a4, a6, h, T, p): NULL;
  D4 = n>=1 ? Flxq_elldivpol34(4, a4, a6, h, T, p): NULL;
  RHS = FlxX_Fl_mul(FlxqX_rem(rhs(a4, a6, get_FlxqX_var(h)), h, T, p), 4, p);
  ff = get_FlxqXQ_algebra(&E, h, T, p);
  divpolmod_init(d, D3, D4, RHS, n, E, ff);
}

/*Computes the n-division polynomial modulo the polynomial h \in Fq[x] */
GEN
Fq_elldivpolmod(GEN a4, GEN a6, long n, GEN h, GEN T, GEN p)
{
  struct divpolmod_red d;
  pari_sp ltop = avma;
  GEN res;
  Fq_elldivpolmod_init(&d, a4, a6, n, h, T, p);
  res = gcopy(divpol(d.t,d.r2,n,d.E,d.ff));
  divpol_free(d.t);
  return gerepileupto(ltop, res);
}

GEN
FpXQ_elldivpol(GEN a4, GEN a6, long n, GEN T, GEN p)
{
  return Fq_elldivpolmod(a4,a6,n,NULL,T,p);
}

GEN
Fp_elldivpol(GEN a4, GEN a6, long n, GEN p)
{
  return Fq_elldivpolmod(a4,a6,n,NULL,NULL,p);
}

static GEN
Fq_ellyn(struct divpolmod_red *d, long k)
{
  pari_sp av = avma;
  void *E = d->E;
  const struct bb_algebra *ff = d->ff;
  if (k==1) return mkvec2(ff->one(E), ff->one(E));
  else
  {
    GEN t = d->t, r2 = d->r2;
    GEN pn2 = divpol(t,r2,k-2,E,ff);
    GEN pp2 = divpol(t,r2,k+2,E,ff);
    GEN pn12 = divpol_f2(t,r2,k-1,E,ff);
    GEN pp12 = divpol_f2(t,r2,k+1,E,ff);
    GEN on = ff->red(E,ff->sub(E, ff->mul(E,pp2,pn12), ff->mul(E,pn2,pp12)));
    GEN f  = divpol(t,r2,k,E,ff);
    GEN f2 = divpol_f2(t,r2,k,E,ff);
    GEN f3 = ff->mul(E,f,f2);
    if (!odd(k)) f3 = ff->mul(E,f3,r2);
    return gerepilecopy(av,mkvec2(on, f3));
  }
}

static void
Fq_elldivpolmod_close(struct divpolmod_red *d)
{
  divpol_free(d->t);
}
static GEN
Fq_elldivpol2(GEN a4, GEN a6, GEN T, GEN p)
{
  return mkpoln(4, utoi(4), gen_0, Fq_mulu(a4, 4, T, p), Fq_mulu(a6, 4, T, p));
}

static GEN
Fq_elldivpol2d(GEN a4, GEN T, GEN p)
{
  return mkpoln(3, utoi(6), gen_0, Fq_mulu(a4, 2, T, p));
}

static GEN
FqX_numer_isog_abscissa(GEN h, GEN a4, GEN a6, GEN T, GEN p, long vx)
{
  GEN mp1, dh, ddh, t, u, t1, t2, t3, t4, f0;
  long m = degpol(h);
  mp1 = gel(h, m + 1); /* negative of first power sum */
  dh = FqX_deriv(h, T, p);
  ddh = FqX_deriv(dh, T, p);
  t  = Fq_elldivpol2(a4, a6, T, p);
  u  = Fq_elldivpol2d(a4, T, p);
  t1 = FqX_sub(FqX_sqr(dh, T, p), FqX_mul(ddh, h, T, p), T, p);
  t2 = FqX_mul(u, FqX_mul(h, dh, T, p), T, p);
  t3 = FqX_mul(FqX_sqr(h, T, p),
               deg1pol_shallow(stoi(2*m), Fq_mulu(mp1, 2, T, p), vx), T, p);
  f0 = FqX_add(FqX_sub(FqX_mul(t, t1, T, p), t2, T, p), t3, T, p);
  t4 = FqX_mul(pol_x(vx),  FqX_sqr(h, T, p), T, p);
  return FqX_add(t4, f0, T, p);
}


/*Gives the first precS terms of the Weierstrass series related to */
/*E: y^2 = x^3 + a4x + a6.  Assumes (precS-2)*(2precS+3) < ULONG_MAX, i.e.
 * precS < 46342 in 32-bit machines */
static GEN
find_coeff(GEN a4, GEN a6, GEN T, GEN p, long precS, GEN pp, long e)
{
  GEN res, den;
  long k, h;
  if (e > 1) { p = sqri(p); e *= 2; }
  res = cgetg(precS+1, t_VEC);
  den = cgetg(precS+1, t_VECSMALL);
  if (precS == 0) return res;
  gel(res, 1) = Fq_div(a4, stoi(-5), T, p);
  den[1] = 0;
  if (precS == 1) return res;
  gel(res, 2) = Fq_div(a6, stoi(-7), T, p);
  den[2] = 0;
  for (k = 3; k <= precS; ++k)
  {
    pari_sp btop = avma;
    GEN a = gen_0, d;
    long v=0;
    if (e > 1)
      for (h = 1; h <= k-2; h++)
        v = maxss(v, den[h]+den[k-1-h]);
    for (h = 1; h <= k-2; h++)
    {
      GEN b = Fq_mul(gel(res, h), gel(res, k-1-h), T, p);
      if (v)
        b = Fq_Fp_mul(b, powiu(pp, v-(den[h]+den[k-1-h])), T, p);
      a = Fq_add(a, b, T, p);
    }
    v += Z_pvalrem(utoi((k-2) * (2*k + 3)), pp, &d);
    a = Zq_div_safe(gmulgs(a, 3), d, T, p, pp, e);
    gel(res, k) = gerepileupto(btop, a);
    den[k] = v;
  }
  return mkvec2(res, den);
}

/****************************************************************************/
/*               SIMPLE ELLIPTIC CURVE OVER Fq                              */
/****************************************************************************/

static GEN
Fq_ellj(GEN a4, GEN a6, GEN T, GEN p)
{
  pari_sp ltop=avma;
  GEN a43 = Fq_mulu(Fq_powu(a4, 3, T, p), 4, T, p);
  GEN j   = Fq_div(Fq_mulu(a43, 1728, T, p),
                   Fq_add(a43, Fq_mulu(Fq_sqr(a6, T, p), 27, T, p), T, p), T, p);
  return gerepileupto(ltop, j);
}

static GEN
Zq_ellj(GEN a4, GEN a6, GEN T, GEN p, GEN pp, long e)
{
  pari_sp ltop=avma;
  GEN a43 = Fq_mulu(Fq_powu(a4, 3, T, p), 4, T, p);
  GEN j   = Zq_div_safe(Fq_mulu(a43, 1728, T, p),
                   Fq_add(a43, Fq_mulu(Fq_sqr(a6, T, p), 27, T, p), T, p), T, p, pp, e);
  return gerepileupto(ltop, j);
}
/****************************************************************************/
/*                              EIGENVALUE                                  */
/****************************************************************************/

static GEN
Fq_to_Flx(GEN a4, GEN T, ulong p)
{
  return typ(a4)==t_INT ? Z_to_Flx(a4, p, get_Flx_var(T)): ZX_to_Flx(a4, p);
}

static GEN
Flxq_find_eigen_Frobenius(GEN a4, GEN a6, GEN h, GEN T, ulong p)
{
  long v = get_FlxqX_var(h);
  GEN RHS = FlxqX_rem(rhs(a4, a6, v), h, T, p);
  return FlxqXQ_halfFrobenius(RHS, h, T, p);
}

static GEN
Fq_find_eigen_Frobenius(GEN a4, GEN a6, GEN h, GEN T, GEN p)
{
  long v = T ? get_FpXQX_var(h): get_FpX_var(h);
  GEN RHS  = FqX_rem(rhs(a4, a6, v), h, T, p);
  return T ? FpXQXQ_halfFrobenius(RHS, h, T, p):
             FpXQ_pow(RHS, shifti(p, -1), h, p);
}
/*Finds the eigenvalue of the Frobenius given E, ell odd prime, h factor of the
 *ell-division polynomial, p and tr the possible values for the trace
 *(useful for primes with one root)*/
static ulong
find_eigen_value_oneroot(GEN a4, GEN a6, ulong ell, GEN tr, GEN h, GEN T, GEN p)
{
  pari_sp ltop = avma;
  ulong t;
  struct divpolmod_red d;
  GEN f, Dy, Gy;
  h = FqX_get_red(h, T, p);
  Gy = Fq_find_eigen_Frobenius(a4, a6, h, T, p);
  t = Fl_div(tr[1], 2, ell);
  if (t < (ell>>1)) t = ell - t;
  Fq_elldivpolmod_init(&d, a4, a6, t, h, T, p);
  f = Fq_ellyn(&d, t);
  Dy = FqXQ_mul(Gy, gel(f,2), h, T, p);
  if (!gequal(gel(f,1), Dy)) t = ell-t;
  Fq_elldivpolmod_close(&d);
  avma = ltop; return t;
}

static ulong
Flxq_find_eigen_value_power(GEN a4, GEN a6, ulong ell, long k, ulong lambda,
                            GEN h, GEN T, ulong p)
{
  pari_sp ltop = avma;
  ulong t, ellk1 = upowuu(ell, k-1), ellk = ell*ellk1;
  pari_timer ti;
  struct divpolmod_red d;
  GEN Gy;
  timer_start(&ti);
  h = FlxqX_get_red(h, T, p);
  Gy = Flxq_find_eigen_Frobenius(a4, a6, h, T, p);
  if (DEBUGLEVEL>2) err_printf(" (%ld ms)",timer_delay(&ti));
  Flxq_elldivpolmod_init(&d, a4, a6, ellk, h, T, p);
  for (t = lambda; t < ellk; t += ellk1)
  {
    GEN f = Fq_ellyn(&d, t);
    GEN Dr = FlxqXQ_mul(Gy, gel(f,2), h, T, p);
    if (varn(gel(f,1))!=varn(Dr)) pari_err_BUG("find_eigen_value_power");
    if (gequal(gel(f,1), Dr)) break;
    if (gequal(gel(f,1), FlxX_neg(Dr,p))) { t = ellk-t; break; }
  }
  if (DEBUGLEVEL>2) err_printf(" (%ld ms)",timer_delay(&ti));
  Fq_elldivpolmod_close(&d);
  avma = ltop; return t;
}

/*Finds the eigenvalue of the Frobenius modulo ell^k given E, ell, k, h factor
 *of the ell-division polynomial, lambda the previous eigen value and p */
static ulong
Fq_find_eigen_value_power(GEN a4, GEN a6, ulong ell, long k, ulong lambda, GEN h, GEN T, GEN p)
{
  pari_sp ltop = avma;
  ulong t, ellk1 = upowuu(ell, k-1), ellk = ell*ellk1;
  pari_timer ti;
  struct divpolmod_red d;
  GEN Gy;
  timer_start(&ti);
  h = FqX_get_red(h, T, p);
  Gy = Fq_find_eigen_Frobenius(a4, a6, h, T, p);
  if (DEBUGLEVEL>2) err_printf(" (%ld ms)",timer_delay(&ti));
  Fq_elldivpolmod_init(&d, a4, a6, ellk, h, T, p);
  for (t = lambda; t < ellk; t += ellk1)
  {
    GEN f = Fq_ellyn(&d, t);
    GEN Dr = FqXQ_mul(Gy, gel(f,2), h, T, p);
    if (varn(gel(f,1))!=varn(Dr)) pari_err_BUG("find_eigen_value_power");
    if (gequal(gel(f,1), Dr)) break;
    if (gequal(gel(f,1), FqX_neg(Dr,T,p))) { t = ellk-t; break; }
  }
  if (DEBUGLEVEL>2) err_printf(" (%ld ms)",timer_delay(&ti));
  Fq_elldivpolmod_close(&d);
  avma = ltop; return t;
}

static ulong
find_eigen_value_power(GEN a4, GEN a6, ulong ell, long k, ulong lambda, GEN hq, GEN T, GEN p)
{
  ulong pp = itou_or_0(p);
  if (pp && T)
  {
    GEN a4p = ZX_to_Flx(a4, pp);
    GEN a6p = ZX_to_Flx(a6, pp);
    GEN hp = ZXXT_to_FlxXT(hq, pp,varn(a4));
    GEN Tp = ZXT_to_FlxT(T, pp);
    return Flxq_find_eigen_value_power(a4p, a6p, ell, k, lambda, hp, Tp, pp);
  }
  return Fq_find_eigen_value_power(a4, a6, ell, k, lambda, hq, T, p);
}

/*Finds the kernel polynomial h, dividing the ell-division polynomial from the
  isogenous curve Eb and trace term pp1. Uses CCR algorithm and returns h.
  Return NULL if E and Eb are *not* isogenous. */
static GEN
find_kernel(GEN a4, GEN a6, ulong ell, GEN a4t, GEN a6t, GEN pp1, GEN T, GEN p, GEN pp, long e)
{
  const long ext = 2;
  pari_sp ltop = avma, btop;
  GEN P, v, tlist, h;
  long i, j, k;
  long deg = (ell - 1)/2, dim = 2 + deg + ext;
  GEN psi2 = Fq_elldivpol2(a4, a6, T, p);
  GEN Dpsi2 = Fq_elldivpol2d(a4, T, p);
  GEN C  = find_coeff(a4, a6, T, p, dim, pp, e);
  GEN Ct = find_coeff(a4t, a6t, T, p, dim, pp, e);
  GEN V = cgetg(dim+1, t_VEC);
  for (k = 1; k <= dim; k++)
  {
    long v = mael(C,2,k);
    GEN z = gmul(gsub(gmael(Ct,1,k), gmael(C,1,k)), shifti(mpfact(2*k), -1));
    if (signe(z) && Zq_pval(z, pp) < v) return NULL;
    gel(V, k) = Zq_divexact(z, powiu(pp, v));
  }
  btop = avma;
  v = zerovec(dim);
  gel(v, 1) = utoi(deg);
  gel(v, 2) = pp1;
  P = pol_x(0);
  for (k = 3; k <= dim; k++)
  {
    GEN s, r = FqX_Fq_mul(Dpsi2, gel(P, 3), T, p);
    for (j = 4; j < lg(P); j++)
    {
      long o = j - 2;
      GEN D = FqX_add(RgX_shift_shallow(Dpsi2, 1), FqX_mulu(psi2, o-1, T, p), T, p);
      GEN E = FqX_Fq_mul(D, Fq_mulu(gel(P, j), o, T, p), T, p);
      r = FqX_add(r, RgX_shift_shallow(E, o-2), T, p);
    }
    P = r;
    s = Fq_mul(gel(P, 2), gel(v, 1), T, p);
    for (j = 3; j < lg(P)-1; j++)
      s = Fq_add(s, Fq_mul(gel(P, j), gel(v, j-1), T, p), T, p);
    gel(v, k) = Zq_Z_div_safe(Fq_sub(gel(V, k-2), s, T, p), gel(P, j), T, p, pp, e);
    if (gc_needed(btop, 1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"find_kernel");
      gerepileall(btop, 2, &v, &P);
    }
  }
  tlist = cgetg(dim, t_VEC);
  gel(tlist, dim-1) = gen_1;
  for (k = 1; k <= dim-2; k++)
  {
    pari_sp btop = avma;
    GEN s = gel(v, k+1);
    for (i = 1; i < k; i++)
      s = Fq_add(s, Fq_mul(gel(tlist, dim-i-1), gel(v, k-i+1), T, p), T, p);
    gel(tlist, dim-k-1) = gerepileupto(btop, Zq_Z_div_safe(s, stoi(-k), T, p, pp, e));
  }
  for (i = 1; i <= ext; i++)
    if (signe(Fq_red(gel(tlist, i),T, pp))) { avma = ltop; return NULL; }
  h = FqX_red(RgV_to_RgX(vecslice(tlist, ext+1, dim-1), 0),T,p);
  return signe(Fq_elldivpolmod(a4, a6, ell, h, T, pp)) ? NULL: h;
}

static GEN
compute_u(GEN gprime, GEN Dxxg, GEN DxJg, GEN DJJg, GEN j, GEN pJ, GEN px, ulong q, GEN E4, GEN E6, GEN T, GEN p, GEN pp, long e)
{
  pari_sp ltop = avma;
  GEN dxxgj = FqX_eval(Dxxg, j, T, p);
  GEN dxJgj = FqX_eval(DxJg, j, T, p);
  GEN dJJgj = FqX_eval(DJJg, j, T, p);
  GEN E42 = Fq_sqr(E4, T, p), E6ovE4 = Zq_div_safe(E6, E4, T, p, pp, e);
  GEN a = Fq_mul(gprime, dxxgj, T, p);
  GEN b = Fq_mul(Fq_mul(Fq_mulu(j,2*q, T, p), dxJgj, T, p), E6ovE4, T, p);
  GEN c = Fq_mul(Zq_div_safe(Fq_sqr(E6ovE4, T, p), gprime, T, p, pp, e), j, T, p);
  GEN d = Fq_mul(Fq_mul(c,sqru(q), T, p), Fq_add(pJ, Fq_mul(j, dJJgj, T, p), T, p), T, p);
  GEN f = Fq_sub(Fq_div(E6ovE4,utoi(3), T, p),
                 Zq_div_safe(E42, Fq_mulu(E6,2,T, p), T, p, pp, e), T, p);
  GEN g = Fq_sub(Fq_sub(b,a,T,p), d, T, p);
  return gerepileupto(ltop, Fq_add(Zq_div_safe(g,px,T,p,pp,e), Fq_mulu(f,q,T,p), T, p));
}

/* Finds the isogenous EC, and the sum of the x-coordinates of the points in
 * the kernel of the isogeny E -> Eb
 * E: elliptic curve, ell: a prime, meqn: Atkin modular equation
 * g: root of meqn defining isogenous curve Eb. */
static GEN
find_isogenous_from_Atkin(GEN a4, GEN a6, ulong ell, struct meqn *MEQN, GEN g, GEN T, GEN pp, long e)
{ 
  pari_sp ltop = avma, btop;
  GEN meqn = MEQN->eq, meqnx, Roots, gprime, u1;
  long k, vJ = MEQN->vy;
  GEN p = e==1 ? pp: powiu(pp, e);
  GEN E4 = Fq_div(a4, stoi(-3), T, p);
  GEN E6 = Fq_neg(Fq_halve(a6, T, p), T, p);
  GEN E42 = Fq_sqr(E4, T, p);
  GEN E43 = Fq_mul(E4, E42, T, p);
  GEN E62 = Fq_sqr(E6, T, p);
  GEN delta = Fq_div(Fq_sub(E43, E62, T, p), utoi(1728), T, p);
  GEN j = Zq_div_safe(E43, delta, T, p, pp, e);
  GEN Dx = RgX_deriv(meqn);
  GEN DJ = deriv(meqn, vJ);
  GEN Dxg = FpXY_Fq_evaly(Dx, g, T, p, vJ);
  GEN px = FqX_eval(Dxg, j, T, p), dx = Fq_mul(px, g, T, p);
  GEN DJg = FpXY_Fq_evaly(DJ, g, T, p, vJ);
  GEN pJ = FqX_eval(DJg, j, T, p), dJ = Fq_mul(pJ, j, T, p);
  GEN Dxx = RgX_deriv(Dx);
  GEN DxJg = FqX_deriv(Dxg, T, p);

  GEN Dxxg = FpXY_Fq_evaly(Dxx, g, T, p, vJ);
  GEN DJJg = FqX_deriv(DJg, T, p);
  GEN a, b;
  if (!signe(dJ) || !signe(dx))
  {
    if (DEBUGLEVEL>0) err_printf("[A: d%c=0]",signe(dJ)? 'x': 'J');
    avma = ltop; return NULL;
  }
  a = Fq_mul(dJ, Fq_mul(g, E6, T, p), T, p);
  b = Fq_mul(E4, dx, T, p);
	if(e==1)// In p-adics this may lead to impossible divisions.
	{
    gprime = Fq_div(a,b, T, p);
		u1 = compute_u(gprime, Dxxg, DxJg, DJJg, j, pJ, px, 1, E4, E6, T, p, pp, e);
	}
  meqnx = FpXY_Fq_evaly(meqn, g, T, p, vJ);
  Roots = FqX_roots(meqnx, T, pp);
  btop = avma;
  for (k = lg(Roots)-1; k >= 1; k--, avma = btop)
  { 
	int val=gvaluation(FqX_eval(RgX_deriv(meqnx),gel(Roots, k),T,p),pp);
	if(val!=0){return NULL;}
	// in that case, it's not possible to lift the root until e, so the algorithm could crash later on.
    GEN jt = e==1 ? gel(Roots, k): ZqX_liftroot(meqnx, gel(Roots, k), T, pp, e);
	//CRASH when counting points of y^2=x^3+x+4 on GF(47**47)
    if (signe(jt) == 0 || signe(Fq_sub(jt, utoi(1728), T, p)) == 0)
    {
      if (DEBUGLEVEL>0) err_printf("[A: jt=%ld]",signe(jt)? 1728: 0);
      avma = ltop; return NULL;
    }
	
    else
    {
      GEN pxstar = FqX_eval(Dxg, jt, T, p);
      GEN dxstar = Fq_mul(pxstar, g, T, p);
      GEN pJstar = FqX_eval(DJg, jt, T, p);
      GEN dJstar = Fq_mul(Fq_mulu(jt, ell, T, p), pJstar, T, p);
      GEN u = Fq_mul(Fq_mul(dxstar, dJ, T, p), E6, T, p);
      GEN v = Fq_mul(Fq_mul(dJstar, dx, T, p), E4, T, p);
      GEN E4t = Zq_div_safe(Fq_mul(Fq_sqr(u, T, p), jt, T, p), Fq_mul(Fq_sqr(v, T, p), Fq_sub(jt, utoi(1728), T, p), T, p), T, p, pp, e);
      GEN E6t = Zq_div_safe(Fq_mul(u, E4t, T, p), v, T, p, pp, e);	
      GEN u2;
      GEN pp1=NULL;
      if(e==1)// In p-adics this may lead to impossible divisions.
      {	
        u2 = compute_u(gprime, Dxxg, DxJg, DJJg, jt, pJstar, pxstar, ell, E4t, E6t, T, p, pp, e);	
      	pp1 = Fq_mulu(Fq_sub(u1, u2, T, p), 3*ell, T, p);
      }

      GEN a4t = Fq_mul(mulsi(-3, powuu(ell,4)), E4t, T, p);
      GEN a6t = Fq_mul(mulsi(-2, powuu(ell,6)), E6t, T, p);
      GEN h ;
	
      if(e>1)
    	  h = find_kernel_LS(a4, a6, ell, a4t, a6t, pp1, T, p, pp, e);
      else
        {h = find_kernel_BMSS(a4, a6, ell, a4t, a6t, pp1, T, p);}
      if (h) return gerepilecopy(ltop, mkvec3(a4t, a6t, h));
    }
  }
  pari_err_BUG("find_isogenous_from_Atkin, kernel not found");
  return NULL;
}

/* Finds E' ell-isogenous to E and the trace term p1 from canonical modular
 *   equation meqn
 * E: elliptic curve, ell: a prime, meqn: canonical modular equation
 * g: root of meqn defining isogenous curve Eb. */
static GEN
find_isogenous_from_canonical(GEN a4, GEN a6, ulong ell, struct meqn *MEQN, GEN g, GEN T, GEN pp, long e)
{

  pari_sp ltop = avma;
  GEN meqn = MEQN->eq;
  long vJ = MEQN->vy;
  GEN p = e==1 ? pp: powiu(pp, e);
  GEN h;
  GEN E4 = Fq_div(a4, stoi(-3), T, p);
  GEN E6 = Fq_neg(Fq_halve(a6, T, p), T, p);
  GEN E42 = Fq_sqr(E4, T, p);
  GEN E43 = Fq_mul(E4, E42, T, p);
  GEN E62 = Fq_sqr(E6, T, p);
  GEN delta = Fq_div(Fq_sub(E43, E62, T, p), utoi(1728), T, p);
  GEN j = Zq_div_safe(E43, delta, T, p, pp, e);
  GEN Dx = RgX_deriv(meqn);
  GEN DJ = deriv(meqn, vJ);
  GEN Dxg = FpXY_Fq_evaly(Dx, g, T, p, vJ);
  GEN px  = FqX_eval(Dxg, j, T, p), dx  = Fq_mul(px, g, T, p);
  GEN DJg = FpXY_Fq_evaly(DJ, g, T, p, vJ);
  GEN pJ = FqX_eval(DJg, j, T, p), dJ = Fq_mul(j, pJ, T, p);
  GEN Dxx = RgX_deriv(Dx);
  GEN DxJg = FqX_deriv(Dxg, T, p);
	
  GEN ExJ = FqX_eval(DxJg, j, T, p);
  ulong tis = ugcd(12, ell-1), is = 12 / tis;
  GEN itis = Fq_inv(stoi(-tis), T, p);
  GEN deltal = Fq_div(Fq_mul(delta, Fq_powu(g, tis, T, p), T, p), powuu(ell, 12), T, p);
  GEN E4l, E6l, a4tilde, a6tilde, p_1;
	
  if (signe(dx)==0)
  {
    if (DEBUGLEVEL>0) err_printf("[C: dx=0]");
    avma = ltop; return NULL;
  }
  if (signe(dJ)==0)
  {
    GEN jl;
    if (DEBUGLEVEL>0) err_printf("[C: dJ=0]");
    E4l = Fq_div(E4, sqru(ell), T, p);
    jl  = Zq_div_safe(Fq_powu(E4l, 3, T, p), deltal, T, p, pp, e);
    E6l = Zq_sqrt(Fq_mul(Fq_sub(jl, utoi(1728), T, p), deltal, T, p), T, p, pp, e);
    p_1 = gen_0;
  }
  else
  { 
    GEN jl, f, fd, Dgs, Djs, jld;
    GEN E2s = Zq_div_safe(Fq_mul(Fq_neg(Fq_mulu(E6, 12, T, p), T, p), dJ, T, p), Fq_mul(Fq_mulu(E4, is, T, p), dx, T, p), T, p, pp, e);
    GEN gd = Fq_mul(Fq_mul(E2s, itis, T, p), g, T, p);
    GEN jd = Zq_div_safe(Fq_mul(Fq_neg(E42, T, p), E6, T, p), delta, T, p, pp, e);
    GEN E0b = Zq_div_safe(E6, Fq_mul(E4, E2s, T, p), T, p, pp, e);
    GEN Dxxgj = FqXY_eval(Dxx, g, j, T, p);
    GEN Dgd = Fq_add(Fq_mul(gd, px, T, p), Fq_mul(g, Fq_add(Fq_mul(gd, Dxxgj, T, p), Fq_mul(jd, ExJ, T, p), T, p), T, p), T, p);
    GEN DJgJj = FqX_eval(FqX_deriv(DJg, T, p), j, T, p);
    GEN Djd = Fq_add(Fq_mul(jd, pJ, T, p), Fq_mul(j, Fq_add(Fq_mul(jd, DJgJj, T, p), Fq_mul(gd, ExJ, T, p), T, p), T, p), T, p);
    GEN E0bd = Zq_div_safe(Fq_sub(Fq_mul(Dgd, itis, T, p), Fq_mul(E0b, Djd, T, p), T, p), dJ, T, p, pp, e);
    E4l = Zq_div_safe(Fq_sub(E4, Fq_mul(E2s, Fq_sub(Fq_sub(Fq_add(Zq_div_safe(Fq_mulu(E0bd, 12, T, p), E0b, T, p, pp, e), Zq_div_safe(Fq_mulu(E42, 6, T, p), E6, T, p, pp, e), T, p), Zq_div_safe(Fq_mulu(E6, 4, T, p), E4, T, p, pp, e), T, p), E2s, T, p), T, p), T, p), sqru(ell), T, p, pp, e);
    jl = Zq_div_safe(Fq_powu(E4l, 3, T, p), deltal, T, p, pp, e);
    if (signe(jl)==0)
    {
      if (DEBUGLEVEL>0) err_printf("[C: jl=0]");
      avma = ltop; return NULL;
    }
    
    f =  Zq_div_safe(powuu(ell, is), g, T, p, pp, e);
    fd = Fq_neg(Fq_mul(Fq_mul(E2s, f, T, p), itis, T, p), T, p);
    Dgs = FqXY_eval(Dx, f, jl, T, p);
    Djs = FqXY_eval(DJ, f, jl, T, p);
    jld = Zq_div_safe(Fq_mul(Fq_neg(fd, T, p), Dgs, T, p), Fq_mulu(Djs, ell, T, p), T, p, pp, e);
    E6l = Zq_div_safe(Fq_mul(Fq_neg(E4l, T, p), jld, T, p), jl, T, p, pp, e);
    p_1 = Fq_neg(Fq_halve(Fq_mulu(E2s, ell, T, p), T, p),T,p);
  }
  a4tilde = Fq_mul(Fq_mul(stoi(-3), powuu(ell,4), T, p), E4l, T, p);
  a6tilde = Fq_mul(Fq_mul(stoi(-2), powuu(ell,6), T, p), E6l, T, p);
  if(e>1)
    h = find_kernel_LS(a4, a6, ell, a4tilde, a6tilde, p_1, T, p, pp, e);
  else
    h = find_kernel_BMSS(a4, a6, ell, a4tilde, a6tilde, p_1, T, p);
  if (!h) return NULL;
  return gerepilecopy(ltop, mkvec3(a4tilde, a6tilde, h));
}

static GEN
corr(GEN c4, GEN c6, GEN T, GEN p, GEN pp, long e)
{
  GEN c46 = Zq_div_safe(Fq_sqr(c4, T, p), c6, T, p, pp, e);
  GEN c64 = Zq_div_safe(c6, c4, T, p, pp, e);
  GEN a = Fp_div(gen_2, utoi(3), p);
  return Fq_add(Fq_halve(c46, T, p), Fq_mul(a, c64, T, p), T, p);
}

static GEN
RgXY_deflatex(GEN H, long n, long d)
{
  long i, l = lg(H);
  GEN R = cgetg(l, t_POL);
  R[1] = H[1];
  for(i = 2; i < l; i++)
  {
    GEN Hi = gel(H, i);
    gel(R,i) = typ(Hi)==t_POL? RgX_deflate(RgX_shift_shallow(Hi, d), n): Hi;
  }
  return RgX_renormalize_lg(R, l);
}

static GEN
Fq_polmodular_eval(GEN meqn, GEN j, long N, GEN T, GEN p, long vJ)
{
  pari_sp av = avma;
  GEN R, dR, ddR;
  long t0 = N%3 == 1 ? 2: 0;
  long t2 = N%3 == 1 ? 0: 2;
  if (N == 3)
  {
    GEN P = FpXX_red(meqn, p);
    GEN dP = deriv(P, -1), ddP = deriv(dP, -1);
    R = FpXY_Fq_evaly(P, j, T, p, vJ);
    dR = FpXY_Fq_evaly(dP, j, T, p, vJ);
    ddR = FpXY_Fq_evaly(ddP, j, T, p, vJ);
    return gerepilecopy(av, mkvec3(R,dR,ddR));
  }
  else
  {
    GEN P5 = FpXX_red(meqn, p);
    GEN H = RgX_splitting(P5, 3);
    GEN H0 = RgXY_deflatex(gel(H,1), 3, -t0);
    GEN H1 = RgXY_deflatex(gel(H,2), 3, -1);
    GEN H2 = RgXY_deflatex(gel(H,3), 3, -t2);
    GEN h0 = FpXY_Fq_evaly(H0, j, T, p, vJ);
    GEN h1 = FpXY_Fq_evaly(H1, j, T, p, vJ);
    GEN h2 = FpXY_Fq_evaly(H2, j, T, p, vJ);
    GEN dH0 = RgX_deriv(H0);
    GEN dH1 = RgX_deriv(H1);
    GEN dH2 = RgX_deriv(H2);
    GEN ddH0 = RgX_deriv(dH0);
    GEN ddH1 = RgX_deriv(dH1);
    GEN ddH2 = RgX_deriv(dH2);
    GEN d0 = FpXY_Fq_evaly(dH0, j, T, p, vJ);
    GEN d1 = FpXY_Fq_evaly(dH1, j, T, p, vJ);
    GEN d2 = FpXY_Fq_evaly(dH2, j, T, p, vJ);
    GEN dd0 = FpXY_Fq_evaly(ddH0, j, T, p, vJ);
    GEN dd1 = FpXY_Fq_evaly(ddH1, j, T, p, vJ);
    GEN dd2 = FpXY_Fq_evaly(ddH2, j, T, p, vJ);
    GEN h02, h12, h22, h03, h13, h23, h012, dh03, dh13, dh23, dh012;
    GEN ddh03, ddh13, ddh23, ddh012;
    GEN R1, dR1, ddR1, ddR2;
    h02 = FqX_sqr(h0, T, p);
    h12 = FqX_sqr(h1, T, p);
    h22 = FqX_sqr(h2, T, p);
    h03 = FqX_mul(h0, h02, T, p);
    h13 = FqX_mul(h1, h12, T, p);
    h23 = FqX_mul(h2, h22, T, p);
    h012 = FqX_mul(FqX_mul(h0, h1, T, p), h2, T, p);
    dh03 = FqX_mul(FqX_mulu(d0, 3, T, p), h02, T, p);
    dh13 = FqX_mul(FqX_mulu(d1, 3, T, p), h12, T, p);
    dh23 = FqX_mul(FqX_mulu(d2, 3, T, p), h22, T, p);
    dh012 = FqX_add(FqX_add(FqX_mul(FqX_mul(d0, h1, T, p), h2, T, p), FqX_mul(FqX_mul(h0, d1, T, p), h2, T, p), T, p), FqX_mul(FqX_mul(h0, h1, T, p), d2, T, p), T, p);
    R1 = FqX_sub(h13, FqX_mulu(h012, 3, T, p), T, p);
    R = FqX_add(FqX_add(FqX_Fq_mul(RgX_shift_shallow(h23, t2), Fq_sqr(j, T, p), T, p), FqX_Fq_mul(RgX_shift_shallow(R1, 1), j, T, p), T, p), RgX_shift_shallow(h03, t0), T, p);
    dR1 = FqX_sub(dh13, FqX_mulu(dh012, 3, T, p), T, p);
    dR = FqX_add(FqX_add(RgX_shift_shallow(FqX_add(FqX_Fq_mul(dh23, Fq_sqr(j, T, p), T, p), FqX_Fq_mul(h23, Fq_mulu(j, 2, T, p), T, p), T, p), t2), RgX_shift_shallow(FqX_add(FqX_Fq_mul(dR1, j, T, p), R1, T, p), 1), T, p), RgX_shift_shallow(dh03, t0), T, p);
    ddh03 = FqX_mulu(FqX_add(FqX_mul(dd0, h02, T, p), FqX_mul(FqX_mulu(FqX_sqr(d0, T, p), 2, T, p), h0, T, p), T, p), 3, T, p);
    ddh13 = FqX_mulu(FqX_add(FqX_mul(dd1, h12, T, p), FqX_mul(FqX_mulu(FqX_sqr(d1, T, p), 2, T, p), h1, T, p), T, p), 3, T, p);
    ddh23 = FqX_mulu(FqX_add(FqX_mul(dd2, h22, T, p), FqX_mul(FqX_mulu(FqX_sqr(d2, T, p), 2, T, p), h2, T, p), T, p), 3, T, p);
    ddh012 = FqX_add(FqX_add(FqX_add(FqX_mul(FqX_mul(dd0, h1, T, p), h2, T, p), FqX_mul(FqX_mul(h0, dd1, T, p), h2, T, p), T, p), FqX_mul(FqX_mul(h0, h1, T, p), dd2, T, p), T, p), FqX_mulu(FqX_add(FqX_add(FqX_mul(FqX_mul(d0, d1, T, p), h2, T, p), FqX_mul(FqX_mul(d0, h1, T, p), d2, T, p), T, p), FqX_mul(FqX_mul(h0, d1, T, p), d2, T, p), T, p), 2, T, p), T, p);
    ddR1 = FqX_sub(ddh13, FqX_mulu(ddh012, 3, T, p), T, p);
    ddR2 = FqX_add(FqX_add(FqX_Fq_mul(ddh23, Fq_sqr(j, T, p), T, p), FqX_Fq_mul(dh23, Fq_mulu(j, 4, T, p), T, p), T, p), FqX_mulu(h23, 2, T, p), T, p);
    ddR = FqX_add(FqX_add(RgX_shift_shallow(ddR2, t2), RgX_shift_shallow(FqX_add(FqX_mulu(dR1, 2, T, p), FqX_Fq_mul(ddR1, j, T, p), T, p), 1), T, p), RgX_shift_shallow(ddh03, t0), T, p);
    return gerepilecopy(av, mkvec3(R ,dR ,ddR));
  }
}

static GEN
meqn_j(struct meqn *MEQN, GEN j, long ell, GEN T, GEN p)
{
  if (MEQN->type=='J')
  {
    MEQN->eval = Fq_polmodular_eval(MEQN->eq, j, ell, T, p, MEQN->vy);
    return gel(MEQN->eval, 1);
  }
  else
    return FqXY_evalx(MEQN->eq, j, T, p);
}

static GEN
find_isogenous_from_J(GEN a4, GEN a6, ulong ell, struct meqn *MEQN, GEN g, GEN T, GEN pp, long e)
{ 
  pari_sp ltop = avma;
  GEN meqn = MEQN->eval;
  GEN p = e==1 ? pp: powiu(pp, e);
  GEN h;
  GEN C4, C6, C4t, C6t;
  GEN j, jp, jtp, jtp2, jtp3;
  GEN Py, Pxy, Pyy, Pxj, Pyj, Pxxj, Pxyj, Pyyj;
  GEN s0, s1, s2, s3;
  GEN den, D, co, cot, c0, p_1, a4tilde, a6tilde;
  if (signe(g) == 0 || signe(Fq_sub(g, utoi(1728), T, p)) == 0)
  {
    if (DEBUGLEVEL>0) err_printf("[J: g=%ld]",signe(g)==0 ?0: 1728);
    avma = ltop; return NULL;
  }
  C4 = Fq_mul(a4, stoi(-48), T, p);
  C6 = Fq_mul(a6, stoi(-864), T, p);
  if (signe(C4)==0 || signe(C6)==0)
  {
    if (DEBUGLEVEL>0) err_printf("[J: C%ld=0]",signe(C4)==0 ?4: 6);
    avma = ltop; return NULL;
  }
  j = Zq_ellj(a4, a6, T, p, pp, e);
  jp = Fq_mul(j, Zq_div_safe(C6, C4, T, p, pp, e), T, p);
  co = corr(C4, C6, T, p, pp, e);
  Py = RgX_deriv(gel(meqn, 1));
  Pxy = RgX_deriv(gel(meqn,2));
  Pyy = RgX_deriv(Py);
  Pxj = FqX_eval(gel(meqn, 2), g, T, p);
  if (signe(Pxj)==0)
  {
    if (DEBUGLEVEL>0) err_printf("[J: Pxj=0]");
    avma = ltop; return NULL;
  }
  Pyj = FqX_eval(Py, g, T, p);
  Pxxj = FqX_eval(gel(meqn, 3), g, T, p);
  Pxyj = FqX_eval(Pxy, g, T, p);
  Pyyj = FqX_eval(Pyy, g, T, p);
  jtp = Fq_div(Fq_mul(jp, Zq_div_safe(Pxj, Pyj, T, p, pp, e), T, p), negi(utoi(ell)), T, p);
  jtp2 = Fq_sqr(jtp,T,p);
  jtp3 = Fq_mul(jtp,jtp2,T,p);
  den = Fq_mul(Fq_sqr(g,T,p),Fq_sub(g,utoi(1728),T,p),T, p);
  D  =  Zq_inv(den,T,p,pp, e);
  C4t = Fq_mul(jtp2,Fq_mul(g, D, T, p), T, p);
  C6t = Fq_mul(jtp3, D, T, p);
  s0 = Fq_mul(Fq_sqr(jp, T, p), Pxxj, T, p);
  s1 = Fq_mul(Fq_mulu(Fq_mul(jp,jtp,T,p),2*ell,T,p), Pxyj, T, p);
  s2 = Fq_mul(Fq_mulu(jtp2,ell*ell,T,p), Pyyj, T, p);
  s3 = Zq_div_safe(Fq_add(s0, Fq_add(s1, s2, T, p), T, p),Fq_mul(jp, Pxj, T, p),T,p,pp,e);
  cot = corr(C4t, C6t, T, p, pp, e);
  c0 = Fq_sub(co,Fq_mulu(cot,ell,T,p),T,p);
  p_1 = Fq_div(Fq_mulu(Fq_add(s3, c0, T, p),ell,T,p),stoi(-4),T,p);
  a4tilde = Fq_mul(Fq_div(C4t, stoi(-48), T, p),powuu(ell,4), T, p);
  a6tilde = Fq_mul(Fq_div(C6t, stoi(-864), T, p),powuu(ell,6), T, p);
  if(e>1)
    h = find_kernel_LS(a4, a6, ell, a4tilde, a6tilde, p_1, T, p, pp, e);
  else
    h = find_kernel_BMSS(a4, a6, ell, a4tilde, a6tilde, p_1, T, p);
  if (!h) return NULL;
  return gerepilecopy(ltop, mkvec3(a4tilde, a6tilde, h));
}

static GEN
find_isogenous(GEN a4,GEN a6, ulong ell, struct meqn *MEQN, GEN g, GEN T,GEN p)
{
  ulong pp = itou_or_0(p);
  long e= (pp && pp <= ell+2*BMSSPREC) ? 3 : 1;//I'm not sure 3 is enough, but in all my tests there was no crash
  if (e > 1)
  {
    GEN pe = powiu(p, e);
    GEN meqnj = meqn_j(MEQN, Zq_ellj(a4, a6, T, pe, p, e), ell, T, pe);
    if(gequal0(FqX_eval(RgX_deriv(meqnj),g,T,p))){return NULL;}
    g = ZqX_liftroot(meqnj, g, T, p, e);
  }
  if(MEQN->type == 'C'&&e>1) return NULL;//TODO: get suitable find_isogenous_from_canonical and find_isogenous_from_J for p-adics
  return (MEQN->type == 'C')
    ? find_isogenous_from_canonical(a4, a6, ell, MEQN, g, T, p, e)
    : (MEQN->type == 'A')
    ? find_isogenous_from_Atkin(a4, a6, ell, MEQN, g, T, p, e)
    : find_isogenous_from_J(a4, a6, ell, MEQN, g, T, p, e);
}

static GEN
FqX_homogenous_eval(GEN P, GEN A, GEN B, GEN T, GEN p)
{
  long d = degpol(P), i, v = varn(A);
  GEN s =  scalar_ZX_shallow(gel(P, d+2), v), Bn = pol_1(v);
  for (i = d-1; i >= 0; i--)
  {
    Bn = FqX_mul(Bn, B, T, p);
    s = FqX_add(FqX_mul(s, A, T, p), FqX_Fq_mul(Bn, gel(P,i+2), T, p), T, p);
  }
  return s;
}

static GEN
FqX_homogenous_div(GEN P, GEN Q, GEN A, GEN B, GEN T, GEN p)
{
  GEN z = cgetg(3, t_RFRAC);
  long d = degpol(Q)-degpol(P);
  gel(z, 1) = FqX_homogenous_eval(P, A, B, T, p);
  gel(z, 2) = FqX_homogenous_eval(Q, A, B, T, p);
  if (d > 0)
    gel(z, 1) = FqX_mul(gel(z, 1), FqX_powu(B, d, T, p), T, p);
  else if (d < 0)
    gel(z, 2) = FqX_mul(gel(z, 2), FqX_powu(B, -d, T, p), T, p);
  return z;
}

static GEN
find_kernel_power(GEN Eba4, GEN Eba6, GEN Eca4, GEN Eca6, ulong ell, struct meqn *MEQN, GEN kpoly, GEN Ib, GEN T, GEN p)
{
  pari_sp ltop = avma, btop;
  GEN a4t, a6t, gtmp;
  GEN num_iso = FqX_numer_isog_abscissa(kpoly, Eba4, Eba6, T, p, 0);
  GEN mpoly = meqn_j(MEQN, Fq_ellj(Eca4, Eca6, T, p), ell, T, p);
  GEN mroots = FqX_roots(mpoly, T, p);
  GEN kpoly2 = FqX_sqr(kpoly, T, p);
  long i, l1 = lg(mroots);
  btop = avma;
  for (i = 1; i < l1; i++)
  {
    GEN h;
    GEN tmp = find_isogenous(Eca4, Eca6, ell, MEQN, gel(mroots, i), T, p);
    if (!tmp) { avma = ltop; return NULL; }
    a4t =  gel(tmp, 1);
    a6t =  gel(tmp, 2);
    gtmp = gel(tmp, 3);

    /*check that the kernel kpoly is the good one */
    h = FqX_homogenous_eval(gtmp, num_iso, kpoly2, T, p);
    if (signe(Fq_elldivpolmod(Eba4, Eba6, ell, h, T, p)))
    {
      GEN Ic = FqX_homogenous_div(num_iso, kpoly2, numer(Ib), denom(Ib), T, p);
      GEN kpoly_new = FqX_homogenous_eval(gtmp, numer(Ic), denom(Ic), T, p);
      return gerepilecopy(ltop, mkvecn(5, a4t, a6t, kpoly_new, gtmp, Ic));
    }
    avma = btop;
  }
  pari_err_BUG("failed to find kernel polynomial");
  return NULL; /*NOT REACHED*/
}

/****************************************************************************/
/*                                  TRACE                                   */
/****************************************************************************/
enum mod_type {MTpathological, MTAtkin, MTElkies, MTone_root, MTroots};

static GEN
Flxq_study_eqn(long ell, GEN mpoly, GEN T, ulong p, long *pt_dG, long *pt_r)
{
  GEN Xq = FlxqX_Frobenius(mpoly, T, p);
  GEN G  = FlxqX_gcd(FlxX_sub(Xq, pol_x(0), p), mpoly, T, p);
  *pt_dG = degpol(G);
  if (!*pt_dG)
  {
    GEN L = FlxqXQ_matrix_pow(Xq, ell+1, ell+1, mpoly, T, p);
    long vT = get_Flx_var(T);
    long s = ell + 1 - FlxqM_rank(FlxM_Flx_add_shallow(L, Fl_to_Flx(p-1, vT), p), T, p);
    *pt_r = (ell + 1)/s;
    return NULL;
  }
  return gel(FlxqX_roots(G, T, p), 1);
}

static GEN
Fp_study_eqn(long ell, GEN mpoly, GEN p, long *pt_dG, long *pt_r)
{
  GEN T  = FpX_get_red(mpoly, p);
  GEN XP = FpX_Frobenius(T, p);
  GEN G  = FpX_gcd(FpX_sub(XP, pol_x(0), p), mpoly, p);
  *pt_dG = degpol(G);
  if (!*pt_dG)
  {
    long s = FpX_nbfact_Frobenius(T, XP, p);
    *pt_r = (ell + 1)/s;
    return NULL;
  }
  return FpX_oneroot(G, p);
}

static GEN
FpXQ_study_eqn(long ell, GEN mpoly, GEN T, GEN p, long *pt_dG, long *pt_r)
{
  GEN G;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN Tp = ZXT_to_FlxT(T,pp);
    GEN mpolyp = ZXX_to_FlxX(mpoly,pp,get_FpX_var(T));
    G = Flxq_study_eqn(ell, mpolyp, Tp, pp, pt_dG, pt_r);
    return G ? Flx_to_ZX(G): NULL;
  }
  else
  {
    GEN Xq = FpXQX_Frobenius(mpoly, T, p);
    G  = FpXQX_gcd(FpXX_sub(Xq, pol_x(0), p), mpoly, T, p);
    *pt_dG = degpol(G);
    if (!*pt_dG)
    {
      GEN L = FpXQXQ_matrix_pow(Xq, ell+1, ell+1, mpoly, T, p);
      long s = ell + 1 - FqM_rank(RgM_Rg_add(L, gen_m1), T, p);
      *pt_r = (ell + 1)/s;
      return NULL;
    }
    return gel(FpXQX_roots(G, T, p), 1);
  }
}

/* Berlekamp variant */
static GEN
study_modular_eqn(long ell, GEN mpoly, GEN T, GEN p, enum mod_type *mt, long *ptr_r)
{
  pari_sp ltop = avma;
  GEN g = gen_0;
  *ptr_r = 0; /*gcc -Wall*/
  if (degpol(FqX_gcd(mpoly, FqX_deriv(mpoly, T, p), T, p)) > 0)
    *mt = MTpathological;
  else
  {
    long dG;
    g = T ? FpXQ_study_eqn(ell, mpoly, T, p, &dG, ptr_r)
            : Fp_study_eqn(ell, mpoly, p, &dG, ptr_r);
    switch(dG)
    {
      case 0:  *mt = MTAtkin; break;
      case 1:  *mt = MTone_root; break;
      case 2:  *mt = MTElkies;   break;
      default: *mt = (dG == ell + 1)? MTroots: MTpathological;
    }
  }
  if (DEBUGLEVEL) switch(*mt)
  {
    case MTone_root: err_printf("One root\t"); break;
    case MTElkies: err_printf("Elkies\t"); break;
    case MTroots: err_printf("l+1 roots\t"); break;
    case MTAtkin: err_printf("Atkin\t"); break;
    case MTpathological: err_printf("Pathological\n"); break;
  }
  return g ? gerepilecopy(ltop, g): NULL;
}

/*Returns the trace modulo ell^k when ell is an Elkies prime */
static GEN
find_trace_Elkies_power(GEN a4, GEN a6, ulong ell, long k, struct meqn *MEQN, GEN g, GEN tr, GEN q, GEN T, GEN p, ulong smallfact, pari_timer *ti)
{
  pari_sp ltop = avma, btop;
  GEN tmp, Eba4, Eba6, Eca4, Eca6, Ib, kpoly;
  ulong lambda, ellk = upowuu(ell, k), pellk = umodiu(q, ellk);
  long cnt;

  if (DEBUGLEVEL) { err_printf("mod %ld", ell); }
  Eba4 = a4;
  Eba6 = a6;
  tmp = find_isogenous(a4,a6, ell, MEQN, g, T, p);
  if (!tmp) { avma = ltop; return NULL; }
  Eca4 =  gel(tmp, 1);
  Eca6 =  gel(tmp, 2);
  kpoly = gel(tmp, 3);
  Ib = pol_x(0);
  lambda = tr ? find_eigen_value_oneroot(a4, a6, ell, tr, kpoly, T, p):
                find_eigen_value_power(a4, a6, ell, 1, 1, kpoly, T, p);
  if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(ti));
  if (smallfact && smallfact%ell!=0)
  {
    ulong pell = pellk%ell;
    ulong ap = Fl_add(lambda, Fl_div(pell, lambda, ell), ell);
    if (Fl_sub(pell, ap, ell)==ell-1) { avma = ltop; return mkvecsmall(ap); }
  }
  btop = avma;
  for (cnt = 2; cnt <= k; cnt++)
  {
    GEN tmp;
    if (DEBUGLEVEL) err_printf(", %Ps", powuu(ell, cnt));
    tmp = find_kernel_power(Eba4, Eba6, Eca4, Eca6, ell, MEQN, kpoly, Ib, T, p);
    if (!tmp) { avma = ltop; return NULL; }
    lambda = find_eigen_value_power(a4, a6, ell, cnt, lambda, gel(tmp,3), T, p);
    Eba4 = Eca4;
    Eba6 = Eca6;
    Eca4 = gel(tmp,1);
    Eca6 = gel(tmp,2);
    kpoly = gel(tmp,4);
    Ib = gel(tmp, 5);
    if (gc_needed(btop, 1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"find_trace_Elkies_power");
      gerepileall(btop, 6, &Eba4, &Eba6, &Eca4, &Eca6, &kpoly, &Ib);
    }
    if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(ti));
  }
  avma = ltop;
  return mkvecsmall(Fl_add(lambda, Fl_div(pellk, lambda, ellk), ellk));
}

/*Returns the possible values of the trace when ell is an Atkin prime, */
/*given r the splitting degree of the modular equation at J = E.j */
static GEN
find_trace_Atkin(ulong ell, long r, GEN q)
{
  pari_sp ltop = avma;
  long nval = 0;
  ulong teta, pell = umodiu(q, ell), invp = Fl_inv(pell, ell);
  GEN val_pos = cgetg(1+ell, t_VECSMALL), P = gel(factoru(r), 1);
  GEN S = mkvecsmall4(0, pell, 0, 1);
  GEN U = mkvecsmall3(0, ell-1, 0);
  pari_sp btop = avma;
  if (r==2 && krouu(ell-pell, ell) < 0)
    val_pos[++nval] = 0;
  for (teta = 1; teta < ell; teta++, avma = btop)
  {
    ulong disc = Fl_sub(Fl_sqr(teta,ell), Fl_mul(4UL,pell,ell), ell);
    GEN a;
    if (krouu(disc, ell) >= 0) continue;
    S[3] = Fl_neg(teta, ell);
    U[3] = Fl_mul(invp, teta, ell);
    a = Flxq_powu(U, r/P[1], S, ell);
    if (!Flx_equal1(a) && Flx_equal1(Flxq_powu(a, P[1], S, ell)))
    {
      pari_sp av = avma;
      long i, l=lg(P);
      for (i = 2; i < l; i++, avma = av)
        if (Flx_equal1(Flxq_powu(U, r/P[i], S, ell))) break;
      if (i==l) val_pos[++nval] = teta;
    }
  }
  return gerepileupto(ltop, vecsmall_shorten(val_pos, nval));
}

/*Returns the possible traces when there is only one root */
static GEN
find_trace_one_root(ulong ell, GEN q)
{
  ulong a = Fl_double(Fl_sqrt(umodiu(q,ell), ell), ell);
  return mkvecsmall2(a, ell - a);
}

static GEN
find_trace_lp1_roots(long ell, GEN q)
{
  ulong ell2 = ell * ell, pell = umodiu(q, ell2);
  ulong a  = Fl_sqrt(pell%ell, ell);
  ulong pa = Fl_add(Fl_div(pell, a, ell2), a, ell2);
  return mkvecsmall2(pa, ell2 - pa);
}

/*trace modulo ell^k: [], [t] or [t1,...,td] */
//requires the elliptic curve to be non singular which is not checked in SEA atm.
//TODO in low caracteristic, for instance in the field GF(53^53) with elliptic curve y^2=x^3+9x+4 I found most mt values were either MtAtkin or MTpathological. Then SEA would never finish and keep looking for non double root modular polynomial.
static GEN
find_trace(GEN a4, GEN a6, GEN j, ulong ell, GEN q, GEN T, GEN p, long *ptr_kt,
  ulong smallfact, long vx, long vy)
{
  pari_sp ltop = avma;
  GEN g, meqnj, tr, tr2;
  long kt, r;
  enum mod_type mt;
  struct meqn MEQN;
  pari_timer ti;

  kt = maxss((long)(log(expi(q)*LOG2)/log((double)ell)), 1);
  if (DEBUGLEVEL)
  { err_printf("SEA: Prime %5ld ", ell); timer_start(&ti); }
  (void) get_modular_eqn(&MEQN, ell, vx, vy);
  meqnj = meqn_j(&MEQN, j, ell, T, p);
  g = study_modular_eqn(ell, meqnj, T, p, &mt, &r);
  /* If l is an Elkies prime, search for a factor of the l-division polynomial.
  * Then deduce the trace by looking for eigenvalues of the Frobenius by
  * computing modulo this factor */
  switch (mt)
  {
  case MTone_root:
	
    tr2 = find_trace_one_root(ell, q);
    kt = 1;
    /* Must take k = 1 because we can't apply Hensel: no guarantee that a
     * root mod ell^2 exists */
    tr = find_trace_Elkies_power(a4,a6,ell, kt, &MEQN, g, tr2, q, T, p, smallfact, &ti);
    if (!tr) tr = tr2;
    break;
  case MTElkies:
    /* Contrary to MTone_root, may look mod higher powers of ell */
    if (abscmpiu(p, 2*ell+3) <= 0)
      kt = 1; /* Not implemented in this case */
    tr = find_trace_Elkies_power(a4,a6,ell, kt, &MEQN, g, NULL, q, T, p, smallfact, &ti);
    if (!tr)
    {
      if (DEBUGLEVEL) err_printf("[fail]\n");
      avma = ltop; return NULL;
    }
    break;
  case MTroots:
    tr = find_trace_lp1_roots(ell, q);
    kt = 2;
    break;
  case MTAtkin:
    tr = find_trace_Atkin(ell, r, q);
    if (lg(tr)==1) pari_err_PRIME("ellap",p);
    kt = 1;
    break;
  default: /* case MTpathological: */
    avma = ltop; return NULL;
  }
  if (DEBUGLEVEL) {
    long n = lg(tr)-1;
    if (n > 1 || mt == MTAtkin)
    {
      err_printf("%3ld trace(s)",n);
      if (DEBUGLEVEL>1) err_printf(" [%ld ms]", timer_delay(&ti));
    }
    if (n > 1) err_printf("\n");
  }
  *ptr_kt = kt;
  return gerepileupto(ltop, tr);
}

/* A partition of compile_atkin in baby and giant is represented as the binary
   developpement of an integer; if the i-th bit is 1, the i-th prime in
   compile-atkin is a baby. The optimum is obtained when the ratio between
   the number of possibilities for traces modulo giants (p_g) and babies (p_b)
   is near 3/4. */
static long
separation(GEN cnt)
{
  pari_sp btop;
  long k = lg(cnt)-1, l = (1L<<k)-1, best_i, i, j;
  GEN best_r, P, P3, r;

  P = gen_1;
  for (j = 1; j <= k; ++j) P = mulis(P, cnt[j]);
  /* p_b * p_g = P is constant */
  P3 = mulsi(3, P);
  btop = avma;
  best_i = 0;
  best_r = P3;
  for (i = 1; i < l; i++)
  {
    /* scan all possibilities */
    GEN p_b = gen_1;
    for (j = 0; j < k; j++)
      if (i & (1L<<j)) p_b = mulis(p_b, cnt[1+j]);
    r = subii(shifti(sqri(p_b), 2), P3); /* (p_b/p_g - 3/4)*4*P */
    if (!signe(r)) { best_i = i; break; }
    if (abscmpii(r, best_r) < 0) { best_i = i; best_r = r; }
    if (gc_needed(btop, 1))
      best_r = gerepileuptoint(btop, best_r);
  }
  return best_i;
}

/* x VEC defined modulo P (= *P), y VECSMALL modulo q, (q,P) = 1. */
/* Update in place:
 *   x to vector mod q P congruent to x mod P (resp. y mod q). */
/*   P ( <-- qP ) */
static void
multiple_crt(GEN x, GEN y, GEN q, GEN P)
{
  pari_sp ltop = avma, av;
  long i, j, k, lx = lg(x)-1, ly = lg(y)-1;
  GEN  a1, a2, u, v, A2X;
  (void)bezout(P,q,&u,&v);
  a1 = mulii(P,u);
  a2 = mulii(q,v); A2X = ZC_Z_mul(x, a2);
  av = avma; affii(mulii(P,q), P);
  for (i = 1, k = 1; i <= lx; i++, avma = av)
  {
    GEN a2x = gel(A2X,i);
    for (j = 1; j <= ly; ++j)
    {
      GEN t = Fp_add(Fp_mulu(a1, y[j], P), a2x, P);
      affii(t, gel(x, k++));
    }
  }
  setlg(x, k); avma = ltop;
}

/****************************************************************************/
/*                              MATCH AND SORT                              */
/****************************************************************************/

static GEN
possible_traces(GEN compile, GEN mask, GEN *P, long larger)
{
  GEN V, Pfinal = gen_1, C = shallowextract(compile, mask);
  long i, lfinal = 1, lC = lg(C), lP;
  pari_sp av = avma;

  for (i = 1; i < lC; i++)
  {
    GEN c = gel(C,i), t;
    Pfinal = mulii(Pfinal, gel(c,1));
    t = muluu(lfinal, lg(gel(c,2))-1);
    lfinal = itou(t);
  }
  Pfinal = gerepileuptoint(av, Pfinal);
  if (larger)
    lP = lgefint(shifti(Pfinal,1));
  else
    lP = lgefint(Pfinal);
  lfinal++;
  /* allocate room for final result */
  V = cgetg(lfinal, t_VEC);
  for (i = 1; i < lfinal; i++) gel(V,i) = cgeti(lP);

  {
    GEN c = gel(C,1), v = gel(c,2);
    long l = lg(v);
    for (i = 1; i < l; i++) affsi(v[i], gel(V,i));
    setlg(V, l); affii(gel(c,1), Pfinal); /* reset Pfinal */
  }
  for (i = 2; i < lC; i++)
  {
    GEN c = gel(C,i);
    multiple_crt(V, gel(c,2), gel(c,1), Pfinal); /* Pfinal updated! */
  }
  *P = Pfinal; return V;
}

static GEN
cost(long mask, GEN cost_vec)
{
  pari_sp ltop = avma;
  long i;
  GEN c = gen_1;
  for (i = 1; i < lg(cost_vec); i++)
    if (mask&(1L<<(i-1)))
      c = mulis(c, cost_vec[i]);
  return gerepileuptoint(ltop, c);
}

static GEN
value(long mask, GEN atkin, long k)
{
  pari_sp ltop = avma;
  long i;
  GEN c = gen_1;
  for (i = 1; i <= k; i++)
    if (mask&(1L<<(i-1)))
      c = mulii(c, gmael(atkin, i, 1));
  return gerepileuptoint(ltop, c);
}

static void
set_cost(GEN B, long b, GEN cost_vec, long *pi)
{
  pari_sp av = avma;
  GEN costb = cost(b, cost_vec);
  long i = *pi;
  while (cmpii(costb, cost(B[i], cost_vec)) < 0) --i;
  B[++i] = b;
  *pi = i; avma = av;
}

static GEN
get_lgatkin(GEN compile_atkin, long k)
{
  GEN v = cgetg(k+1, t_VECSMALL);
  long j;
  for (j = 1; j <= k; ++j) v[j] = lg(gmael(compile_atkin, j, 2))-1;
  return v;
}

static GEN
champion(GEN atkin, long k, GEN bound_champ)
{
  const long two_k = 1L<<k;
  pari_sp ltop = avma;
  long i, j, n, i1, i2;
  GEN B, Bp, cost_vec, res = NULL;

  cost_vec = get_lgatkin(atkin, k);
  if (k == 1) return mkvec2(gen_1, utoipos(cost_vec[1]));

  B  = zero_zv(two_k);
  Bp = zero_zv(two_k);
  Bp[2] = 1;
  for (n = 2, j = 2; j <= k; j++)
  {
    long b;
    i = 1;
    for (i1 = 2, i2 = 1; i1 <= n; )
    {
      pari_sp av = avma;
      long b1 = Bp[i1], b2 = Bp[i2]|(1L<<(j-1));
      if (cmpii(value(b1, atkin, k), value(b2, atkin, k)) < 0)
        { b = b1; i1++; } else { b = b2; i2++; }
      avma = av;
      set_cost(B, b, cost_vec, &i);
    }
    for ( ; i2 <= n; i2++)
    {
      b = Bp[i2]|(1L<<(j-1));
      set_cost(B, b, cost_vec, &i);
    }
    n = i;
    for (i = 1; i <= n; i++)
      Bp[i] = B[i];
  }
  for (i = 1; i <= two_k; i++)
    if (B[i])
    {
      GEN b = cost (B[i], cost_vec);
      GEN v = value(B[i], atkin, k);
      if (cmpii(v, bound_champ) <=0) continue;
      if (res && gcmp(b, gel(res, 2)) >=0) continue;
      res = mkvec2(utoi(B[i]), b);
    }
  return gerepilecopy(ltop, res);
}

static GEN
compute_diff(GEN v)
{
  pari_sp av = avma;
  long i, l = lg(v) - 1;
  GEN diff = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(diff, i) = subii(gel(v, i+1), gel(v, i));
  return gerepileupto(av, ZV_sort_uniq(diff));
}

static int
cmp_atkin(void*E, GEN a, GEN b)
{
  long ta=typ(a)==t_INT, tb=typ(b)==t_INT, c;
  (void) E;
  if (ta || tb) return ta-tb;
  c = lg(gel(a,2)) - lg(gel(b,2));
  if (c) return c;
  return cmpii(gel(b,1), gel(a,1));
}

static void
add_atkin(GEN atkin, GEN trace, long *nb)
{
  long l = lg(atkin)-1;
  long i, k = gen_search(atkin, trace, 1, NULL, cmp_atkin);
  if (k==0 || k > l) return;
  for (i = l; i > k; i--)
    gel(atkin,i) = gel(atkin,i-1);
  if (typ(gel(atkin,l))==t_INT) (*nb)++;
  gel(atkin,k) = trace;
}

/* V = baby / giant, P = Pb / Pg */
static GEN
BSGS_pre(GEN *pdiff, GEN V, GEN P, void *E, const struct bb_group *grp)
{
  GEN diff = compute_diff(V);
  GEN pre = cgetg(lg(diff), t_VEC);
  long i, l = lg(diff);
  gel(pre, 1) = grp->pow(E, P, gel(diff, 1));
  /* what we'd _really_ want here is a hashtable diff[i] -> pre[i]  */
  for (i = 2; i < l; i++)
  {
    pari_sp av = avma;
    GEN d = subii(gel(diff, i), gel(diff, i-1));
    GEN Q = grp->mul(E, gel(pre, i-1), grp->pow(E, P, d));
    gel(pre, i) = gerepilecopy(av, Q);
  }
  *pdiff = diff; return pre;
}

/* u = trace_elkies, Mu = prod_elkies. Let caller collect garbage */
/* Match & sort: variant from Lercier's thesis, section 11.2.3 */
/* baby/giant/table updated in place: this routines uses
 *   size(baby)+size(giant)+size(table)+size(table_ind) + O(log p)
 * bits of stack */
static GEN
match_and_sort(GEN compile_atkin, GEN Mu, GEN u, GEN q, void *E, const struct bb_group *grp)
{
  pari_sp av1, av2;
  GEN baby, giant, SgMb, Mb, Mg, den, Sg, dec_inf, div, pp1 = addis(q,1);
  GEN P, Pb, Pg, point, diff, pre, table, table_ind;
  long best_i, i, lbaby, lgiant, k = lg(compile_atkin)-1;
  GEN bound = sqrti(shifti(q, 2)), card;
  const long lcard = 100;
  long lq = lgefint(q), nbcard;
  pari_timer ti;

  if (k == 1)
  { /*only one Atkin prime, check the cardinality with random points */
    GEN r = gel(compile_atkin, 1), r1 = gel(r,1), r2 = gel(r,2);
    long l = lg(r2), j;
    GEN card = cgetg(l, t_VEC), Cs2, C, U;
    Z_chinese_pre(Mu, r1, &C,&U, NULL);
    Cs2 = shifti(C, -1);
    for (j = 1, i = 1; i < l; i++)
    {
      GEN t = Z_chinese_post(u, stoi(r2[i]), C, U, NULL);
      t = Fp_center(t, C, Cs2);
      if (abscmpii(t, bound) <= 0)
        gel(card, j++) = subii(pp1, t);
    }
    setlg(card, j);
    return gen_select_order(card, E, grp);
  }
  if (DEBUGLEVEL>=2) timer_start(&ti);
  av1 = avma;
  best_i = separation( get_lgatkin(compile_atkin, k) );
  avma = av1;

  baby  = possible_traces(compile_atkin, stoi(best_i), &Mb, 1);
  giant = possible_traces(compile_atkin, subis(int2n(k), best_i+1), &Mg, 0);
  lbaby = lg(baby);
  lgiant = lg(giant);
  den = Fp_inv(Fp_mul(Mu, Mb, Mg), Mg);
  av2 = avma;
  for (i = 1; i < lgiant; i++, avma = av2)
    affii(Fp_mul(gel(giant,i), den, Mg), gel(giant,i));
  gen_sort_inplace(giant, (void*)&cmpii, &cmp_nodata, NULL);
  Sg = Fp_mul(negi(u), den, Mg);
  den = Fp_inv(Fp_mul(Mu, Mg, Mb), Mb);
  dec_inf = divii(mulii(Mb,addii(Mg,shifti(Sg,1))), shifti(Mg,1));
  togglesign(dec_inf); /* now, dec_inf = ceil(- (Mb/2 + Sg Mb/Mg) ) */
  div = mulii(truedivii(dec_inf, Mb), Mb);
  av2 = avma;
  for (i = 1; i < lbaby; i++, avma = av2)
  {
    GEN b = addii(Fp_mul(Fp_sub(gel(baby,i), u, Mb), den, Mb), div);
    if (cmpii(b, dec_inf) < 0) b = addii(b, Mb);
    affii(b, gel(baby,i));
  }
  gen_sort_inplace(baby, (void*)&cmpii, &cmp_nodata, NULL);

  SgMb = mulii(Sg, Mb);
  card = cgetg(lcard+1,t_VEC);
  for (i = 1; i <= lcard; i++) gel(card,i) = cgetipos(lq+1);

  av2 = avma;
MATCH_RESTART:
  avma = av2;
  nbcard = 0;
  P = grp->rand(E);
  point = grp->pow(E,P, Mu);
  Pb = grp->pow(E,point, Mg);
  Pg = grp->pow(E,point, Mb);
  /* Precomputation for babies */
  pre = BSGS_pre(&diff, baby, Pb, E, grp);

  /*Now we compute the table of babies, this table contains only the */
  /*lifted x-coordinate of the points in order to use less memory */
  table = cgetg(lbaby, t_VECSMALL);
  av1 = avma;
  /* (p+1 - u - Mu*Mb*Sg) P - (baby[1]) Pb */
  point = grp->pow(E,P, subii(subii(pp1, u), mulii(Mu, addii(SgMb, mulii(Mg, gel(baby,1))))));
  table[1] = grp->hash(gel(point,1));
  for (i = 2; i < lbaby; i++)
  {
    GEN d = subii(gel(baby, i), gel(baby, i-1));
    point =  grp->mul(E, point, grp->pow(E, gel(pre, ZV_search(diff, d)), gen_m1));
    table[i] = grp->hash(gel(point,1));
    if (gc_needed(av1,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"match_and_sort, baby = %ld", i);
      point = gerepileupto(av1, point);
    }
  }
  avma = av1;
  /* Precomputations for giants */
  pre = BSGS_pre(&diff, giant, Pg, E, grp);

  /* Look for a collision among the x-coordinates */
  table_ind = vecsmall_indexsort(table);
  table = perm_mul(table,table_ind);

  av1 = avma;
  point = grp->pow(E, Pg, gel(giant, 1));
  for (i = 1; ; i++)
  {
    GEN d;
    long h = grp->hash(gel(point, 1));
    long s = zv_search(table, h);
    if (s) {
      while (table[s] == h && s) s--;
      for (s++; s < lbaby && table[s] == h; s++)
      {
        GEN B = gel(baby,table_ind[s]), G = gel(giant,i);
        GEN GMb = mulii(G, Mb), BMg = mulii(B, Mg);
        GEN Be = subii(subii(pp1, u), mulii(Mu, addii(SgMb, BMg)));
        GEN Bp = grp->pow(E,P, Be);
        /* p+1 - u - Mu (Sg Mb + GIANT Mb + BABY Mg) */
        if (gequal(gel(Bp,1),gel(point,1)))
        {
          GEN card1 = subii(Be, mulii(Mu, GMb));
          GEN card2 = addii(card1, mulii(mulsi(2,Mu), GMb));
          if (DEBUGLEVEL>=2) timer_printf(&ti,"match_and_sort");
          if (abscmpii(subii(pp1, card1), bound) <= 0)
            affii(card1, gel(card, ++nbcard));
          if (nbcard >= lcard) goto MATCH_RESTART;
          if (abscmpii(subii(pp1, card2), bound) <= 0)
            affii(card2, gel(card, ++nbcard));
          if (nbcard >= lcard) goto MATCH_RESTART;
        }
      }
    }
    if (i==lgiant-1) break;
    d = subii(gel(giant, i+1), gel(giant, i));
    point = grp->mul(E,point, gel(pre, ZV_search(diff, d)));
    if (gc_needed(av1,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"match_and_sort, giant = %ld", i);
      point = gerepileupto(av1, point);
    }
  }
  setlg(card, nbcard+1);
  return gen_select_order(card, E, grp);
}

static GEN
get_bound_bsgs(long lp)
{
  GEN B;
  if (lp <= 160)
    B = divru(powru(dbltor(1.048), lp), 9);
  else if (lp <= 192)
    B = divrr(powru(dbltor(1.052), lp), dbltor(16.65));
  else
    B = mulrr(powru(dbltor(1.035), minss(lp,307)), dbltor(1.35));
  return mulru(B, 1000000);
}

/*FIXME: the name of the function does not quite match what it does*/
static const struct bb_group *
get_FqE_group(void ** pt_E, GEN a4, GEN a6, GEN T, GEN p)
{
  if (!T) return get_FpE_group(pt_E,a4,a6,p);
  else if (lgefint(p)==3)
  {
    ulong pp = uel(p,2);
    GEN Tp = ZXT_to_FlxT(T,pp);
    return get_FlxqE_group(pt_E, Fq_to_Flx(a4, Tp, pp), Fq_to_Flx(a6, Tp, pp),
                           Tp, pp);
  }
  return get_FpXQE_group(pt_E,a4,a6,T,p);
}

/* E is an elliptic curve defined over Z or over Fp in ellinit format, defined
 * by the equation E: y^2 + a1*x*y + a2*y = x^3 + a2*x^2 + a4*x + a6
 * p is a prime number
 * set smallfact to stop whenever a small factor of the order, not dividing smallfact,
 * is detected. Useful when searching for a good curve for cryptographic
 * applications */
//NEED TO CHECK IF THE CURVE IF SUPERSINGULAR
GEN
Fq_ellcard_SEA(GEN a4, GEN a6, GEN q, GEN T, GEN p, ulong smallfact)
{
  const long MAX_ATKIN = 21;
  pari_sp ltop = avma, btop;
  long ell, i, nb_atkin, vx,vy;
  GEN TR, TR_mod, compile_atkin, bound, bound_bsgs, champ;
  GEN prod_atkin = gen_1, max_traces = gen_0;
  GEN j;
  double bound_gr = 1.;
  const double growth_factor = 1.26;
  forprime_t TT;

  j = Fq_ellj(a4, a6, T, p);
  if (signe(j) == 0 || signe(Fq_sub(j, utoi(1728), T, p)) == 0)
    return T ? FpXQ_ellcard(Fq_to_FpXQ(a4, T, p), Fq_to_FpXQ(a6, T, p), T, p)
             : Fp_ellcard(a4, a6, p);
  /*First compute the trace modulo 2 */
  switch(FqX_nbroots(rhs(a4, a6, 0), T, p))
  {
  case 3: /* bonus time: 4 | #E(Fq) = q+1 - t */
    i = mod4(q)+1; if (i > 2) i -= 4;
    TR_mod = utoipos(4);
    TR = stoi(i); break;
  case 1:
    TR_mod = gen_2;
    TR = gen_0; break;
  default : /* 0 */
    TR_mod = gen_2;
    TR = gen_1; break;
  }
  if (odd(smallfact) && !mpodd(TR))
  {
    if (DEBUGLEVEL) err_printf("Aborting: #E(Fq) divisible by 2\n");
    avma = ltop; return gen_0;
  }
  vy = fetch_var();
  vx = fetch_var_higher();

  /* compile_atkin is a vector containing informations about Atkin primes,
   * informations about Elkies primes lie in Mod(TR, TR_mod). */
  u_forprime_init(&TT, 3, ULONG_MAX);
  bound = sqrti(shifti(q, 4));
  bound_bsgs = get_bound_bsgs(expi(q));
  compile_atkin = zerovec(MAX_ATKIN); nb_atkin = 0;
  btop = avma;
  while ( (ell = u_forprime_next(&TT)) )
  {
    long ellkt, kt = 1, nbtrace;
    GEN trace_mod;
    if (absequalui(ell, p)) continue;
    trace_mod = find_trace(a4, a6, j, ell, q, T, p, &kt, smallfact, vx,vy);
    if (!trace_mod) continue;

    nbtrace = lg(trace_mod) - 1;
    ellkt = (long)upowuu(ell, kt);
    if (nbtrace == 1)
    {
      long t_mod_ellkt = trace_mod[1];
      if (smallfact && smallfact%ell!=0)
      { /* does ell divide q + 1 - t ? */
        long card_mod_ell = umodsu(umodiu(q,ell) + 1 - t_mod_ellkt, ell) ;
        if (!card_mod_ell)
        {
          if (DEBUGLEVEL)
            err_printf("\nAborting: #E(Fq) divisible by %ld\n",ell);
          avma = ltop; return gen_0;
        }
      }
      (void)Z_incremental_CRT(&TR, t_mod_ellkt, &TR_mod, ellkt);
      if (DEBUGLEVEL)
        err_printf(", missing %ld bits\n",expi(bound)-expi(TR_mod));
    }
    else
    {
      add_atkin(compile_atkin, mkvec2(utoipos(ellkt), trace_mod), &nb_atkin);
      prod_atkin = value(-1, compile_atkin, nb_atkin);
    }
    if (cmpii(mulii(TR_mod, prod_atkin), bound) > 0)
    {
      GEN bound_tr;
      if (!nb_atkin) return gerepileuptoint(ltop, subii(addis(q, 1), TR));
      bound_tr = mulrr(bound_bsgs, dbltor(bound_gr));
      bound_gr *= growth_factor;
      if (signe(max_traces))
      {
        max_traces = divis(muliu(max_traces,nbtrace), ellkt);
        if (DEBUGLEVEL>=3)
          err_printf("At least %Ps remaining possibilities.\n",max_traces);
      }
      if (cmpir(max_traces, bound_tr) < 0)
      {
        GEN bound_atkin = truedivii(bound, TR_mod);
        champ = champion(compile_atkin, nb_atkin, bound_atkin);
        max_traces = gel(champ,2);
        if (DEBUGLEVEL>=2)
          err_printf("%Ps remaining possibilities.\n", max_traces);
        if (cmpir(max_traces, bound_tr) < 0)
        {
          GEN res, cat = shallowextract(compile_atkin, gel(champ,1));
          const struct bb_group *grp;
          void *E;
          if (DEBUGLEVEL)
            err_printf("Match and sort for %Ps possibilities.\n", max_traces);
          delete_var(); delete_var();
          grp = get_FqE_group(&E,a4,a6,T,p);
          res = match_and_sort(cat, TR_mod, TR, q, E, grp);
          return gerepileuptoint(ltop, res);
        }
      }
    }
    if (gc_needed(btop, 1))
      gerepileall(btop,5, &TR,&TR_mod, &compile_atkin, &max_traces, &prod_atkin);
  }
  return NULL;/*not reached*/
}

GEN
Fp_ellcard_SEA(GEN a4, GEN a6, GEN p, ulong smallfact)
{
  return Fq_ellcard_SEA(a4, a6, p, NULL, p, smallfact);
}

int main()
{	
  pari_init(10000000000,2);

  temps_kernel=clock();
  temps_equadiff=clock();
  temps_euclide=clock();
  temps_comp=clock();
  temps_total=clock();
  GEN p=gp_read_str("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084171");
  GEN a4=gp_read_str("1161082089530208694079656498916828112373758883");
  GEN a6=gp_read_str("564989168281123737588839386922876088484808");
  clock_t tmp=clock();
  pari_printf("%Ps\n",Fp_ellcard(a4,a6,p));
  temps_total=clock()-tmp;
  printf("temps kernel :%f\ntemps equadiff :%f\n",(double)temps_kernel/CLOCKS_PER_SEC,(double)temps_equadiff/CLOCKS_PER_SEC);
  printf("temps euclide :%f\ntemps comp :%f\n",(double)temps_euclide/CLOCKS_PER_SEC,(double)temps_comp/CLOCKS_PER_SEC);
  printf("temps total:%f\n",(double)temps_total/CLOCKS_PER_SEC);
  return 0;
}
