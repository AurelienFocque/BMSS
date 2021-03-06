
#include "pari/pari.h"
#include "pari/paripriv.h"
#define BMSSPREC 1
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
static GEN
Zq_divexact(GEN a, GEN b)
{
  return typ(a)==t_INT ? diviiexact(a, b): ZX_Z_divexact(a, b);
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
    if (v>w) {return NULL;}
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

static GEN FqX_modXn(GEN P,long n,GEN T,GEN p)
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
  if(t2>110)// compute the whole product is quicker
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
  GEN ret;
  GEN tmpol;
  if(lg(H)==6)
  {	
    tmpol=FqX_sqr(S,T,p);
    ret=FqXn_mul(tmpol,S,n,T,p);	
    ret=FqX_add(FqX_Fq_add(FqX_Fq_mul(tmpol,gel(H,4),T,p),gen_1,T,p),FqX_Fq_mul(ret,gel(H,5),T,p),T,p);
    ret=FqXn_mul(ret,RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);
    return ret;
  }
  if(lg(H)==5)
  {
    tmpol=FqX_sqr(S,T,p);
    ret=FqX_Fq_add(FqX_Fq_mul(tmpol,gel(H,4),T,p),gen_1,T,p);
    ret=FqXn_mul(ret,RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);
    return ret;
  }
  else
  {
    ret=FqXn_mul(mkpoln(1,Fq_ui(1,T,p)),RgX_shift(S,-1),n,T,p);
    gerepileupto(avma,ret);
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
  { //we compute the inverse and the sqrt at the same time, ret denotes the sqrt and i the inverse        
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
  return ret;
}
static GEN find_S(long m,GEN G,GEN H,GEN T,GEN p,GEN pp,long e)
//inspired of Luka De Feo thesis.
// requires p<2*m+1
//returns the approximation of the taylor serie solution of G*(S'^2)=(S/x)*(HoS) mod x^m
{   	
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
    // NB: there may be a way to calculate ki quicker computing only the high degree terms of (S/x)*HoS
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
  return S;
}
static GEN D_from_euclide_truncated(GEN R,long l,GEN T, GEN p)
//suitable for Fq
// given R=D.reverse()/N.reverse() mod x^2l return D
{	

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
  gerepileupto(avma,r1);
  return r1;
}

static GEN D_from_HGCD(GEN R,long l,GEN T, GEN p)
// given R=D.reverse()/N.reverse() mod x^2l return D
// not suitable for Fq
{
  GEN ret;
  GEN r1=R;
  GEN r0=RgX_shift(mkpoln(1,gen_1),2*l);
  GEN M=FpXQX_halfgcd(r0,r1,T, p);
  ret=gel( row(M,2),2);
  //ret stands for N.reverse() atm
  ret=FqXn_mul(FqX_red(ret,T,p),FqX_modXn(R,l,T,p),l,T,p);
  ret=FqX_normalize(RgX_recip(ret),T,p);
  gerepileupto(avma,ret);
  return ret;
}

GEN find_kernel_LS(GEN a4,GEN a6,long l,GEN b4,GEN b6,GEN T,GEN p,GEN pp,long e)
//requires both the isogeny to be normalized and separable.
//suitable for padics when pp<l+2*BMSSPREC.
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
  D=FqXn_sqrt(D,l,T,pp);
  if(D==NULL){return NULL;}
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
  if(l==3)
  {
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
  if(lg(Ge)==(l-1)/2+3){return Ge;}
  else{return NULL;}
	
}

int main()
{	
  pari_init(10000000000,2);
  //EXEMPLE 1 LERCIER SIRVENT cf. https://hal.inria.fr/tel-00377306/document
  GEN pp=mkintn(1,5);	
  GEN a4=mkintn(1,1);
  GEN a6=mkintn(1,4);
  GEN b4=gneg(mkintn(1,7329));
  GEN b6=gneg(mkintn(1,3934));
  long l =11;
  long e = 6;
  pari_printf("Premier exemple de Lercier Sirvent\nkerpoly=%Ps\n",find_kernel_LS(a4,a6,l,b4,b6,NULL,gpowgs(pp,3),pp,3));
  //EXEMPLE 2 LERCIER SIRVENT
  pp=mkintn(1,7);
  GEN T=mkpoln(6,gen_1,gen_0,gen_0,gen_0,gen_1,mkintn(1,4));
  a4=mkpoln(4,mkintn(1,5),mkintn(1,2),mkintn(1,4),mkintn(1,6));
  a6=mkpoln(5,mkintn(1,6),mkintn(1,4),mkintn(1,5),mkintn(1,3),mkintn(1,4));
  b4=mkpoln(5,gneg(mkintn(1,104574295)),gneg(mkintn(1,111798340)),gneg(mkintn(1,21387164
  )),gneg(mkintn(1,24214869)),mkintn(1,36208471));
  b6=mkpoln(5,mkintn(1,88497100),mkintn(1,47971900),mkintn(1,32578586),mkintn(1,122102312),gneg(mkintn(1,83236646)));
  e=3;l=47;
  b4=Fq_red(b4,T,gpowgs(pp,e));
  b6=Fq_red(b6,T,gpowgs(pp,e));
  pari_printf("Second exemple de Lercier Sirvent\nkerpoly=%Ps\n",find_kernel_LS(a4,a6,l,b4,b6,T,gpowgs(pp,e),pp,e));

  // EXEMPLE DE BMSS cf. http://arxiv.org/abs/cs/0609020
  GEN p=mkintn(1,101);
  l=11;
  T=NULL;
  GEN sig=mkintn(1,25);
  a4=gen_1;
  a6=gen_1;
  b4=mkintn(1,75);
  b6=mkintn(1,16);
  pari_printf("Exemple BMSS\nkerpoly=%Ps\n",find_kernel_BMSS(a4, a6,l, b4, b6, sig,T,p));

  gerepileupto(avma,0);
  return 0;
}
