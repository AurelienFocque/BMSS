/* Copyright (C) 2000-2005  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/***********************************************************************/
/**                                                                   **/
/**               ARITHMETIC OPERATIONS ON POLYNOMIALS                **/
/**                         (third part)                              **/
/**                                                                   **/
/***********************************************************************/
#include "pari.h"
#include "paripriv.h"

/************************************************************************
 **                                                                    **
 **                      Ring membership                               **
 **                                                                    **
 ************************************************************************/
struct charact {
  GEN q;
  int isprime;
};
static void
char_update_prime(struct charact *S, GEN p)
{
  if (!S->isprime) { S->isprime = 1; S->q = p; }
  if (!equalii(p, S->q)) pari_err_MODULUS("characteristic", S->q, p);
}
static void
char_update_int(struct charact *S, GEN n)
{
  if (S->isprime)
  {
    if (dvdii(n, S->q)) return;
    pari_err_MODULUS("characteristic", S->q, n);
  }
  S->q = gcdii(S->q, n);
}
static void
charact(struct charact *S, GEN x)
{
  const long tx = typ(x);
  long i, l;
  switch(tx)
  {
    case t_INTMOD:char_update_int(S, gel(x,1)); break;
    case t_FFELT: char_update_prime(S, gel(x,4)); break;
    case t_COMPLEX: case t_QUAD:
    case t_POLMOD: case t_POL: case t_SER: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      l = lg(x);
      for (i=lontyp[tx]; i < l; i++) charact(S,gel(x,i));
      break;
    case t_LIST:
      x = list_data(x);
      if (x) charact(S, x);
      break;
  }
}
static void
charact_res(struct charact *S, GEN x)
{
  const long tx = typ(x);
  long i, l;
  switch(tx)
  {
    case t_INTMOD:char_update_int(S, gel(x,1)); break;
    case t_FFELT: char_update_prime(S, gel(x,4)); break;
    case t_PADIC: char_update_prime(S, gel(x,2)); break;
    case t_COMPLEX: case t_QUAD:
    case t_POLMOD: case t_POL: case t_SER: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      l = lg(x);
      for (i=lontyp[tx]; i < l; i++) charact_res(S,gel(x,i));
      break;
    case t_LIST:
      x = list_data(x);
      if (x) charact_res(S, x);
      break;
  }
}
GEN
characteristic(GEN x)
{
  struct charact S;
  S.q = gen_0; S.isprime = 0;
  charact(&S, x); return S.q;
}
GEN
residual_characteristic(GEN x)
{
  struct charact S;
  S.q = gen_0; S.isprime = 0;
  charact_res(&S, x); return S.q;
}

int
Rg_is_Fp(GEN x, GEN *pp)
{
  GEN mod;
  switch(typ(x))
  {
  case t_INTMOD:
    mod = gel(x,1);
    if (!*pp) *pp = mod;
    else if (mod != *pp && !equalii(mod, *pp))
    {
      if (DEBUGLEVEL) pari_warn(warner,"different moduli in Rg_is_Fp");
      return 0;
    }
    return 1;
  case t_INT:
    return 1;
  default: return 0;
  }
}

int
RgX_is_FpX(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++)
    if (!Rg_is_Fp(gel(x, i), pp))
      return 0;
  return 1;
}

int
RgV_is_FpV(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (!Rg_is_Fp(gel(x,i), pp)) return 0;
  return 1;
}

int
RgM_is_FpM(GEN x, GEN *pp)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++)
    if (!RgV_is_FpV(gel(x, i), pp)) return 0;
  return 1;
}

int
Rg_is_FpXQ(GEN x, GEN *pT, GEN *pp)
{
  GEN pol, mod, p;
  switch(typ(x))
  {
  case t_INTMOD:
    return Rg_is_Fp(x, pp);
  case t_INT:
    return 1;
  case t_POL:
    return RgX_is_FpX(x, pp);
  case t_FFELT:
    mod = FF_1(x); p = FF_p_i(x);
    if (!*pp) *pp = p;
    if (!*pT) *pT = mod;
    if ((p != *pp && !equalii(p, *pp)) || (mod != *pT && !gequal(mod, *pT)))
    {
      if (DEBUGLEVEL) pari_warn(warner,"different moduli in Rg_is_FpXQ");
      return 0;
    }
    return 1;
  case t_POLMOD:
    mod = gel(x,1); pol = gel(x, 2);
    if (!RgX_is_FpX(mod, pp)) return 0;
    if (typ(pol)==t_POL)
    {
      if (!RgX_is_FpX(pol, pp)) return 0;
    }
    else if (!Rg_is_Fp(pol, pp)) return 0;
    if (!*pT) *pT = mod;
    else if (mod != *pT && !gequal(mod, *pT))
    {
      if (DEBUGLEVEL) pari_warn(warner,"different moduli in Rg_is_FpXQ");
      return 0;
    }
    return 1;

  default: return 0;
  }
}

int
RgX_is_FpXQX(GEN x, GEN *pT, GEN *pp)
{
  long i, lx = lg(x);
  for (i = 2; i < lx; i++)
    if (!Rg_is_FpXQ(gel(x,i), pT, pp)) return 0;
  return 1;
}

/************************************************************************
 **                                                                    **
 **                      Ring conversion                               **
 **                                                                    **
 ************************************************************************/

/* p > 0 a t_INT, return lift(x * Mod(1,p)).
 * If x is an INTMOD, assume modulus is a multiple of p. */
GEN
Rg_to_Fp(GEN x, GEN p)
{
  if (lgefint(p) == 3) return utoi(Rg_to_Fl(x, uel(p,2)));
  switch(typ(x))
  {
    case t_INT: return modii(x, p);
    case t_FRAC: {
      pari_sp av = avma;
      GEN z = modii(gel(x,1), p);
      if (z == gen_0) return gen_0;
      return gerepileuptoint(av, remii(mulii(z, Fp_inv(gel(x,2), p)), p));
    }
    case t_PADIC: return padic_to_Fp(x, p);
    case t_INTMOD: {
      GEN q = gel(x,1), a = gel(x,2);
      if (equalii(q, p)) return icopy(a);
      if (!dvdii(q,p)) pari_err_MODULUS("Rg_to_Fp", q, p);
      return remii(a, p);
    }
    default: pari_err_TYPE("Rg_to_Fp",x);
      return NULL; /* not reached */
  }
}
/* If x is a POLMOD, assume modulus is a multiple of T. */
GEN
Rg_to_FpXQ(GEN x, GEN T, GEN p)
{
  long ta, tx = typ(x), v = get_FpX_var(T);
  GEN a, b;
  if (is_const_t(tx))
  {
    if (tx == t_FFELT)
    {
      GEN z = FF_to_FpXQ(x);
      setvarn(z, v);
      return z;
    }
    return scalar_ZX(Rg_to_Fp(x, p), v);
  }
  switch(tx)
  {
    case t_POLMOD:
      b = gel(x,1);
      a = gel(x,2); ta = typ(a);
      if (is_const_t(ta)) return scalar_ZX(Rg_to_Fp(a, p), v);
      b = RgX_to_FpX(b, p); if (varn(b) != v) break;
      a = RgX_to_FpX(a, p); if (ZX_equal(b,get_FpX_mod(T))) return a;
      if (signe(FpX_rem(b,T,p))==0) return FpX_rem(a, T, p);
      break;
    case t_POL:
      if (varn(x) != v) break;
      return FpX_rem(RgX_to_FpX(x,p), T, p);
    case t_RFRAC:
      a = Rg_to_FpXQ(gel(x,1), T,p);
      b = Rg_to_FpXQ(gel(x,2), T,p);
      return FpXQ_div(a,b, T,p);
  }
  pari_err_TYPE("Rg_to_FpXQ",x);
  return NULL; /* not reached */
}
GEN
RgX_to_FpX(GEN x, GEN p)
{
  long i, l;
  GEN z = cgetg_copy(x, &l); z[1] = x[1];
  for (i = 2; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return FpX_renormalize(z, l);
}

GEN
RgV_to_FpV(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return z;
}

GEN
RgC_to_FpC(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_COL);
  for (i = 1; i < l; i++) gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return z;
}

GEN
RgM_to_FpM(GEN x, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(z,i) = RgC_to_FpC(gel(x,i), p);
  return z;
}
GEN
RgV_to_Flv(GEN x, ulong p)
{
  long l = lg(x), i;
  GEN a = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) a[i] = Rg_to_Fl(gel(x,i), p);
  return a;
}
GEN
RgM_to_Flm(GEN x, ulong p)
{
  long l, i;
  GEN a = cgetg_copy(x, &l);
  for (i=1; i<l; i++) gel(a,i) = RgV_to_Flv(gel(x,i), p);
  return a;
}

GEN
RgX_to_FpXQX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++) gel(z,i) = Rg_to_FpXQ(gel(x,i), T,p);
  return FpXQX_renormalize(z, l);
}
GEN
RgX_to_FqX(GEN x, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  if (T)
    for (i = 2; i < l; i++)
      gel(z,i) = simplify_shallow(Rg_to_FpXQ(gel(x,i), T, p));
  else
    for (i = 2; i < l; i++)
      gel(z,i) = Rg_to_Fp(gel(x,i), p);
  return FpXQX_renormalize(z, l);
}

/* lg(V) > 1 */
GEN
FpXV_FpC_mul(GEN V, GEN W, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(V);
  GEN z = ZX_Z_mul(gel(V,1),gel(W,1));
  for(i=2; i<l; i++)
  {
    z = ZX_add(z, ZX_Z_mul(gel(V,i),gel(W,i)));
    if ((i & 7) == 0) z = gerepileupto(av, z);
  }
  return gerepileupto(av, FpX_red(z,p));
}

GEN
FqX_Fq_add(GEN y, GEN x, GEN T, GEN p)
{
  long i, lz = lg(y);
  GEN z;
  if (!T) return FpX_Fp_add(y, x, p);
  if (lz == 2) return scalarpol(x, varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Fq_add(gel(y,2),x, T, p);
  if (lz == 3) z = FpXX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = gcopy(gel(y,i));
  return z;
}

GEN
FqX_Fq_mul_to_monic(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP-1; i++) gel(res,i) = Fq_mul(U,gel(P,i), T,p);
  gel(res,lP-1) = gen_1; return res;
}

GEN
FpXQX_normalize(GEN z, GEN T, GEN p)
{
  GEN lc;
  if (lg(z) == 2) return z;
  lc = leading_coeff(z);
  if (typ(lc) == t_POL)
  {
    if (lg(lc) > 3) /* non-constant */
      return FqX_Fq_mul_to_monic(z, Fq_inv(lc,T,p), T,p);
    /* constant */
    lc = gel(lc,2);
    z = shallowcopy(z);
    gel(z, lg(z)-1) = lc;
  }
  /* lc a t_INT */
  if (equali1(lc)) return z;
  return FqX_Fq_mul_to_monic(z, Fp_inv(lc,p), T,p);
}

GEN
FqX_eval(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av;
  GEN p1, r;
  long j, i=lg(x)-1;
  if (i<=2)
    return (i==2)? Fq_red(gel(x,2), T, p): gen_0;
  av=avma; p1=gel(x,i);
  /* specific attention to sparse polynomials (see poleval)*/
  /*You've guessed it! It's a copy-paste(tm)*/
  for (i--; i>=2; i=j-1)
  {
    for (j=i; !signe(gel(x,j)); j--)
      if (j==2)
      {
        if (i!=j) y = Fq_pow(y,utoipos(i-j+1), T, p);
        return gerepileupto(av, Fq_mul(p1,y, T, p));
      }
    r = (i==j)? y: Fq_pow(y, utoipos(i-j+1), T, p);
    p1 = Fq_add(Fq_mul(p1,r,T,p), gel(x,j), T, p);
  }
  return gerepileupto(av, p1);
}

GEN
FqXY_evalx(GEN Q, GEN x, GEN T, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  if (!T) return FpXY_evalx(Q, x, p);
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FqX_eval(q, x, T, p);
  }
  return FpXQX_renormalize(z, lb);
}

/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FqXY_eval(GEN Q, GEN y, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  if (!T) return FpXY_eval(Q, y, x, p);
  return gerepileupto(av, FqX_eval(FqXY_evalx(Q, x, T, p), y, T, p));
}

/* a X^d */
GEN
monomial(GEN a, long d, long v)
{
  long i, lP = d+3;
  GEN P;
  if (d < 0) {
    if (isrationalzero(a)) return pol_0(v);
    P = cgetg(3, t_RFRAC);
    gel(P,1) = a;
    gel(P,2) = monomial(gen_1, -d, v);
  } else {
    P = cgetg(lP, t_POL);
    if (gequal0(a))
    {
      if (isexactzero(a)) return scalarpol_shallow(a,v);
      P[1] = evalsigne(0) | evalvarn(v);
    }
    else
      P[1] = evalsigne(1) | evalvarn(v);
    lP--; gel(P,lP) = a;
    for (i=2; i<lP; i++) gel(P,i) = gen_0;
  }
  return P;
}
GEN
monomialcopy(GEN a, long d, long v)
{
  long i, lP = d+3;
  GEN P;
  if (d < 0) {
    if (isrationalzero(a)) return pol_0(v);
    P = cgetg(3, t_RFRAC);
    gel(P,1) = gcopy(a);
    gel(P,2) = monomial(gen_1, -d, v);
  } else {
    P = cgetg(lP, t_POL);
    if (gequal0(a))
    {
      if (isexactzero(a)) return scalarpol(a,v);
      P[1] = evalsigne(0) | evalvarn(v);
    }
    else
      P[1] = evalsigne(1) | evalvarn(v);
    lP--; gel(P,lP) = gcopy(a);
    for (i=2; i<lP; i++) gel(P,i) = gen_0;
  }
  return P;
}
GEN
pol_x_powers(long N, long v)
{
  GEN L = cgetg(N+1,t_VEC);
  long i;
  for (i=1; i<=N; i++) gel(L,i) = monomial(gen_1, i-1, v);
  return L;
}

GEN
FqXQ_powers(GEN x, long l, GEN S, GEN T, GEN p)
{
  return T ? FpXQXQ_powers(x, l, S, T, p): FpXQ_powers(x, l, S, p);
}

GEN
FqXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, GEN p)
{
  return T ? FpXQXQ_matrix_pow(y, n, m, S, T, p): FpXQ_matrix_pow(y, n, m, S, p);
}

/*******************************************************************/
/*                                                                 */
/*                             Fq                                  */
/*                                                                 */
/*******************************************************************/

GEN
Fq_add(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_add(x,y,p);
    case 1: return FpX_Fp_add(x,y,p);
    case 2: return FpX_Fp_add(y,x,p);
    case 3: return FpX_add(x,y,p);
  }
  return NULL;
}

GEN
Fq_sub(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_sub(x,y,p);
    case 1: return FpX_Fp_sub(x,y,p);
    case 2: return Fp_FpX_sub(x,y,p);
    case 3: return FpX_sub(x,y,p);
  }
  return NULL;
}

GEN
Fq_neg(GEN x, GEN T/*unused*/, GEN p)
{
  (void)T;
  return (typ(x)==t_POL)? FpX_neg(x,p): Fp_neg(x,p);
}

GEN
Fq_halve(GEN x, GEN T/*unused*/, GEN p)
{
  (void)T;
  return (typ(x)==t_POL)? FpX_halve(x,p): Fp_halve(x,p);
}

/* If T==NULL do not reduce*/
GEN
Fq_mul(GEN x, GEN y, GEN T, GEN p)
{
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_mul(x,y,p);
    case 1: return FpX_Fp_mul(x,y,p);
    case 2: return FpX_Fp_mul(y,x,p);
    case 3: if (T) return FpXQ_mul(x,y,T,p);
            else return FpX_mul(x,y,p);
  }
  return NULL;
}

/* If T==NULL do not reduce*/
GEN
Fq_mulu(GEN x, ulong y, /*unused*/GEN T, GEN p)
{
  (void) T;
  return typ(x)==t_POL ? FpX_Fp_mul(x,utoi(y),p): Fp_mulu(x, y, p);
}

/* y t_INT */
GEN
Fq_Fp_mul(GEN x, GEN y, GEN T/*unused*/, GEN p)
{
  (void)T;
  return (typ(x) == t_POL)? FpX_Fp_mul(x,y,p)
                          : Fp_mul(x,y,p);
}
/* If T==NULL do not reduce*/
GEN
Fq_sqr(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_POL)
  {
    if (T) return FpXQ_sqr(x,T,p);
    else return FpX_sqr(x,p);
  }
  else
    return Fp_sqr(x,p);
}

GEN
Fq_neg_inv(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_INT) return Fp_inv(Fp_neg(x,p),p);
  return FpXQ_inv(FpX_neg(x,p),T,p);
}

GEN
Fq_invsafe(GEN x, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_invsafe(x,p);
  return FpXQ_invsafe(x,pol,p);
}

GEN
Fq_inv(GEN x, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_inv(x,p);
  return FpXQ_inv(x,pol,p);
}

GEN
Fq_div(GEN x, GEN y, GEN pol, GEN p)
{
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return Fp_div(x,y,p);
    case 1: return FpX_Fp_mul(x,Fp_inv(y,p),p);
    case 2: return FpX_Fp_mul(FpXQ_inv(y,pol,p),x,p);
    case 3: return FpXQ_div(x,y,pol,p);
  }
  return NULL;
}

GEN
Fq_pow(GEN x, GEN n, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_pow(x,n,p);
  return FpXQ_pow(x,n,pol,p);
}

GEN
Fq_powu(GEN x, ulong n, GEN pol, GEN p)
{
  if (typ(x) == t_INT) return Fp_powu(x,n,p);
  return FpXQ_powu(x,n,pol,p);
}

GEN
Fq_sqrt(GEN x, GEN T, GEN p)
{
  if (typ(x) == t_INT)
  {
    if (!T || odd(get_FpX_degree(T))) return Fp_sqrt(x,p);
    x = scalarpol_shallow(x, get_FpX_var(T));
  }
  return FpXQ_sqrt(x,T,p);
}
GEN
Fq_sqrtn(GEN x, GEN n, GEN T, GEN p, GEN *zeta)
{
  if (typ(x) == t_INT)
  {
    long d;
    if (!T) return Fp_sqrtn(x,n,p,zeta);
    d = get_FpX_degree(T);
    if (ugcd(umodiu(n,d),d) == 1)
    {
      if (!zeta)
        return Fp_sqrtn(x,n,p,NULL);
      else
      {
        /* gcd(n,p-1)=gcd(n,p^d-1) <=> same number of solutions if Fp and F_{p^d} */
        if (equalii(gcdii(subiu(p,1),n), gcdii(subiu(Fp_powu(p,d,n), 1), n)))
          return Fp_sqrtn(x,n,p,zeta);
      }
    }
    x = scalarpol(x, get_FpX_var(T)); /* left on stack */
  }
  return FpXQ_sqrtn(x,n,T,p,zeta);
}

struct _Fq_field
{
  GEN T, p;
};

static GEN
_Fq_red(void *E, GEN x)
{ struct _Fq_field *s = (struct _Fq_field *)E;
  return Fq_red(x, s->T, s->p);
}

static GEN
_Fq_add(void *E, GEN x, GEN y)
{
  (void) E;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return addii(x,y);
    case 1: return ZX_Z_add(x,y);
    case 2: return ZX_Z_add(y,x);
    default: return ZX_add(x,y);
  }
}

static GEN
_Fq_neg(void *E, GEN x) { (void) E; return typ(x)==t_POL?ZX_neg(x):negi(x); }

static GEN
_Fq_mul(void *E, GEN x, GEN y)
{
  (void) E;
  switch((typ(x)==t_POL)|((typ(y)==t_POL)<<1))
  {
    case 0: return mulii(x,y);
    case 1: return ZX_Z_mul(x,y);
    case 2: return ZX_Z_mul(y,x);
    default: return ZX_mul(x,y);
  }
}

static GEN
_Fq_inv(void *E, GEN x)
{ struct _Fq_field *s = (struct _Fq_field *)E;
  return Fq_inv(x,s->T,s->p);
}

static int
_Fq_equal0(GEN x) { return signe(x)==0; }

static GEN
_Fq_s(void *E, long x) { (void) E; return stoi(x); }

static const struct bb_field Fq_field={_Fq_red,_Fq_add,_Fq_mul,_Fq_neg,
                                       _Fq_inv,_Fq_equal0,_Fq_s};

const struct bb_field *get_Fq_field(void **E, GEN T, GEN p)
{
  GEN z = new_chunk(sizeof(struct _Fq_field));
  struct _Fq_field *e = (struct _Fq_field *) z;
  e->T = T; e->p  = p; *E = (void*)e;
  return &Fq_field;
}

/*******************************************************************/
/*                                                                 */
/*                             Fq[X]                               */
/*                                                                 */
/*******************************************************************/
/* P(X + c) */
GEN
FpX_translate(GEN P, GEN c, GEN p)
{
  pari_sp av = avma;
  GEN Q, *R;
  long i, k, n;

  if (!signe(P) || !signe(c)) return ZX_copy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
      R[k] = Fp_add(R[k], Fp_mul(c, R[k+1], p), p);

    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, FpX_renormalize(Q, lg(Q)));
}
/* P(X + c), c an Fq */
GEN
FqX_translate(GEN P, GEN c, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN Q, *R;
  long i, k, n;

  /* signe works for t_(INT|POL) */
  if (!signe(P) || !signe(c)) return RgX_copy(P);
  Q = leafcopy(P);
  R = (GEN*)(Q+2); n = degpol(P);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
      R[k] = Fq_add(R[k], Fq_mul(c, R[k+1], T, p), T, p);

    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FqX_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q); R = (GEN*)Q+2;
    }
  }
  return gerepilecopy(av, FpXQX_renormalize(Q, lg(Q)));
}

GEN
FqV_roots_to_pol(GEN V, GEN T, GEN p, long v)
{
  pari_sp ltop = avma;
  long k;
  GEN W;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    GEN Tl = ZX_to_Flx(T, pp);
    GEN Vl = FqV_to_FlxV(V, T, p);
    Tl = FlxqV_roots_to_pol(Vl, Tl, pp, v);
    return gerepileupto(ltop, FlxX_to_ZXX(Tl));
  }
  W = cgetg(lg(V),t_VEC);
  for(k=1; k < lg(V); k++)
    gel(W,k) = deg1pol_shallow(gen_1,Fq_neg(gel(V,k),T,p),v);
  return gerepileupto(ltop, FpXQXV_prod(W, T, p));
}

GEN
FqV_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l, typ(z));
  for(i=1;i<l;i++) gel(res,i) = Fq_red(gel(z,i),T,p);
  return res;
}

GEN
FqC_add(GEN x, GEN y, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN z;
  if (!T) return FpC_add(x, y, p);
  z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fq_add(gel(x, i), gel(y, i), T, p);
  return z;
}

GEN
FqC_sub(GEN x, GEN y, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN z;
  if (!T) return FpC_sub(x, y, p);
  z = cgetg(lx, t_COL);
  for (i = 1; i < lx; i++) gel(z, i) = Fq_sub(gel(x, i), gel(y, i), T, p);
  return z;
}

GEN
FqC_Fq_mul(GEN x, GEN y, GEN T, GEN p)
{
  long i, l = lg(x);
  GEN z;
  if (!T) return FpC_Fp_mul(x, y, p);
  z = cgetg(l, t_COL);
  for (i=1;i<l;i++) gel(z,i) = Fq_mul(gel(x,i),y,T,p);
  return z;
}

GEN
FqV_to_FlxV(GEN v, GEN T, GEN pp)
{
  long j, N = lg(v);
  long vT = evalvarn(get_FpX_var(T));
  ulong p = pp[2];
  GEN y = cgetg(N, t_VEC);
  for (j=1; j<N; j++)
    gel(y,j) = (typ(gel(v,j))==t_INT?  Z_to_Flx(gel(v,j), p, vT)
                                    : ZX_to_Flx(gel(v,j), p));
  return y;
}

GEN
FqC_to_FlxC(GEN v, GEN T, GEN pp)
{
  long j, N = lg(v);
  long vT = evalvarn(get_FpX_var(T));
  ulong p = pp[2];
  GEN y = cgetg(N, t_COL);
  for (j=1; j<N; j++)
    gel(y,j) = (typ(gel(v,j))==t_INT?  Z_to_Flx(gel(v,j), p, vT)
                                    : ZX_to_Flx(gel(v,j), p));
  return y;
}

GEN
FqM_to_FlxM(GEN x, GEN T, GEN pp)
{
  long j, n = lg(x);
  GEN y = cgetg(n,t_MAT);
  if (n == 1) return y;
  for (j=1; j<n; j++)
    gel(y,j) = FqC_to_FlxC(gel(x,j), T, pp);
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                          MODULAR GCD                            */
/*                                                                 */
/*******************************************************************/
/* return z = a mod q, b mod p (p,q) = 1. qinv = 1/q mod p */
static GEN
Fl_chinese_coprime(GEN a, ulong b, GEN q, ulong p, ulong qinv, GEN pq)
{
  ulong d, amod = umodiu(a, p);
  pari_sp av = avma;
  GEN ax;

  if (b == amod) return NULL;
  d = (b > amod)? b - amod: p - (amod - b); /* (b - a) mod p */
  (void)new_chunk(lgefint(pq)<<1); /* HACK */
  ax = mului(Fl_mul(d,qinv,p), q); /* d mod p, 0 mod q */
  avma = av; return addii(a, ax); /* in ]-q, pq[ assuming a in -]-q,q[ */
}
GEN
Z_init_CRT(ulong Hp, ulong p) { return stoi(Fl_center(Hp, p, p>>1)); }
GEN
ZX_init_CRT(GEN Hp, ulong p, long v)
{
  long i, l = lg(Hp), lim = (long)(p>>1);
  GEN H = cgetg(l, t_POL);
  H[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<l; i++)
    gel(H,i) = stoi(Fl_center(Hp[i], p, lim));
  return H;
}

/* assume lg(Hp) > 1 */
GEN
ZM_init_CRT(GEN Hp, ulong p)
{
  long i,j, m = lgcols(Hp), l = lg(Hp), lim = (long)(p>>1);
  GEN c,cp,H = cgetg(l, t_MAT);
  for (j=1; j<l; j++)
  {
    cp = gel(Hp,j);
    c = cgetg(m, t_COL);
    gel(H,j) = c;
    for (i=1; i<m; i++) gel(c,i) = stoi(Fl_center(cp[i],p, lim));
  }
  return H;
}

int
Z_incremental_CRT(GEN *H, ulong Hp, GEN *ptq, ulong p)
{
  GEN h, q = *ptq, qp = muliu(q,p), lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  int stable = 1;
  h = Fl_chinese_coprime(*H,Hp,q,p,qinv,qp);
  if (h)
  {
    if (cmpii(h,lim) > 0) h = subii(h,qp);
    *H = h; stable = 0;
  }
  *ptq = qp; return stable;
}

static int
ZX_incremental_CRT_raw(GEN *ptH, GEN Hp, GEN q, GEN qp, ulong p)
{
  GEN H = *ptH, h, lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  long i, l = lg(H), lp = lg(Hp);
  int stable = 1;

  if (l < lp)
  { /* degree increases */
    GEN x = cgetg(lp, t_POL);
    for (i=1; i<l; i++)  x[i] = H[i];
    for (   ; i<lp; i++) gel(x,i) = gen_0;
    *ptH = H = x;
    stable = 0;
  } else if (l > lp)
  { /* degree decreases */
    GEN x = cgetg(l, t_VECSMALL);
    for (i=1; i<lp; i++)  x[i] = Hp[i];
    for (   ; i<l; i++) x[i] = 0;
    Hp = x; lp = l;
  }
  for (i=2; i<lp; i++)
  {
    h = Fl_chinese_coprime(gel(H,i),Hp[i],q,p,qinv,qp);
    if (h)
    {
      if (cmpii(h,lim) > 0) h = subii(h,qp);
      gel(H,i) = h; stable = 0;
    }
  }
  return stable;
}

int
ZX_incremental_CRT(GEN *ptH, GEN Hp, GEN *ptq, ulong p)
{
  GEN q = *ptq, qp = muliu(q,p);
  int stable = ZX_incremental_CRT_raw(ptH, Hp, q, qp, p);
  *ptq = qp; return stable;
}

int
ZM_incremental_CRT(GEN *pH, GEN Hp, GEN *ptq, ulong p)
{
  GEN h, H = *pH, q = *ptq, qp = muliu(q, p), lim = shifti(qp,-1);
  ulong qinv = Fl_inv(umodiu(q,p), p);
  long i,j, l = lg(H), m = lgcols(H);
  int stable = 1;
  for (j=1; j<l; j++)
    for (i=1; i<m; i++)
    {
      h = Fl_chinese_coprime(gcoeff(H,i,j), coeff(Hp,i,j),q,p,qinv,qp);
      if (h)
      {
        if (cmpii(h,lim) > 0) h = subii(h,qp);
        gcoeff(H,i,j) = h; stable = 0;
      }
    }
  *ptq = qp; return stable;
}

/* record the degrees of Euclidean remainders (make them as large as
 * possible : smaller values correspond to a degenerate sequence) */
static void
Flx_resultant_set_dglist(GEN a, GEN b, GEN dglist, ulong p)
{
  long da,db,dc, ind;
  pari_sp av = avma;

  if (lgpol(a)==0 || lgpol(b)==0) return;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  { swapspec(a,b, da,db); }
  else if (!da) return;
  ind = 0;
  while (db)
  {
    GEN c = Flx_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) break;

    ind++;
    if (dc > dglist[ind]) dglist[ind] = dc;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_resultant_all");
      gerepileall(av, 2, &a,&b);
    }
    db = dc; /* = degpol(b) */
  }
  if (ind+1 > lg(dglist)) setlg(dglist,ind+1);
  avma = av; return;
}
/* assuming the PRS finishes on a degree 1 polynomial C0 + C1X, with
 * "generic" degree sequence as given by dglist, set *Ci and return
 * resultant(a,b). Modular version of Collins's subresultant */
static ulong
Flx_resultant_all(GEN a, GEN b, long *C0, long *C1, GEN dglist, ulong p)
{
  long da,db,dc, ind;
  ulong lb, res, g = 1UL, h = 1UL, ca = 1UL, cb = 1UL;
  int s = 1;
  pari_sp av = avma;

  *C0 = 1; *C1 = 0;
  if (lgpol(a)==0 || lgpol(b)==0) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) s = -s;
  }
  else if (!da) return 1; /* = a[2] ^ db, since 0 <= db <= da = 0 */
  ind = 0;
  while (db)
  { /* sub-resultant algo., applied to ca * a and cb * b, ca,cb scalars,
     * da = deg a, db = deg b */
    GEN c = Flx_rem(a,b, p);
    long delta = da - db;

    if (both_odd(da,db)) s = -s;
    lb = Fl_mul(b[db+2], cb, p);
    a = b; b = c; dc = degpol(c);
    ind++;
    if (dc != dglist[ind]) { avma = av; return 0; } /* degenerates */
    if (g == h)
    { /* frequent */
      ulong cc = Fl_mul(ca, Fl_powu(Fl_div(lb,g,p), delta+1, p), p);
      ca = cb;
      cb = cc;
    }
    else
    {
      ulong cc = Fl_mul(ca, Fl_powu(lb, delta+1, p), p);
      ulong ghdelta = Fl_mul(g, Fl_powu(h, delta, p), p);
      ca = cb;
      cb = Fl_div(cc, ghdelta, p);
    }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */

    g = lb;
    if (delta == 1)
      h = g; /* frequent */
    else
      h = Fl_mul(h, Fl_powu(Fl_div(g,h,p), delta, p), p);

    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_resultant_all");
      gerepileall(av, 2, &a,&b);
    }
  }
  if (da > 1) return 0; /* Failure */
  /* last non-constant polynomial has degree 1 */
  *C0 = Fl_mul(ca, a[2], p);
  *C1 = Fl_mul(ca, a[3], p);
  res = Fl_mul(cb, b[2], p);
  if (s == -1) res = p - res;
  avma = av; return res;
}

/* Q a vector of polynomials representing B in Fp[X][Y], evaluate at X = x,
 * Return 0 in case of degree drop. */
static GEN
FlxY_evalx_drop(GEN Q, ulong x, ulong p)
{
  GEN z;
  long i, lb = lg(Q);
  ulong leadz = Flx_eval(leading_coeff(Q), x, p);
  long vs=mael(Q,2,1);
  if (!leadz) return zero_Flx(vs);

  z = cgetg(lb, t_VECSMALL); z[1] = vs;
  for (i=2; i<lb-1; i++) z[i] = Flx_eval(gel(Q,i), x, p);
  z[i] = leadz; return z;
}

GEN
FpXY_Fq_evaly(GEN Q, GEN y, GEN T, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (!T) return FpXY_evaly(Q, y, p, vx);
  if (lb == 2) return pol_0(vx);
  z = gel(Q, lb-1);
  if (lb == 3 || !signe(y)) return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);

  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--)
  {
    GEN c = gel(Q,i);
    z = FqX_Fq_mul(z, y, T, p);
    z = typ(c) == t_INT? FqX_Fq_add(z,c,T,p): FqX_add(z,c,T,p);
  }
  return gerepileupto(av, z);
}

static GEN
ZX_norml1(GEN x)
{
  long i, l = lg(x);
  GEN s;

  if (l == 2) return gen_0;
  s = gel(x, l-1); /* != 0 */
  for (i = l-2; i > 1; i--) {
    GEN xi = gel(x,i);
    if (!signe(x)) continue;
    s = addii_sign(s,1, xi,1);
  }
  return s;
}

/* Interpolate at roots of 1 and use Hadamard bound for univariate resultant:
 *   bound = N_2(A)^degpol B N_2(B)^degpol(A),  where
 *     N_2(A) = sqrt(sum (N_1(Ai))^2)
 * Return e such that Res(A, B) < 2^e */
ulong
ZX_ZXY_ResBound(GEN A, GEN B, GEN dB)
{
  pari_sp av = avma;
  GEN a = gen_0, b = gen_0;
  long i , lA = lg(A), lB = lg(B);
  double loga, logb;
  for (i=2; i<lA; i++) a = addii(a, sqri(gel(A,i)));
  for (i=2; i<lB; i++)
  {
    GEN t = gel(B,i);
    if (typ(t) == t_POL) t = ZX_norml1(t);
    b = addii(b, sqri(t));
  }
  loga = dbllog2(a);
  logb = dbllog2(b); if (dB) logb -= 2 * dbllog2(dB);
  i = (long)((degpol(B) * loga + degpol(A) * logb) / 2);
  avma = av; return (i <= 0)? 1: 1 + (ulong)i;
}

/* return Res(a(Y), b(n,Y)) over Fp. la = leading_coeff(a) [for efficiency] */
static ulong
Flx_FlxY_eval_resultant(GEN a, GEN b, ulong n, ulong p, ulong la)
{
  GEN ev = FlxY_evalx(b, n, p);
  long drop = lg(b) - lg(ev);
  ulong r = Flx_resultant(a, ev, p);
  if (drop && la != 1) r = Fl_mul(r, Fl_powu(la, drop,p),p);
  return r;
}
static GEN
FpX_FpXY_eval_resultant(GEN a, GEN b, GEN n, GEN p, GEN la, long db, long vX)
{
  GEN ev = FpXY_evaly(b, n, p, vX);
  long drop = db-degpol(ev);
  GEN r = FpX_resultant(a, ev, p);
  if (drop && !gequal1(la)) r = Fp_mul(r, Fp_powu(la, drop,p),p);
  return r;
}

/* assume dres := deg(Res_X(a,b), Y) <= deg(a,X) * deg(b,Y) < p */
/* Return a Fly */
static GEN
Flx_FlxY_resultant_polint(GEN a, GEN b, ulong p, ulong dres, long sx)
{
  ulong i, n, la = Flx_lead(a);
  GEN  x = cgetg(dres+2, t_VECSMALL);
  GEN  y = cgetg(dres+2, t_VECSMALL);
 /* Evaluate at dres+ 1 points: 0 (if dres even) and +/- n, so that P_n(X) =
  * P_{-n}(-X), where P_i is Lagrange polynomial: P_i(j) = delta_{i,j} */
  for (i=0,n = 1; i < dres; n++)
  {
    x[++i] = n;   y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
    x[++i] = p-n; y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
  }
  if (i == dres)
  {
    x[++i] = 0;   y[i] = Flx_FlxY_eval_resultant(a,b, x[i], p,la);
  }
  return Flv_polint(x,y, p, sx);
}

static GEN
FlxX_pseudorem(GEN x, GEN y, ulong p)
{
  long vx = varn(x), dx, dy, dz, i, lx, dp;
  pari_sp av = avma, av2;

  if (!signe(y)) pari_err_INV("FlxX_pseudorem",y);
  (void)new_chunk(2);
  dx=degpol(x); x = RgX_recip_shallow(x)+2;
  dy=degpol(y); y = RgX_recip_shallow(y)+2; dz=dx-dy; dp = dz+1;
  av2 = avma;
  for (;;)
  {
    gel(x,0) = Flx_neg(gel(x,0), p); dp--;
    for (i=1; i<=dy; i++)
      gel(x,i) = Flx_add( Flx_mul(gel(y,0), gel(x,i), p),
                              Flx_mul(gel(x,0), gel(y,i), p), p );
    for (   ; i<=dx; i++)
      gel(x,i) = Flx_mul(gel(y,0), gel(x,i), p);
    do { x++; dx--; } while (dx >= 0 && lg(gel(x,0))==2);
    if (dx < dy) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FlxX_pseudorem dx = %ld >= %ld",dx,dy);
      gerepilecoeffs(av2,x,dx+1);
    }
  }
  if (dx < 0) return zero_Flx(0);
  lx = dx+3; x -= 2;
  x[0]=evaltyp(t_POL) | evallg(lx);
  x[1]=evalsigne(1) | evalvarn(vx);
  x = RgX_recip_shallow(x);
  if (dp)
  { /* multiply by y[0]^dp   [beware dummy vars from FpX_FpXY_resultant] */
    GEN t = Flx_powu(gel(y,0), dp, p);
    for (i=2; i<lx; i++)
      gel(x,i) = Flx_mul(gel(x,i), t, p);
  }
  return gerepilecopy(av, x);
}

/* return a Flx */
GEN
FlxX_resultant(GEN u, GEN v, ulong p, long sx)
{
  pari_sp av = avma, av2;
  long degq,dx,dy,du,dv,dr,signh;
  GEN z,g,h,r,p1;

  dx=degpol(u); dy=degpol(v); signh=1;
  if (dx < dy)
  {
    swap(u,v); lswap(dx,dy);
    if (both_odd(dx, dy)) signh = -signh;
  }
  if (dy < 0) return zero_Flx(sx);
  if (dy==0) return gerepileupto(av, Flx_powu(gel(v,2),dx,p));

  g = h = pol1_Flx(sx); av2 = avma;
  for(;;)
  {
    r = FlxX_pseudorem(u,v,p); dr = lg(r);
    if (dr == 2) { avma = av; return zero_Flx(sx); }
    du = degpol(u); dv = degpol(v); degq = du-dv;
    u = v; p1 = g; g = leading_coeff(u);
    switch(degq)
    {
      case 0: break;
      case 1:
        p1 = Flx_mul(h,p1, p); h = g; break;
      default:
        p1 = Flx_mul(Flx_powu(h,degq,p), p1, p);
        h = Flx_div(Flx_powu(g,degq,p), Flx_powu(h,degq-1,p), p);
    }
    if (both_odd(du,dv)) signh = -signh;
    v = FlxY_Flx_div(r, p1, p);
    if (dr==3) break;
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"resultant_all, dr = %ld",dr);
      gerepileall(av2,4, &u, &v, &g, &h);
    }
  }
  z = gel(v,2);
  if (dv > 1) z = Flx_div(Flx_powu(z,dv,p), Flx_powu(h,dv-1,p), p);
  if (signh < 0) z = Flx_neg(z,p);
  return gerepileupto(av, z);
}

/* Warning:
 * This function switches between valid and invalid variable ordering*/

static GEN
FlxY_to_FlyX(GEN b, long sv)
{
  long i, n=-1;
  long sw = b[1]&VARNBITS;
  for(i=2;i<lg(b);i++) n = maxss(n,lgpol(gel(b,i)));
  return Flm_to_FlxX(Flm_transpose(FlxX_to_Flm(b,n)),sv,sw);
}

/* Return a Fly*/
GEN
Flx_FlxY_resultant(GEN a, GEN b, ulong pp)
{
  pari_sp ltop=avma;
  long dres = degpol(a)*degpol(b);
  long sx=a[1], sy=b[1]&VARNBITS;
  GEN z;
  b = FlxY_to_FlyX(b,sx);
  if ((ulong)dres >= pp)
    z = FlxX_resultant(Fly_to_FlxY(a, sy), b, pp, sx);
  else
    z = Flx_FlxY_resultant_polint(a, b, pp, (ulong)dres, sy);
  return gerepileupto(ltop,z);
}

/* return a t_POL (in variable v >= 0) whose coeffs are the coeffs of b,
 * in variable v. This is an incorrect PARI object if initially varn(b) << v.
 * We could return a vector of coeffs, but it is convenient to have degpol()
 * and friends available. Even in that case, it will behave nicely with all
 * functions treating a polynomial as a vector of coeffs (eg poleval).
 * FOR INTERNAL USE! */
GEN
swap_vars(GEN b0, long v)
{
  long i, n = RgX_degree(b0, v);
  GEN b, x;
  if (n < 0) return pol_0(v);
  b = cgetg(n+3, t_POL); x = b + 2;
  b[1] = evalsigne(1) | evalvarn(v);
  for (i=0; i<=n; i++) gel(x,i) = polcoeff_i(b0, i, v);
  return b;
}

/* assume varn(b) << varn(a) */
/* return a FpY*/
GEN
FpX_FpXY_resultant(GEN a, GEN b, GEN p)
{
  long i,n,dres, db, vY = varn(b), vX = varn(a);
  GEN la,x,y;

  if (lgefint(p) == 3)
  {
    ulong pp = uel(p,2);
    b = ZXX_to_FlxX(b, pp, vX);
    a = ZX_to_Flx(a, pp);
    x = Flx_FlxY_resultant(a, b, pp);
    return Flx_to_ZX(x);
  }
  db = RgXY_degreex(b);
  dres = degpol(a)*degpol(b);
  la = leading_coeff(a);
  x = cgetg(dres+2, t_VEC);
  y = cgetg(dres+2, t_VEC);
 /* Evaluate at dres+ 1 points: 0 (if dres even) and +/- n, so that P_n(X) =
  * P_{-n}(-X), where P_i is Lagrange polynomial: P_i(j) = delta_{i,j} */
  for (i=0,n = 1; i < dres; n++)
  {
    gel(x,++i) = utoipos(n);
    gel(y,i) = FpX_FpXY_eval_resultant(a,b,gel(x,i),p,la,db,vY);
    gel(x,++i) = subis(p,n);
    gel(y,i) = FpX_FpXY_eval_resultant(a,b,gel(x,i),p,la,db,vY);
  }
  if (i == dres)
  {
    gel(x,++i) = gen_0;
    gel(y,i) = FpX_FpXY_eval_resultant(a,b, gel(x,i), p,la,db,vY);
  }
  return FpV_polint(x,y, p, vY);
}

GEN
FpX_direct_compositum(GEN a, GEN b, GEN p)
{
  GEN x = deg1pol_shallow(gen_1, pol_x(varn(a)), fetch_var_higher()); /* x+y */
  x = FpX_FpXY_resultant(a, poleval(b,x),p);
  (void)delete_var(); return x;
}

/* 0, 1, -1, 2, -2, ... */
#define next_lambda(a) (a>0 ? -a : 1-a)
GEN
FpX_compositum(GEN a, GEN b, GEN p)
{
  long k, v = fetch_var_higher();
  for (k = 1;; k = next_lambda(k))
  {
    GEN x = deg1pol_shallow(gen_1, gmulsg(k, pol_x(v)), 0); /* x + k y */
    GEN C = FpX_FpXY_resultant(a, poleval(b,x),p);
    if (FpX_is_squarefree(C, p)) { (void)delete_var(); return C; }
  }
}

/* Assume A in Z[Y], B in Q[Y][X], and Res_Y(A, B) in Z[X].
 * If lambda = NULL, return Res_Y(A,B).
 * Otherwise, find a small lambda (start from *lambda, use the sequence above)
 * such that R(X) = Res_Y(A(Y), B(X + lambda Y)) is squarefree, reset *lambda
 * to the chosen value and return R
 *
 * If LERS is non-NULL, set it to the Last non-constant polynomial in the
 * Euclidean Remainder Sequence */
GEN
ZX_ZXY_resultant_all(GEN A, GEN B0, long *plambda, GEN *LERS)
{
  int checksqfree = plambda? 1: 0, stable;
  long lambda = plambda? *plambda: 0, cnt = 0;
  ulong bound, dp;
  pari_sp av = avma, av2 = 0;
  long i,n, lb, degA = degpol(A), dres = degA*degpol(B0);
  long v = fetch_var_higher();
  long vX = varn(B0), vY = varn(A); /* assume vY has lower priority */
  long sX = evalvarn(vX);
  GEN x, y, dglist, dB, B, q, a, b, ev, H, H0, H1, Hp, H0p, H1p, C0, C1;
  forprime_t S;

  dglist = Hp = H0p = H1p = C0 = C1 = NULL; /* gcc -Wall */
  if (LERS)
  {
    if (!checksqfree)
      pari_err_BUG("ZX_ZXY_resultant_all [LERS != NULL needs lambda]");
    C0 = cgetg(dres+2, t_VECSMALL);
    C1 = cgetg(dres+2, t_VECSMALL);
    dglist = cgetg(dres+1, t_VECSMALL);
  }
  x = cgetg(dres+2, t_VECSMALL);
  y = cgetg(dres+2, t_VECSMALL);
  B0 = Q_remove_denom(B0, &dB);
  if (!dB) B0 = leafcopy(B0);
  A = leafcopy(A);
  B = B0;
  setvarn(A,v);
  /* make sure p large enough */
INIT:
  /* always except the first time */
  if (av2) { avma = av2; lambda = next_lambda(lambda); }
  if (lambda) B = RgX_translate(B0, monomial(stoi(lambda), 1, vY));
  B = swap_vars(B, vY); setvarn(B,v);
  /* B0(lambda v + x, v) */
  if (DEBUGLEVEL>4 && checksqfree) err_printf("Trying lambda = %ld\n", lambda);
  av2 = avma;

  if (degA <= 3)
  { /* sub-resultant faster for small degrees */
    if (LERS)
    { /* implies checksqfree */
      H = resultant_all(A,B,&q);
      if (typ(q) != t_POL || degpol(q)!=1) goto INIT;
      H0 = gel(q,2);
      if (typ(H0) == t_POL) setvarn(H0,vX); else H0 = scalarpol(H0,vX);
      H1 = gel(q,3);
      if (typ(H1) == t_POL) setvarn(H1,vX); else H1 = scalarpol(H1,vX);
    }
    else
      H = resultant(A,B);
    if (checksqfree && !ZX_is_squarefree(H)) goto INIT;
    goto END;
  }

  H = H0 = H1 = NULL;
  lb = lg(B);
  bound = ZX_ZXY_ResBound(A, B, dB);
  if (DEBUGLEVEL>4) err_printf("bound for resultant coeffs: 2^%ld\n",bound);
  dp = 1;
  init_modular_big(&S);
  while (1)
  {
    ulong p = u_forprime_next(&S);
    if (dB) { dp = umodiu(dB, p); if (!dp) continue; }

    a = ZX_to_Flx(A, p);
    b = ZXX_to_FlxX(B, p, varn(A));
    if (LERS)
    {
      GEN Hi;
      if (degpol(a) < degA || lg(b) < lb) continue; /* p | lc(A)lc(B) */
      if (checksqfree)
      { /* find degree list for generic Euclidean Remainder Sequence */
        long goal = minss(degpol(a), degpol(b)); /* longest possible */
        for (n=1; n <= goal; n++) dglist[n] = 0;
        setlg(dglist, 1);
        for (n=0; n <= dres; n++)
        {
          ev = FlxY_evalx_drop(b, n, p);
          Flx_resultant_set_dglist(a, ev, dglist, p);
          if (lg(dglist)-1 == goal) break;
        }
        /* last pol in ERS has degree > 1 ? */
        goal = lg(dglist)-1;
        if (degpol(B) == 1) { if (!goal) goto INIT; }
        else
        {
          if (goal <= 1) goto INIT;
          if (dglist[goal] != 0 || dglist[goal-1] != 1) goto INIT;
        }
        if (DEBUGLEVEL>4)
          err_printf("Degree list for ERS (trials: %ld) = %Ps\n",n+1,dglist);
      }

      for (i=0,n = 0; i <= dres; n++)
      {
        ev = FlxY_evalx_drop(b, n, p);
        x[++i] = n; y[i] = Flx_resultant_all(a, ev, C0+i, C1+i, dglist, p);
        if (!C1[i]) i--; /* C1(i) = 0. No way to recover C0(i) */
      }
      Hi = Flv_Flm_polint(x, mkvec3(y,C0,C1), p, 0);
      Hp = gel(Hi,1); H0p = gel(Hi,2); H1p = gel(Hi,3);
    }
    else
    {
      long dropa = degA - degpol(a), dropb = lb - lg(b);
      Hp = Flx_FlxY_resultant_polint(a, b, p, (ulong)dres, sX);
      if (dropa && dropb)
        Hp = zero_Flx(sX);
      else {
        if (dropa)
        { /* multiply by ((-1)^deg B lc(B))^(deg A - deg a) */
          GEN c = gel(b,lb-1); /* lc(B) */
          if (!odd(lb)) c = Flx_neg(c, p); /* deg B = lb - 3 */
          if (!Flx_equal1(c)) {
            c = Flx_powu(c, dropa, p);
            if (!Flx_equal1(c)) Hp = Flx_mul(Hp, c, p);
          }
        }
        else if (dropb)
        { /* multiply by lc(A)^(deg B - deg b) */
          ulong c = a[degA+2]; /* lc(A) */
          c = Fl_powu(c, dropb, p);
          if (c != 1) Hp = Flx_Fl_mul(Hp, c, p);
        }
      }
    }
    if (!H && degpol(Hp) != dres) continue;
    if (dp != 1) Hp = Flx_Fl_mul(Hp, Fl_powu(Fl_inv(dp,p), degA, p), p);
    if (checksqfree) {
      if (!Flx_is_squarefree(Hp, p)) goto INIT;
      if (DEBUGLEVEL>4) err_printf("Final lambda = %ld\n", lambda);
      checksqfree = 0;
    }

    if (!H)
    { /* initialize */
      q = utoipos(p); stable = 0;
      H = ZX_init_CRT(Hp, p,vX);
      if (LERS) {
        H0= ZX_init_CRT(H0p, p,vX);
        H1= ZX_init_CRT(H1p, p,vX);
      }
    }
    else
    {
      if (LERS) {
        GEN qp = muliu(q,p);
        stable  = ZX_incremental_CRT_raw(&H, Hp, q,qp, p)
                & ZX_incremental_CRT_raw(&H0,H0p, q,qp, p)
                & ZX_incremental_CRT_raw(&H1,H1p, q,qp, p);
        q = qp;
      }
      else
        stable = ZX_incremental_CRT(&H, Hp, &q, p);
    }
    /* could make it probabilistic for H ? [e.g if stable twice, etc]
     * Probabilistic anyway for H0, H1 */
    if (DEBUGLEVEL>5 && (stable ||  ++cnt==100))
    { cnt=0; err_printf("%ld%%%s ",100*expi(q)/bound,stable?"s":""); }
    if (stable && (ulong)expi(q) >= bound) break; /* DONE */
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZX_ZXY_rnfequation");
      gerepileall(av2, LERS? 4: 2, &H, &q, &H0, &H1);
    }
  }
END:
  if (DEBUGLEVEL>5) err_printf(" done\n");
  setvarn(H, vX); (void)delete_var();
  if (plambda) *plambda = lambda;
  if (LERS)
  {
    *LERS = mkvec2(H0,H1);
    gerepileall(av, 2, &H, LERS);
    return H;
  }
  return gerepilecopy(av, H);
}

GEN
ZX_ZXY_rnfequation(GEN A, GEN B, long *lambda)
{
  return ZX_ZXY_resultant_all(A, B, lambda, NULL);
}

/* If lambda = NULL, return caract(Mod(A, T)), T,A in Z[X].
 * Otherwise find a small lambda such that caract (Mod(A + lambda X, T)) is
 * squarefree */
GEN
ZXQ_charpoly_sqf(GEN A, GEN T, long *lambda, long v)
{
  pari_sp av = avma;
  GEN R, a;
  long dA;
  int delvar;

  if (v < 0) v = 0;
  switch (typ(A))
  {
    case t_POL: dA = degpol(A); if (dA > 0) break;
      A = constant_coeff(A);
    default:
      if (lambda) { A = scalar_ZX_shallow(A,varn(T)); dA = 0; break;}
      return gerepileupto(av, gpowgs(gsub(pol_x(v), A), degpol(T)));
  }
  delvar = 0;
  if (varn(T) == 0)
  {
    long v0 = fetch_var(); delvar = 1;
    T = leafcopy(T); setvarn(T,v0);
    A = leafcopy(A); setvarn(A,v0);
  }
  R = ZX_ZXY_rnfequation(T, deg1pol_shallow(gen_1, gneg_i(A), 0), lambda);
  if (delvar) (void)delete_var();
  setvarn(R, v); a = leading_coeff(T);
  if (!gequal1(a)) R = gdiv(R, powiu(a, dA));
  return gerepileupto(av, R);
}


/* charpoly(Mod(A,T)), A may be in Q[X], but assume T and result are integral */
GEN
ZXQ_charpoly(GEN A, GEN T, long v)
{
  return (degpol(T) < 16) ? RgXQ_charpoly(A,T,v): ZXQ_charpoly_sqf(A,T, NULL, v);
}

GEN
QXQ_charpoly(GEN A, GEN T, long v)
{
  pari_sp av = avma;
  GEN den, B = Q_remove_denom(A, &den);
  GEN P = ZXQ_charpoly(B, T, v);
  return gerepilecopy(av, den ? RgX_rescale(P, ginv(den)): P);
}

static GEN
trivial_case(GEN A, GEN B)
{
  long d;
  if (typ(A) == t_INT) return powiu(A, degpol(B));
  d = degpol(A);
  if (d == 0) return trivial_case(gel(A,2),B);
  if (d < 0) return gen_0;
  return NULL;
}

static long
get_nbprimes(ulong bound, ulong *pt_start)
{
#ifdef LONG_IS_64BIT
  ulong pstart = 4611686018427388039UL;
#else
  ulong pstart = 1073741827UL;
#endif
  *pt_start = pstart;
  return (bound/expu(pstart))+1;
}

static ulong
ZX_resultant_prime(GEN a, GEN b, GEN dB, long degA, long degB, ulong p)
{
  pari_sp av = avma;
  ulong H;
  long dropa, dropb;
  ulong dp = dB ? umodiu(dB, p): 1;
  if (!b) b = Flx_deriv(a, p);
  dropa = degA - degpol(a);
  dropb = degB - degpol(b);
  if (dropa && dropb) /* p | lc(A), p | lc(B) */
  { avma = av; return 0; }
  H = Flx_resultant(a, b, p);
  if (dropa)
  { /* multiply by ((-1)^deg B lc(B))^(deg A - deg a) */
    ulong c = b[degB+2]; /* lc(B) */
    if (odd(degB)) c = p - c;
    c = Fl_powu(c, dropa, p);
    if (c != 1) H = Fl_mul(H, c, p);
  }
  else if (dropb)
  { /* multiply by lc(A)^(deg B - deg b) */
    ulong c = a[degA+2]; /* lc(A) */
    c = Fl_powu(c, dropb, p);
    if (c != 1) H = Fl_mul(H, c, p);
  }
  if (dp != 1) H = Fl_mul(H, Fl_powu(Fl_inv(dp,p), degA, p), p);
  avma = av; return H;
}

/* If B=NULL, assume B=A' */
static GEN
ZX_resultant_slice(GEN A, GEN B, GEN dB, GEN P, GEN *mod)
{
  pari_sp av = avma;
  long degA, degB, i, n = lg(P)-1;
  GEN H, T;

  degA = degpol(A);
  degB = B ? degpol(B): degA - 1;
  if (n == 1)
  {
    ulong Hp, p = uel(P,1);
    GEN a, b;
    a = ZX_to_Flx(A, p), b = B ? ZX_to_Flx(B, p): NULL;
    Hp = ZX_resultant_prime(a, b, dB, degA, degB, p);
    avma = av;
    *mod = utoi(p); return utoi(Hp);
  }
  T = ZV_producttree(P);
  A = ZX_nv_mod_tree(A, P, T);
  if (B) B = ZX_nv_mod_tree(B, P, T);
  H = cgetg(n+1, t_VECSMALL);
  for(i=1; i <= n; i++)
  {
    ulong p = P[i];
    GEN a = gel(A, i), b = B ? gel(B, i): NULL;
    H[i] = ZX_resultant_prime(a, b, dB, degA, degB, p);
  }
  H = ZV_chinese_tree(H, P, T, mod);
  gerepileall(av, 2, &H, mod);
  return H;
}

GEN
ZX_resultant_worker(GEN P, GEN A, GEN B, GEN dB)
{
  GEN V = cgetg(3, t_VEC);
  if (isintzero(B)) B = NULL;
  if (isintzero(dB)) dB = NULL;
  gel(V,1) = ZX_resultant_slice(A,B,dB,P,&gel(V,2));
  return V;
}

static GEN
primelist_disc(ulong *p, long n, GEN dB)
{
  GEN P = cgetg(n+1, t_VECSMALL);
  long i;
  for (i=1; i <= n; i++, *p = unextprime(*p+1))
  {
    if (dB && umodiu(dB, *p)==0) { i--; continue; }
    P[i] = *p;
  }
  return P;
}

/* Res(A, B/dB), assuming the A,B in Z[X] and result is integer */
/* if B=NULL, take B = A' */
GEN
ZX_resultant_all(GEN A, GEN B, GEN dB, ulong bound)
{
  ulong p;
  pari_sp av = avma;
  long n, m;
  GEN  H, P, mod;
  int is_disc = !B;
  if (is_disc) B = ZX_deriv(A);

  if ((H = trivial_case(A,B)) || (H = trivial_case(B,A))) return H;
  if (!bound) bound = ZX_ZXY_ResBound(A, B, dB);
  n = get_nbprimes(bound+1, &p);/* +1 to account for sign */
  if (is_disc)
    B = NULL;
  m = minss(degpol(A)+(B ? degpol(B): 0), n);
  if (m == 1)
  {
    GEN P = primelist_disc(&p, n, dB);
    H = ZX_resultant_slice(A, B, dB, P, &mod);
  }
  else
  {
    long i, s = n/m, r = n - m*s, di = 0;
    GEN worker = strtoclosure("_ZX_resultant_worker", 3, A, B?B:gen_0, dB?dB:gen_0);
    struct pari_mt pt;
    long pending;
    if (DEBUGLEVEL > 4)
      err_printf("ZX_resultant: bound 2^%ld, nb primes: %ld\n",bound, n);
    H = cgetg(m+1+!!r, t_VEC); P = cgetg(m+1+!!r, t_VEC);
    mt_queue_start(&pt, worker);
    for (i=1; i<=m || pending; i++)
    {
      GEN done;
      mt_queue_submit(&pt, i, i<=m ? mkvec(primelist_disc(&p, s, dB)): NULL);
      done = mt_queue_get(&pt, NULL, &pending);
      if (done)
      {
        di++;
        gel(H, di) = gel(done,1);
        gel(P, di) = gel(done,2);
        if (DEBUGLEVEL>5) err_printf("%ld%% ",100*di/m);
      }
    }
    mt_queue_end(&pt);
    if (r)
    {
      GEN Pr = primelist_disc(&p, r, dB);
      gel(H, m+1) = ZX_resultant_slice(A, B, dB, Pr, &gel(P, m+1));
    }
    H = ZV_chinese(H, P, &mod);
    if (DEBUGLEVEL>5) err_printf("done\n");
  }
  H = Fp_center(H, mod, shifti(mod,-1));
  return gerepileuptoint(av, H);
}

/* A0 and B0 in Q[X] */
GEN
QX_resultant(GEN A0, GEN B0)
{
  GEN s, a, b, A, B;
  pari_sp av = avma;

  A = Q_primitive_part(A0, &a);
  B = Q_primitive_part(B0, &b);
  s = ZX_resultant(A, B);
  if (!signe(s)) { avma = av; return gen_0; }
  if (a) s = gmul(s, gpowgs(a,degpol(B)));
  if (b) s = gmul(s, gpowgs(b,degpol(A)));
  return gerepileupto(av, s);
}

GEN
ZX_resultant(GEN A, GEN B) { return ZX_resultant_all(A,B,NULL,0); }

GEN
QXQ_intnorm(GEN A, GEN B)
{
  GEN c, n, R, lB;
  long dA = degpol(A), dB = degpol(B);
  pari_sp av = avma;
  if (dA < 0) return gen_0;
  A = Q_primitive_part(A, &c);
  if (!c || typ(c) == t_INT) {
    n = c;
    R = ZX_resultant(B, A);
  } else {
    n = gel(c,1);
    R = ZX_resultant_all(B, A, gel(c,2), 0);
  }
  if (n && !equali1(n)) R = mulii(R, powiu(n, dB));
  lB = leading_coeff(B);
  if (!equali1(lB)) R = diviiexact(R, powiu(lB, dA));
  return gerepileuptoint(av, R);
}

GEN
QXQ_norm(GEN A, GEN B)
{
  GEN c, R, lB;
  long dA = degpol(A), dB = degpol(B);
  pari_sp av = avma;
  if (dA < 0) return gen_0;
  A = Q_primitive_part(A, &c);
  R = ZX_resultant(B, A);
  if (c) R = gmul(R, gpowgs(c, dB));
  lB = leading_coeff(B);
  if (!equali1(lB)) R = gdiv(R, gpowgs(lB, dA));
  return gerepileupto(av, R);
}

/* assume x has integral coefficients */
GEN
ZX_disc_all(GEN x, ulong bound)
{
  pari_sp av = avma;
  GEN l, R;
  long s, d = degpol(x);
  if (d <= 1) return d ? gen_1: gen_0;
  s = (d & 2) ? -1: 1;
  l = leading_coeff(x);
  R = ZX_resultant_all(x, NULL, NULL, bound);
  if (is_pm1(l))
  { if (signe(l) < 0) s = -s; }
  else
    R = diviiexact(R,l);
  if (s == -1) togglesign_safe(&R);
  return gerepileuptoint(av,R);
}
GEN ZX_disc(GEN x) { return ZX_disc_all(x,0); }

GEN
QX_disc(GEN x)
{
  pari_sp av = avma;
  GEN c, d = ZX_disc( Q_primitive_part(x, &c) );
  if (c) d = gmul(d, gpowgs(c, 2*degpol(x) - 2));
  return gerepileupto(av, d);
}

/* lift(1 / Mod(A,B)). B a ZX, A a scalar or a QX */
GEN
QXQ_inv(GEN A, GEN B)
{
  GEN D, cU, q, U, V;
  ulong p;
  pari_sp av2, av = avma;
  forprime_t S;
  pari_timer ti;
  if (is_scalar_t(typ(A))) return scalarpol(ginv(A), varn(B));
  /* A a QX, B a ZX */
  if (degpol(A) < 15) return RgXQ_inv(A,B);
  A = Q_primitive_part(A, &D);
  /* A, B in Z[X] */
  init_modular_small(&S);
  if (DEBUGLEVEL>5) timer_start(&ti);
  av2 = avma; U = NULL;
  while ((p = u_forprime_next(&S)))
  {
    GEN a, b, qp, Up, Vp;
    int stable;

    a = ZX_to_Flx(A, p);
    b = ZX_to_Flx(B, p);
    /* if p | Res(A/G, B/G), discard */
    if (!Flx_extresultant(b,a,p, &Vp,&Up)) continue;

    if (!U)
    { /* First time */
      U = ZX_init_CRT(Up,p,varn(A));
      V = ZX_init_CRT(Vp,p,varn(A));
      q = utoipos(p); continue;
    }
    if (DEBUGLEVEL>5) timer_printf(&ti,"QXQ_inv: mod %ld (bound 2^%ld)", p,expi(q));
    qp = muliu(q,p);
    stable = ZX_incremental_CRT_raw(&U, Up, q,qp, p)
           & ZX_incremental_CRT_raw(&V, Vp, q,qp, p);
    if (stable)
    { /* all stable: check divisibility */
      GEN res = ZX_add(ZX_mul(A,U), ZX_mul(B,V));
      if (degpol(res) == 0) {
        res = gel(res,2);
        D = D? gmul(D, res): res;
        break;
      } /* DONE */
      if (DEBUGLEVEL) err_printf("QXQ_inv: char 0 check failed");
    }
    q = qp;
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"QXQ_inv");
      gerepileall(av2, 3, &q,&U,&V);
    }
  }
  if (!p) pari_err_OVERFLOW("QXQ_inv [ran out of primes]");
  cU = ZX_content(U);
  if (!is_pm1(cU)) { U = Q_div_to_int(U, cU); D = gdiv(D, cU); }
  return gerepileupto(av, RgX_Rg_div(U, D));
}

/************************************************************************
 *                                                                      *
 *                   IRREDUCIBLE POLYNOMIAL / Fp                        *
 *                                                                      *
 ************************************************************************/

/* irreducible (unitary) polynomial of degree n over Fp */
GEN
ffinit_rand(GEN p,long n)
{
  for(;;) {
    pari_sp av = avma;
    GEN pol = ZX_add(monomial(gen_1, n, 0), random_FpX(n-1,0, p));
    if (FpX_is_irred(pol, p)) return pol;
    avma = av;
  }
}

/* return an extension of degree 2^l of F_2, assume l > 0
 * Not stack clean. */
static GEN
f2init(long l)
{
  GEN Q, T, S;
  long i, v;

  if (l == 1) return polcyclo(3, 0);
  v = fetch_var_higher();
  S = mkpoln(4, gen_1,gen_1,gen_0,gen_0); /* y(y^2 + y) */
  Q = mkpoln(3, gen_1,gen_1, S); /* x^2 + x + y(y^2+y) */
  setvarn(Q, v);

  /* x^4+x+1, irred over F_2, minimal polynomial of a root of Q */
  T = mkpoln(5, gen_1,gen_0,gen_0,gen_1,gen_1);
  setvarn(T, v);
  /* Q = x^2 + x + a(y) irred. over K = F2[y] / (T(y))
   * ==> x^2 + x + a(y) b irred. over K for any root b of Q
   * ==> x^2 + x + (b^2+b)b */
  for (i=2; i<l; i++) T = FpX_FpXY_resultant(T, Q, gen_2); /* minpoly(b) / F2*/
  (void)delete_var(); setvarn(T,0); return T;
}

/* return an extension of degree p^l of F_p, assume l > 0
 * Not stack clean. */
GEN
ffinit_Artin_Shreier(GEN ip, long l)
{
  long i, v, p = itos(ip);
  GEN T, Q, xp = monomial(gen_1,p,0); /* x^p */
  T = ZX_sub(xp, deg1pol_shallow(gen_1,gen_1,0)); /* x^p - x - 1 */
  if (l == 1) return T;

  v = fetch_var_higher();
  setvarn(xp, v);
  Q = ZX_sub(monomial(gen_1,2*p-1,0), monomial(gen_1,p,0));
  Q = gsub(xp, deg1pol_shallow(gen_1, Q, v)); /* x^p - x - (y^(2p-1)-y^p) */
  for (i = 2; i <= l; ++i) T = FpX_FpXY_resultant(T, Q, ip);
  (void)delete_var(); setvarn(T,0); return T;
}

/* check if polsubcyclo(n,l,0) is irreducible modulo p */
static long
fpinit_check(GEN p, long n, long l)
{
  ulong q;
  if (!uisprime(n)) return 0;
  q = umodiu(p,n); if (!q) return 0;
  return cgcd((n-1)/Fl_order(q, n-1, n), l) == 1;
}

/* let k=2 if p%4==1, and k=4 else and assume k*p does not divide l.
 * Return an irreducible polynomial of degree l over F_p.
 * Variant of Adleman and Lenstra "Finding irreducible polynomials over
 * finite fields", ACM, 1986 (5) 350--355.
 * Not stack clean */
static GEN
fpinit(GEN p, long l)
{
  ulong n = 1+l;
  while (!fpinit_check(p,n,l)) n += l;
  if (DEBUGLEVEL>=4) err_printf("FFInit: using polsubcyclo(%ld, %ld)\n",n,l);
  return FpX_red(polsubcyclo(n,l,0),p);
}

static GEN
ffinit_fact(GEN p, long n)
{
  GEN P, F = gel(factoru_pow(n),3);
  long i;
  if (!odd(n) && absequaliu(p, 2))
    P = f2init(vals(n)); /* if n is even, F[1] = 2^vals(n)*/
  else
    P = fpinit(p, F[1]);
  for (i = 2; i < lg(F); ++i)
    P = FpX_direct_compositum(fpinit(p, F[i]), P, p);
  return P;
}

static GEN
ffinit_nofact(GEN p, long n)
{
  GEN P, Q = NULL;
  if (lgefint(p)==3)
  {
    ulong pp = p[2], q;
    long v = u_lvalrem(n,pp,&q);
    if (v>0)
    {
      Q = (pp == 2)? f2init(v): fpinit(p,n/q);
      n = q;
    }
  }
  /* n coprime to p */
  if (n==1) P = Q;
  else
  {
    P = fpinit(p, n);
    if (Q) P = FpX_direct_compositum(P, Q, p);
  }
  return P;
}

static GEN
init_Fq_i(GEN p, long n, long v)
{
  GEN P;
  if (n <= 0) pari_err_DOMAIN("ffinit", "degree", "<=", gen_0, stoi(n));
  if (typ(p) != t_INT) pari_err_TYPE("ffinit",p);
  if (signe(p) <= 0) pari_err_PRIME("ffinit",p);
  if (v < 0) v = 0;
  if (n == 1) return pol_x(v);
  if (fpinit_check(p, n+1, n)) return polcyclo(n+1, v);
  if (lgefint(p)-2 <= expu(n))
    P = ffinit_fact(p,n);
  else
    P = ffinit_nofact(p,n);
  setvarn(P, v); return P;
}
GEN
init_Fq(GEN p, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, init_Fq_i(p, n, v));
}
GEN
ffinit(GEN p, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, FpX_to_mod(init_Fq_i(p, n, v), p));
}

GEN
ffnbirred(GEN p, long n)
{
  pari_sp av = avma;
  long j;
  GEN s = gen_0, dk, pd;
  dk = divisorsu(n);
  for (j = 1; j < lg(dk); ++j)
  {
    long d = dk[j];
    long m = moebiusu(d);
    if (!m) continue;
    pd = powiu(p, n/d);
    s = m>0 ? addii(s, pd): subii(s,pd);
  }
  return gerepileuptoint(av, divis(s, n));
}

GEN
ffsumnbirred(GEN p, long n)
{
  pari_sp av = avma;
  long i,j;
  GEN v,q, t = gen_0;
  v = cgetg(n+1,t_VECSMALL); v[1] = 1;
  q = cgetg(n+1,t_VEC); gel(q,1) = p;
  for(i=2; i<=n; i++)
  {
    v[i] = moebiusu(i);
    gel(q,i) = mulii(gel(q,i-1), p);
  }
  for(i=1; i<=n; i++)
  {
    GEN s = gen_0;
    GEN dk = divisorsu(i);
    for (j = 1; j < lg(dk); ++j)
    {
      long d = dk[j], m = v[d];
      if (!m) continue;
      s = m>0 ? addii(s, gel(q, i/d)): subii(s, gel(q, i/d));
    }
    t = addii(t, divis(s, i));
  }
  return gerepileuptoint(av, t);
}

GEN
ffnbirred0(GEN p, long n, long flag)
{
  if (typ(p) != t_INT) pari_err_TYPE("ffnbirred", p);
  if (n <= 0) pari_err_DOMAIN("ffnbirred", "degree", "<=", gen_0, stoi(n));
  switch(flag)
  {
    case 0:
      return ffnbirred(p, n);
    case 1:
      return ffsumnbirred(p, n);
    default:
      pari_err_FLAG("ffnbirred");
  }
  return NULL; /* NOT REACHED */
}
