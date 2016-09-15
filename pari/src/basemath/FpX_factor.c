/* Copyright (C) 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

/***********************************************************************/
/**                                                                   **/
/**               Factorisation over finite field                     **/
/**                                                                   **/
/***********************************************************************/

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
/* Check types and replace F by a monic normalized FpX having the same roots
 * Don't bother to make constant polynomials monic */
static void
factmod_init(GEN *F, GEN p)
{
  if (typ(p)!=t_INT) pari_err_TYPE("factmod",p);
  if (signe(p) < 0) pari_err_PRIME("factmod",p);
  if (typ(*F)!=t_POL) pari_err_TYPE("factmod",*F);
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    if (pp < 2) pari_err_PRIME("factmod", p);
    *F = RgX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
  }
  else
  {
    *F = RgX_to_FpX(*F, p);
    if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  }
}
/* as above, assume p prime and *F a ZX */
static void
ZX_factmod_init(GEN *F, GEN p)
{
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    *F = ZX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
  }
  else
  {
    *F = FpX_red(*F, p);
    if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  }
}

/* return 1,...,p-1 [not_0 = 1] or 0,...,p [not_0 = 0] */
static GEN
all_roots_mod_p(ulong p, int not_0)
{
  GEN r;
  ulong i;
  if (not_0) {
    r = cgetg(p, t_VECSMALL);
    for (i = 1; i < p; i++) r[i] = i;
  } else {
    r = cgetg(p+1, t_VECSMALL);
    for (i = 0; i < p; i++) r[i+1] = i;
  }
  return r;
}

/* X^n - 1 */
static GEN
Flx_Xnm1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  t[1] = sv;
  t[2] = p - 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}
/* X^n + 1 */
static GEN
Flx_Xn1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  (void) p;
  t[1] = sv;
  t[2] = 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}

static ulong
Fl_nonsquare(ulong p)
{
  long k = 2;
  for (;; k++)
  {
    long i = krouu(k, p);
    if (!i) pari_err_PRIME("Fl_nonsquare",utoipos(p));
    if (i < 0) return k;
  }
}

/* f monic Flx, f(0) != 0. Return a monic squarefree g with the same
 * roots as f */
static GEN
Flx_cut_out_roots(GEN f, ulong p)
{
  GEN g = Flx_mod_Xnm1(f, p-1, p); /* f mod x^(p-1) - 1 */
  if (g != f && degpol(g) >= 0) {
    (void)Flx_valrem(g, &g); /* reduction may introduce 0 root */
    g = Flx_gcd(g, Flx_Xnm1(g[1], p-1, p), p);
    g = Flx_normalize(g, p);
  }
  return g;
}

/* by checking f(0..p-1) */
GEN
Flx_roots_naive(GEN f, ulong p)
{
  long d, n = 0;
  ulong s = 1UL, r;
  GEN q, y = cgetg(degpol(f) + 1, t_VECSMALL);
  pari_sp av2, av = avma;

  if (Flx_valrem(f, &f)) y[++n] = 0;
  f = Flx_cut_out_roots(f, p);
  d = degpol(f);
  if (d < 0) return all_roots_mod_p(p, n == 0);
  av2 = avma;
  while (d > 1) /* d = current degree of f */
  {
    q = Flx_div_by_X_x(f, s, p, &r); /* TODO: FFT-type multi-evaluation */
    if (r) avma = av2; else { y[++n] = s; d--; f = q; av2 = avma; }
    if (++s == p) break;
  }
  if (d == 1)
  { /* -f[2]/f[3], root of deg 1 polynomial */
    r = Fl_mul(p - Fl_inv(f[3], p), f[2], p);
    if (r >= s) y[++n] = r; /* otherwise double root */
  }
  avma = av; fixlg(y, n+1); return y;
}
static GEN
Flx_root_mod_2(GEN f)
{
  int z1, z0 = !(f[2] & 1);
  long i,n;
  GEN y;

  for (i=2, n=1; i < lg(f); i++) n += f[i];
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_VECSMALL); i = 1;
  if (z0) y[i++] = 0;
  if (z1) y[i  ] = 1;
  return y;
}
static ulong
Flx_oneroot_mod_2(GEN f)
{
  long i,n;
  if (!(f[2] & 1)) return 0;
  for (i=2, n=1; i < lg(f); i++) n += f[i];
  if (n & 1) return 1;
  return 2;
}

static GEN FpX_roots_i(GEN f, GEN p);
static GEN Flx_roots_i(GEN f, ulong p);
static GEN FpX_Berlekamp_i(GEN f, GEN pp, long flag);

static int
cmpGuGu(GEN a, GEN b) { return (ulong)a < (ulong)b? -1: (a == b? 0: 1); }

/* Generic driver to computes the roots of f modulo pp, using 'Roots' when
 * pp is a small prime.
 * if (gpwrap), check types thoroughly and return t_INTMODs, otherwise
 * assume that f is an FpX, pp a prime and return t_INTs */
static GEN
rootmod_aux(GEN f, GEN pp, GEN (*Roots)(GEN,ulong), int gpwrap)
{
  pari_sp av = avma;
  GEN y;
  if (gpwrap)
    factmod_init(&f, pp);
  else
    ZX_factmod_init(&f, pp);
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("rootmod");
    case 3: avma = av; return cgetg(1,t_COL);
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong p = pp[2];
    if (p == 2)
      y = Flx_root_mod_2(f);
    else
    {
      if (!odd(p)) pari_err_PRIME("rootmod",utoi(p));
      y = Roots(f, p);
    }
    y = Flc_to_ZC(y);
  }
  else
    y = FpX_roots_i(f, pp);
  if (gpwrap) y = FpC_to_mod(y, pp);
  return gerepileupto(av, y);
}
/* assume that f is a ZX an pp a prime */
GEN
FpX_roots(GEN f, GEN pp)
{ return rootmod_aux(f, pp, Flx_roots_i, 0); }
/* no assumptions on f and pp */
GEN
rootmod2(GEN f, GEN pp) { return rootmod_aux(f, pp, &Flx_roots_naive, 1); }
GEN
rootmod(GEN f, GEN pp) { return rootmod_aux(f, pp, &Flx_roots_i, 1); }
GEN
rootmod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return rootmod(f,p);
    case 1: return rootmod2(f,p);
    default: pari_err_FLAG("polrootsmod");
  }
  return NULL; /* not reached */
}

/* assume x reduced mod p > 2, monic. */
static int
FpX_quad_factortype(GEN x, GEN p)
{
  GEN b = gel(x,3), c = gel(x,2);
  GEN D = subii(sqri(b), shifti(c,2));
  return kronecker(D,p);
}
/* assume x reduced mod p, monic. Return one root, or NULL if irreducible */
GEN
FpX_quad_root(GEN x, GEN p, int unknown)
{
  GEN s, D, b = gel(x,3), c = gel(x,2);

  if (absequaliu(p, 2)) {
    if (!signe(b)) return c;
    return signe(c)? NULL: gen_1;
  }
  D = subii(sqri(b), shifti(c,2));
  D = remii(D,p);
  if (unknown && kronecker(D,p) == -1) return NULL;

  s = Fp_sqrt(D,p);
  /* p is not prime, go on and give e.g. maxord a chance to recover */
  if (!s) return NULL;
  return Fp_halve(Fp_sub(s,b, p), p);
}
static GEN
FpX_otherroot(GEN x, GEN r, GEN p)
{ return Fp_neg(Fp_add(gel(x,3), r, p), p); }

/* disc(x^2+bx+c) = b^2 - 4c */
static ulong
Fl_disc_bc(ulong b, ulong c, ulong p)
{ return Fl_sub(Fl_sqr(b,p), Fl_double(Fl_double(c,p),p), p); }
/* p > 2 */
static ulong
Flx_quad_root(GEN x, ulong p, int unknown)
{
  ulong s, b = x[3], c = x[2];
  ulong D = Fl_disc_bc(b, c, p);
  if (unknown && krouu(D,p) == -1) return p;
  s = Fl_sqrt(D,p);
  if (s==~0UL) return p;
  return Fl_halve(Fl_sub(s,b, p), p);
}
static ulong
Flx_otherroot(GEN x, ulong r, ulong p)
{ return Fl_neg(Fl_add(x[3], r, p), p); }


/* 'todo' contains the list of factors to be split.
 * 'done' the list of finished factors, no longer touched */
struct split_t { GEN todo, done; };
static void
split_init(struct split_t *S, long max)
{
  S->todo = vectrunc_init(max);
  S->done = vectrunc_init(max);
}
#if 0
/* move todo[i] to done */
static void
split_convert(struct split_t *S, long i)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, gel(S->todo,i));
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);
}
#endif
/* append t to todo */
static void
split_add(struct split_t *S, GEN t) { vectrunc_append(S->todo, t); }
/* delete todo[i], add t to done */
static void
split_moveto_done(struct split_t *S, long i, GEN t)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, t);
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);

}
/* append t to done */
static void
split_add_done(struct split_t *S, GEN t)
{ vectrunc_append(S->done, t); }
/* split todo[i] into a and b */
static void
split_todo(struct split_t *S, long i, GEN a, GEN b)
{
  gel(S->todo, i) = a;
  split_add(S, b);
}
/* split todo[i] into a and b, moved to done */
static void
split_done(struct split_t *S, long i, GEN a, GEN b)
{
  split_moveto_done(S, i, a);
  split_add_done(S, b);
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
FpX_roots_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  struct split_t S;

  split_init(&S, lg(f)-1);
  settyp(S.done, t_COL);
  if (ZX_valrem(f, &f)) split_add_done(&S, gen_0);
  switch(degpol(f))
  {
    case 0: return ZC_copy(S.done);
    case 1: split_add_done(&S, subii(p, gel(f,2))); return ZC_copy(S.done);
    case 2: {
      GEN s, r = FpX_quad_root(f, p, 1);
      if (r) {
        split_add_done(&S, r);
        s = FpX_otherroot(f,r, p);
        /* f not known to be square free yet */
        if (!equalii(r, s)) split_add_done(&S, s);
      }
      return sort(S.done);
    }
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  if (!degpol(a)) return ZC_copy(S.done);
  split_add(&S, FpX_normalize(a,p));

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2] = 1;; pol0[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) return sort(S.done);
    if (pol0[2] == 100 && !BPSW_psp(p)) pari_err_PRIME("polrootsmod",p);
    for (j = 1; j < l; j++)
    {
      GEN c = gel(S.todo,j);
      switch(degpol(c))
      { /* convert linear and quadratics to roots, try to split the rest */
        case 1:
          split_moveto_done(&S, j, subii(p, gel(c,2)));
          j--; l--; break;
        case 2: {
          GEN r = FpX_quad_root(c, p, 0), s;
          if (!r) pari_err_PRIME("polrootsmod",p);
          s = FpX_otherroot(c,r, p);
          split_done(&S, j, r, s);
          j--; l--; break;
        }
        default: {
          /* b = pol^(p-1)/2 - 1 */
          GEN b = FpX_Fp_sub_shallow(FpXQ_pow(pol,q, c,p), gen_1, p);
          long db;
          b = FpX_gcd(c,b, p); db = degpol(b);
          if (db && db < degpol(c))
          {
            b = FpX_normalize(b, p);
            c = FpX_div(c,b, p);
            split_todo(&S, j, b, c);
          }
        }
      }
    }
  }
}

/* Assume f is normalized */
static ulong
Flx_cubic_root(GEN ff, ulong p)
{
  GEN f = Flx_normalize(ff,p);
  ulong pi = get_Fl_red(p);
  ulong a = f[4], b=f[3], c=f[2], p3 = p%3==1 ? (2*p+1)/3 :(p+1)/3;
  ulong t = Fl_mul_pre(a, p3, p, pi), t2 = Fl_sqr_pre(t, p, pi);
  ulong A = Fl_sub(b, Fl_triple(t2, p), p);
  ulong B = Fl_addmul_pre(t, Fl_sub(Fl_double(t2, p), b, p), c, p, pi);
  ulong A3 =  Fl_mul_pre(A, p3, p, pi);
  ulong A32 = Fl_sqr_pre(A3, p, pi), A33 = Fl_mul_pre(A3, A32, p, pi);
  ulong S = Fl_neg(B,p), P = Fl_neg(A3,p);
  ulong D = Fl_add(Fl_sqr_pre(S, p, pi), Fl_double(Fl_double(A33, p), p), p);
  ulong s = Fl_sqrt_pre(D, p, pi), vS1, vS2;
  if (s!=~0UL)
  {
    ulong S1 = S==s ? S: Fl_halve(Fl_sub(S, s, p), p);
    if (p%3==2) /* 1 solutions */
      vS1 = Fl_powu_pre(S1, (2*p-1)/3, p, pi);
    else
    {
      vS1 = Fl_sqrtl_pre(S1, 3, p, pi);
      if (vS1==~0UL) return p; /*0 solutions*/
      /*3 solutions*/
    }
    vS2 = P? Fl_mul_pre(P, Fl_inv(vS1, p), p, pi): 0;
    return Fl_sub(Fl_add(vS1,vS2, p), t, p);
  }
  else
  {
    pari_sp av = avma;
    GEN S1 = mkvecsmall2(Fl_halve(S, p), Fl_halve(1UL, p));
    GEN vS1 = Fl2_sqrtn_pre(S1, utoi(3), D, p, pi, NULL);
    ulong Sa;
    if (!vS1) return p; /*0 solutions, p%3==2*/
    Sa = vS1[1];
    if (p%3==1) /*1 solutions*/
    {
      ulong Fa = Fl2_norm_pre(vS1, D, p, pi);
      if (Fa!=P)
        Sa = Fl_mul(Sa, Fl_div(Fa, P, p),p);
    }
    avma = av;
    return Fl_sub(Fl_double(Sa,p),t,p);
  }
}

/* assume p > 2 prime */
static ulong
Flx_oneroot_i(GEN f, ulong p, long fl)
{
  GEN pol, a;
  ulong q;
  long da;

  if (Flx_val(f)) return 0;
  switch(degpol(f))
  {
    case 1: return Fl_neg(f[2], p);
    case 2: return Flx_quad_root(f, p, 1);
    case 3: if (p>3) return Flx_cubic_root(f, p); /*FALL THROUGH*/
  }

  if (!fl)
  {
    a = Flxq_powu(polx_Flx(f[1]), p - 1, f,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod f */
    a = Flx_gcd(f,a, p);
  } else a = f;
  da = degpol(a);
  if (!da) return p;
  a = Flx_normalize(a,p);

  q = p >> 1;
  pol = polx_Flx(f[1]);
  for(pol[2] = 1;; pol[2]++)
  {
    if (pol[2] == 1000 && !uisprime(p)) pari_err_PRIME("Flx_oneroot",utoipos(p));
    switch(da)
    {
      case 1: return Fl_neg(a[2], p);
      case 2: return Flx_quad_root(a, p, 0);
      case 3: if (p>3) return Flx_cubic_root(a, p); /*FALL THROUGH*/
      default: {
        GEN b = Flx_Fl_add(Flxq_powu(pol,q, a,p), p-1, p);
        long db;
        b = Flx_gcd(a,b, p); db = degpol(b);
        if (db && db < da)
        {
          b = Flx_normalize(b, p);
          if (db <= (da >> 1)) {
            a = b;
            da = db;
          } else {
            a = Flx_div(a,b, p);
            da -= db;
          }
        }
      }
    }
  }
}

/* assume p > 2 prime */
static GEN
FpX_oneroot_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  long da;

  if (ZX_val(f)) return gen_0;
  switch(degpol(f))
  {
    case 1: return subii(p, gel(f,2));
    case 2: return FpX_quad_root(f, p, 1);
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  da = degpol(a);
  if (!da) return NULL;
  a = FpX_normalize(a,p);

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2]=1; ; pol0[2]++)
  {
    if (pol0[2] == 1000 && !BPSW_psp(p)) pari_err_PRIME("FpX_oneroot",p);
    switch(da)
    {
      case 1: return subii(p, gel(a,2));
      case 2: return FpX_quad_root(a, p, 0);
      default: {
        GEN b = FpX_Fp_sub_shallow(FpXQ_pow(pol,q, a,p), gen_1, p);
        long db;
        b = FpX_gcd(a,b, p); db = degpol(b);
        if (db && db < da)
        {
          b = FpX_normalize(b, p);
          if (db <= (da >> 1)) {
            a = b;
            da = db;
          } else {
            a = FpX_div(a,b, p);
            da -= db;
          }
        }
      }
    }
  }
}

ulong
Flx_oneroot(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 0);
  avma = av; return r;
}

ulong
Flx_oneroot_split(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 1);
  avma = av; return r;
}

/* assume that p is prime */
GEN
FpX_oneroot(GEN f, GEN pp) {
  pari_sp av = avma;
  ZX_factmod_init(&f, pp);
  switch(lg(f))
  {
    case 2: avma = av; return gen_0;
    case 3: avma = av; return NULL;
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong r, p = pp[2];
    if (p == 2)
      r = Flx_oneroot_mod_2(f);
    else
      r = Flx_oneroot_i(f, p, 0);
    avma = av;
    return (r == p)? NULL: utoi(r);
  }
  f = FpX_oneroot_i(f, pp);
  if (!f) { avma = av; return NULL; }
  return gerepileuptoint(av, f);
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/

/* Functions giving information on the factorisation. */

/* u in Z[X], return kernel of (Frob - Id) over Fp[X] / u */
GEN
FpX_Berlekamp_ker(GEN u, GEN p)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Q  = FpX_matFrobenius(u, p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Fp_sub(gcoeff(Q,j,j), gen_1, p);
  return gerepileupto(ltop, FpM_ker(Q,p));
}

GEN
F2x_Berlekamp_ker(GEN u)
{
  pari_sp ltop=avma;
  long j,N = F2x_degree(u);
  GEN Q;
  pari_timer T;
  timer_start(&T);
  Q = F2x_matFrobenius(u);
  for (j=1; j<=N; j++)
    F2m_flip(Q,j,j);
  if(DEBUGLEVEL>=9) timer_printf(&T,"Berlekamp matrix");
  Q = F2m_ker_sp(Q,0);
  if(DEBUGLEVEL>=9) timer_printf(&T,"kernel");
  return gerepileupto(ltop,Q);
}

GEN
Flx_Berlekamp_ker(GEN u, ulong l)
{
  pari_sp ltop=avma;
  long j,N = degpol(u);
  GEN Q;
  pari_timer T;
  timer_start(&T);
  Q  = Flx_matFrobenius(u, l);
  for (j=1; j<=N; j++)
    coeff(Q,j,j) = Fl_sub(coeff(Q,j,j),1,l);
  if(DEBUGLEVEL>=9) timer_printf(&T,"Berlekamp matrix");
  Q = Flm_ker_sp(Q,l,0);
  if(DEBUGLEVEL>=9) timer_printf(&T,"kernel");
  return gerepileupto(ltop,Q);
}

/* product of terms of degree 1 in factorization of f */
GEN
FpX_split_part(GEN f, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpX_red(f, p);
  z = FpX_sub(FpX_Frobenius(f, p), X, p);
  return FpX_gcd(z,f,p);
}

/* Compute the number of roots in Fp without counting multiplicity
 * return -1 for 0 polynomial. lc(f) must be prime to p. */
long
FpX_nbroots(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_split_part(f, p);
  avma = av; return degpol(z);
}

int
FpX_is_totally_split(GEN f, GEN p)
{
  long n=degpol(f);
  pari_sp av = avma;
  if (n <= 1) return 1;
  if (abscmpui(n, p) > 0) return 0;
  f = FpX_red(f, p);
  avma = av; return gequalX(FpX_Frobenius(f, p));
}

long
Flx_nbroots(GEN f, ulong p)
{
  long n = degpol(f);
  pari_sp av = avma;
  GEN z;
  if (n <= 1) return n;
  if (n == 2)
  {
    ulong D;
    if (p==2) return (f[2]==0) + (f[2]!=f[3]);
    D = Fl_sub(Fl_sqr(f[3], p), Fl_mul(Fl_mul(f[4], f[2], p), 4%p, p), p);
    return 1 + krouu(D,p);
  }
  z = Flx_sub(Flx_Frobenius(f, p), polx_Flx(f[1]), p);
  z = Flx_gcd(z, f, p);
  avma = av; return degpol(z);
}

/* See <http://www.shoup.net/papers/factorimpl.pdf> */
static GEN
FpX_ddf(GEN T, GEN XP, GEN p)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Tr, xq;
  long i, j, n, v;
  long B, l, m;
  pari_timer ti;
  n = get_FpX_degree(T); v = get_FpX_var(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_FpX_mod(T));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = FpX_get_red(T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = pol_x(v);
  gel(b, 2) = XP;
  if (DEBUGLEVEL>=7) timer_start(&ti);
  xq = FpXQ_powers(gel(b, 2), brent_kung_optpow(n, l-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: xq baby");
  for (i = 3; i <= l+1; i++)
    gel(b, i) = FpX_FpXQV_eval(gel(b, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: baby");
  xq = FpXQ_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = FpX_FpXQV_eval(gel(g, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = FpX_sub(gj, gel(b, 1), p);
    for (i = 2; i <= l; i++)
      e = FpXQ_mul(e, FpX_sub(gj, gel(b, i), p), T, p);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: diff");
  Tr = get_FpX_mod(T);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    gel(F, j) = FpX_gcd(Tr, gel(h, j), p);
    Tr = FpX_div(Tr, gel(F,j), p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: F");
  f = const_vec(n, pol_1(v));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = FpX_gcd(e, FpX_sub(gel(g, j), gel(b, i+1), p), p);
      if (degpol(u))
      {
        gel(f, l*j-i) = u;
        e = FpX_div(e, u, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf: f");
  if (degpol(Tr)) gel(f, degpol(Tr)) = Tr;
  return gerepilecopy(av, f);
}

static void
FpX_edf_simple(GEN Tp, GEN XP, long d, GEN p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d;
  GEN T, f, ff;
  GEN p2;
  if (r==1) { gel(V, idx) = Tp; return; }
  p2 = shifti(p,-1);
  T = FpX_get_red(Tp, p);
  XP = FpX_rem(XP, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_FpX(n, varn(Tp), p);
    GEN t = gel(FpXQ_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (signe(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN R = FpXQ_pow(FpX_Fp_add(t, randomi(p), p), p2, T, p);
      f = FpX_gcd(FpX_Fp_sub(R, gen_1, p), Tp, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = FpX_normalize(f, p);
  ff = FpX_div(Tp, f ,p);
  FpX_edf_simple(f, XP, d, p, V, idx);
  FpX_edf_simple(ff, XP, d, p, V, idx+degpol(f)/d);
}

static void
FpX_edf_rec(GEN T, GEN hp, GEN t, long d, GEN p2, GEN p, GEN V, long idx)
{
  pari_sp av;
  GEN Tp = get_FpX_mod(T);
  long n = degpol(hp), vT = varn(Tp);
  GEN u1, u2, f1, f2;
  GEN R, h;
  h = FpX_get_red(hp, p);
  t = FpX_rem(t, T, p);
  av = avma;
  do
  {
    avma = av;
    R = FpXQ_pow(deg1pol(gen_1, randomi(p), vT), p2, h, p);
    u1 = FpX_gcd(FpX_Fp_sub(R, gen_1, p), hp, p);
  } while (degpol(u1)==0 || degpol(u1)==n);
  f1 = FpX_gcd(FpX_FpXQ_eval(u1, t, T, p), Tp, p);
  f1 = FpX_normalize(f1, p);
  u2 = FpX_div(hp, u1, p);
  f2 = FpX_div(Tp, f1, p);
  if (degpol(u1)==1)
    gel(V, idx) = f1;
  else
    FpX_edf_rec(FpX_get_red(f1, p), u1, t, d, p2, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
    gel(V, idx) = f2;
  else
    FpX_edf_rec(FpX_get_red(f2, p), u2, t, d, p2, p, V, idx);
}

static void
FpX_edf(GEN Tp, GEN XP, long d, GEN p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d, vT = varn(Tp);
  GEN T, h, t;
  pari_timer ti;
  if (r==1) { gel(V, idx) = Tp; return; }
  T = FpX_get_red(Tp, p);
  XP = FpX_rem(XP, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_FpX(n, vT, p);
    t = gel(FpXQ_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_edf: FpXQ_auttrace");
    h = FpXQ_minpoly(t, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_edf: FpXQ_minpoly");
  } while (degpol(h) != r);
  FpX_edf_rec(T, h, t, d, shifti(p, -1), p, V, idx);
}

static GEN
FpX_factor_Shoup(GEN T, GEN p)
{
  long i, n, s = 0;
  GEN XP, D, V;
  long e = expi(p);
  pari_timer ti;
  n = get_FpX_degree(T);
  T = FpX_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = FpX_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_Frobenius");
  D = FpX_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_ddf");
  for (i = 1; i <= n; i++)
    s += degpol(gel(D,i))/i;
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = FpX_normalize(Di, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      FpX_edf(Di, XP, i, p, V, s);
    else
      FpX_edf_simple(Di, XP, i, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
FpX_simplefact_Shoup(GEN T, GEN p)
{
  long i, n, s = 0, j = 1, k;
  GEN XP, D, V;
  pari_timer ti;
  n = get_FpX_degree(T);
  T = FpX_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = FpX_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_Frobenius");
  D = FpX_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_ddf");
  for (i = 1; i <= n; i++)
    s += degpol(gel(D,i))/i;
  V = cgetg(s+1, t_VEC);
  for (i = 1; i <= n; i++)
  {
    long ni = degpol(gel(D,i)), ri = ni/i;
    if (ni == 0) continue;
    for (k = 1; k <= ri; k++)
      gel(V, j++) = utoi(i);
  }
  return V;
}

/* Yun algorithm: Assume p > degpol(T) */
static GEN
FpX_factor_Yun(GEN T, GEN p)
{
  long n = degpol(T);
  long i = 1;
  GEN d = FpX_deriv(T, p);
  GEN a, b, c;
  GEN V = cgetg(n+1,t_VEC);
  a = FpX_gcd(T, d, p);
  if (degpol(a) == 0) return mkvec(T);
  b = FpX_div(T, a, p);
  do
  {
    c = FpX_div(d, a, p);
    d = FpX_sub(c, FpX_deriv(b, p), p);
    a = FpX_normalize(FpX_gcd(b, d, p), p);
    gel(V, i++) = a;
    b = FpX_div(b, a, p);
  } while (degpol(b));
  setlg(V, i); return V;
}
GEN
FpX_factor_squarefree(GEN T, GEN p)
{
  if (abscmpiu(p, degpol(T)) <= 0)
  {
    ulong pp = (ulong)p[2];
    GEN u = Flx_factor_squarefree(ZX_to_Flx(T,pp), pp);
    return FlxV_to_ZXV(u);
  }
  return FpX_factor_Yun(T, p);
}

/* F / E  a vector of factors / exponents of virtual length l
 * (their real lg may be larger). Set their lg to j and return [F,E] */
static GEN
FE_setlg(GEN F, GEN E, long l)
{
  setlg(E,l);
  setlg(F,l); return mkvec2(F,E);
}
/* F / E  a vector of vectors of factors / exponents of virtual length l
 * (their real lg may be larger). Set their lg to j, concat and return [F,E] */
static GEN
FE_concat(GEN F, GEN E, long l)
{
  setlg(E,l); E = shallowconcat1(E);
  setlg(F,l); F = shallowconcat1(F); return mkvec2(F,E);
}

static GEN
FpX_factor_Cantor(GEN T, GEN p)
{
  GEN E, F, V = FpX_factor_Yun(T, p);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = FpX_factor_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpii);
}

static GEN
FpX_simplefact_Cantor(GEN T, GEN p)
{
  GEN E, F, V;
  long i, j, l;
  V = FpX_factor_Yun(get_FpX_mod(T), p);
  l = lg(V);
  E = cgetg(l, t_VEC);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = FpX_simplefact_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor(FE_concat(F,E,j), (void*)&cmpGuGu, cmp_nodata);
}

static int
FpX_isirred_Cantor(GEN Tp, GEN p)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN T = get_FpX_mod(Tp);
  GEN dT = FpX_deriv(T, p);
  GEN XP, D;
  if (degpol(FpX_gcd(T, dT, p)) != 0) { avma = av; return 0; }
  n = get_FpX_degree(T);
  T = FpX_get_red(Tp, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = FpX_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_Frobenius");
  D = FpX_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_ddf");
  d = degpol(gel(D, n));
  avma = av; return d==n;
}

static GEN FpX_factor_deg2(GEN f, GEN p, long d, long flag);

/*Assume that p is large and odd*/
static GEN
FpX_factcantor_i(GEN f, GEN pp, long flag)
{
  long d = degpol(f);
  if (d <= 2) return FpX_factor_deg2(f,pp,d,flag);
  switch(flag)
  {
    default: return FpX_factor_Cantor(f, pp);
    case 1: return FpX_simplefact_Cantor(f, pp);
    case 2: return FpX_isirred_Cantor(f, pp)? gen_1: NULL;
  }
}

long
FpX_nbfact_Frobenius(GEN T, GEN XP, GEN p)
{
  pari_sp av = avma;
  GEN ddf = FpX_ddf(T, XP, p);
  long l = lg(ddf), i, s=0;
  for(i = 1; i < l; i++)
    s += degpol(gel(ddf,i))/i;
  avma = av; return s;
}

long
FpX_nbfact(GEN T, GEN p)
{
  pari_sp av = avma;
  GEN XP = FpX_Frobenius(T, p);
  long n = FpX_nbfact_Frobenius(T, XP, p);
  avma = av; return n;
}

/* p > 2 */
static GEN
FpX_is_irred_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:
    case 0: return NULL;
    case 1: return gen_1;
  }
  return FpX_quad_factortype(f, p) == -1? gen_1: NULL;
}
/* p > 2 */
static GEN
FpX_degfact_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:retmkvec2(mkvecsmall(-1),mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkvec2(mkvecsmall(1), mkvecsmall(1));
  }
  switch(FpX_quad_factortype(f, p)) {
    case  1: retmkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1: retmkvec2(mkvecsmall(2), mkvecsmall(1));
    default: retmkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

GEN
prime_fact(GEN x) { retmkmat2(mkcolcopy(x), mkcol(gen_1)); }
GEN
trivial_fact(void) { retmkmat2(cgetg(1,t_COL), cgetg(1,t_COL)); }

/* Mod(0,p) * x, where x is f's main variable */
static GEN
Mod0pX(GEN f, GEN p)
{ return scalarpol(mkintmod(gen_0, p), varn(f)); }
static GEN
zero_fact_intmod(GEN f, GEN p) { return prime_fact(Mod0pX(f,p)); }

/* not gerepile safe */
static GEN
FpX_factor_2(GEN f, GEN p, long d)
{
  GEN r, s, R, S;
  long v;
  int sgn;
  switch(d)
  {
    case -1: retmkvec2(mkcol(pol_0(varn(f))), mkvecsmall(1));
    case  0: retmkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
    case  1: retmkvec2(mkcol(f), mkvecsmall(1));
  }
  r = FpX_quad_root(f, p, 1);
  if (!r) return mkvec2(mkcol(f), mkvecsmall(1));
  v = varn(f);
  s = FpX_otherroot(f, r, p);
  if (signe(r)) r = subii(p, r);
  if (signe(s)) s = subii(p, s);
  sgn = cmpii(s, r); if (sgn < 0) swap(s,r);
  R = deg1pol_shallow(gen_1, r, v);
  if (!sgn) return mkvec2(mkcol(R), mkvecsmall(2));
  S = deg1pol_shallow(gen_1, s, v);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
FpX_factor_deg2(GEN f, GEN p, long d, long flag)
{
  switch(flag) {
    case 2: return FpX_is_irred_2(f, p, d);
    case 1: return FpX_degfact_2(f, p, d);
    default: return FpX_factor_2(f, p, d);
  }
}

static int
F2x_quad_factortype(GEN x)
{ return x[2] == 7 ? -1: x[2] == 6 ? 1 :0; }

static GEN
F2x_is_irred_2(GEN f, long d)
{ return d == 1 || (d==2 && F2x_quad_factortype(f) == -1)? gen_1: NULL; }

static GEN
F2x_degfact_2(GEN f, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(F2x_quad_factortype(f)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

static GEN
F2x_factor_2(GEN f, long d)
{
  long v = f[1];
  if (d < 0) pari_err(e_ROOTS0,"Flx_factor_2");
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (d == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  switch(F2x_quad_factortype(f))
  {
  case -1: return mkvec2(mkcol(f), mkvecsmall(1));
  case 0:  return mkvec2(mkcol(mkvecsmall2(v,2+F2x_coeff(f,0))), mkvecsmall(2));
  default: return mkvec2(mkcol2(mkvecsmall2(v,2),mkvecsmall2(v,3)), mkvecsmall2(1,1));
  }
}
static GEN
F2x_factor_deg2(GEN f, long d, long flag)
{
  switch(flag) {
    case 2: return F2x_is_irred_2(f, d);
    case 1: return F2x_degfact_2(f, d);
    default: return F2x_factor_2(f, d);
  }
}

static void
split_squares(struct split_t *S, GEN g, ulong p)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xnm1(g, q, p); /* mod x^(p-1)/2 - 1 */
  if (degpol(a) < 0)
  {
    ulong i;
    split_add_done(S, (GEN)1);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_sqr(i,p));
  } else {
    (void)Flx_valrem(a, &a);
    if (degpol(a))
    {
      a = Flx_gcd(a, Flx_Xnm1(g[1], q, p), p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
static void
split_nonsquares(struct split_t *S, GEN g, ulong p)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xn1(g, q, p); /* mod x^(p-1)/2 + 1 */
  if (degpol(a) < 0)
  {
    ulong i, z = Fl_nonsquare(p);
    split_add_done(S, (GEN)z);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_mul(z, Fl_sqr(i,p), p));
  } else {
    (void)Flx_valrem(a, &a);
    if (degpol(a))
    {
      a = Flx_gcd(a, Flx_Xn1(g[1], q, p), p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
/* p > 2. f monic Flx, f(0) != 0. Add to split_t structs coprime factors
 * of g = \prod_{f(a) = 0} (X - a). Return 0 when f(x) = 0 for all x in Fp* */
static int
split_Flx_cut_out_roots(struct split_t *S, GEN f, ulong p)
{
  GEN a, g = Flx_mod_Xnm1(f, p-1, p); /* f mod x^(p-1) - 1 */
  long d = degpol(g);
  if (d < 0) return 0;
  if (g != f) { (void)Flx_valrem(g, &g); d = degpol(g); } /*kill powers of x*/
  if (!d) return 1;
  if (p <= 1.4 * (ulong)d) {
    /* small p; split further using x^((p-1)/2) +/- 1.
     * 30% degree drop makes the extra gcd worth it. */
    split_squares(S, g, p);
    split_nonsquares(S, g, p);
  } else { /* large p; use x^(p-1) - 1 directly */
    a = Flxq_powu(polx_Flx(f[1]), p-1, g,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod g */
    g = Flx_gcd(g,a, p);
    if (degpol(g)) split_add(S, Flx_normalize(g,p));
  }
  return 1;
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
Flx_roots_i(GEN f, ulong p)
{
  GEN pol, g;
  long v = Flx_valrem(f, &g);
  ulong q;
  struct split_t S;

  /* optimization: test for small degree first */
  switch(degpol(g))
  {
    case 1: {
      ulong r = p - g[2];
      return v? mkvecsmall2(0, r): mkvecsmall(r);
    }
    case 2: {
      ulong r = Flx_quad_root(g, p, 1), s;
      if (r == p) return v? mkvecsmall(0): cgetg(1,t_VECSMALL);
      s = Flx_otherroot(g,r, p);
      if (r < s)
        return v? mkvecsmall3(0, r, s): mkvecsmall2(r, s);
      else if (r > s)
        return v? mkvecsmall3(0, s, r): mkvecsmall2(s, r);
      else
        return v? mkvecsmall2(0, s): mkvecsmall(s);
    }
  }
  q = p >> 1;
  split_init(&S, lg(f)-1);
  settyp(S.done, t_VECSMALL);
  if (v) split_add_done(&S, (GEN)0);
  if (! split_Flx_cut_out_roots(&S, g, p))
    return all_roots_mod_p(p, lg(S.done) == 1);
  pol = polx_Flx(f[1]);
  for (pol[2]=1; ; pol[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) { vecsmall_sort(S.done); return S.done; }
    if (pol[2] == 100 && !uisprime(p)) pari_err_PRIME("polrootsmod",utoipos(p));
    for (j = 1; j < l; j++)
    {
      GEN c = gel(S.todo,j);
      switch(degpol(c))
      {
        case 1:
          split_moveto_done(&S, j, (GEN)(p - c[2]));
          j--; l--; break;
        case 2: {
          ulong r = Flx_quad_root(c, p, 0), s;
          if (r == p) pari_err_PRIME("polrootsmod",utoipos(p));
          s = Flx_otherroot(c,r, p);
          split_done(&S, j, (GEN)r, (GEN)s);
          j--; l--; break;
        }
        default: {
          GEN b = Flx_Fl_add(Flxq_powu(pol,q, c,p), p-1, p); /* pol^(p-1)/2 */
          long db;
          b = Flx_gcd(c,b, p); db = degpol(b);
          if (db && db < degpol(c))
          {
            b = Flx_normalize(b, p);
            c = Flx_div(c,b, p);
            split_todo(&S, j, b, c);
          }
        }
      }
    }
  }
}

GEN
Flx_roots(GEN f, ulong p)
{
  pari_sp av = avma;
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("Flx_roots");
    case 3: avma = av; return cgetg(1, t_VECSMALL);
  }
  if (p == 2) return Flx_root_mod_2(f);
  return gerepileuptoleaf(av, Flx_roots_i(Flx_normalize(f, p), p));
}

/* assume x reduced mod p, monic. */
static int
Flx_quad_factortype(GEN x, ulong p)
{
  ulong b = x[3], c = x[2];
  return krouu(Fl_disc_bc(b, c, p), p);
}
static GEN
Flx_is_irred_2(GEN f, ulong p, long d)
{
  if (!d) return NULL;
  if (d == 1) return gen_1;
  return Flx_quad_factortype(f, p) == -1? gen_1: NULL;
}
static GEN
Flx_degfact_2(GEN f, ulong p, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(Flx_quad_factortype(f, p)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}
/* p > 2 */
static GEN
Flx_factor_2(GEN f, ulong p, long d)
{
  ulong r, s;
  GEN R,S;
  long v = f[1];
  if (d < 0) pari_err(e_ROOTS0,"Flx_factor_2");
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (d == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  r = Flx_quad_root(f, p, 1);
  if (r==p) return mkvec2(mkcol(f), mkvecsmall(1));
  s = Flx_otherroot(f, r, p);
  r = Fl_neg(r, p);
  s = Fl_neg(s, p);
  if (s < r) lswap(s,r);
  R = mkvecsmall3(v,r,1);
  if (s == r) return mkvec2(mkcol(R), mkvecsmall(2));
  S = mkvecsmall3(v,s,1);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
Flx_factor_deg2(GEN f, ulong p, long d, long flag)
{
  switch(flag) {
    case 2: return Flx_is_irred_2(f, p, d);
    case 1: return Flx_degfact_2(f, p, d);
    default: return Flx_factor_2(f, p, d);
  }
}

void
F2xV_to_FlxV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_Flx(gel(v,i));
}
void
FlxV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= Flx_to_ZX(gel(v,i));
}
void
F2xV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_ZX(gel(v,i));
}

/* Adapted from Shoup NTL */
GEN
F2x_factor_squarefree(GEN f)
{
  GEN r, t, v, tv;
  long i, q, n = F2x_degree(f);
  GEN u = const_vec(n+1, pol1_F2x(f[1]));
  for(q = 1;;q *= 2)
  {
    r = F2x_gcd(f, F2x_deriv(f));
    if (F2x_degree(r) == 0)
    {
      gel(u, q) = f;
      break;
    }
    t = F2x_div(f, r);
    if (F2x_degree(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = F2x_gcd(r, t);
        tv = F2x_div(t, v);
        if (F2x_degree(tv) > 0)
          gel(u, j*q) = tv;
        if (F2x_degree(v) <= 0) break;
        r = F2x_div(r, v);
        t = v;
      }
      if (F2x_degree(r) == 0) break;
    }
    f = F2x_sqrt(r);
  }
  for (i = n; i; i--)
    if (F2x_degree(gel(u,i))) break;
  setlg(u,i+1); return u;
}

static GEN
F2x_ddf_simple(GEN T, GEN XP)
{
  pari_sp av = avma, av2;
  GEN f, z, Tr, X;
  long j, n = F2x_degree(T), v = T[1], B = n/2;
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(T);
  z = XP; Tr = T; X = polx_F2x(v);
  f = const_vec(n, pol1_F2x(v));
  av2 = avma;
  for (j = 1; j <= B; j++)
  {
    GEN u = F2x_gcd(Tr, F2x_add(z, X));
    if (F2x_degree(u))
    {
      gel(f, j) = u;
      Tr = F2x_div(Tr, u);
      av2 = avma;
    } else z = gerepileuptoleaf(av2, z);
    if (!F2x_degree(Tr)) break;
    z = F2xq_sqr(z, Tr);
  }
  if (F2x_degree(Tr)) gel(f, F2x_degree(Tr)) = Tr;
  return gerepilecopy(av, f);
}

static GEN
F2xq_frobtrace(GEN a, long d, GEN T)
{
  pari_sp av = avma;
  long i;
  GEN x = a;
  for(i=1; i<d; i++)
  {
    x = F2x_add(a, F2xq_sqr(x,T));
    if (gc_needed(av, 2))
      x = gerepileuptoleaf(av, x);
  }
  return x;
}

static void
F2x_edf_simple(GEN Tp, GEN XP, long d, GEN V, long idx)
{
  long n = F2x_degree(Tp), r = n/d;
  GEN T, f, ff;
  if (r==1) { gel(V, idx) = Tp; return; }
  T = Tp;
  XP = F2x_rem(XP, T);
  while (1)
  {
    pari_sp btop = avma;
    long df;
    GEN g = random_F2x(n, Tp[1]);
    GEN t = F2xq_frobtrace(g, d, T);
    if (lgpol(t) == 0) continue;
    f = F2x_gcd(t, Tp); df = F2x_degree(f);
    if (df > 0 && df < n) break;
    avma = btop;
  }
  ff = F2x_div(Tp, f);
  F2x_edf_simple(f, XP, d, V, idx);
  F2x_edf_simple(ff, XP, d, V, idx+F2x_degree(f)/d);
}

static GEN
F2x_factor_Shoup(GEN T)
{
  long i, n, s = 0;
  GEN XP, D, V;
  pari_timer ti;
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf");
  for (i = 1; i <= n; i++)
    s += F2x_degree(gel(D,i))/i;
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = F2x_degree(Di), ri = ni/i;
    if (ni == 0) continue;
    if (ni == i) { gel(V, s++) = Di; continue; }
    F2x_edf_simple(Di, XP, i, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
F2x_simplefact_Shoup(GEN T)
{
  long i, n, s = 0, j = 1, k;
  GEN XP, D, V;
  pari_timer ti;
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf");
  for (i = 1; i <= n; i++)
    s += F2x_degree(gel(D,i))/i;
  V = cgetg(s+1, t_VECSMALL);
  for (i = 1; i <= n; i++)
  {
    long ni = F2x_degree(gel(D,i)), ri = ni/i;
    if (ni == 0) continue;
    for (k = 1; k <= ri; k++)
      V[j++] = i;
  }
  return V;
}

static GEN
F2x_factor_Cantor(GEN T)
{
  GEN E, F, V = F2x_factor_squarefree(T);
  long i, j, l = lg(V);
  E = cgetg(l, t_VEC);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (F2x_degree(gel(V,i)))
    {
      GEN Fj = F2x_factor_Shoup(gel(V,i));
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpGuGu);
}

static GEN
F2x_simplefact_Cantor(GEN T)
{
  GEN E, F, V = F2x_factor_squarefree(T);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (F2x_degree(gel(V,i)))
    {
      GEN Fj = F2x_simplefact_Shoup(gel(V,i));
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor(FE_concat(F,E,j), (void*)&cmpGuGu, cmp_nodata);
}

static int
F2x_isirred_Cantor(GEN T)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN dT = F2x_deriv(T);
  GEN XP, D;
  if (F2x_degree(F2x_gcd(T, dT)) != 0) { avma = av; return 0; }
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf");
  d = F2x_degree(gel(D, n));
  avma = av; return d==n;
}

static GEN
F2x_factcantor_i(GEN f, long flag)
{
  long d = F2x_degree(f);
  if (d <= 2) return F2x_factor_deg2(f,d,flag);
  switch(flag)
  {
    default: return F2x_factor_Cantor(f);
    case 1: return F2x_simplefact_Cantor(f);
    case 2: return F2x_isirred_Cantor(f)? gen_1: NULL;
  }
}

GEN
F2x_factcantor(GEN f, long flag)
{
  pari_sp av = avma;
  GEN z = F2x_factcantor_i(f, flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}

GEN
F2x_degfact(GEN f)
{
  pari_sp av = avma;
  GEN z = F2x_factcantor_i(f, 1);
  return gerepilecopy(av, z);
}

int
F2x_is_irred(GEN f) { return !!F2x_factcantor_i(f, 2); }

/* Adapted from Shoup NTL */
GEN
Flx_factor_squarefree(GEN f, ulong p)
{
  long i, q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_Flx(f[1]));
  for(q = 1;;q *= p)
  {
    GEN t, v, tv, r = Flx_gcd(f, Flx_deriv(f, p), p);
    if (degpol(r) == 0) { gel(u, q) = f; break; }
    t = Flx_div(f, r, p);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = Flx_gcd(r, t, p);
        tv = Flx_div(t, v, p);
        if (degpol(tv) > 0) gel(u, j*q) = tv;
        if (degpol(v) <= 0) break;
        r = Flx_div(r, v, p);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    f = Flx_deflate(r, p);
  }
  for (i = n; i; i--)
    if (degpol(gel(u,i))) break;
  setlg(u,i+1); return u;
}

/* See <http://www.shoup.net/papers/factorimpl.pdf> */
static GEN
Flx_ddf(GEN T, GEN XP, ulong p)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Tr, xq;
  long i, j, n, v, bo, ro;
  long B, l, m;
  pari_timer ti;
  n = get_Flx_degree(T); v = get_Flx_var(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_Flx_mod(T));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = Flx_get_red(T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = polx_Flx(v);
  gel(b, 2) = XP;
  bo = brent_kung_optpow(n, l-1, 1);
  ro = (bo-1) + (l-1)*((n-1)/bo);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  if (expu(p) <= ro)
    for (i = 3; i <= l+1; i++)
      gel(b, i) = Flxq_powu(gel(b, i-1), p, T, p);
  else
  {
    xq = Flxq_powers(gel(b, 2), bo,  T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: xq baby");
    for (i = 3; i <= l+1; i++)
      gel(b, i) = Flx_FlxqV_eval(gel(b, i-1), xq, T, p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: baby");
  xq = Flxq_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = Flx_FlxqV_eval(gel(g, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = Flx_sub(gj, gel(b, 1), p);
    for (i = 2; i <= l; i++)
      e = Flxq_mul(e, Flx_sub(gj, gel(b, i), p), T, p);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: diff");
  Tr = get_Flx_mod(T);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    gel(F, j) = Flx_gcd(Tr, gel(h, j), p);
    Tr = Flx_div(Tr, gel(F,j), p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: F");
  f = const_vec(n, pol1_Flx(v));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = Flx_gcd(e, Flx_sub(gel(g, j), gel(b, i+1), p), p);
      if (degpol(u))
      {
        gel(f, l*j-i) = u;
        e = Flx_div(e, u, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf: f");
  if (degpol(Tr)) gel(f, degpol(Tr)) = Tr;
  return gerepilecopy(av, f);
}

static void
Flx_edf_simple(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d;
  GEN T, f, ff;
  ulong p2;
  if (r==1) { gel(V, idx) = Tp; return; }
  p2 = p>>1;
  T = Flx_get_red(Tp, p);
  XP = Flx_rem(XP, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_Flx(n, Tp[1], p);
    GEN t = gel(Flxq_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (lgpol(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN R = Flxq_powu(Flx_Fl_add(t, random_Fl(p), p), p2, T, p);
      f = Flx_gcd(Flx_Fl_add(R, p-1, p), Tp, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = Flx_normalize(f, p);
  ff = Flx_div(Tp, f ,p);
  Flx_edf_simple(f, XP, d, p, V, idx);
  Flx_edf_simple(ff, XP, d, p, V, idx+degpol(f)/d);
}
static void
Flx_edf(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx);

static void
Flx_edf_rec(GEN T, GEN XP, GEN hp, GEN t, long d, ulong p, GEN V, long idx)
{
  pari_sp av;
  GEN Tp = get_Flx_mod(T);
  long n = degpol(hp), vT = Tp[1];
  GEN u1, u2, f1, f2;
  ulong p2 = p>>1;
  GEN R, h;
  h = Flx_get_red(hp, p);
  t = Flx_rem(t, T, p);
  av = avma;
  do
  {
    avma = av;
    R = Flxq_powu(mkvecsmall3(vT, random_Fl(p), 1), p2, h, p);
    u1 = Flx_gcd(Flx_Fl_add(R, p-1, p), hp, p);
  } while (degpol(u1)==0 || degpol(u1)==n);
  f1 = Flx_gcd(Flx_Flxq_eval(u1, t, T, p), Tp, p);
  f1 = Flx_normalize(f1, p);
  u2 = Flx_div(hp, u1, p);
  f2 = Flx_div(Tp, f1, p);
  if (degpol(u1)==1)
  {
    if (degpol(f1)==d)
      gel(V, idx) = f1;
    else
      Flx_edf(f1, XP, d, p, V, idx);
  }
  else
    Flx_edf_rec(Flx_get_red(f1, p), XP, u1, t, d, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
  {
    if (degpol(f2)==d)
      gel(V, idx) = f2;
    else
      Flx_edf(f2, XP, d, p, V, idx);
  }
  else
    Flx_edf_rec(Flx_get_red(f2, p), XP, u2, t, d, p, V, idx);
}

static void
Flx_edf(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d, vT = Tp[1];
  GEN T, h, t;
  pari_timer ti;
  if (r==1) { gel(V, idx) = Tp; return; }
  T = Flx_get_red(Tp, p);
  XP = Flx_rem(XP, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_Flx(n, vT, p);
    t = gel(Flxq_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_edf: Flxq_auttrace");
    h = Flxq_minpoly(t, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_edf: Flxq_minpoly");
  } while (degpol(h) <= 1);
  Flx_edf_rec(T, XP, h, t, d, p, V, idx);
}

static GEN
Flx_factor_Shoup(GEN T, ulong p)
{
  long i, n, s = 0;
  GEN XP, D, V;
  long e = expu(p);
  pari_timer ti;
  n = get_Flx_degree(T);
  T = Flx_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf");
  for (i = 1; i <= n; i++)
    s += degpol(gel(D,i))/i;
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = Flx_normalize(Di, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      Flx_edf(Di, XP, i, p, V, s);
    else
      Flx_edf_simple(Di, XP, i, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
Flx_simplefact_Shoup(GEN T, ulong p)
{
  long i, n, s = 0, j = 1, k;
  GEN XP, D, V;
  pari_timer ti;
  n = get_Flx_degree(T);
  T = Flx_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf");
  for (i = 1; i <= n; i++)
    s += degpol(gel(D,i))/i;
  V = cgetg(s+1, t_VECSMALL);
  for (i = 1; i <= n; i++)
  {
    long ni = degpol(gel(D,i)), ri = ni/i;
    if (ni == 0) continue;
    for (k = 1; k <= ri; k++)
      V[j++] = i;
  }
  return V;
}

static GEN
Flx_factor_Cantor(GEN T, ulong p)
{
  GEN E, F, V = Flx_factor_squarefree(get_Flx_mod(T), p);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = Flx_factor_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpGuGu);
}

static GEN
Flx_simplefact_Cantor(GEN T, ulong p)
{
  GEN E, F, V = Flx_factor_squarefree(get_Flx_mod(T), p);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = Flx_simplefact_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor(FE_concat(F,E,j), (void*)&cmpGuGu, cmp_nodata);
}

static int
Flx_isirred_Cantor(GEN Tp, ulong p)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN T = get_Flx_mod(Tp);
  GEN dT = Flx_deriv(T, p);
  GEN XP, D;
  if (degpol(Flx_gcd(T, dT, p)) != 0) { avma = av; return 0; }
  n = get_Flx_degree(T);
  T = Flx_get_red(Tp, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf");
  d = degpol(gel(D, n));
  avma = av; return d==n;
}

static GEN
Flx_factcantor_i(GEN f, ulong pp, long flag)
{
  long d;
  if (pp==2) { /*We need to handle 2 specially */
    GEN F = F2x_factcantor_i(Flx_to_F2x(f),flag);
    if (flag==0) F2xV_to_FlxV_inplace(gel(F,1));
    return F;
  }
  d = degpol(f);
  if (d <= 2) return Flx_factor_deg2(f,pp,d,flag);
  switch(flag)
  {
    default: return Flx_factor_Cantor(f, pp);
    case 1: return Flx_simplefact_Cantor(f, pp);
    case 2: return Flx_isirred_Cantor(f, pp)? gen_1: NULL;
  }
}

GEN
Flx_factcantor(GEN f, ulong p, long flag)
{
  pari_sp av = avma;
  GEN z = Flx_factcantor_i(Flx_normalize(f,p),p,flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}

GEN
Flx_degfact(GEN f, ulong p)
{
  pari_sp av = avma;
  GEN z = Flx_factcantor_i(Flx_normalize(f,p),p,1);
  return gerepilecopy(av, z);
}

/* T must be squarefree mod p*/
GEN
Flx_nbfact_by_degree(GEN T, long *nb, ulong p)
{
  GEN XP, D;
  pari_timer ti;
  long i, s, n = get_Flx_degree(T);
  GEN V = const_vecsmall(n, 0);
  pari_sp av = avma;
  T = Flx_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf");
  for (i = 1, s = 0; i <= n; i++)
  {
    V[i] = degpol(gel(D,i))/i;
    s += V[i];
  }
  *nb = s;
  avma = av; return V;
}

long
Flx_nbfact_Frobenius(GEN T, GEN XP, ulong p)
{
  pari_sp av = avma;
  GEN ddf = Flx_ddf(T, XP, p);
  long l = lg(ddf), i, s=0;
  for(i = 1; i < l; i++)
    s += degpol(gel(ddf,i))/i;
  avma = av; return s;
}

/* T must be squarefree mod p*/
long
Flx_nbfact(GEN T, ulong p)
{
  pari_sp av = avma;
  GEN XP = Flx_Frobenius(T, p);
  long n = Flx_nbfact_Frobenius(T, XP, p);
  avma = av; return n;
}

int
Flx_is_irred(GEN f, ulong p) { return !!Flx_factcantor_i(f,p,2); }

/* factor f (FpX or Flx) mod pp.
 * flag = 1: return the degrees, not the factors
 * flag = 2: return NULL if f is not irreducible.
 * Not gerepile-safe */
static GEN
factcantor_i(GEN f, GEN pp, long flag)
{
  if (typ(f) == t_VECSMALL)
  { /* lgefint(pp) = 3 */
    GEN F;
    ulong p = pp[2];
    if (p==2) {
      F = F2x_factcantor_i(Flx_to_F2x(f),flag);
      if (flag==0) F2xV_to_ZXV_inplace(gel(F,1));
    } else {
      F = Flx_factcantor_i(f,p,flag);
      if (flag==0) FlxV_to_ZXV_inplace(gel(F,1));
    }
    return F;
  }
  return FpX_factcantor_i(f, pp, flag);
}
GEN
FpX_factcantor(GEN f, GEN pp, long flag)
{
  pari_sp av = avma;
  GEN z;
  ZX_factmod_init(&f,pp);
  z = factcantor_i(f,pp,flag);
  if (flag == 2) { avma = av; return z; }
  return gerepilecopy(av, z);
}

static GEN
factmod_aux(GEN f, GEN p, GEN (*Factor)(GEN,GEN,long), long flag)
{
  pari_sp av = avma;
  long j, lfact;
  GEN z, t, E, y, u, v;

  factmod_init(&f, p);
  switch(lg(f))
  {
    case 3: avma = av; return trivial_fact();
    case 2: return gerepileupto(av, zero_fact_intmod(f, p));
  }
  z = Factor(f,p,flag); t = gel(z,1); E = gel(z,2);
  lfact = lg(t); y = cgetg(3, t_MAT);
  gel(y,1) = u = cgetg(lfact,t_COL);
  gel(y,2) = v = cgetg(lfact,t_COL);
  if (flag)
    for (j=1; j<lfact; j++)
    {
      gel(u,j) = utoi(uel(t,j));
      gel(v,j) = utoi(uel(E,j));
    }
  else
    for (j=1; j<lfact; j++)
    {
      gel(u,j) = FpX_to_mod(gel(t,j), p);
      gel(v,j) = utoi(uel(E,j));
    }
  return gerepileupto(av, y);
}
GEN
factcantor0(GEN f, GEN p, long flag)
{ return factmod_aux(f, p, &factcantor_i, flag); }
GEN
factmod(GEN f, GEN p)
{ return factmod_aux(f, p, &FpX_Berlekamp_i, 0); }

/* Use this function when you think f is reducible, and that there are lots of
 * factors. If you believe f has few factors, use FpX_nbfact(f,p)==1 instead */
int
FpX_is_irred(GEN f, GEN p) {
  ZX_factmod_init(&f,p);
  return !!factcantor_i(f,p,2);
}
GEN
FpX_degfact(GEN f, GEN p) {
  pari_sp av = avma;
  GEN z;
  ZX_factmod_init(&f,p);
  z = factcantor_i(f,p,1);
  return gerepilecopy(av, z);
}
GEN
factcantor(GEN f, GEN p) { return factcantor0(f,p,0); }
GEN
simplefactmod(GEN f, GEN p) { return factcantor0(f,p,1); }

/* set x <-- x + c*y mod p */
/* x is not required to be normalized.*/
static void
Flx_addmul_inplace(GEN gx, GEN gy, ulong c, ulong p)
{
  long i, lx, ly;
  ulong *x=(ulong *)gx;
  ulong *y=(ulong *)gy;
  if (!c) return;
  lx = lg(gx);
  ly = lg(gy);
  if (lx<ly) pari_err_BUG("lx<ly in Flx_addmul_inplace");
  if (SMALL_ULONG(p))
    for (i=2; i<ly;  i++) x[i] = (x[i] + c*y[i]) % p;
  else
    for (i=2; i<ly;  i++) x[i] = Fl_add(x[i], Fl_mul(c,y[i],p),p);
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}
/* assume x1 != 0 */
static GEN
deg1_Flx(ulong x1, ulong x0, ulong sv)
{
  return mkvecsmall3(sv, x0, x1);
}

long
F2x_split_Berlekamp(GEN *t)
{
  GEN u = *t, a, b, vker;
  long lb, d, i, ir, L, la, sv = u[1], du = F2x_degree(u);

  if (du == 1) return 1;
  if (du == 2)
  {
    if (F2x_quad_factortype(u) == 1) /* 0 is a root: shouldn't occur */
    {
      t[0] = mkvecsmall2(sv, 2);
      t[1] = mkvecsmall2(sv, 3);
      return 2;
    }
    return 1;
  }

  vker = F2x_Berlekamp_ker(u);
  lb = lgcols(vker);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol;
    if (d == 2)
      pol = F2v_to_F2x(gel(vker,2), sv);
    else
    {
      GEN v = zero_zv(lb);
      v[1] = du;
      v[2] = random_Fl(2); /*Assume vker[1]=1*/
      for (i=2; i<=d; i++)
        if (random_Fl(2)) F2v_add_inplace(v, gel(vker,i));
      pol = F2v_to_F2x(v, sv);
    }
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = F2x_degree(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        if (F2x_quad_factortype(a) == 1) /* 0 is a root: shouldn't occur */
        {
          t[i] = mkvecsmall2(sv, 2);
          t[L] = mkvecsmall2(sv, 3); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        long lb;
        b = F2x_rem(pol, a);
        if (F2x_degree(b) <= 0) { avma=av; continue; }
        b = F2x_gcd(a,b); lb = F2x_degree(b);
        if (lb && lb < la)
        {
          t[L] = F2x_div(a,b);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

/* p != 2 */
long
Flx_split_Berlekamp(GEN *t, ulong p)
{
  GEN u = *t, a,b,vker;
  long d, i, ir, L, la, lb, sv = u[1];
  long l = lg(u);
  ulong po2;

  if (p == 2)
  {
    *t = Flx_to_F2x(*t);
    d = F2x_split_Berlekamp(t);
    for (i = 1; i <= d; i++) t[i] = F2x_to_Flx(t[i]);
    return d;
  }
  la = degpol(u);
  if (la == 1) return 1;
  if (la == 2)
  {
    ulong r = Flx_quad_root(u,p,1);
    if (r != p)
    {
      t[0] = deg1_Flx(1, p - r, sv); r = Flx_otherroot(u,r,p);
      t[1] = deg1_Flx(1, p - r, sv);
      return 2;
    }
    return 1;
  }

  vker = Flx_Berlekamp_ker(u,p);
  vker = Flm_to_FlxV(vker, sv);
  d = lg(vker)-1;
  po2 = p >> 1; /* (p-1) / 2 */
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol = zero_zv(l-2);
    pol[1] = sv;
    pol[2] = random_Fl(p); /*Assume vker[1]=1*/
    for (i=2; i<=d; i++)
      Flx_addmul_inplace(pol, gel(vker,i), random_Fl(p), p);
    (void)Flx_renormalize(pol,l-1);

    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        ulong r = Flx_quad_root(a,p,1);
        if (r != p)
        {
          t[i] = deg1_Flx(1, p - r, sv); r = Flx_otherroot(a,r,p);
          t[L] = deg1_Flx(1, p - r, sv); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        b = Flx_rem(pol, a, p);
        if (degpol(b) <= 0) { avma=av; continue; }
        b = Flx_Fl_add(Flxq_powu(b,po2, a,p), p-1, p);
        b = Flx_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = Flx_normalize(b, p);
          t[L] = Flx_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

long
FpX_split_Berlekamp(GEN *t, GEN p)
{
  GEN u = *t, a,b,po2,vker;
  long d, i, ir, L, la, lb, vu = varn(u);
  if (lgefint(p) == 3)
  {
    ulong up = p[2];
    if (up == 2)
    {
      *t = ZX_to_F2x(*t);
      d = F2x_split_Berlekamp(t);
      for (i = 0; i < d; i++) t[i] = F2x_to_ZX(t[i]);
    }
    else
    {
      *t = ZX_to_Flx(*t, up);
      d = Flx_split_Berlekamp(t, up);
      for (i = 0; i < d; i++) t[i] = Flx_to_ZX(t[i]);
    }
    return d;
  }
  la = degpol(u);
  if (la == 1) return 1;
  if (la == 2)
  {
    GEN r = FpX_quad_root(u,p,1);
    if (r)
    {
      t[0] = deg1pol_shallow(gen_1, subii(p,r), vu); r = FpX_otherroot(u,r,p);
      t[1] = deg1pol_shallow(gen_1, subii(p,r), vu);
      return 2;
    }
    return 1;
  }
  vker = FpX_Berlekamp_ker(u,p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  po2 = shifti(p, -1); /* (p-1) / 2 */
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol = scalar_ZX_shallow(randomi(p), vu);
    for (i=2; i<=d; i++)
      pol = ZX_add(pol, ZX_Z_mul(gel(vker,i), randomi(p)));
    pol = FpX_red(pol,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        GEN r = FpX_quad_root(a,p,1);
        if (r)
        {
          t[i] = deg1pol_shallow(gen_1, subii(p,r), vu); r = FpX_otherroot(a,r,p);
          t[L] = deg1pol_shallow(gen_1, subii(p,r), vu); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        b = FpX_rem(pol, a, p);
        if (degpol(b) <= 0) { avma=av; continue; }
        b = FpX_Fp_sub_shallow(FpXQ_pow(b,po2, a,p), gen_1, p);
        b = FpX_gcd(a,b, p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpX_normalize(b, p);
          t[L] = FpX_div(a,b,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

static GEN
F2x_Berlekamp_i(GEN f, long flag)
{
  long lfact, val, d = F2x_degree(f), j, k, lV;
  GEN y, E, t, V;

  if (d <= 2) return F2x_factor_deg2(f, d, flag);

  val = F2x_valrem(f, &f);
  if (flag == 2 && val > 1) return NULL;
  V = F2x_factor_squarefree(f); lV = lg(V);
  if (flag == 2 && lV > 2) return NULL;

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  lfact = 1;
  if (val) {
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = polx_F2x(f[1]);
    E[1] = val; lfact++;
  }

  for (k=1; k<lV; k++)
  {
    if (F2x_degree(gel(V, k))==0) continue;
    gel(t,lfact) = gel(V, k);
    d = F2x_split_Berlekamp(&gel(t,lfact));
    if (flag == 2 && d != 1) return NULL;
    if (flag == 1)
      for (j=0; j<d; j++) t[lfact+j] = F2x_degree(gel(t,lfact+j));
    for (j=0; j<d; j++) E[lfact+j] = k;
    lfact += d;
  }
  if (flag == 2) return gen_1; /* irreducible */
  y = FE_setlg(t,E, lfact);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}

static GEN
Flx_Berlekamp_i(GEN f, ulong p, long flag)
{
  long lfact, val, d = degpol(f), j, k, lV;
  GEN y, E, t, V;

  if (p == 2)
  {
    GEN F = F2x_Berlekamp_i(Flx_to_F2x(f),flag);
    if (flag==0) F2xV_to_FlxV_inplace(gel(F,1));
    return F;
  }
  if (d <= 2) return Flx_factor_deg2(f,p,d,flag);
  val = Flx_valrem(f, &f);
  if (flag == 2 && val > 1) return NULL;
  V = Flx_factor_squarefree(f, p); lV = lg(V);
  if (flag == 2 && lV > 2) return NULL;

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  lfact = 1;
  if (val) {
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = polx_Flx(f[1]);
    E[1] = val; lfact++;
  }

  for (k=1; k<lV; k++)
  {
    if (degpol(gel(V, k))==0) continue;
    gel(t,lfact) = Flx_normalize(gel(V, k), p);
    d = Flx_split_Berlekamp(&gel(t,lfact), p);
    if (flag == 2 && d != 1) return NULL;
    if (flag == 1)
      for (j=0; j<d; j++) t[lfact+j] = degpol(gel(t,lfact+j));
    for (j=0; j<d; j++) E[lfact+j] = k;
    lfact += d;
  }
  if (flag == 2) return gen_1; /* irreducible */
  y = FE_setlg(t,E,lfact);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}

/* f an FpX or an Flx */
static GEN
FpX_Berlekamp_i(GEN f, GEN p, long flag)
{
  long lfact, val, d = degpol(f), j, k, lV;
  GEN y, E, t ,V;

  if (typ(f) == t_VECSMALL)
  {/* lgefint(p) == 3 */
    ulong pp = p[2];
    GEN F;
    if (pp == 2) {
      F = F2x_Berlekamp_i(Flx_to_F2x(f), flag);
      if (flag==0) F2xV_to_ZXV_inplace(gel(F,1));
    } else {
      F = Flx_Berlekamp_i(f, pp, flag);
      if (flag==0) FlxV_to_ZXV_inplace(gel(F,1));
    }
    return F;
  }
  /* p is large (and odd) */
  if (d <= 2) return FpX_factor_deg2(f, p, d, flag);
  val = ZX_valrem(f, &f);
  if (flag == 2 && val > 1) return NULL;
  V = FpX_factor_Yun(f, p); lV = lg(V);
  if (flag == 2 && lg(V) > 2) return NULL;

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  lfact = 1;
  if (val) {
    if (flag == 1)
      t[1] = 1;
    else
      gel(t,1) = pol_x(varn(f));
    E[1] = val; lfact++;
  }

  for (k=1; k<lV; k++)
  {
    if (degpol(gel(V,k))==0) continue;
    gel(t,lfact) = FpX_normalize(gel(V, k), p);
    d = FpX_split_Berlekamp(&gel(t,lfact), p);
    if (flag == 2 && d != 1) return NULL;
    if (flag == 1)
      for (j=0; j<d; j++) t[lfact+j] = degpol(gel(t,lfact+j));
    for (j=0; j<d; j++) E[lfact+j] = k;
    lfact += d;
  }
  if (flag == 2) return gen_1; /* irreducible */
  y = FE_setlg(t,E, lfact);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpii);
}
GEN
FpX_factor(GEN f, GEN p)
{
  pari_sp av = avma;
  ZX_factmod_init(&f, p);
  return gerepilecopy(av, FpX_Berlekamp_i(f, p, 0));
}
GEN
Flx_factor(GEN f, ulong p)
{
  pari_sp av = avma;
  GEN F = (degpol(f)>log2(p))? Flx_factcantor_i(f,p,0): Flx_Berlekamp_i(f,p,0);
  return gerepilecopy(av, F);
}
GEN
F2x_factor(GEN f)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2x_Berlekamp_i(f, 0));
}

GEN
factormod0(GEN f, GEN p, long flag)
{
  switch(flag)
  {
    case 0: return factmod(f,p);
    case 1: return simplefactmod(f,p);
    default: pari_err_FLAG("factormod");
  }
  return NULL; /* not reached */
}
