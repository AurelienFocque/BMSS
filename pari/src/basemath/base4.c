/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                                                                 */
/*                       BASIC NF OPERATIONS                       */
/*                           (continued)                           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                     IDEAL OPERATIONS                            */
/*                                                                 */
/*******************************************************************/

/* A valid ideal is either principal (valid nf_element), or prime, or a matrix
 * on the integer basis in HNF.
 * A prime ideal is of the form [p,a,e,f,b], where the ideal is p.Z_K+a.Z_K,
 * p is a rational prime, a belongs to Z_K, e=e(P/p), f=f(P/p), and b
 * is Lenstra's constant, such that p.P^(-1)= p Z_K + b Z_K.
 *
 * An extended ideal is a couple [I,F] where I is a valid ideal and F is
 * either an algebraic number, or a factorization matrix attached to an
 * algebraic number. All routines work with either extended ideals or ideals
 * (an omitted F is assumed to be [;] <-> 1).
 * All ideals are output in HNF form. */

/* types and conversions */

long
idealtyp(GEN *ideal, GEN *arch)
{
  GEN x = *ideal;
  long t,lx,tx = typ(x);

  if (tx==t_VEC && lg(x)==3)
  { *arch = gel(x,2); x = gel(x,1); tx = typ(x); }
  else
    *arch = NULL;
  switch(tx)
  {
    case t_MAT: lx = lg(x);
      if (lx == 1) { t = id_PRINCIPAL; x = gen_0; break; }
      if (lx != lgcols(x)) pari_err_TYPE("idealtyp [non-square t_MAT]",x);
      t = id_MAT;
      break;

    case t_VEC: if (lg(x)!=6) pari_err_TYPE("idealtyp",x);
      t = id_PRIME; break;

    case t_POL: case t_POLMOD: case t_COL:
    case t_INT: case t_FRAC:
      t = id_PRINCIPAL; break;
    default:
      pari_err_TYPE("idealtyp",x);
      return 0; /*not reached*/
  }
  *ideal = x; return t;
}

/* nf a true nf; v = [a,x,...], a in Z. Return (a,x) */
GEN
idealhnf_two(GEN nf, GEN v)
{
  GEN p = gel(v,1), pi = gel(v,2), m = zk_scalar_or_multable(nf, pi);
  if (typ(m) == t_INT) return scalarmat(gcdii(m,p), nf_get_degree(nf));
  return ZM_hnfmodid(m, p);
}

static GEN
ZM_Q_mul(GEN x, GEN y)
{ return typ(y) == t_INT? ZM_Z_mul(x,y): RgM_Rg_mul(x,y); }


GEN
idealhnf_principal(GEN nf, GEN x)
{
  GEN cx;
  x = nf_to_scalar_or_basis(nf, x);
  switch(typ(x))
  {
    case t_COL: break;
    case t_INT:  if (!signe(x)) return cgetg(1,t_MAT);
      return scalarmat(absi(x), nf_get_degree(nf));
    case t_FRAC:
      return scalarmat(Q_abs_shallow(x), nf_get_degree(nf));
    default: pari_err_TYPE("idealhnf",x);
  }
  x = Q_primitive_part(x, &cx);
  RgV_check_ZV(x, "idealhnf");
  x = zk_multable(nf, x);
  x = ZM_hnfmodid(x, zkmultable_capZ(x));
  return cx? ZM_Q_mul(x,cx): x;
}

/* x integral ideal in t_MAT form, nx columns */
static GEN
vec_mulid(GEN nf, GEN x, long nx, long N)
{
  GEN m = cgetg(nx*N + 1, t_MAT);
  long i, j, k;
  for (i=k=1; i<=nx; i++)
    for (j=1; j<=N; j++) gel(m, k++) = zk_ei_mul(nf, gel(x,i),j);
  return m;
}
GEN
idealhnf_shallow(GEN nf, GEN x)
{
  long tx = typ(x), lx = lg(x), N;

  /* cannot use idealtyp because here we allow non-square matrices */
  if (tx == t_VEC && lx == 3) { x = gel(x,1); tx = typ(x); lx = lg(x); }
  if (tx == t_VEC && lx == 6) return idealhnf_two(nf,x); /* PRIME */
  switch(tx)
  {
    case t_MAT:
    {
      GEN cx;
      long nx = lx-1;
      N = nf_get_degree(nf);
      if (nx == 0) return cgetg(1, t_MAT);
      if (nbrows(x) != N) pari_err_TYPE("idealhnf [wrong dimension]",x);
      if (nx == 1) return idealhnf_principal(nf, gel(x,1));

      if (nx == N && RgM_is_ZM(x) && ZM_ishnf(x)) return x;
      x = Q_primitive_part(x, &cx);
      if (nx < N) x = vec_mulid(nf, x, nx, N);
      x = ZM_hnfmod(x, ZM_detmult(x));
      return cx? ZM_Q_mul(x,cx): x;
    }
    case t_QFI:
    case t_QFR:
    {
      pari_sp av = avma;
      GEN u, D = nf_get_disc(nf), T = nf_get_pol(nf), f = nf_get_index(nf);
      GEN A = gel(x,1), B = gel(x,2);
      N = nf_get_degree(nf);
      if (N != 2)
        pari_err_TYPE("idealhnf [Qfb for non-quadratic fields]", x);
      if (!equalii(qfb_disc(x), D))
        pari_err_DOMAIN("idealhnf [Qfb]", "disc(q)", "!=", D, x);
      /* x -> A Z + (-B + sqrt(D)) / 2 Z
         K = Q[t]/T(t), t^2 + ut + v = 0,  u^2 - 4v = Df^2
         => t = (-u + sqrt(D) f)/2
         => sqrt(D)/2 = (t + u/2)/f */
      u = gel(T,3);
      B = deg1pol_shallow(ginv(f),
                          gsub(gdiv(u, shifti(f,1)), gdiv(B,gen_2)),
                          varn(T));
      return gerepileupto(av, idealhnf_two(nf, mkvec2(A,B)));
    }
    default: return idealhnf_principal(nf, x); /* PRINCIPAL */
  }
}
GEN
idealhnf(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN y = idealhnf_shallow(checknf(nf), x);
  return (avma == av)? gcopy(y): gerepileupto(av, y);
}

/* GP functions */

GEN
idealtwoelt0(GEN nf, GEN x, GEN a)
{
  if (!a) return idealtwoelt(nf,x);
  return idealtwoelt2(nf,x,a);
}

GEN
idealpow0(GEN nf, GEN x, GEN n, long flag)
{
  if (flag) return idealpowred(nf,x,n);
  return idealpow(nf,x,n);
}

GEN
idealmul0(GEN nf, GEN x, GEN y, long flag)
{
  if (flag) return idealmulred(nf,x,y);
  return idealmul(nf,x,y);
}

GEN
idealdiv0(GEN nf, GEN x, GEN y, long flag)
{
  switch(flag)
  {
    case 0: return idealdiv(nf,x,y);
    case 1: return idealdivexact(nf,x,y);
    default: pari_err_FLAG("idealdiv");
  }
  return NULL; /* not reached */
}

GEN
idealaddtoone0(GEN nf, GEN arg1, GEN arg2)
{
  if (!arg2) return idealaddmultoone(nf,arg1);
  return idealaddtoone(nf,arg1,arg2);
}

/* b not a scalar */
static GEN
hnf_Z_ZC(GEN nf, GEN a, GEN b) { return hnfmodid(zk_multable(nf,b), a); }
/* b not a scalar */
static GEN
hnf_Z_QC(GEN nf, GEN a, GEN b)
{
  GEN db;
  b = Q_remove_denom(b, &db);
  if (db) a = mulii(a, db);
  b = hnf_Z_ZC(nf,a,b);
  return db? RgM_Rg_div(b, db): b;
}
/* b not a scalar (not point in trying to optimize for this case) */
static GEN
hnf_Q_QC(GEN nf, GEN a, GEN b)
{
  GEN da, db;
  if (typ(a) == t_INT) return hnf_Z_QC(nf, a, b);
  da = gel(a,2);
  a = gel(a,1);
  b = Q_remove_denom(b, &db);
  /* write da = d*A, db = d*B, gcd(A,B) = 1
   * gcd(a/(d A), b/(d B)) = gcd(a B, A b) / A B d = gcd(a B, b) / A B d */
  if (db)
  {
    GEN d = gcdii(da,db);
    if (!is_pm1(d)) db = diviiexact(db,d); /* B */
    if (!is_pm1(db))
    {
      a = mulii(a, db); /* a B */
      da = mulii(da, db); /* A B d = lcm(denom(a),denom(b)) */
    }
  }
  return RgM_Rg_div(hnf_Z_ZC(nf,a,b), da);
}
static GEN
hnf_QC_QC(GEN nf, GEN a, GEN b)
{
  GEN da, db, d, x;
  a = Q_remove_denom(a, &da);
  b = Q_remove_denom(b, &db);
  if (da) b = ZC_Z_mul(b, da);
  if (db) a = ZC_Z_mul(a, db);
  d = mul_denom(da, db);
  a = zk_multable(nf,a); da = zkmultable_capZ(a);
  b = zk_multable(nf,b); db = zkmultable_capZ(b);
  x = ZM_hnfmodid(shallowconcat(a,b), gcdii(da,db));
  return d? RgM_Rg_div(x, d): x;
}
static GEN
hnf_Q_Q(GEN nf, GEN a, GEN b) {return scalarmat(Q_gcd(a,b), nf_get_degree(nf));}
GEN
idealhnf0(GEN nf, GEN a, GEN b)
{
  long ta, tb;
  pari_sp av;
  GEN x;
  if (!b) return idealhnf(nf,a);

  /* HNF of aZ_K+bZ_K */
  av = avma; nf = checknf(nf);
  a = nf_to_scalar_or_basis(nf,a); ta = typ(a);
  b = nf_to_scalar_or_basis(nf,b); tb = typ(b);
  if (ta == t_COL)
    x = (tb==t_COL)? hnf_QC_QC(nf, a,b): hnf_Q_QC(nf, b,a);
  else
    x = (tb==t_COL)? hnf_Q_QC(nf, a,b): hnf_Q_Q(nf, a,b);
  return gerepileupto(av, x);
}

/*******************************************************************/
/*                                                                 */
/*                       TWO-ELEMENT FORM                          */
/*                                                                 */
/*******************************************************************/
static GEN idealapprfact_i(GEN nf, GEN x, int nored);

static int
ok_elt(GEN x, GEN xZ, GEN y)
{
  pari_sp av = avma;
  int r = ZM_equal(x, ZM_hnfmodid(y, xZ));
  avma = av; return r;
}

static GEN
addmul_col(GEN a, long s, GEN b)
{
  long i,l;
  if (!s) return a? leafcopy(a): a;
  if (!a) return gmulsg(s,b);
  l = lg(a);
  for (i=1; i<l; i++)
    if (signe(gel(b,i))) gel(a,i) = addii(gel(a,i), mulsi(s, gel(b,i)));
  return a;
}

/* a <-- a + s * b, all coeffs integers */
static GEN
addmul_mat(GEN a, long s, GEN b)
{
  long j,l;
  /* copy otherwise next call corrupts a */
  if (!s) return a? RgM_shallowcopy(a): a;
  if (!a) return gmulsg(s,b);
  l = lg(a);
  for (j=1; j<l; j++)
    (void)addmul_col(gel(a,j), s, gel(b,j));
  return a;
}

static GEN
get_random_a(GEN nf, GEN x, GEN xZ)
{
  pari_sp av1;
  long i, lm, l = lg(x);
  GEN a, z, beta, mul;

  beta= cgetg(l, t_VEC);
  mul = cgetg(l, t_VEC); lm = 1; /* = lg(mul) */
  /* look for a in x such that a O/xZ = x O/xZ */
  for (i = 2; i < l; i++)
  {
    GEN t, y, xi = gel(x,i);
    av1 = avma;
    y = zk_scalar_or_multable(nf, xi); /* ZM, cannot be a scalar */
    t = FpM_red(y, xZ);
    if (gequal0(t)) { avma = av1; continue; }
    if (ok_elt(x,xZ, t)) return xi;
    gel(beta,lm) = xi;
    /* mul[i] = { canonical generators for x[i] O/xZ as Z-module } */
    gel(mul,lm) = t; lm++;
  }
  setlg(mul, lm);
  setlg(beta,lm);
  z = cgetg(lm, t_VECSMALL);
  for(av1=avma;;avma=av1)
  {
    for (a=NULL,i=1; i<lm; i++)
    {
      long t = random_bits(4) - 7; /* in [-7,8] */
      z[i] = t;
      a = addmul_mat(a, t, gel(mul,i));
    }
    /* a = matrix (NOT HNF) of ideal generated by beta.z in O/xZ */
    if (a && ok_elt(x,xZ, a)) break;
  }
  for (a=NULL,i=1; i<lm; i++)
    a = addmul_col(a, z[i], gel(beta,i));
  return a;
}

/* if x square matrix, assume it is HNF */
static GEN
mat_ideal_two_elt(GEN nf, GEN x)
{
  GEN y, a, cx, xZ;
  long N = nf_get_degree(nf);
  pari_sp av, tetpil;

  if (N == 2) return mkvec2copy(gcoeff(x,1,1), gel(x,2));

  y = cgetg(3,t_VEC); av = avma;
  cx = Q_content(x);
  xZ = gcoeff(x,1,1);
  if (gequal(xZ, cx)) /* x = (cx) */
  {
    gel(y,1) = cx;
    gel(y,2) = gen_0; return y;
  }
  if (equali1(cx)) cx = NULL;
  else
  {
    x = Q_div_to_int(x, cx);
    xZ = gcoeff(x,1,1);
  }
  if (N < 6)
    a = get_random_a(nf, x, xZ);
  else
  {
    const long FB[] = { _evallg(15+1) | evaltyp(t_VECSMALL),
      2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47
    };
    GEN P, E, a1 = Z_smoothen(xZ, (GEN)FB, &P, &E);
    if (!a1) /* factors completely */
      a = idealapprfact_i(nf, idealfactor(nf,x), 1);
    else if (lg(P) == 1) /* no small factors */
      a = get_random_a(nf, x, xZ);
    else /* general case */
    {
      GEN A0, A1, a0, u0, u1, v0, v1, pi0, pi1, t, u;
      a0 = diviiexact(xZ, a1);
      A0 = ZM_hnfmodid(x, a0); /* smooth part of x */
      A1 = ZM_hnfmodid(x, a1); /* cofactor */
      pi0 = idealapprfact_i(nf, idealfactor(nf,A0), 1);
      pi1 = get_random_a(nf, A1, a1);
      (void)bezout(a0, a1, &v0,&v1);
      u0 = mulii(a0, v0);
      u1 = mulii(a1, v1);
      if (typ(pi0) != t_COL) t = addmulii(u0, pi0, u1);
      else
      { t = ZC_Z_mul(pi0, u1); gel(t,1) = addii(gel(t,1), u0); }
      u = ZC_Z_mul(pi1, u0); gel(u,1) = addii(gel(u,1), u1);
      a = nfmuli(nf, centermod(u, xZ), centermod(t, xZ));
    }
  }
  if (cx)
  {
    a = centermod(a, xZ);
    tetpil = avma;
    if (typ(cx) == t_INT)
    {
      gel(y,1) = mulii(xZ, cx);
      gel(y,2) = ZC_Z_mul(a, cx);
    }
    else
    {
      gel(y,1) = gmul(xZ, cx);
      gel(y,2) = RgC_Rg_mul(a, cx);
    }
  }
  else
  {
    tetpil = avma;
    gel(y,1) = icopy(xZ);
    gel(y,2) = centermod(a, xZ);
  }
  gerepilecoeffssp(av,tetpil,y+1,2); return y;
}

/* Given an ideal x, returns [a,alpha] such that a is in Q,
 * x = a Z_K + alpha Z_K, alpha in K^*
 * a = 0 or alpha = 0 are possible, but do not try to determine whether
 * x is principal. */
GEN
idealtwoelt(GEN nf, GEN x)
{
  pari_sp av;
  GEN z;
  long tx = idealtyp(&x,&z);
  nf = checknf(nf);
  if (tx == id_MAT) return mat_ideal_two_elt(nf,x);
  if (tx == id_PRIME) return mkvec2copy(gel(x,1), gel(x,2));
  /* id_PRINCIPAL */
  av = avma; x = nf_to_scalar_or_basis(nf, x);
  return gerepilecopy(av, typ(x)==t_COL? mkvec2(gen_0,x):
                                         mkvec2(Q_abs_shallow(x),gen_0));
}

/*******************************************************************/
/*                                                                 */
/*                         FACTORIZATION                           */
/*                                                                 */
/*******************************************************************/
/* x integral ideal in HNF, return v_p(Nx), *vz = v_p(x \cap Z)
 * Use x[1,1] = x \cap Z */
long
val_norm(GEN x, GEN p, long *vz)
{
  long i,l = lg(x), v;
  *vz = v = Z_pval(gcoeff(x,1,1), p);
  if (!v) return 0;
  for (i=2; i<l; i++) v += Z_pval(gcoeff(x,i,i), p);
  return v;
}

/* return factorization of Nx, x integral in HNF */
GEN
factor_norm(GEN x)
{
  GEN r = gcoeff(x,1,1), f, p, e;
  long i, k, l;
  if (typ(r)!=t_INT) pari_err_TYPE("idealfactor",r);
  f = Z_factor(r); p = gel(f,1); e = gel(f,2); l = lg(p);
  for (i=1; i<l; i++) e[i] = val_norm(x,gel(p,i), &k);
  settyp(e, t_VECSMALL); return f;
}

/* X integral ideal */
static GEN
idealfactor_HNF(GEN nf, GEN x)
{
  const long N = lg(x)-1;
  long i, j, k, lf, lc, v, vc;
  GEN f, f1, f2, c1, c2, y1, y2, p1, cx, P;

  x = Q_primitive_part(x, &cx);
  if (!cx)
  {
    c1 = c2 = NULL; /* gcc -Wall */
    lc = 1;
  }
  else
  {
    f = Z_factor(cx);
    c1 = gel(f,1);
    c2 = gel(f,2); lc = lg(c1);
  }
  f = factor_norm(x);
  f1 = gel(f,1);
  f2 = gel(f,2); lf = lg(f1);
  y1 = cgetg((lf+lc-2)*N+1, t_COL);
  y2 = cgetg((lf+lc-2)*N+1, t_VECSMALL);
  k = 1;
  for (i=1; i<lf; i++)
  {
    long l = f2[i]; /* = v_p(Nx) */
    p1 = idealprimedec(nf,gel(f1,i));
    vc = cx? Z_pval(cx,gel(f1,i)): 0;
    for (j=1; j<lg(p1); j++)
    {
      P = gel(p1,j);
      v = idealval(nf,x,P);
      l -= v*pr_get_f(P);
      v += vc * pr_get_e(P); if (!v) continue;
      gel(y1,k) = P;
      y2[k] = v; k++;
      if (l == 0) break; /* now only the content contributes */
    }
    if (vc == 0) continue;
    for (j++; j<lg(p1); j++)
    {
      P = gel(p1,j);
      gel(y1,k) = P;
      y2[k++] = vc * pr_get_e(P);
    }
  }
  for (i=1; i<lc; i++)
  {
    /* p | Nx already treated */
    if (dvdii(gcoeff(x,1,1),gel(c1,i))) continue;
    p1 = idealprimedec(nf,gel(c1,i));
    vc = itos(gel(c2,i));
    for (j=1; j<lg(p1); j++)
    {
      P = gel(p1,j);
      gel(y1,k) = P;
      y2[k++] = vc * pr_get_e(P);
    }
  }
  setlg(y1, k);
  setlg(y2, k);
  return mkmat2(y1, zc_to_ZC(y2));
}

GEN
idealfactor(GEN nf, GEN x)
{
  pari_sp av = avma;
  long tx;
  GEN fa, f, y;

  nf = checknf(nf);
  tx = idealtyp(&x,&y);
  if (tx == id_PRIME)
  {
    y = cgetg(3,t_MAT);
    gel(y,1) = mkcolcopy(x);
    gel(y,2) = mkcol(gen_1); return y;
  }
  if (tx == id_PRINCIPAL)
  {
    y = nf_to_scalar_or_basis(nf, x);
    if (typ(y) != t_COL)
    {
      GEN c1, c2;
      long lfa, i,j;
      if (isintzero(y)) pari_err_DOMAIN("idealfactor", "ideal", "=",gen_0,x);
      f = factor(Q_abs_shallow(y));
      c1 = gel(f,1); lfa = lg(c1);
      if (lfa == 1) { avma = av; return trivial_fact(); }
      c2 = gel(f,2);
      settyp(c1, t_VEC); /* for shallowconcat */
      settyp(c2, t_VEC); /* for shallowconcat */
      for (i = 1; i < lfa; i++)
      {
        GEN P = idealprimedec(nf, gel(c1,i)), E = gel(c2,i), z;
        long lP = lg(P);
        z = cgetg(lP, t_COL);
        for (j = 1; j < lP; j++) gel(z,j) = mului(pr_get_e(gel(P,j)), E);
        gel(c1,i) = P;
        gel(c2,i) = z;
      }
      c1 = shallowconcat1(c1); settyp(c1, t_COL);
      c2 = shallowconcat1(c2);
      gel(f,1) = c1;
      gel(f,2) = c2; return gerepilecopy(av, f);
    }
  }
  y = idealnumden(nf, x);
  if (isintzero(gel(y,1))) pari_err_DOMAIN("idealfactor", "ideal", "=",gen_0,x);
  fa = idealfactor_HNF(nf, gel(y,1));
  if (!isint1(gel(y,2)))
  {
    GEN fa2 = idealfactor_HNF(nf, gel(y,2));
    fa2 = famat_inv_shallow(fa2);
    fa = famat_mul_shallow(fa, fa2);
  }
  fa = gerepilecopy(av, fa);
  return sort_factor(fa, (void*)&cmp_prime_ideal, &cmp_nodata);
}

/* P prime ideal in idealprimedec format. Return valuation(ix) at P */
long
idealval(GEN nf, GEN ix, GEN P)
{
  pari_sp av = avma, av1;
  long N, vmax, vd, v, e, f, i, j, k, tx = typ(ix);
  GEN mul, B, a, x, y, r, p, pk, cx, vals;

  if (is_extscalar_t(tx) || tx==t_COL) return nfval(nf,ix,P);
  tx = idealtyp(&ix,&a);
  if (tx == id_PRINCIPAL) return nfval(nf,ix,P);
  checkprid(P);
  if (tx == id_PRIME) return pr_equal(nf, P, ix)? 1: 0;
  /* id_MAT */
  nf = checknf(nf);
  N = nf_get_degree(nf);
  ix = Q_primitive_part(ix, &cx);
  p = pr_get_p(P);
  f = pr_get_f(P);
  if (f == N) { v = cx? Q_pval(cx,p): 0; avma = av; return v; }
  i = val_norm(ix,p, &k);
  if (!i) { v = cx? pr_get_e(P) * Q_pval(cx,p): 0; avma = av; return v; }

  e = pr_get_e(P);
  vd = cx? e * Q_pval(cx,p): 0;
  /* 0 <= ceil[v_P(ix) / e] <= v_p(ix \cap Z) --> v_P <= e * v_p */
  j = k * e;
  /* 0 <= v_P(ix) <= floor[v_p(Nix) / f] */
  i = i / f;
  vmax = minss(i,j); /* v_P(ix) <= vmax */

  mul = pr_get_tau(P);
  /* occurs when reading from file a prid in old format */
  if (typ(mul) != t_MAT) mul = zk_scalar_or_multable(nf,mul);
  B = cgetg(N+1,t_MAT);
  pk = powiu(p, (ulong)ceil((double)vmax / e));
  /* B[1] not needed: v_pr(ix[1]) = v_pr(ix \cap Z) is known already */
  gel(B,1) = gen_0; /* dummy */
  for (j=2; j<=N; j++)
  {
    x = gel(ix,j);
    y = cgetg(N+1, t_COL); gel(B,j) = y;
    for (i=1; i<=N; i++)
    { /* compute a = (x.t0)_i, ix in HNF ==> x[j+1..N] = 0 */
      a = mulii(gel(x,1), gcoeff(mul,i,1));
      for (k=2; k<=j; k++) a = addii(a, mulii(gel(x,k), gcoeff(mul,i,k)));
      /* p | a ? */
      gel(y,i) = dvmdii(a,p,&r);
      if (signe(r)) { avma = av; return vd; }
    }
  }
  vals = cgetg(N+1, t_VECSMALL);
  /* vals[1] not needed */
  for (j = 2; j <= N; j++)
  {
    gel(B,j) = Q_primitive_part(gel(B,j), &cx);
    vals[j] = cx? 1 + e * Q_pval(cx, p): 1;
  }
  av1 = avma;
  y = cgetg(N+1,t_COL);
  /* can compute mod p^ceil((vmax-v)/e) */
  for (v = 1; v < vmax; v++)
  { /* we know v_pr(Bj) >= v for all j */
    if (e == 1 || (vmax - v) % e == 0) pk = diviiexact(pk, p);
    for (j = 2; j <= N; j++)
    {
      x = gel(B,j); if (v < vals[j]) continue;
      for (i=1; i<=N; i++)
      {
        pari_sp av2 = avma;
        a = mulii(gel(x,1), gcoeff(mul,i,1));
        for (k=2; k<=N; k++) a = addii(a, mulii(gel(x,k), gcoeff(mul,i,k)));
        /* a = (x.t_0)_i; p | a ? */
        a = dvmdii(a,p,&r);
        if (signe(r)) { avma = av; return v + vd; }
        if (lgefint(a) > lgefint(pk)) a = remii(a, pk);
        gel(y,i) = gerepileuptoint(av2, a);
      }
      gel(B,j) = y; y = x;
      if (gc_needed(av1,3))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"idealval");
        gerepileall(av1,3, &y,&B,&pk);
      }
    }
  }
  avma = av; return v + vd;
}
GEN
gpidealval(GEN nf, GEN ix, GEN P)
{
  long v = idealval(nf,ix,P);
  return v == LONG_MAX? mkoo(): stoi(v);
}

/* gcd and generalized Bezout */

GEN
idealadd(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  long tx, ty;
  GEN z, a, dx, dy, dz;

  tx = idealtyp(&x,&z);
  ty = idealtyp(&y,&z); nf = checknf(nf);
  if (tx != id_MAT) x = idealhnf_shallow(nf,x);
  if (ty != id_MAT) y = idealhnf_shallow(nf,y);
  if (lg(x) == 1) return gerepilecopy(av,y);
  if (lg(y) == 1) return gerepilecopy(av,x); /* check for 0 ideal */
  dx = Q_denom(x);
  dy = Q_denom(y); dz = lcmii(dx,dy);
  if (is_pm1(dz)) dz = NULL; else {
    x = Q_muli_to_int(x, dz);
    y = Q_muli_to_int(y, dz);
  }
  a = gcdii(gcoeff(x,1,1), gcoeff(y,1,1));
  if (is_pm1(a))
  {
    long N = lg(x)-1;
    if (!dz) { avma = av; return matid(N); }
    return gerepileupto(av, scalarmat(ginv(dz), N));
  }
  z = ZM_hnfmodid(shallowconcat(x,y), a);
  if (dz) z = RgM_Rg_div(z,dz);
  return gerepileupto(av,z);
}

static GEN
trivial_merge(GEN x)
{ return (lg(x) == 1 || !is_pm1(gcoeff(x,1,1)))? NULL: gen_1; }
GEN
idealaddtoone_i(GEN nf, GEN x, GEN y)
{
  GEN a;
  long tx = idealtyp(&x, &a/*junk*/);
  long ty = idealtyp(&y, &a/*junk*/);
  if (tx != id_MAT) x = idealhnf_shallow(nf, x);
  if (ty != id_MAT) y = idealhnf_shallow(nf, y);
  if (lg(x) == 1)
    a = trivial_merge(y);
  else if (lg(y) == 1)
    a = trivial_merge(x);
  else {
    a = hnfmerge_get_1(x, y);
    if (a && typ(a) == t_COL) a = ZC_reducemodlll(a, idealmul_HNF(nf,x,y));
  }
  if (!a) pari_err_COPRIME("idealaddtoone",x,y);
  return a;
}

GEN
idealaddtoone(GEN nf, GEN x, GEN y)
{
  GEN z = cgetg(3,t_VEC), a;
  pari_sp av = avma;
  nf = checknf(nf);
  a = gerepileupto(av, idealaddtoone_i(nf,x,y));
  gel(z,1) = a;
  gel(z,2) = typ(a) == t_COL? Z_ZC_sub(gen_1,a): subui(1,a);
  return z;
}

/* assume elements of list are integral ideals */
GEN
idealaddmultoone(GEN nf, GEN list)
{
  pari_sp av = avma;
  long N, i, l, nz, tx = typ(list);
  GEN H, U, perm, L;

  nf = checknf(nf); N = nf_get_degree(nf);
  if (!is_vec_t(tx)) pari_err_TYPE("idealaddmultoone",list);
  l = lg(list);
  L = cgetg(l, t_VEC);
  if (l == 1)
    pari_err_DOMAIN("idealaddmultoone", "sum(ideals)", "!=", gen_1, L);
  nz = 0; /* number of non-zero ideals in L */
  for (i=1; i<l; i++)
  {
    GEN I = gel(list,i);
    if (typ(I) != t_MAT) I = idealhnf_shallow(nf,I);
    if (lg(I) != 1)
    {
      nz++; RgM_check_ZM(I,"idealaddmultoone");
      if (lgcols(I) != N+1) pari_err_TYPE("idealaddmultoone [not an ideal]", I);
    }
    gel(L,i) = I;
  }
  H = ZM_hnfperm(shallowconcat1(L), &U, &perm);
  if (lg(H) == 1 || !equali1(gcoeff(H,1,1)))
    pari_err_DOMAIN("idealaddmultoone", "sum(ideals)", "!=", gen_1, L);
  for (i=1; i<=N; i++)
    if (perm[i] == 1) break;
  U = gel(U,(nz-1)*N + i); /* (L[1]|...|L[nz]) U = 1 */
  nz = 0;
  for (i=1; i<l; i++)
  {
    GEN c = gel(L,i);
    if (lg(c) == 1)
      c = gen_0;
    else {
      c = ZM_ZC_mul(c, vecslice(U, nz*N + 1, (nz+1)*N));
      nz++;
    }
    gel(L,i) = c;
  }
  return gerepilecopy(av, L);
}

/* multiplication */

/* x integral ideal (without archimedean component) in HNF form
 * y = [a,alpha] corresponds to the integral ideal aZ_K+alpha Z_K, a in Z,
 * alpha a ZV or a ZM (multiplication table). Multiply them */
static GEN
idealmul_HNF_two(GEN nf, GEN x, GEN y)
{
  GEN m, a = gel(y,1), alpha = gel(y,2);
  long i, N;

  if (typ(alpha) != t_MAT)
  {
    alpha = zk_scalar_or_multable(nf, alpha);
    if (typ(alpha) == t_INT) /* e.g. y inert ? 0 should not (but may) occur */
      return signe(a)? ZM_Z_mul(x, gcdii(a, alpha)): cgetg(1,t_MAT);
  }
  N = lg(x)-1; m = cgetg((N<<1)+1,t_MAT);
  for (i=1; i<=N; i++) gel(m,i)   = ZM_ZC_mul(alpha,gel(x,i));
  for (i=1; i<=N; i++) gel(m,i+N) = ZC_Z_mul(gel(x,i), a);
  return ZM_hnfmodid(m, mulii(a, gcoeff(x,1,1)));
}

/* Assume ix and iy are integral in HNF form [NOT extended]. Not memory clean.
 * HACK: ideal in iy can be of the form [a,b], a in Z, b in Z_K */
GEN
idealmul_HNF(GEN nf, GEN x, GEN y)
{
  GEN z;
  if (typ(y) == t_VEC)
    z = idealmul_HNF_two(nf,x,y);
  else
  { /* reduce one ideal to two-elt form. The smallest */
    GEN xZ = gcoeff(x,1,1), yZ = gcoeff(y,1,1);
    if (cmpii(xZ, yZ) < 0)
    {
      if (is_pm1(xZ)) return gcopy(y);
      z = idealmul_HNF_two(nf, y, mat_ideal_two_elt(nf,x));
    }
    else
    {
      if (is_pm1(yZ)) return gcopy(x);
      z = idealmul_HNF_two(nf, x, mat_ideal_two_elt(nf,y));
    }
  }
  return z;
}

/* operations on elements in factored form */

GEN
famat_mul_shallow(GEN f, GEN g)
{
  if (lg(f) == 1) return g;
  if (lg(g) == 1) return f;
  return mkmat2(shallowconcat(gel(f,1), gel(g,1)),
                shallowconcat(gel(f,2), gel(g,2)));
}

GEN
to_famat(GEN x, GEN y) {
  GEN fa = cgetg(3, t_MAT);
  gel(fa,1) = mkcol(gcopy(x));
  gel(fa,2) = mkcol(gcopy(y)); return fa;
}
GEN
to_famat_shallow(GEN x, GEN y) {
  GEN fa = cgetg(3, t_MAT);
  gel(fa,1) = mkcol(x);
  gel(fa,2) = mkcol(y); return fa;
}

static GEN
append(GEN v, GEN x)
{
  long i, l = lg(v);
  GEN w = cgetg(l+1, typ(v));
  for (i=1; i<l; i++) gel(w,i) = gcopy(gel(v,i));
  gel(w,i) = gcopy(x); return w;
}

/* add x^1 to famat f */
static GEN
famat_add(GEN f, GEN x)
{
  GEN h = cgetg(3,t_MAT);
  if (lg(f) == 1)
  {
    gel(h,1) = mkcolcopy(x);
    gel(h,2) = mkcol(gen_1);
  }
  else
  {
    gel(h,1) = append(gel(f,1), x); /* x may be a t_COL */
    gel(h,2) = gconcat(gel(f,2), gen_1);
  }
  return h;
}

GEN
famat_mul(GEN f, GEN g)
{
  GEN h;
  if (typ(g) != t_MAT) {
    if (typ(f) == t_MAT) return famat_add(f, g);
    h = cgetg(3, t_MAT);
    gel(h,1) = mkcol2(gcopy(f), gcopy(g));
    gel(h,2) = mkcol2(gen_1, gen_1);
  }
  if (typ(f) != t_MAT) return famat_add(g, f);
  if (lg(f) == 1) return gcopy(g);
  if (lg(g) == 1) return gcopy(f);
  h = cgetg(3,t_MAT);
  gel(h,1) = gconcat(gel(f,1), gel(g,1));
  gel(h,2) = gconcat(gel(f,2), gel(g,2));
  return h;
}

GEN
famat_sqr(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  if (typ(f) != t_MAT) return to_famat(f,gen_2);
  h = cgetg(3,t_MAT);
  gel(h,1) = gcopy(gel(f,1));
  gel(h,2) = gmul2n(gel(f,2),1);
  return h;
}
GEN
famat_inv_shallow(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  if (typ(f) != t_MAT) return to_famat_shallow(f,gen_m1);
  h = cgetg(3,t_MAT);
  gel(h,1) = gel(f,1);
  gel(h,2) = ZC_neg(gel(f,2));
  return h;
}
GEN
famat_inv(GEN f)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  if (typ(f) != t_MAT) return to_famat(f,gen_m1);
  h = cgetg(3,t_MAT);
  gel(h,1) = gcopy(gel(f,1));
  gel(h,2) = ZC_neg(gel(f,2));
  return h;
}
GEN
famat_pow(GEN f, GEN n)
{
  GEN h;
  if (lg(f) == 1) return cgetg(1,t_MAT);
  if (typ(f) != t_MAT) return to_famat(f,n);
  h = cgetg(3,t_MAT);
  gel(h,1) = gcopy(gel(f,1));
  gel(h,2) = ZC_Z_mul(gel(f,2),n);
  return h;
}

GEN
famat_Z_gcd(GEN M, GEN n)
{
  pari_sp av=avma;
  long i, j, l=lgcols(M);
  GEN F=cgetg(3,t_MAT);
  gel(F,1)=cgetg(l,t_COL);
  gel(F,2)=cgetg(l,t_COL);
  for (i=1, j=1; i<l; i++)
  {
    GEN p = gcoeff(M,i,1);
    GEN e = gminsg(Z_pval(n,p),gcoeff(M,i,2));
    if (signe(e))
    {
      gcoeff(F,j,1)=p;
      gcoeff(F,j,2)=e;
      j++;
    }
  }
  setlg(gel(F,1),j); setlg(gel(F,2),j);
  return gerepilecopy(av,F);
}

/* x assumed to be a t_MATs (factorization matrix), or compatible with
 * the element_* functions. */
static GEN
ext_sqr(GEN nf, GEN x) {
  if (typ(x) == t_MAT) return famat_sqr(x);
  return nfsqr(nf, x);
}
static GEN
ext_mul(GEN nf, GEN x, GEN y) {
  if (typ(x) == t_MAT) return (x == y)? famat_sqr(x): famat_mul(x,y);
  return nfmul(nf, x, y);
}
static GEN
ext_inv(GEN nf, GEN x) {
  if (typ(x) == t_MAT) return famat_inv(x);
  return nfinv(nf, x);
}
static GEN
ext_pow(GEN nf, GEN x, GEN n) {
  if (typ(x) == t_MAT) return famat_pow(x,n);
  return nfpow(nf, x, n);
}

/* x, y 2 extended ideals whose first component is an integral HNF */
GEN
extideal_HNF_mul(GEN nf, GEN x, GEN y)
{
  return mkvec2(idealmul_HNF(nf, gel(x,1), gel(y,1)),
                ext_mul(nf, gel(x,2), gel(y,2)));
}

GEN
famat_to_nf(GEN nf, GEN f)
{
  GEN t, x, e;
  long i;
  if (lg(f) == 1) return gen_1;

  x = gel(f,1);
  e = gel(f,2);
  t = nfpow(nf, gel(x,1), gel(e,1));
  for (i=lg(x)-1; i>1; i--)
    t = nfmul(nf, t, nfpow(nf, gel(x,i), gel(e,i)));
  return t;
}

/* "compare" two nf elt. Goal is to quickly sort for uniqueness of
 * representation, not uniqueness of represented element ! */
static int
elt_cmp(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (ty == tx)
    return (tx == t_POL || tx == t_POLMOD)? cmp_RgX(x,y): lexcmp(x,y);
  return tx - ty;
}
static int
elt_egal(GEN x, GEN y)
{
  if (typ(x) == typ(y)) return gequal(x,y);
  return 0;
}

GEN
famat_reduce(GEN fa)
{
  GEN E, G, L, g, e;
  long i, k, l;

  if (lg(fa) == 1) return fa;
  g = gel(fa,1); l = lg(g);
  e = gel(fa,2);
  L = gen_indexsort(g, (void*)&elt_cmp, &cmp_nodata);
  G = cgetg(l, t_COL);
  E = cgetg(l, t_COL);
  /* merge */
  for (k=i=1; i<l; i++,k++)
  {
    gel(G,k) = gel(g,L[i]);
    gel(E,k) = gel(e,L[i]);
    if (k > 1 && elt_egal(gel(G,k), gel(G,k-1)))
    {
      gel(E,k-1) = addii(gel(E,k), gel(E,k-1));
      k--;
    }
  }
  /* kill 0 exponents */
  l = k;
  for (k=i=1; i<l; i++)
    if (!gequal0(gel(E,i)))
    {
      gel(G,k) = gel(G,i);
      gel(E,k) = gel(E,i); k++;
    }
  setlg(G, k);
  setlg(E, k); return mkmat2(G,E);
}

GEN
famatsmall_reduce(GEN fa)
{
  GEN E, G, L, g, e;
  long i, k, l;
  if (lg(fa) == 1) return fa;
  g = gel(fa,1); l = lg(g);
  e = gel(fa,2);
  L = vecsmall_indexsort(g);
  G = cgetg(l, t_VECSMALL);
  E = cgetg(l, t_VECSMALL);
  /* merge */
  for (k=i=1; i<l; i++,k++)
  {
    G[k] = g[L[i]];
    E[k] = e[L[i]];
    if (k > 1 && G[k] == G[k-1])
    {
      E[k-1] += E[k];
      k--;
    }
  }
  /* kill 0 exponents */
  l = k;
  for (k=i=1; i<l; i++)
    if (E[i])
    {
      G[k] = G[i];
      E[k] = E[i]; k++;
    }
  setlg(G, k);
  setlg(E, k); return mkmat2(G,E);
}

GEN
ZM_famat_limit(GEN fa, GEN limit)
{
  pari_sp av;
  GEN E, G, g, e, r;
  long i, k, l, n, lG;

  if (lg(fa) == 1) return fa;
  g = gel(fa,1); l = lg(g);
  e = gel(fa,2);
  for(n=0, i=1; i<l; i++)
    if (cmpii(gel(g,i),limit)<=0) n++;
  lG = n<l-1 ? n+2 : n+1;
  G = cgetg(lG, t_COL);
  E = cgetg(lG, t_COL);
  av = avma;
  for (i=1, k=1, r = gen_1; i<l; i++)
  {
    if (cmpii(gel(g,i),limit)<=0)
    {
      gel(G,k) = gel(g,i);
      gel(E,k) = gel(e,i);
      k++;
    } else r = mulii(r, powii(gel(g,i), gel(e,i)));
  }
  if (k<i)
  {
    gel(G, k) = gerepileuptoint(av, r);
    gel(E, k) = gen_1;
  }
  return mkmat2(G,E);
}

/* assume pr has degree 1 and coprime to Q_denom(x) */
static GEN
to_Fp_coprime(GEN nf, GEN x, GEN modpr)
{
  GEN d, r, p = modpr_get_p(modpr);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return Rg_to_Fp(x,p);
  x = Q_remove_denom(x, &d);
  r = zk_to_Fq(x, modpr);
  if (d) r = Fp_div(r, d, p);
  return r;
}

/* pr coprime to all denominators occurring in x */
static GEN
famat_to_Fp_coprime(GEN nf, GEN x, GEN modpr)
{
  GEN p = modpr_get_p(modpr);
  GEN t = NULL, g = gel(x,1), e = gel(x,2), q = subiu(p,1);
  long i, l = lg(g);
  for (i = 1; i < l; i++)
  {
    GEN n = modii(gel(e,i), q);
    if (signe(n))
    {
      GEN h = to_Fp_coprime(nf, gel(g,i), modpr);
      h = Fp_pow(h, n, p);
      t = t? Fp_mul(t, h, p): h;
    }
  }
  return t? modii(t, p): gen_1;
}

/* cf famat_to_nf_modideal_coprime, modpr attached to prime of degree 1 */
GEN
nf_to_Fp_coprime(GEN nf, GEN x, GEN modpr)
{
  return typ(x)==t_MAT? famat_to_Fp_coprime(nf, x, modpr)
                      : to_Fp_coprime(nf, x, modpr);
}

static long
zk_pvalrem(GEN x, GEN p, GEN *py)
{ return (typ(x) == t_INT)? Z_pvalrem(x, p, py): ZV_pvalrem(x, p, py); }
/* x a QC or Q. Return a ZC or Z, whose content is coprime to Z. Set v, dx
 * such that x = p^v (newx / dx); dx = NULL if 1 */
static GEN
nf_remove_denom_p(GEN nf, GEN x, GEN p, GEN *pdx, long *pv)
{
  long vcx;
  GEN dx;
  x = nf_to_scalar_or_basis(nf, x);
  x = Q_remove_denom(x, &dx);
  if (dx)
  {
    vcx = - Z_pvalrem(dx, p, &dx);
    if (!vcx) vcx = zk_pvalrem(x, p, &x);
    if (isint1(dx)) dx = NULL;
  }
  else
  {
    vcx = zk_pvalrem(x, p, &x);
    dx = NULL;
  }
  *pv = vcx;
  *pdx = dx; return x;
}
/* x = b^e/p^(e-1) in Z_K; x = 0 mod p/pr^e, (x,pr) = 1. Return NULL
 * if p inert (instead of 1) */
static GEN
p_makecoprime(GEN pr)
{
  GEN B = pr_get_tau(pr), b;
  long i, e;

  if (typ(B) == t_INT) return NULL;
  b = gel(B,1); /* B = multiplication table by b */
  e = pr_get_e(pr);
  if (e == 1) return b;
  /* one could also divide (exactly) by p in each iteration */
  for (i = 1; i < e; i++) b = ZM_ZC_mul(B, b);
  return ZC_Z_divexact(b, powiu(pr_get_p(pr), e-1));
}

/* Compute A = prod g[i]^e[i] mod pr^k, assuming (A, pr) = 1.
 * Method: modify each g[i] so that it becomes coprime to pr,
 * g[i] *= (b/p)^v_pr(g[i]), where b/p = pr^(-1) times something integral
 * and prime to p; globally, we multiply by (b/p)^v_pr(A) = 1.
 * Optimizations:
 * 1) remove all powers of p from contents, and consider extra generator p^vp;
 * modified as p * (b/p)^e = b^e / p^(e-1)
 * 2) remove denominators, coprime to p, by multiplying by inverse mod prk\cap Z
 *
 * EX = multiple of exponent of (O_K / pr^k)^* used to reduce the product in
 * case the e[i] are large */
GEN
famat_makecoprime(GEN nf, GEN g, GEN e, GEN pr, GEN prk, GEN EX)
{
  GEN G, E, t, vp = NULL, p = pr_get_p(pr), prkZ = gcoeff(prk, 1,1);
  long i, l = lg(g);

  G = cgetg(l+1, t_VEC);
  E = cgetg(l+1, t_VEC); /* l+1: room for "modified p" */
  for (i=1; i < l; i++)
  {
    long vcx;
    GEN dx, x = nf_remove_denom_p(nf, gel(g,i), p, &dx, &vcx);
    if (vcx) /* = v_p(content(g[i])) */
    {
      GEN a = mulsi(vcx, gel(e,i));
      vp = vp? addii(vp, a): a;
    }
    /* x integral, content coprime to p; dx coprime to p */
    if (typ(x) == t_INT)
    { /* x coprime to p, hence to pr */
      x = modii(x, prkZ);
      if (dx) x = Fp_div(x, dx, prkZ);
    }
    else
    {
      (void)ZC_nfvalrem(nf, x, pr, &x); /* x *= (b/p)^v_pr(x) */
      x = ZC_hnfrem(FpC_red(x,prkZ), prk);
      if (dx) x = FpC_Fp_mul(x, Fp_inv(dx,prkZ), prkZ);
    }
    gel(G,i) = x;
    gel(E,i) = gel(e,i);
  }

  t = vp? p_makecoprime(pr): NULL;
  if (!t)
  { /* no need for extra generator */
    setlg(G,l);
    setlg(E,l);
  }
  else
  {
    gel(G,i) = FpC_red(t, prkZ);
    gel(E,i) = vp;
  }
  return famat_to_nf_modideal_coprime(nf, G, E, prk, EX);
}

/* prod g[i]^e[i] mod bid, assume (g[i], id) = 1 */
GEN
famat_to_nf_moddivisor(GEN nf, GEN g, GEN e, GEN bid)
{
  GEN t, cyc;
  if (lg(g) == 1) return gen_1;
  cyc = bid_get_cyc(bid);
  if (lg(cyc) == 1)
    t = gen_1;
  else
    t = famat_to_nf_modideal_coprime(nf, g, e, bid_get_ideal(bid), gel(cyc,1));
  return set_sign_mod_divisor(nf, mkmat2(g,e), t, bid_get_sarch(bid));
}

GEN
vecmul(GEN x, GEN y)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return gmul(x,y);
  z = cgetg_copy(x, &lx);
  for (i=1; i<lx; i++) gel(z,i) = vecmul(gel(x,i), gel(y,i));
  return z;
}

GEN
vecinv(GEN x)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return ginv(x);
  z = cgetg_copy(x, &lx);
  for (i=1; i<lx; i++) gel(z,i) = vecinv(gel(x,i));
  return z;
}

GEN
vecpow(GEN x, GEN n)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return powgi(x,n);
  z = cgetg_copy(x, &lx);
  for (i=1; i<lx; i++) gel(z,i) = vecpow(gel(x,i), n);
  return z;
}

GEN
vecdiv(GEN x, GEN y)
{
  long i,lx, tx = typ(x);
  GEN z;
  if (is_scalar_t(tx)) return gdiv(x,y);
  z = cgetg_copy(x, &lx);
  for (i=1; i<lx; i++) gel(z,i) = vecdiv(gel(x,i), gel(y,i));
  return z;
}

/* A ideal as a square t_MAT */
static GEN
idealmulelt(GEN nf, GEN x, GEN A)
{
  long i, lx;
  GEN dx, dA, D;
  if (lg(A) == 1) return cgetg(1, t_MAT);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL)
    return isintzero(x)? cgetg(1,t_MAT): RgM_Rg_mul(A, Q_abs_shallow(x));
  x = Q_remove_denom(x, &dx);
  A = Q_remove_denom(A, &dA);
  x = zk_multable(nf, x);
  D = mulii(zkmultable_capZ(x), gcoeff(A,1,1));
  x = zkC_multable_mul(A, x);
  settyp(x, t_MAT); lx = lg(x);
  /* x may contain scalars (at most 1 since the ideal is non-0)*/
  for (i=1; i<lx; i++)
    if (typ(gel(x,i)) == t_INT)
    {
      if (i > 1) swap(gel(x,1), gel(x,i)); /* help HNF */
      gel(x,1) = scalarcol_shallow(gel(x,1), lx-1);
      break;
    }
  x = ZM_hnfmodid(x, D);
  dx = mul_denom(dx,dA);
  return dx? gdiv(x,dx): x;
}

/* nf a true nf, tx <= ty */
static GEN
idealmul_aux(GEN nf, GEN x, GEN y, long tx, long ty)
{
  GEN z, cx, cy;
  switch(tx)
  {
    case id_PRINCIPAL:
      switch(ty)
      {
        case id_PRINCIPAL:
          return idealhnf_principal(nf, nfmul(nf,x,y));
        case id_PRIME:
        {
          GEN p = gel(y,1), pi = gel(y,2), cx;
          if (pr_is_inert(y)) return RgM_Rg_mul(idealhnf_principal(nf,x),p);

          x = nf_to_scalar_or_basis(nf, x);
          switch(typ(x))
          {
            case t_INT:
              if (!signe(x)) return cgetg(1,t_MAT);
              return ZM_Z_mul(idealhnf_two(nf,y), absi(x));
            case t_FRAC:
              return RgM_Rg_mul(idealhnf_two(nf,y), Q_abs_shallow(x));
          }
          /* t_COL */
          x = Q_primitive_part(x, &cx);
          x = zk_multable(nf, x);
          z = shallowconcat(ZM_Z_mul(x,p), ZM_ZC_mul(x,pi));
          z = ZM_hnfmodid(z, mulii(p, zkmultable_capZ(x)));
          return cx? ZM_Q_mul(z, cx): z;
        }
        default: /* id_MAT */
          return idealmulelt(nf, x,y);
      }
    case id_PRIME:
      if (ty==id_PRIME)
      { y = idealhnf_two(nf,y); cy = NULL; }
      else
        y = Q_primitive_part(y, &cy);
      y = idealmul_HNF_two(nf,y,x);
      return cy? RgM_Rg_mul(y,cy): y;

    default: /* id_MAT */
      x = Q_primitive_part(x, &cx);
      y = Q_primitive_part(y, &cy); cx = mul_content(cx,cy);
      y = idealmul_HNF(nf,x,y);
      return cx? ZM_Q_mul(y,cx): y;
  }
}

/* output the ideal product ix.iy */
GEN
idealmul(GEN nf, GEN x, GEN y)
{
  pari_sp av;
  GEN res, ax, ay, z;
  long tx = idealtyp(&x,&ax);
  long ty = idealtyp(&y,&ay), f;
  if (tx>ty) { swap(ax,ay); swap(x,y); lswap(tx,ty); }
  f = (ax||ay); res = f? cgetg(3,t_VEC): NULL; /*product is an extended ideal*/
  av = avma;
  z = gerepileupto(av, idealmul_aux(checknf(nf), x,y, tx,ty));
  if (!f) return z;
  if (ax && ay)
    ax = ext_mul(nf, ax, ay);
  else
    ax = gcopy(ax? ax: ay);
  gel(res,1) = z; gel(res,2) = ax; return res;
}

/* Return x, integral in 2-elt form, such that pr^2 = c * x. cf idealpowprime
 * nf = true nf */
static GEN
idealsqrprime(GEN nf, GEN pr, GEN *pc)
{
  GEN p = pr_get_p(pr), q, gen;
  long e = pr_get_e(pr), f = pr_get_f(pr);

  q = (e == 1)? sqri(p): p;
  if (e <= 2 && e * f == nf_get_degree(nf))
  { /* pr^e = (p) */
    *pc = q;
    return mkvec2(gen_1,gen_0);
  }
  gen = nfsqr(nf, pr_get_gen(pr));
  gen = FpC_red(gen, q);
  *pc = NULL;
  return mkvec2(q, gen);
}
/* cf idealpow_aux */
static GEN
idealsqr_aux(GEN nf, GEN x, long tx)
{
  GEN T = nf_get_pol(nf), m, cx, a, alpha;
  long N = degpol(T);
  switch(tx)
  {
    case id_PRINCIPAL:
      return idealhnf_principal(nf, nfsqr(nf,x));
    case id_PRIME:
      if (pr_is_inert(x)) return scalarmat(sqri(gel(x,1)), N);
      x = idealsqrprime(nf, x, &cx);
      x = idealhnf_two(nf,x);
      return cx? ZM_Z_mul(x, cx): x;
    default:
      x = Q_primitive_part(x, &cx);
      a = mat_ideal_two_elt(nf,x); alpha = gel(a,2); a = gel(a,1);
      alpha = nfsqr(nf,alpha);
      m = zk_scalar_or_multable(nf, alpha);
      if (typ(m) == t_INT) {
        x = gcdii(sqri(a), m);
        if (cx) x = gmul(x, gsqr(cx));
        x = scalarmat(x, N);
      }
      else
      {
        x = ZM_hnfmodid(m, gcdii(sqri(a), zkmultable_capZ(m)));
        if (cx) cx = gsqr(cx);
        if (cx) x = RgM_Rg_mul(x, cx);
      }
      return x;
  }
}
GEN
idealsqr(GEN nf, GEN x)
{
  pari_sp av;
  GEN res, ax, z;
  long tx = idealtyp(&x,&ax);
  res = ax? cgetg(3,t_VEC): NULL; /*product is an extended ideal*/
  av = avma;
  z = gerepileupto(av, idealsqr_aux(checknf(nf), x, tx));
  if (!ax) return z;
  gel(res,1) = z;
  gel(res,2) = ext_sqr(nf, ax); return res;
}

/* norm of an ideal */
GEN
idealnorm(GEN nf, GEN x)
{
  pari_sp av;
  GEN y, T;
  long tx;

  switch(idealtyp(&x,&y))
  {
    case id_PRIME: return pr_norm(x);
    case id_MAT: return RgM_det_triangular(x);
  }
  /* id_PRINCIPAL */
  nf = checknf(nf); T = nf_get_pol(nf); av = avma;
  x = nf_to_scalar_or_alg(nf, x);
  x = (typ(x) == t_POL)? RgXQ_norm(x, T): gpowgs(x, degpol(T));
  tx = typ(x);
  if (tx == t_INT) return gerepileuptoint(av, absi(x));
  if (tx != t_FRAC) pari_err_TYPE("idealnorm",x);
  return gerepileupto(av, Q_abs(x));
}

/* I^(-1) = { x \in K, Tr(x D^(-1) I) \in Z }, D different of K/Q
 *
 * nf[5][6] = pp( D^(-1) ) = pp( HNF( T^(-1) ) ), T = (Tr(wi wj))
 * nf[5][7] = same in 2-elt form.
 * Assume I integral. Return the integral ideal (I\cap Z) I^(-1) */
GEN
idealinv_HNF_Z(GEN nf, GEN I)
{
  GEN J, dual, IZ = gcoeff(I,1,1); /* I \cap Z */
  if (isint1(IZ)) return matid(lg(I)-1);
  J = idealmul_HNF(nf,I, gmael(nf,5,7));
 /* I in HNF, hence easily inverted; multiply by IZ to get integer coeffs
  * missing content cancels while solving the linear equation */
  dual = shallowtrans( hnf_divscale(J, gmael(nf,5,6), IZ) );
  return ZM_hnfmodid(dual, IZ);
}
/* I HNF with rational coefficients (denominator d). */
GEN
idealinv_HNF(GEN nf, GEN I)
{
  GEN J, IQ = gcoeff(I,1,1); /* I \cap Q; d IQ = dI \cap Z */
  J = idealinv_HNF_Z(nf, Q_remove_denom(I, NULL)); /* = (dI)^(-1) * (d IQ) */
  return equali1(IQ)? J: RgM_Rg_div(J, IQ);
}

/* return p * P^(-1)  [integral] */
GEN
pr_inv_p(GEN pr)
{
  if (pr_is_inert(pr)) return matid(pr_get_f(pr));
  return ZM_hnfmodid(pr_get_tau(pr), pr_get_p(pr));
}
GEN
pr_inv(GEN pr)
{
  GEN p = pr_get_p(pr);
  if (pr_is_inert(pr)) return scalarmat(ginv(p), pr_get_f(pr));
  return RgM_Rg_div(ZM_hnfmodid(pr_get_tau(pr),p), p);
}

GEN
idealinv(GEN nf, GEN x)
{
  GEN res, ax;
  pari_sp av;
  long tx = idealtyp(&x,&ax), N;

  res = ax? cgetg(3,t_VEC): NULL;
  nf = checknf(nf); av = avma;
  N = nf_get_degree(nf);
  switch (tx)
  {
    case id_MAT:
      if (lg(x)-1 != N) pari_err_DIM("idealinv");
      x = idealinv_HNF(nf,x); break;
    case id_PRINCIPAL:
      x = nf_to_scalar_or_basis(nf, x);
      if (typ(x) != t_COL)
        x = idealhnf_principal(nf,ginv(x));
      else
      { /* nfinv + idealhnf where we already know (x) \cap Z */
        GEN c, d;
        x = Q_remove_denom(x, &c);
        x = zk_inv(nf, x);
        x = Q_remove_denom(x, &d); /* true inverse is c/d * x */
        if (!d) /* x and x^(-1) integral => x a unit */
          x = scalarmat_shallow(c? c: gen_1, N);
        else
        {
          c = c? gdiv(c,d): ginv(d);
          x = zk_multable(nf, x);
          x = ZM_Q_mul(ZM_hnfmodid(x,d), c);
        }
      }
      break;
    case id_PRIME:
      x = pr_inv(x); break;
  }
  x = gerepileupto(av,x); if (!ax) return x;
  gel(res,1) = x;
  gel(res,2) = ext_inv(nf, ax); return res;
}

/* write x = A/B, A,B coprime integral ideals */
GEN
idealnumden(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN x0, ax, c, d, A, B, J;
  long tx = idealtyp(&x,&ax);
  nf = checknf(nf);
  switch (tx)
  {
    case id_PRIME:
      retmkvec2(idealhnf(nf, x), gen_1);
    case id_PRINCIPAL:
    {
      GEN xZ, mx;
      x = nf_to_scalar_or_basis(nf, x);
      switch(typ(x))
      {
        case t_INT: return gerepilecopy(av, mkvec2(absi(x),gen_1));
        case t_FRAC:return gerepilecopy(av, mkvec2(absi(gel(x,1)), gel(x,2)));
      }
      /* t_COL */
      x = Q_remove_denom(x, &d);
      if (!d) return gerepilecopy(av, mkvec2(idealhnf(nf, x), gen_1));
      mx = zk_multable(nf, x);
      xZ = zkmultable_capZ(mx);
      x = ZM_hnfmodid(mx, xZ); /* principal ideal (x) */
      x0 = mkvec2(xZ, mx); /* same, for fast multiplication */
      break;
    }
    default: /* id_MAT */
    {
      long n = lg(x)-1;
      if (n == 0) return mkvec2(gen_0, gen_1);
      if (n != nf_get_degree(nf)) pari_err_DIM("idealnumden");
      x0 = x = Q_remove_denom(x, &d);
      if (!d) return gerepilecopy(av, mkvec2(x, gen_1));
      break;
    }
  }
  J = hnfmodid(x, d); /* = d/B */
  c = gcoeff(J,1,1); /* (d/B) \cap Z, divides d */
  B = idealinv_HNF_Z(nf, J); /* (d/B \cap Z) B/d */
  if (!equalii(c,d)) B = ZM_Z_mul(B, diviiexact(d,c)); /* = B ! */
  A = idealmul_HNF(nf, B, x0); /* d * (original x) * B = d A */
  A = ZM_Z_divexact(A, d); /* = A ! */
  return gerepilecopy(av, mkvec2(A, B));
}

/* Return x, integral in 2-elt form, such that pr^n = c * x. Assume n != 0.
 * nf = true nf */
static GEN
idealpowprime(GEN nf, GEN pr, GEN n, GEN *pc)
{
  GEN p = pr_get_p(pr), q, gen;

  *pc = NULL;
  if (is_pm1(n)) /* n = 1 special cased for efficiency */
  {
    q = p;
    if (typ(pr_get_tau(pr)) == t_INT) /* inert */
    {
      *pc = (signe(n) >= 0)? p: ginv(p);
      return mkvec2(gen_1,gen_0);
    }
    if (signe(n) >= 0) gen = pr_get_gen(pr);
    else
    {
      gen = pr_get_tau(pr); /* possibly t_MAT */
      *pc = ginv(p);
    }
  }
  else if (equalis(n,2)) return idealsqrprime(nf, pr, pc);
  else
  {
    long e = pr_get_e(pr), f = pr_get_f(pr);
    GEN r, m = truedvmdis(n, e, &r);
    if (e * f == nf_get_degree(nf))
    { /* pr^e = (p) */
      if (signe(m)) *pc = powii(p,m);
      if (!signe(r)) return mkvec2(gen_1,gen_0);
      q = p;
      gen = nfpow(nf, pr_get_gen(pr), r);
    }
    else
    {
      m = absi(m);
      if (signe(r)) m = addiu(m,1);
      q = powii(p,m); /* m = ceil(|n|/e) */
      if (signe(n) >= 0) gen = nfpow(nf, pr_get_gen(pr), n);
      else
      {
        gen = pr_get_tau(pr);
        if (typ(gen) == t_MAT) gen = gel(gen,1);
        n = negi(n);
        gen = ZC_Z_divexact(nfpow(nf, gen, n), powii(p, subii(n,m)));
        *pc = ginv(q);
      }
    }
    gen = FpC_red(gen, q);
  }
  return mkvec2(q, gen);
}

/* x * pr^n. Assume x in HNF or scalar (possibly non-integral) */
GEN
idealmulpowprime(GEN nf, GEN x, GEN pr, GEN n)
{
  GEN c, cx, y;
  long N;

  nf = checknf(nf);
  N = nf_get_degree(nf);
  if (!signe(n)) return typ(x) == t_MAT? x: scalarmat_shallow(x, N);

  /* inert, special cased for efficiency */
  if (pr_is_inert(pr))
  {
    GEN q = powii(pr_get_p(pr), n);
    return typ(x) == t_MAT? RgM_Rg_mul(x,q): scalarmat_shallow(gmul(x,q), N);
  }

  y = idealpowprime(nf, pr, n, &c);
  if (typ(x) == t_MAT)
  { x = Q_primitive_part(x, &cx); if (is_pm1(gcoeff(x,1,1))) x = NULL; }
  else
  { cx = x; x = NULL; }
  cx = mul_content(c,cx);
  if (x)
    x = idealmul_HNF_two(nf,x,y);
  else
    x = idealhnf_two(nf,y);
  if (cx) x = RgM_Rg_mul(x,cx);
  return x;
}
GEN
idealdivpowprime(GEN nf, GEN x, GEN pr, GEN n)
{
  return idealmulpowprime(nf,x,pr, negi(n));
}

/* nf = true nf */
static GEN
idealpow_aux(GEN nf, GEN x, long tx, GEN n)
{
  GEN T = nf_get_pol(nf), m, cx, n1, a, alpha;
  long N = degpol(T), s = signe(n);
  if (!s) return matid(N);
  switch(tx)
  {
    case id_PRINCIPAL:
      return idealhnf_principal(nf, nfpow(nf,x,n));
    case id_PRIME:
      if (pr_is_inert(x)) return scalarmat(powii(gel(x,1), n), N);
      x = idealpowprime(nf, x, n, &cx);
      x = idealhnf_two(nf,x);
      return cx? RgM_Rg_mul(x, cx): x;
    default:
      if (is_pm1(n)) return (s < 0)? idealinv(nf, x): gcopy(x);
      n1 = (s < 0)? negi(n): n;

      x = Q_primitive_part(x, &cx);
      a = mat_ideal_two_elt(nf,x); alpha = gel(a,2); a = gel(a,1);
      alpha = nfpow(nf,alpha,n1);
      m = zk_scalar_or_multable(nf, alpha);
      if (typ(m) == t_INT) {
        x = gcdii(powii(a,n1), m);
        if (s<0) x = ginv(x);
        if (cx) x = gmul(x, powgi(cx,n));
        x = scalarmat(x, N);
      }
      else
      {
        x = ZM_hnfmodid(m, gcdii(powii(a,n1), zkmultable_capZ(m)));
        if (cx) cx = powgi(cx,n);
        if (s<0) {
          GEN xZ = gcoeff(x,1,1);
          cx = cx ? gdiv(cx, xZ): ginv(xZ);
          x = idealinv_HNF_Z(nf,x);
        }
        if (cx) x = RgM_Rg_mul(x, cx);
      }
      return x;
  }
}

/* raise the ideal x to the power n (in Z) */
GEN
idealpow(GEN nf, GEN x, GEN n)
{
  pari_sp av;
  long tx;
  GEN res, ax;

  if (typ(n) != t_INT) pari_err_TYPE("idealpow",n);
  tx = idealtyp(&x,&ax);
  res = ax? cgetg(3,t_VEC): NULL;
  av = avma;
  x = gerepileupto(av, idealpow_aux(checknf(nf), x, tx, n));
  if (!ax) return x;
  ax = ext_pow(nf, ax, n);
  gel(res,1) = x;
  gel(res,2) = ax;
  return res;
}

/* Return ideal^e in number field nf. e is a C integer. */
GEN
idealpows(GEN nf, GEN ideal, long e)
{
  long court[] = {evaltyp(t_INT) | _evallg(3),0,0};
  affsi(e,court); return idealpow(nf,ideal,court);
}

static GEN
_idealmulred(GEN nf, GEN x, GEN y)
{ return idealred(nf,idealmul(nf,x,y)); }
static GEN
_idealsqrred(GEN nf, GEN x)
{ return idealred(nf,idealsqr(nf,x)); }
static GEN
_mul(void *data, GEN x, GEN y) { return _idealmulred((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return _idealsqrred((GEN)data, x); }

/* compute x^n (x ideal, n integer), reducing along the way */
GEN
idealpowred(GEN nf, GEN x, GEN n)
{
  pari_sp av = avma;
  long s;
  GEN y;

  if (typ(n) != t_INT) pari_err_TYPE("idealpowred",n);
  s = signe(n); if (s == 0) return idealpow(nf,x,n);
  y = gen_pow(x, n, (void*)nf, &_sqr, &_mul);

  if (s < 0) y = idealinv(nf,y);
  if (s < 0 || is_pm1(n)) y = idealred(nf,y);
  return gerepileupto(av,y);
}

GEN
idealmulred(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, _idealmulred(nf,x,y));
}

long
isideal(GEN nf,GEN x)
{
  long N, i, j, lx, tx = typ(x);
  pari_sp av;
  GEN T, xZ;

  nf = checknf(nf); T = nf_get_pol(nf); lx = lg(x);
  if (tx==t_VEC && lx==3) { x = gel(x,1); tx = typ(x); lx = lg(x); }
  switch(tx)
  {
    case t_INT: case t_FRAC: return 1;
    case t_POL: return varn(x) == varn(T);
    case t_POLMOD: return RgX_equal_var(T, gel(x,1));
    case t_VEC: return get_prid(x)? 1 : 0;
    case t_MAT: break;
    default: return 0;
  }
  N = degpol(T);
  if (lx-1 != N) return (lx == 1);
  if (nbrows(x) != N) return 0;

  av = avma; x = Q_primpart(x);
  if (!ZM_ishnf(x)) return 0;
  xZ = gcoeff(x,1,1);
  for (j=2; j<=N; j++)
    if (!dvdii(xZ, gcoeff(x,j,j))) { avma = av; return 0; }
  for (i=2; i<=N; i++)
    for (j=2; j<=N; j++)
      if (! hnf_invimage(x, zk_ei_mul(nf,gel(x,i),j))) { avma = av; return 0; }
  avma=av; return 1;
}

GEN
idealdiv(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma, tetpil;
  GEN z = idealinv(nf,y);
  tetpil = avma; return gerepile(av,tetpil, idealmul(nf,x,z));
}

/* This routine computes the quotient x/y of two ideals in the number field nf.
 * It assumes that the quotient is an integral ideal.  The idea is to find an
 * ideal z dividing y such that gcd(Nx/Nz, Nz) = 1.  Then
 *
 *   x + (Nx/Nz)    x
 *   ----------- = ---
 *   y + (Ny/Nz)    y
 *
 * Proof: we can assume x and y are integral. Let p be any prime ideal
 *
 * If p | Nz, then it divides neither Nx/Nz nor Ny/Nz (since Nx/Nz is the
 * product of the integers N(x/y) and N(y/z)).  Both the numerator and the
 * denominator on the left will be coprime to p.  So will x/y, since x/y is
 * assumed integral and its norm N(x/y) is coprime to p.
 *
 * If instead p does not divide Nz, then v_p (Nx/Nz) = v_p (Nx) >= v_p(x).
 * Hence v_p (x + Nx/Nz) = v_p(x).  Likewise for the denominators.  QED.
 *
 *                Peter Montgomery.  July, 1994. */
static void
err_divexact(GEN x, GEN y)
{ pari_err_DOMAIN("idealdivexact","denominator(x/y)", "!=",
                  gen_1,mkvec2(x,y)); }
GEN
idealdivexact(GEN nf, GEN x0, GEN y0)
{
  pari_sp av = avma;
  GEN x, y, yZ, Nx, Ny, Nz, cy, q, r;

  nf = checknf(nf);
  x = idealhnf_shallow(nf, x0);
  y = idealhnf_shallow(nf, y0);
  if (lg(y) == 1) pari_err_INV("idealdivexact", y0);
  if (lg(x) == 1) { avma = av; return cgetg(1, t_MAT); } /* numerator is zero */
  y = Q_primitive_part(y, &cy);
  if (cy) x = RgM_Rg_div(x,cy);
  Nx = idealnorm(nf,x);
  Ny = idealnorm(nf,y);
  if (typ(Nx) != t_INT) err_divexact(x,y);
  q = dvmdii(Nx,Ny, &r);
  if (signe(r)) err_divexact(x,y);
  if (is_pm1(q)) { avma = av; return matid(nf_get_degree(nf)); }
  /* Find a norm Nz | Ny such that gcd(Nx/Nz, Nz) = 1 */
  for (Nz = Ny;;) /* q = Nx/Nz */
  {
    GEN p1 = gcdii(Nz, q);
    if (is_pm1(p1)) break;
    Nz = diviiexact(Nz,p1);
    q = mulii(q,p1);
  }
  /* Replace x/y  by  x+(Nx/Nz) / y+(Ny/Nz) */
  x = ZM_hnfmodid(x, q);
  /* y reduced to unit ideal ? */
  if (Nz == Ny) return gerepileupto(av, x);

  y = ZM_hnfmodid(y, diviiexact(Ny,Nz));
  yZ = gcoeff(y,1,1);
  y = idealmul_HNF(nf,x, idealinv_HNF_Z(nf,y));
  return gerepileupto(av, RgM_Rg_div(y, yZ));
}

GEN
idealintersect(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  long lz, lx, i;
  GEN z, dx, dy, xZ, yZ;;

  nf = checknf(nf);
  x = idealhnf_shallow(nf,x);
  y = idealhnf_shallow(nf,y);
  if (lg(x) == 1 || lg(y) == 1) { avma = av; return cgetg(1,t_MAT); }
  x = Q_remove_denom(x, &dx);
  y = Q_remove_denom(y, &dy);
  if (dx) y = ZM_Z_mul(y, dx);
  if (dy) x = ZM_Z_mul(x, dy);
  xZ = gcoeff(x,1,1);
  yZ = gcoeff(y,1,1);
  dx = mul_denom(dx,dy);
  z = ZM_lll(shallowconcat(x,y), 0.99, LLL_KER); lz = lg(z);
  lx = lg(x);
  for (i=1; i<lz; i++) setlg(z[i], lx);
  z = ZM_hnfmodid(ZM_mul(x,z), lcmii(xZ, yZ));
  if (dx) z = RgM_Rg_div(z,dx);
  return gerepileupto(av,z);
}

/*******************************************************************/
/*                                                                 */
/*                      T2-IDEAL REDUCTION                         */
/*                                                                 */
/*******************************************************************/

static GEN
chk_vdir(GEN nf, GEN vdir)
{
  long i, l = lg(vdir);
  GEN v;
  if (l != lg(nf_get_roots(nf))) pari_err_DIM("idealred");
  switch(typ(vdir))
  {
    case t_VECSMALL: return vdir;
    case t_VEC: break;
    default: pari_err_TYPE("idealred",vdir);
  }
  v = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) v[i] = itos(gceil(gel(vdir,i)));
  return v;
}

static void
twistG(GEN G, long r1, long i, long v)
{
  long j, lG = lg(G);
  if (i <= r1) {
    for (j=1; j<lG; j++) gcoeff(G,i,j) = gmul2n(gcoeff(G,i,j), v);
  } else {
    long k = (i<<1) - r1;
    for (j=1; j<lG; j++)
    {
      gcoeff(G,k-1,j) = gmul2n(gcoeff(G,k-1,j), v);
      gcoeff(G,k  ,j) = gmul2n(gcoeff(G,k  ,j), v);
    }
  }
}

GEN
nf_get_Gtwist(GEN nf, GEN vdir)
{
  long i, l, v, r1;
  GEN G;

  if (!vdir) return nf_get_roundG(nf);
  if (typ(vdir) == t_MAT)
  {
    long N = nf_get_degree(nf);
    if (lg(vdir) != N+1 || lgcols(vdir) != N+1) pari_err_DIM("idealred");
    return vdir;
  }
  vdir = chk_vdir(nf, vdir);
  G = RgM_shallowcopy(nf_get_G(nf));
  r1 = nf_get_r1(nf);
  l = lg(vdir);
  for (i=1; i<l; i++)
  {
    v = vdir[i]; if (!v) continue;
    twistG(G, r1, i, v);
  }
  return RM_round_maxrank(G);
}
GEN
nf_get_Gtwist1(GEN nf, long i)
{
  GEN G = RgM_shallowcopy( nf_get_G(nf) );
  long r1 = nf_get_r1(nf);
  twistG(G, r1, i, 10);
  return RM_round_maxrank(G);
}

GEN
RM_round_maxrank(GEN G0)
{
  long e, r = lg(G0)-1;
  pari_sp av = avma;
  GEN G = G0;
  for (e = 4; ; e <<= 1)
  {
    GEN H = ground(G);
    if (ZM_rank(H) == r) return H; /* maximal rank ? */
    avma = av;
    G = gmul2n(G0, e);
  }
}

GEN
idealred0(GEN nf, GEN I, GEN vdir)
{
  pari_sp av = avma;
  GEN G, aI, IZ, J, y, yZ, my, c1 = NULL;
  long N;

  nf = checknf(nf);
  N = nf_get_degree(nf);
  /* put first for sanity checks, unused when I obviously principal */
  G = nf_get_Gtwist(nf, vdir);
  switch (idealtyp(&I,&aI))
  {
    case id_PRIME:
      if (pr_is_inert(I)) {
        if (!aI) { avma = av; return matid(N); }
        c1 = gel(I,1); I = matid(N);
        goto END;
      }
      IZ = pr_get_p(I);
      J = pr_inv_p(I);
      I = idealhnf_two(nf,I);
      break;
    case id_MAT:
      I = Q_primitive_part(I, &c1);
      IZ = gcoeff(I,1,1);
      if (is_pm1(IZ))
      {
        if (!aI) { avma = av; return matid(N); }
        goto END;
      }
      J = idealinv_HNF_Z(nf, I);
      break;
    default: /* id_PRINCIPAL, silly case */
      if (gequal0(I)) I = cgetg(1,t_MAT); else { c1 = I; I = matid(N); }
      if (!aI) return I;
      goto END;
  }
  /* now I integral, HNF; and J = (I\cap Z) I^(-1), integral */
  y = idealpseudomin(J, G); /* small elt in (I\cap Z)I^(-1), integral */
  if (ZV_isscalar(y))
  { /* already reduced */
    if (!aI) return gerepilecopy(av, I);
    goto END;
  }

  my = zk_multable(nf, y);
  I = ZM_Z_divexact(ZM_mul(my, I), IZ); /* y I / (I\cap Z), integral */
  c1 = mul_content(c1, IZ);
  my = ZM_gauss(my, col_ei(N,1)); /* y^-1 */
  yZ = Q_denom(my); /* (y) \cap Z */
  I = hnfmodid(I, yZ);
  if (!aI) return gerepileupto(av, I);
  c1 = RgC_Rg_mul(my, c1);
END:
  if (c1) aI = ext_mul(nf, aI,c1);
  return gerepilecopy(av, mkvec2(I, aI));
}

GEN
idealmin(GEN nf, GEN x, GEN vdir)
{
  pari_sp av = avma;
  GEN y, dx;
  nf = checknf(nf);
  switch( idealtyp(&x,&y) )
  {
    case id_PRINCIPAL: return gcopy(x);
    case id_PRIME: x = idealhnf_two(nf,x); break;
    case id_MAT: if (lg(x) == 1) return gen_0;
  }
  x = Q_remove_denom(x, &dx);
  y = idealpseudomin(x, nf_get_Gtwist(nf,vdir));
  if (dx) y = RgC_Rg_div(y, dx);
  return gerepileupto(av, y);
}

/*******************************************************************/
/*                                                                 */
/*                   APPROXIMATION THEOREM                         */
/*                                                                 */
/*******************************************************************/
/* a = ppi(a,b) ppo(a,b), where ppi regroups primes common to a and b
 * and ppo(a,b) = coprime_part(a,b) */
/* return gcd(a,b),ppi(a,b),ppo(a,b) */
GEN
Z_ppio(GEN a, GEN b)
{
  GEN x, y, d = gcdii(a,b);
  if (is_pm1(d)) return mkvec3(gen_1, gen_1, a);
  x = d; y = diviiexact(a,d);
  for(;;)
  {
    GEN g = gcdii(x,y);
    if (is_pm1(g)) return mkvec3(d, x, y);
    x = mulii(x,g); y = diviiexact(y,g);
  }
}
/* a = ppg(a,b)pple(a,b), where ppg regroups primes such that v(a) > v(b)
 * and pple all others */
/* return gcd(a,b),ppg(a,b),pple(a,b) */
GEN
Z_ppgle(GEN a, GEN b)
{
  GEN x, y, g, d = gcdii(a,b);
  if (equalii(a, d)) return mkvec3(a, gen_1, a);
  x = diviiexact(a,d); y = d;
  for(;;)
  {
    g = gcdii(x,y);
    if (is_pm1(g)) return mkvec3(d, x, y);
    x = mulii(x,g); y = diviiexact(y,g);
  }
}
static void
Z_dcba_rec(GEN L, GEN a, GEN b)
{
  GEN x, r, v, g, h, c, c0;
  long n;
  if (is_pm1(b)) {
    if (!is_pm1(a)) vectrunc_append(L, a);
    return;
  }
  v = Z_ppio(a,b);
  a = gel(v,2);
  r = gel(v,3);
  if (!is_pm1(r)) vectrunc_append(L, r);
  v = Z_ppgle(a,b);
  g = gel(v,1);
  h = gel(v,2);
  x = c0 = gel(v,3);
  for (n = 1; !is_pm1(h); n++)
  {
    GEN d, y;
    long i;
    v = Z_ppgle(h,sqri(g));
    g = gel(v,1);
    h = gel(v,2);
    c = gel(v,3); if (is_pm1(c)) continue;
    d = gcdii(c,b);
    x = mulii(x,d);
    y = d; for (i=1; i < n; i++) y = sqri(y);
    Z_dcba_rec(L, diviiexact(c,y), d);
  }
  Z_dcba_rec(L,diviiexact(b,x), c0);
}
static GEN
Z_cba_rec(GEN L, GEN a, GEN b)
{
  GEN g;
  if (lg(L) > 10)
  { /* a few naive steps before switching to dcba */
    Z_dcba_rec(L, a, b);
    return gel(L, lg(L)-1);
  }
  if (is_pm1(a)) return b;
  g = gcdii(a,b);
  if (is_pm1(g)) { vectrunc_append(L, a); return b; }
  a = diviiexact(a,g);
  b = diviiexact(b,g);
  return Z_cba_rec(L, Z_cba_rec(L, a, g), b);
}
GEN
Z_cba(GEN a, GEN b)
{
  GEN L = vectrunc_init(expi(a) + expi(b) + 2);
  GEN t = Z_cba_rec(L, a, b);
  if (!is_pm1(t)) vectrunc_append(L, t);
  return L;
}

/* write x = x1 x2, x2 maximal s.t. (x2,f) = 1, return x2 */
GEN
coprime_part(GEN x, GEN f)
{
  for (;;)
  {
    f = gcdii(x, f); if (is_pm1(f)) break;
    x = diviiexact(x, f);
  }
  return x;
}
/* write x = x1 x2, x2 maximal s.t. (x2,f) = 1, return x2 */
ulong
ucoprime_part(ulong x, ulong f)
{
  for (;;)
  {
    f = ugcd(x, f); if (f == 1) break;
    x /= f;
  }
  return x;
}

/* x t_INT, f ideal. Write x = x1 x2, sqf(x1) | f, (x2,f) = 1. Return x2 */
static GEN
nf_coprime_part(GEN nf, GEN x, GEN listpr)
{
  long v, j, lp = lg(listpr), N = nf_get_degree(nf);
  GEN x1, x2, ex;

#if 0 /*1) via many gcds. Expensive ! */
  GEN f = idealprodprime(nf, listpr);
  f = ZM_hnfmodid(f, x); /* first gcd is less expensive since x in Z */
  x = scalarmat(x, N);
  for (;;)
  {
    if (gequal1(gcoeff(f,1,1))) break;
    x = idealdivexact(nf, x, f);
    f = ZM_hnfmodid(shallowconcat(f,x), gcoeff(x,1,1)); /* gcd(f,x) */
  }
  x2 = x;
#else /*2) from prime decomposition */
  x1 = NULL;
  for (j=1; j<lp; j++)
  {
    GEN pr = gel(listpr,j);
    v = Z_pval(x, pr_get_p(pr)); if (!v) continue;

    ex = muluu(v, pr_get_e(pr)); /* = v_pr(x) > 0 */
    x1 = x1? idealmulpowprime(nf, x1, pr, ex)
           : idealpow(nf, pr, ex);
  }
  x = scalarmat(x, N);
  x2 = x1? idealdivexact(nf, x, x1): x;
#endif
  return x2;
}

/* L0 in K^*, assume (L0,f) = 1. Return L integral, L0 = L mod f  */
GEN
make_integral(GEN nf, GEN L0, GEN f, GEN listpr)
{
  GEN fZ, t, L, D2, d1, d2, d;

  L = Q_remove_denom(L0, &d);
  if (!d) return L0;

  /* L0 = L / d, L integral */
  fZ = gcoeff(f,1,1);
  if (typ(L) == t_INT) return Fp_mul(L, Fp_inv(d, fZ), fZ);
  /* Kill denom part coprime to fZ */
  d2 = coprime_part(d, fZ);
  t = Fp_inv(d2, fZ); if (!is_pm1(t)) L = ZC_Z_mul(L,t);
  if (equalii(d, d2)) return L;

  d1 = diviiexact(d, d2);
  /* L0 = (L / d1) mod f. d1 not coprime to f
   * write (d1) = D1 D2, D2 minimal, (D2,f) = 1. */
  D2 = nf_coprime_part(nf, d1, listpr);
  t = idealaddtoone_i(nf, D2, f); /* in D2, 1 mod f */
  L = nfmuli(nf,t,L);

  /* if (L0, f) = 1, then L in D1 ==> in D1 D2 = (d1) */
  return Q_div_to_int(L, d1); /* exact division */
}

/* assume L is a list of prime ideals. Return the product */
GEN
idealprodprime(GEN nf, GEN L)
{
  long l = lg(L), i;
  GEN z;
  if (l == 1) return matid(nf_get_degree(nf));
  z = idealhnf_two(nf, gel(L,1));
  for (i=2; i<l; i++) z = idealmul_HNF_two(nf,z, gel(L,i));
  return z;
}

/* optimize for the frequent case I = nfhnf()[2]: lots of them are 1 */
GEN
idealprod(GEN nf, GEN I)
{
  long i, l = lg(I);
  GEN z;
  for (i = 1; i < l; i++)
    if (!equali1(gel(I,i))) break;
  if (i == l) return gen_1;
  z = gel(I,i);
  for (i++; i<l; i++) z = idealmul(nf, z, gel(I,i));
  return z;
}

/* assume L is a list of prime ideals. Return prod L[i]^e[i] */
GEN
factorbackprime(GEN nf, GEN L, GEN e)
{
  long l = lg(L), i;
  GEN z;

  if (l == 1) return matid(nf_get_degree(nf));
  z = idealpow(nf, gel(L,1), gel(e,1));
  for (i=2; i<l; i++)
    if (signe(gel(e,i))) z = idealmulpowprime(nf,z, gel(L,i),gel(e,i));
  return z;
}

/* F in Z, divisible exactly by pr.p. Return F-uniformizer for pr, i.e.
 * a t in Z_K such that v_pr(t) = 1 and (t, F/pr) = 1 */
GEN
pr_uniformizer(GEN pr, GEN F)
{
  GEN p = pr_get_p(pr), t = pr_get_gen(pr);
  if (!equalii(F, p))
  {
    long e = pr_get_e(pr);
    GEN u, v, q = (e == 1)? sqri(p): p;
    u = mulii(q, Fp_inv(q, diviiexact(F,p))); /* 1 mod F/p, 0 mod q */
    v = subui(1UL, u); /* 0 mod F/p, 1 mod q */
    if (pr_is_inert(pr))
      t = addii(mulii(p, v), u);
    else
    {
      t = ZC_Z_mul(t, v);
      gel(t,1) = addii(gel(t,1), u); /* return u + vt */
    }
  }
  return t;
}
/* L = list of prime ideals, return lcm_i (L[i] \cap \ZM) */
GEN
prV_lcm_capZ(GEN L)
{
  long i, r = lg(L);
  GEN F;
  if (r == 1) return gen_1;
  F = pr_get_p(gel(L,1));
  for (i = 2; i < r; i++)
  {
    GEN pr = gel(L,i), p = pr_get_p(pr);
    if (!dvdii(F, p)) F = mulii(F,p);
  }
  return F;
}

/* Given a prime ideal factorization with possibly zero or negative
 * exponents, gives b such that v_p(b) = v_p(x) for all prime ideals pr | x
 * and v_pr(b)> = 0 for all other pr.
 * For optimal performance, all [anti-]uniformizers should be precomputed,
 * but no support for this yet.
 *
 * If nored, do not reduce result.
 * No garbage collecting */
static GEN
idealapprfact_i(GEN nf, GEN x, int nored)
{
  GEN z, d, L, e, e2, F;
  long i, r;
  int flagden;

  nf = checknf(nf);
  L = gel(x,1);
  e = gel(x,2);
  F = prV_lcm_capZ(L);
  flagden = 0;
  z = NULL; r = lg(e);
  for (i = 1; i < r; i++)
  {
    long s = signe(gel(e,i));
    GEN pi, q;
    if (!s) continue;
    if (s < 0) flagden = 1;
    pi = pr_uniformizer(gel(L,i), F);
    q = nfpow(nf, pi, gel(e,i));
    z = z? nfmul(nf, z, q): q;
  }
  if (!z) return gen_1;
  if (nored || typ(z) != t_COL) return z;
  e2 = cgetg(r, t_VEC);
  for (i=1; i<r; i++) gel(e2,i) = addis(gel(e,i), 1);
  x = factorbackprime(nf, L,e2);
  if (flagden) /* denominator */
  {
    z = Q_remove_denom(z, &d);
    d = diviiexact(d, coprime_part(d, F));
    x = RgM_Rg_mul(x, d);
  }
  else
    d = NULL;
  z = ZC_reducemodlll(z, x);
  return d? RgC_Rg_div(z,d): z;
}

GEN
idealapprfact(GEN nf, GEN x) {
  pari_sp av = avma;
  return gerepileupto(av, idealapprfact_i(nf, x, 0));
}
GEN
idealappr(GEN nf, GEN x) {
  pari_sp av = avma;
  if (!is_nf_extfactor(x)) x = idealfactor(nf, x);
  return gerepileupto(av, idealapprfact_i(nf, x, 0));
}

/* OBSOLETE */
GEN
idealappr0(GEN nf, GEN x, long fl) { (void)fl; return idealappr(nf, x); }

/* merge a^e b^f. Assume a and b sorted. Keep 0 exponents and *append* new
 * entries from b [ result not sorted ] */
static void
merge_fact(GEN *pa, GEN *pe, GEN b, GEN f)
{
  GEN A, E, a = *pa, e = *pe;
  long k, i, la = lg(a), lb = lg(b), l = la+lb-1;

  *pa = A = cgetg(l, t_COL);
  *pe = E = cgetg(l, t_COL);
  k = 1;
  for (i=1; i<la; i++)
  {
    gel(A,i) = gel(a,i);
    gel(E,i) = gel(e,i);
    if (k < lb && gequal(gel(A,i), gel(b,k)))
    {
      gel(E,i) = addii(gel(E,i), gel(f,k));
      k++;
    }
  }
  for (; k < lb; i++,k++)
  {
    gel(A,i) = gel(b,k);
    gel(E,i) = gel(f,k);
  }
  setlg(A, i);
  setlg(E, i);
}

static int
isprfact(GEN x)
{
  long i, l;
  GEN L, E;
  if (typ(x) != t_MAT || lg(x) != 3) return 0;
  L = gel(x,1); l = lg(L);
  E = gel(x,2);
  for(i=1; i<l; i++)
  {
    checkprid(gel(L,i));
    if (typ(gel(E,i)) != t_INT) return 0;
  }
  return 1;
}

/* initialize projectors mod pr[i]^e[i] for idealchinese */
static GEN
pr_init(GEN nf, GEN fa, GEN w, GEN dw)
{
  GEN L = gel(fa,1), E = gel(fa,2);
  long r = lg(L);

  if (w && lg(w) != r) pari_err_TYPE("idealchinese", w);
  if (r > 1)
  {
    GEN U, F;
    long i;
    if (dw)
    {
      GEN p = gen_indexsort(L, (void*)&cmp_prime_ideal, cmp_nodata);
      GEN fw = idealfactor(nf, dw); /* sorted */
      L = vecpermute(L, p);
      E = vecpermute(E, p);
      w = vecpermute(w, p);
      merge_fact(&L, &E, gel(fw,1), gel(fw,2));
      /* L and E lenghtened, with factors of dw coming last */
    }
    else
      E = leafcopy(E); /* do not destroy fa[2] */

    for (i=1; i<r; i++)
      if (signe(gel(E,i)) < 0) gel(E,i) = gen_0;
    F = factorbackprime(nf, L, E);
    U = cgetg(r, t_VEC);
    for (i = 1; i < r; i++)
    {
      GEN u;
      if (w && gequal0(gel(w,i))) u = gen_0; /* unused */
      else
      {
        GEN pr = gel(L,i), e = gel(E,i), t;
        t = idealdivpowprime(nf,F, pr, e);
        u = hnfmerge_get_1(t, idealpow(nf, pr, e));
        if (!u) pari_err_COPRIME("idealchinese", t,pr);
      }
      gel(U,i) = u;
    }
    F = idealpseudored(F, nf_get_roundG(nf));
    fa = mkvec2(F, U);
  }
  else
    fa = cgetg(1,t_VEC);
  return fa;
}

static GEN
pl_normalize(GEN nf, GEN pl)
{
  const char *fun = "idealchinese";
  if (lg(pl)-1 != nf_get_r1(nf)) pari_err_TYPE(fun,pl);
  switch(typ(pl))
  {
    case t_VEC:
      RgV_check_ZV(pl,fun);
      pl = ZV_to_zv(pl);
      /* fall through */
    case t_VECSMALL: break;
    default: pari_err_TYPE(fun,pl);
  }
  return pl;
}

static int
is_chineseinit(GEN x)
{
  GEN fa, pl;
  long l;
  if (typ(x) != t_VEC || lg(x)!=3) return 0;
  fa = gel(x,1);
  pl = gel(x,2);
  if (typ(fa) != t_VEC || typ(pl) != t_VEC) return 0;
  l = lg(fa);
  if (l != 1)
  {
    if (l != 3 || typ(gel(fa,1)) != t_MAT || typ(gel(fa,2)) != t_VEC)
      return 0;
  }
  l = lg(pl);
  if (l != 1)
  {
    if (l != 5 || typ(gel(pl,1)) != t_MAT || typ(gel(pl,2)) != t_MAT
               || typ(gel(pl,3)) != t_COL || typ(gel(pl,4)) != t_VECSMALL)
      return 0;
  }
  return 1;
}

/* nf a true 'nf' */
static GEN
chineseinit_i(GEN nf, GEN fa, GEN w, GEN dw)
{
  const char *fun = "idealchineseinit";
  GEN nz = NULL, pl = NULL;
  switch(typ(fa))
  {
    case t_VEC:
      if (is_chineseinit(fa))
      {
        if (dw) pari_err_DOMAIN(fun, "denom(y)", "!=", gen_1, w);
        return fa;
      }
      if (lg(fa) != 3) pari_err_TYPE(fun, fa);
      /* of the form [x,s] */
      pl = pl_normalize(nf, gel(fa,2));
      fa = gel(fa,1);
      nz = vecsmall01_to_indices(pl);
      if (is_chineseinit(fa)) { fa = gel(fa,1); break; /* keep fa, reset pl */ }
      /* fall through */
    case t_MAT: /* factorization? */
      if (isprfact(fa)) { fa = pr_init(nf, fa, w, dw); break; }
    default: pari_err_TYPE(fun,fa);
  }

  if (pl)
  {
    GEN C, Mr, MI, lambda, mlambda;
    GEN F = (lg(fa) == 1)? NULL: gel(fa,1);
    long i, r;
    Mr = rowpermute(nf_get_M(nf), nz);
    MI = F? RgM_mul(Mr, F): Mr;
    lambda = gmul2n(matrixnorm(MI,DEFAULTPREC), -1);
    mlambda = gneg(lambda);
    r = lg(nz);
    C = cgetg(r, t_COL);
    for (i = 1; i < r; i++) gel(C,i) = pl[nz[i]] < 0? mlambda: lambda;
    pl = mkvec4(MI, Mr, C, pl);
  }
  else
    pl = cgetg(1,t_VEC);
  return mkvec2(fa, pl);
}

/* Given a prime ideal factorization x, possibly with 0 or negative exponents,
 * and a vector w of elements of nf, gives b such that
 * v_p(b-w_p)>=v_p(x) for all prime ideals p in the ideal factorization
 * and v_p(b)>=0 for all other p, using the standard proof given in GTM 138. */
GEN
idealchinese(GEN nf, GEN x, GEN w)
{
  const char *fun = "idealchinese";
  pari_sp av = avma;
  GEN x1, x2, s, dw;

  nf = checknf(nf);
  if (!w) return gerepilecopy(av, chineseinit_i(nf,x,NULL,NULL));

  if (typ(w) != t_VEC) pari_err_TYPE(fun,w);
  w = Q_remove_denom(matalgtobasis(nf,w), &dw);
  if (!is_chineseinit(x)) x = chineseinit_i(nf,x,w,dw);
  /* x is a 'chineseinit' */
  x1 = gel(x,1); s = NULL;
  if (lg(x1) != 1)
  {
    GEN F = gel(x1,1), U = gel(x1,2);
    long i, r = lg(w);
    for (i=1; i<r; i++)
      if (!gequal0(gel(w,i)))
      {
        GEN t = nfmuli(nf, gel(U,i), gel(w,i));
        s = s? ZC_add(s,t): t;
      }
    if (s) s = ZC_reducemodmatrix(s, F);
  }
  if (!s) { s = zerocol(nf_get_degree(nf)); dw = NULL; }

  x2 = gel(x,2);
  if (lg(x2) != 1)
  {
    GEN pl = gel(x2,4);
    if (!nfchecksigns(nf, s, pl))
    {
      GEN MI = gel(x2,1), Mr = gel(x2,2), C = gel(x2,3);
      GEN t = RgC_sub(C, RgM_RgC_mul(Mr,s));
      long e;
      t = grndtoi(RgM_RgC_invimage(MI,t), &e);
      if (lg(x1) != 1) { GEN F = gel(x1,1); t = ZM_ZC_mul(F, t); }
      s = ZC_add(s, t);
    }
  }
  if (dw) s = RgC_Rg_div(s,dw);
  return gerepileupto(av, s);
}

static GEN
mat_ideal_two_elt2(GEN nf, GEN x, GEN a)
{
  GEN F = idealfactor(nf,a), P = gel(F,1), E = gel(F,2);
  long i, r = lg(E);
  for (i=1; i<r; i++) gel(E,i) = stoi( idealval(nf,x,gel(P,i)) );
  return idealapprfact_i(nf,F,1);
}

static void
not_in_ideal(GEN a) {
  pari_err_DOMAIN("idealtwoelt2","element mod ideal", "!=", gen_0, a);
}
/* x integral in HNF, a an 'nf' */
static int
in_ideal(GEN x, GEN a)
{
  switch(typ(a))
  {
    case t_INT: return dvdii(a, gcoeff(x,1,1));
    case t_COL: return RgV_is_ZV(a) && !!hnf_invimage(x, a);
    default: return 0;
  }
}

/* Given an integral ideal x and a in x, gives a b such that
 * x = aZ_K + bZ_K using the approximation theorem */
GEN
idealtwoelt2(GEN nf, GEN x, GEN a)
{
  pari_sp av = avma;
  GEN cx, b;

  nf = checknf(nf);
  a = nf_to_scalar_or_basis(nf, a);
  x = idealhnf_shallow(nf,x);
  if (lg(x) == 1)
  {
    if (!isintzero(a)) not_in_ideal(a);
    avma = av; return zerocol(nf_get_degree(nf));
  }
  x = Q_primitive_part(x, &cx);
  if (cx) a = gdiv(a, cx);
  if (!in_ideal(x, a)) not_in_ideal(a);
  b = mat_ideal_two_elt2(nf, x, a);
  if (typ(b) == t_COL)
  {
    GEN mod = idealhnf_principal(nf,a);
    b = ZC_hnfrem(b,mod);
    if (ZV_isscalar(b)) b = gel(b,1);
  }
  else
  {
    GEN aZ = typ(a) == t_COL? Q_denom(zk_inv(nf,a)): a; /* (a) \cap Z */
    b = centermodii(b, aZ, shifti(aZ,-1));
  }
  b = cx? gmul(b,cx): gcopy(b);
  return gerepileupto(av, b);
}

/* Given 2 integral ideals x and y in nf, returns a beta in nf such that
 * beta * x is an integral ideal coprime to y */
GEN
idealcoprimefact(GEN nf, GEN x, GEN fy)
{
  GEN L = gel(fy,1), e;
  long i, r = lg(L);

  e = cgetg(r, t_COL);
  for (i=1; i<r; i++) gel(e,i) = stoi( -idealval(nf,x,gel(L,i)) );
  return idealapprfact_i(nf, mkmat2(L,e), 0);
}
GEN
idealcoprime(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  return gerepileupto(av, idealcoprimefact(nf, x, idealfactor(nf,y)));
}

GEN
nfmulmodpr(GEN nf, GEN x, GEN y, GEN modpr)
{
  pari_sp av = avma;
  GEN z, p, pr = modpr, T;

  nf = checknf(nf); modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  x = nf_to_Fq(nf,x,modpr);
  y = nf_to_Fq(nf,y,modpr);
  z = Fq_mul(x,y,T,p);
  return gerepileupto(av, algtobasis(nf, Fq_to_nf(z,modpr)));
}

GEN
nfdivmodpr(GEN nf, GEN x, GEN y, GEN modpr)
{
  pari_sp av = avma;
  nf = checknf(nf);
  return gerepileupto(av, nfreducemodpr(nf, nfdiv(nf,x,y), modpr));
}

GEN
nfpowmodpr(GEN nf, GEN x, GEN k, GEN modpr)
{
  pari_sp av=avma;
  GEN z, T, p, pr = modpr;

  nf = checknf(nf); modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  z = nf_to_Fq(nf,x,modpr);
  z = Fq_pow(z,k,T,p);
  return gerepileupto(av, algtobasis(nf, Fq_to_nf(z,modpr)));
}

GEN
nfkermodpr(GEN nf, GEN x, GEN modpr)
{
  pari_sp av = avma;
  GEN T, p, pr = modpr;

  nf = checknf(nf); modpr = nf_to_Fq_init(nf, &pr,&T,&p);
  if (typ(x)!=t_MAT) pari_err_TYPE("nfkermodpr",x);
  x = nfM_to_FqM(x, nf, modpr);
  return gerepilecopy(av, FqM_to_nfM(FqM_ker(x,T,p), modpr));
}

GEN
nfsolvemodpr(GEN nf, GEN a, GEN b, GEN pr)
{
  const char *f = "nfsolvemodpr";
  pari_sp av = avma;
  GEN T, p, modpr;

  nf = checknf(nf);
  modpr = nf_to_Fq_init(nf, &pr,&T,&p);
  if (typ(a)!=t_MAT) pari_err_TYPE(f,a);
  a = nfM_to_FqM(a, nf, modpr);
  switch(typ(b))
  {
    case t_MAT:
      b = nfM_to_FqM(b, nf, modpr);
      b = FqM_gauss(a,b,T,p);
      if (!b) pari_err_INV(f,a);
      a = FqM_to_nfM(b, modpr);
      break;
    case t_COL:
      b = nfV_to_FqV(b, nf, modpr);
      b = FqM_FqC_gauss(a,b,T,p);
      if (!b) pari_err_INV(f,a);
      a = FqV_to_nfV(b, modpr);
      break;
    default: pari_err_TYPE(f,b);
  }
  return gerepilecopy(av, a);
}
