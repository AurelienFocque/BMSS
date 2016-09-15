/* Copyright (C) 2000  The PARI group.

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

/*********************************************************************/
/**                                                                 **/
/**                  GENERIC ABELIAN CHARACTERS                     **/
/**                                                                 **/
/*********************************************************************/

/* check whether G is a bidZ */
static int
checkbidZ_i(GEN G)
{
  return (typ(G) == t_VEC && lg(G) == 6
      && typ(bid_get_fact(G)) == t_VEC
      && typ(bid_get_mod(G)) == t_VEC && lg(bid_get_mod(G)) == 3);
}

int
char_check(GEN cyc, GEN chi)
{ return typ(chi) == t_VEC && lg(chi) == lg(cyc) && RgV_is_ZV(chi); }

/* Shallow; return [ d[1],  d[1]/d[2],...,d[1]/d[n] ] */
GEN
cyc_normalize(GEN d)
{
  long i, l = lg(d);
  GEN C, D;
  if (l == 1) return mkvec(gen_1);
  D = cgetg(l, t_VEC); gel(D,1) = C = gel(d,1);
  for (i = 2; i < l; i++) gel(D,i) = diviiexact(C, gel(d,i));
  return D;
}

/* chi character [D,C] given by chi(g_i) = \zeta_D^C[i] for all i, return
 * [d,c] such that chi(g_i) = \zeta_d^c[i] for all i and d minimal */
GEN
char_simplify(GEN D, GEN C)
{
  GEN d = D;
  if (lg(C) == 1) d = gen_1;
  else
  {
    GEN t = gcdii(d, ZV_content(C));
    if (!equali1(t))
    {
      C = ZC_Z_divexact(C, t);
      d = diviiexact(d, t);
    }
  }
  return mkvec2(d,C);
}

/* Shallow; ncyc from cyc_normalize(): ncyc[1] = cyc[1],
 * ncyc[i] = cyc[i]/cyc[1] for i > 1; chi character on G ~ cyc.
 * Return [d,c] such that: chi( g_i ) = e(chi[i] / cyc[i]) = e(c[i]/ d) */
GEN
char_normalize(GEN chi, GEN ncyc)
{
  long i, l = lg(chi);
  GEN c = cgetg(l, t_VEC);
  if (l > 1) {
    gel(c,1) = gel(chi,1);
    for (i = 2; i < l; i++) gel(c,i) = mulii(gel(chi,i), gel(ncyc,i));
  }
  return char_simplify(gel(ncyc,1), c);
}

/* Called by function 's'. x is a group object affording ".cyc" method, and
 * chi an abelian character. Return NULL if the group is (Z/nZ)^* [special
 * case more character types allowed] and x.cyc otherwise */
static GEN
get_cyc(GEN x, GEN chi, const char *s)
{
  if (nftyp(x) == typ_BID && checkbidZ_i(x))
  {
    if (!zncharcheck(x, chi)) pari_err_TYPE(s, chi);
    return NULL;
  }
  else
  {
    if (typ(x) != t_VEC || !RgV_is_ZV(x)) x = member_cyc(x);
    if (!char_check(x, chi)) pari_err_TYPE(s, chi);
    return x;
  }
}

/* conjugate character [ZV/ZC] */
GEN
charconj(GEN cyc, GEN chi)
{
  long i, l;
  GEN z = cgetg_copy(chi, &l);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(chi,i);
    gel(z,i) = signe(c)? subii(gel(cyc,i), c): gen_0;
  }
  return z;
}
GEN
charconj0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charconj");
  return cyc? charconj(cyc, chi): zncharconj(x, chi);
}

/* exp(2iPi/d), assume d a t_INT */
GEN
char_rootof1(GEN d, long prec)
{
  GEN c, s;
  if (lgefint(d) == 3) return char_rootof1_u((ulong)d[2], prec);
  gsincos(divri(Pi2n(1, prec), d), &s, &c, prec);
  return mkcomplex(c, s);
}
/* exp(2iPi/d) */
GEN
char_rootof1_u(ulong d, long prec)
{
  GEN c, s;
  switch(d)
  {
    case 1: return gen_1;
    case 2: return gen_m1;
    case 4: return gen_I();
  }
  gsincos(divru(Pi2n(1, prec), d), &s, &c, prec);
  return mkcomplex(c, s);
}

GEN
charorder(GEN cyc, GEN x)
{
  pari_sp av = avma;
  long i, l = lg(cyc);
  GEN f = gen_1;
  for (i = 1; i < l; i++)
  {
    GEN o = gel(cyc,i), c = gcdii(o, gel(x,i));
    if (!is_pm1(c)) o = diviiexact(o,c);
    f = lcmii(f, o);
  }
  return gerepileuptoint(av, f);
}
GEN
charorder0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charorder");
  return cyc? charorder(cyc, chi): zncharorder(x, chi);
}

/* chi character of abelian G: chi[i] = chi(z_i), where G = \oplus Z/cyc[i] z_i.
 * Return Ker chi */
GEN
charker(GEN cyc, GEN chi)
{
  long i, l = lg(cyc);
  GEN nchi, ncyc, m, U;

  if (l == 1) return cgetg(1,t_MAT); /* trivial subgroup */
  ncyc = cyc_normalize(cyc);
  nchi = char_normalize(chi, ncyc);
  m = shallowconcat(gel(nchi,2), gel(nchi,1));
  U = gel(ZV_extgcd(m), 2); setlg(U,l);
  for (i = 1; i < l; i++) setlg(U[i], l);
  return hnfmodid(U, gel(ncyc,1));
}
GEN
charker0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charker");
  return cyc? charker(cyc, chi): zncharker(x, chi);
}

GEN
charmul(GEN cyc, GEN a, GEN b)
{
  long i, l;
  GEN v = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(v,i) = Fp_add(gel(a,i), gel(b,i), gel(cyc,i));
  return v;
}
GEN
chardiv(GEN cyc, GEN a, GEN b)
{
  long i, l;
  GEN v = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(v,i) = Fp_sub(gel(a,i), gel(b,i), gel(cyc,i));
  return v;
}
GEN
charmul0(GEN x, GEN a, GEN b)
{
  const char *s = "charmul";
  GEN cyc = get_cyc(x, a, s);
  if (!cyc)
  {
    if (!zncharcheck(x, b)) pari_err_TYPE(s, b);
    return zncharmul(x, a, b);
  }
  else
  {
    if (!char_check(cyc, b)) pari_err_TYPE(s, b);
    return charmul(cyc, a, b);
  }
}
GEN
chardiv0(GEN x, GEN a, GEN b)
{
  const char *s = "chardiv";
  GEN cyc = get_cyc(x, a, s);
  if (!cyc)
  {
    if (!zncharcheck(x, b)) pari_err_TYPE(s, b);
    return znchardiv(x, a, b);
  }
  else
  {
    if (!char_check(cyc, b)) pari_err_TYPE(s, b);
    return chardiv(cyc, a, b);
  }
}

static GEN
chareval_i(GEN nchi, GEN dlog, GEN z)
{
  GEN o, q, r, b = gel(nchi,1);
  GEN a = FpV_dotproduct(gel(nchi,2), dlog, b);
  /* image is a/b in Q/Z */
  if (!z) return gdiv(a,b);
  if (typ(z) == t_INT)
  {
    q = dvmdii(z, b, &r);
    if (signe(r)) pari_err_TYPE("chareval", z);
    return mulii(a, q);
  }
  /* return z^(a*o/b), assuming z^o = 1 and b | o */
  if (typ(z) != t_VEC || lg(z) != 3) pari_err_TYPE("chareval", z);
  o = gel(z,2); if (typ(o) != t_INT) pari_err_TYPE("chareval", z);
  q = dvmdii(o, b, &r); if (signe(r)) pari_err_TYPE("chareval", z);
  q = mulii(a, q); /* in [0, o[ since a is reduced mod b */
  z = gel(z,1);
  if (typ(z) == t_VEC)
  {
    if (itos_or_0(o) != lg(z)-1) pari_err_TYPE("chareval", z);
    return gcopy(gel(z, itos(q)));
  }
  else
    return gpow(z, q, DEFAULTPREC);
}

static GEN
not_coprime(GEN z)
{ return (!z || typ(z) == t_INT)? gen_m1: gen_0; }

static GEN
get_chi(GEN cyc, GEN chi)
{
  if (!char_check(cyc,chi)) pari_err_TYPE("chareval", chi);
  return char_normalize(chi, cyc_normalize(cyc));
}
/* G a bnr.  FIXME: horribly inefficient to check that (x,N)=1, what to do ? */
static int
bnr_coprime(GEN G, GEN x)
{
  GEN t, N = gel(bnr_get_mod(G), 1);
  if (typ(x) == t_INT) /* shortcut */
  {
    t = gcdii(gcoeff(N,1,1), x);
    if (equali1(t)) return 1;
    t = idealadd(G, N, x);
    return equali1(gcoeff(t,1,1));
  }
  x = idealnumden(G, x);
  t = idealadd(G, N, gel(x,1));
  if (!equali1(gcoeff(t,1,1))) return 0;
  t = idealadd(G, N, gel(x,2));
  return equali1(gcoeff(t,1,1));
}
GEN
chareval(GEN G, GEN chi, GEN x, GEN z)
{
  pari_sp av = avma;
  GEN nchi, L;

  switch(nftyp(G))
  {
    case typ_BNR:
      if (!bnr_coprime(G, x)) return not_coprime(z);
      L = isprincipalray(G, x);
      nchi = get_chi(bnr_get_cyc(G), chi);
      break;
    case typ_BNF:
      L = isprincipal(G, x);
      nchi = get_chi(bnf_get_cyc(G), chi);
      break;
    case typ_BID:
      if (checkbidZ_i(G)) return gerepileupto(av, znchareval(G, chi, x, z));
      /* don't implement chars on general bid: need an nf... */
    default:
      pari_err_TYPE("chareval", G);
      return NULL;/* not reached */
  }
  return gerepileupto(av, chareval_i(nchi, L, z));
}

/*********************************************************************/
/**                                                                 **/
/**                  (Z/NZ)^* AND DIRICHLET CHARACTERS              **/
/**                                                                 **/
/*********************************************************************/

GEN
ZNstar(GEN N, long flag)
{
  GEN F = NULL, P, E, cyc, gen, mod, G;
  long i, i0, l, nbprimes;
  pari_sp av = avma;
  const long dogen = flag & nf_GEN;

  if ((F = check_arith_all(N,"znstar")))
  {
    F = clean_Z_factor(F);
    N = typ(N) == t_VEC? gel(N,1): factorback(F);
  }
  if (!signe(N))
  {
    avma = av;
    if (flag & nf_GEN)
      retmkvec3(gen_2, mkvec(gen_2), mkvec(gen_m1));
    else
      retmkvec2(gen_2, mkvec(gen_2));
  }
  if (signe(N) < 0) N = absi(N);
  if (abscmpiu(N,2) <= 0)
  {
    if (flag & nf_GEN)
      G = mkvec3(gen_1, cgetg(1,t_VEC), cgetg(1,t_VEC));
    else
      G = mkvec2(gen_1, cgetg(1,t_VEC));
    if (flag & nf_INIT)
    {
      GEN v = const_vec(6,cgetg(1,t_VEC));
      gel(v,3) = cgetg(1,t_MAT);
      F = equali1(N)? mkvec2(cgetg(1,t_COL),cgetg(1,t_VECSMALL))
                    : mkvec2(mkcol(gen_2), mkvecsmall(1));
      G = mkvec5(mkvec2(N,mkvec(gen_0)), G, F, v, cgetg(1,t_MAT));
    }
    return gerepilecopy(av,G);
  }
  if (!F) F = Z_factor(N);
  P = gel(F,1); nbprimes = lg(P)-1;
  E = ZV_to_nv( gel(F,2) );
  switch(mod8(N))
  {
    case 0:
      P = shallowconcat(gen_2,P);
      E = vecsmall_prepend(E, E[1]); /* add a copy of p=2 row */
      i = 2; /* 2 generators at 2 */
      break;
    case 4:
      i = 1; /* 1 generator at 2 */
      break;
    case 2: case 6:
      P = vecsplice(P,1);
      E = vecsplice(E,1); /* remove 2 */
      i = 0; /* no generator at 2 */
      break;
    default:
      i = 0; /* no generator at 2 */
      break;
  }
  l = lg(P);
  cyc = cgetg(l,t_VEC);
  gen = cgetg(l,t_VEC);
  mod = cgetg(l,t_VEC);
  /* treat p=2 first */
  if (i == 2)
  {
    long v2 = E[1];
    GEN q = int2n(v2);
    gel(cyc,1) = gen_2;
    gel(gen,1) = subiu(q,1); /* -1 */
    gel(mod,1) = q;
    gel(cyc,2) = int2n(v2-2);
    gel(gen,2) = utoipos(5); /* Conrey normalization */
    gel(mod,2) = q;
    i0 = 3;
  }
  else if (i == 1)
  {
    gel(cyc,1) = gen_2;
    gel(gen,1) = utoipos(3);
    gel(mod,1) = utoipos(4);
    i0 = 2;
  }
  else
    i0 = 1;
  /* odd primes, fill remaining entries */
  for (i = i0; i < l; i++)
  {
    long e = E[i];
    GEN p = gel(P,i), q = powiu(p, e-1), Q = mulii(p, q);
    gel(cyc,i) = subii(Q, q); /* phi(p^e) */
    gel(gen,i) = pgener_Zp(p);/* Conrey normalization, for e = 1 also */
    gel(mod,i) = Q;
  }
  /* gen[i] has order cyc[i] and generates (Z/mod[i]Z)^* */
  if (dogen && nbprimes > 1) /* lift generators to (Z/NZ)^*, = 1 mod N/mod[i] */
    for (i=1; i<l; i++)
    {
      GEN Q = gel(mod,i), g = gel(gen,i), qinv = Fp_inv(Q, diviiexact(N,Q));
      g = addii(g, mulii(mulii(subsi(1,g),qinv),Q));
      gel(gen,i) = modii(g, N);
    }

  /* cyc[i] > 1 and remain so in the loop, gen[i] = 1 mod (N/mod[i]) */
  if (!(flag & nf_INIT))
  { /* update generators in place; about twice faster */
    G = gen;
    for (i=l-1; i>=2; i--)
    {
      GEN ci = gel(cyc,i), gi = dogen? gel(G,i): NULL;
      long j;
      for (j=i-1; j>=1; j--) /* we want cyc[i] | cyc[j] */
      {
        GEN cj = gel(cyc,j), qj, v, d;

        d = dogen? bezout(ci,cj,NULL,&v): gcdii(ci,cj); /* > 1 */
        if (absequalii(ci, d)) continue; /* ci | cj */
        if (absequalii(cj, d)) { /* cj | ci */
          if (dogen)
          {
            swap(gel(G,j),gel(G,i));
            gi = gel(G,i);
          }
          swap(gel(cyc,j),gel(cyc,i));
          ci = gel(cyc,i); continue;
        }

        qj = diviiexact(cj,d);
        gel(cyc,j) = mulii(ci,qj);
        gel(cyc,i) = d;

        /* [1,v*cj/d; 0,1]*[1,0;-1,1]*diag(cj,ci)*[ci/d,-v; cj/d,u]
         * = diag(lcm,gcd), with u ci + v cj = d */
        if (dogen)
        {
          GEN gj = gel(G,j);
          /* (gj, gi) *= [1,0; -1,1]^-1 */
          gj = Fp_mul(gj, gi, N); /* order ci*qj = lcm(ci,cj) */
          /* (gj,gi) *= [1,v*qj; 0,1]^-1 */
          togglesign_safe(&v);
          if (signe(v) < 0) v = modii(v,ci); /* >= 0 to avoid inversions */
          gel(G,i) = gi = Fp_mul(gi, Fp_pow(gj, mulii(qj, v), N), N);
          gel(G,j) = gj;
        }
        ci = d; if (absequaliu(ci, 2)) break;
      }
    }
    if (dogen)
      G = mkvec3(ZV_prod(cyc), cyc, FpV_to_mod(G,N));
    else
      G = mkvec2(ZV_prod(cyc), cyc);
  }
  else
  { /* keep matrices between generators, return an 'init' structure */
    GEN D, U, Ui, fao = cgetg(l, t_VEC), lo = cgetg(l, t_VEC);
    F = mkvec2(P, E);
    D = ZV_snf_group(cyc,&U,&Ui);
    for (i = 1; i < l; i++)
    {
      GEN t = gen_0, p = gel(P,i), p_1 = subiu(p,1);
      long e = E[i];
      gel(fao,i) = get_arith_ZZM(p_1);
      if (e >= 2 && !absequaliu(p,2))
      {
        GEN q = gel(mod,i), g = Fp_pow(gel(gen,i),p_1,q);
        if (e == 2)
          t = Fp_inv(diviiexact(subiu(g,1), p), p);
        else
          t = ginv(Qp_log(cvtop(g,p,e)));
      }
      gel(lo,i) = t;
    }
    if (dogen)
    {
      G = cgetg(l, t_VEC);
      for (i = 1; i < l; i++) gel(G,i) = FpV_factorback(gen, gel(Ui,i), N);
      G = mkvec3(ZV_prod(D), D, G);
    }
    else
      G = mkvec2(ZV_prod(D), D);
    G = mkvec5(mkvec2(N,mkvec(gen_0)), G, F,
               mkvecn(6,mod,fao,Ui,gen,cyc,lo), U);
  }
  return gerepilecopy(av, G);
}
GEN
znstar(GEN N) { return ZNstar(N, nf_GEN); }
GEN
znstar0(GEN N,long flag)
{
  switch(flag)
  {
    case 0: return ZNstar(N, nf_GEN);
    case 1: return ZNstar(N, nf_INIT);
    case 2: return ZNstar(N, nf_INIT|nf_GEN);
    default: pari_err_FLAG("znstar");
  }
  return NULL; /* not reached */
}

/* g has order 2^(e-2), g,h = 1 (mod 4); return x s.t. g^x = h (mod 2^e) */
static GEN
Zideallog_2k(GEN h, GEN g, long e, GEN pe)
{
  GEN a = Fp_log(h, g, int2n(e-2), pe);
  if (typ(a) != t_INT) return NULL;
  return a;
}

/* ord = get_arith_ZZM(p-1), simplified form of znlog_rec: g is known
 * to be a primitive root mod p^e; lo = 1/log_p(g^(p-1)) */
static GEN
Zideallog_pk(GEN h, GEN g, GEN p, long e, GEN pe, GEN ord, GEN lo)
{
  GEN gp = (e == 1)? g: modii(g, p);
  GEN hp = (e == 1)? h: modii(h, p);
  GEN a = Fp_log(hp, gp, ord, p);
  if (typ(a) != t_INT) return NULL;
  if (e > 1)
  { /* find a s.t. g^a = h (mod p^e), p odd prime, e > 0, (h,p) = 1 */
    /* use p-adic log: O(log p + e) mul*/
    GEN b, p_1 = gel(ord,1);
    h = Fp_mul(h, Fp_pow(g, negi(a), pe), pe);
    /* g,h = 1 mod p; compute b s.t. h = g^b */
    if (e == 2) /* simpler */
      b = Fp_mul(diviiexact(subiu(h,1), p), lo, p);
    else
      b = padic_to_Q(gmul(Qp_log(cvtop(h, p, e)), lo));
    a = addii(a, mulii(p_1, b));
  }
  return a;
}

int
znconrey_check(GEN cyc, GEN chi)
{ return typ(chi) == t_COL && lg(chi) == lg(cyc) && RgV_is_ZV(chi); }

static GEN
bidZ_get_cycg(GEN G) { return gmael(G,4,5); }

int
zncharcheck(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: return 1;
    case t_COL: return znconrey_check(bidZ_get_cycg(G), chi);
    case t_VEC: return char_check(bid_get_cyc(G), chi);
  }
  return 0;
}

GEN
znconreyfromchar_normalized(GEN bid, GEN chi)
{
  GEN nchi, U = bid_get_U(bid);
  long l = lg(chi);
  if (l == 1) retmkvec2(gen_1,cgetg(1,t_VEC));
  if (!RgV_is_ZV(chi) || lgcols(U) != l) pari_err_TYPE("lfunchiZ", chi);
  nchi = char_normalize(chi, cyc_normalize(bid_get_cyc(bid)));
  gel(nchi,2) = ZV_ZM_mul(gel(nchi,2),U); return nchi;
}

GEN
znconreyfromchar(GEN bid, GEN chi)
{
  GEN nchi = znconreyfromchar_normalized(bid, chi);
  GEN v = char_denormalize(bidZ_get_cycg(bid), gel(nchi,1), gel(nchi,2));
  settyp(v, t_COL); return v;
}

/* discrete log on canonical "primitive root" generators
 * Allow log(x) instead of x [usual discrete log on bid's generators */
GEN
znconreylog(GEN bid, GEN x)
{
  pari_sp av = avma;
  GEN N, L, F, P,E, y, pe, fao, gen, lo, cycg;
  long i, l;
  if (!checkbidZ_i(bid)) pari_err_TYPE("znconreylog", bid);
  N = bid_get_ideal(bid);
  if (typ(N) != t_INT) pari_err_TYPE("znconreylog", N);
  if (abscmpiu(N, 2) <= 0) return cgetg(1, t_COL);
  L = gel(bid,4);
  cycg = bidZ_get_cycg(bid);
  switch(typ(x))
  {
    GEN Ui;
    case t_INT:
      if (!signe(x)) pari_err_COPRIME("znconreylog", x, N);
      break;
    case t_COL: /* log_bid(x) */
      Ui = gel(L,3);
      if (!RgV_is_ZV(x) || lg(x) != lg(Ui)) pari_err_TYPE("znconreylog", x);
      return gerepileupto(av, vecmodii(ZM_ZC_mul(Ui,x), cycg));
    case t_VEC:
      return gerepilecopy(av, znconreyfromchar(bid, x));
    default: pari_err_TYPE("znconreylog", x);
  }
  F = bid_get_fact(bid); /* factor(N) */
  P = gel(F, 1); /* prime divisors of N */
  E = gel(F, 2); /* exponents */
  pe = gel(L,1);
  fao = gel(L,2);
  gen = gel(L,4); /* local generators of (Z/p^k)^* */
  lo = gel(L,6); /* 1/log_p((g_i)^(p_i-1)) */

  l = lg(gen); i = 1;
  y = cgetg(l, t_COL);
  if (!mod2(N) && !mod2(x)) pari_err_COPRIME("znconreylog", x, N);
  if (absequaliu(gel(P,1), 2) && E[1] >= 2)
  {
    if (E[1] == 2)
      gel(y,i++) = mod4(x) == 1? gen_0: gen_1;
    else
    {
      GEN a, x2, q2 = gel(pe,1);
      x2 = modii(x, q2);
      if (mod4(x) == 1) /* 1 or 5 mod 8*/
        gel(y,i++) = gen_0;
      else /* 3 or 7 */
      { gel(y,i++) = gen_1; x2 = subii(q2, x2); }
      /* x2 = 5^x mod q */
      a = Zideallog_2k(x2, gel(gen,i), E[1], q2);
      if (!a) pari_err_COPRIME("znconreylog", x, N);
      gel(y, i++) = a;
    }
  }
  while (i < l)
  {
    GEN p = gel(P,i), q = gel(pe,i), xpe = modii(x, q);
    GEN a = Zideallog_pk(xpe, gel(gen,i), p, E[i], q, gel(fao,i), gel(lo,i));
    if (!a) pari_err_COPRIME("znconreylog", x, N);
    gel(y, i++) = a;
  }
  return gerepilecopy(av, y);
}
GEN
Zideallog(GEN bid, GEN x)
{
  pari_sp av = avma;
  GEN y = znconreylog(bid, x), U = bid_get_U(bid);
  return gerepileupto(av, ZM_ZC_mul(U, y));
}
GEN
znlog0(GEN h, GEN g, GEN o)
{
  if (typ(g) == t_VEC)
  {
    GEN N;
    if (o) pari_err_TYPE("znlog [with znstar]", o);
    if (!checkbidZ_i(g)) pari_err_TYPE("znlog", h);
    N = bid_get_ideal(g);
    h = Rg_to_Fp(h,N);
    return Zideallog(g, h);
  }
  return znlog(h, g, o);
}

GEN
znconreyexp(GEN bid, GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN L, pe, gen, cycg, v;
  int e2;
  switch(typ(x))
  {
    case t_VEC:
      x = znconreylog(bid, x);
      break;
    case t_COL:
      if (!checkbidZ_i(bid)) pari_err_TYPE("znconreyexp", bid);
      if (RgV_is_ZV(x)) break;
    default: pari_err_TYPE("znconreyexp",x);
  }
  L = gel(bid,4);
  pe = gel(L,1);
  gen = gel(L,4); /* local generators of (Z/p^k)^* */
  cycg = bidZ_get_cycg(bid);
  l = lg(x); v = cgetg(l, t_VEC);
  e2 = !mod8(bid_get_ideal(bid)); /* 2 generators at p = 2 */
  for (i = 1; i < l; i++)
  {
    GEN q, g, m;
    if (i == 1 && e2) { gel(v,1) = NULL; continue; }
    q = gel(pe,i);
    g = gel(gen,i);
    m = modii(gel(x,i), gel(cycg,i));
    m = Fp_pow(g, m, q);
    if (i == 2 && e2 && signe(gel(x,1))) m = Fp_neg(m, q);
    gel(v,i) = mkintmod(m, q);
  }
  if (e2) v = vecsplice(v, 1);
  v = chinese1_coprime_Z(v);
  return gerepilecopy(av, gel(v,2));
}

/* Return Dirichlet character \chi_q(m,.), where bid = znstar(q);
 * m is either a t_INT, or a t_COL [Conrey logarithm] */
GEN
znconreychar(GEN bid, GEN m)
{
  pari_sp av = avma;
  GEN c, d, L, Ui, nchi;

  switch(typ(m))
  {
    case t_COL:
    case t_INT:
      nchi = znconrey_normalized(bid,m); /* images of primroot gens */
      break;
    default:
      pari_err_TYPE("znconreychar",m);
      return NULL;/*not reached*/
  }
  L = gel(bid,4);
  Ui = gel(L,3);
  d = gel(nchi,1);
  c = ZV_ZM_mul(gel(nchi,2), Ui); /* images of bid gens */
  return gerepilecopy(av, char_denormalize(bid_get_cyc(bid),d,c));
}

/* chi a t_INT or Conrey log describing a character. Return conductor, as an
 * integer if primitive; as a t_VEC [N,factor(N)] if not. Set *pm=m to the
 * attached primitive character: chi(g_i) = m[i]/ord(g_i)
 * Caller should use znconreylog_normalize(BID, m), once BID(conductor) is
 * computed (wasteful to do it here since BID is shared by many characters) */
GEN
znconreyconductor(GEN bid, GEN chi, GEN *pm)
{
  pari_sp av = avma;
  GEN q, m, F, P, E;
  long i, j, l;
  int e2, primitive = 1;

  if (!checkbidZ_i(bid)) pari_err_TYPE("znconreyconductor", bid);
  if (typ(chi) == t_COL)
  {
    if (!znconrey_check(bidZ_get_cycg(bid), chi))
      pari_err_TYPE("znconreyconductor",chi);
  }
  else
    chi = znconreylog(bid, chi);
  l = lg(chi);
  F = bid_get_fact(bid);
  P = gel(F,1);
  E = gel(F,2);
  if (l == 1)
  {
    avma = av;
    if (pm) *pm = cgetg(1,t_COL);
    if (lg(P) == 1) return gen_1;
    retmkvec2(gen_1, trivial_fact());
  }
  P = leafcopy(P);
  E = leafcopy(E);
  m = cgetg(l, t_COL);
  e2 = (E[1] >= 3 && absequaliu(gel(P,1),2));
  i = j = 1;
  if (e2)
  { /* two generators at p=2 */
    GEN a1 = gel(chi,1), a = gel(chi,2);
    i = 3;
    if (!signe(a))
    {
      e2 =  primitive = 0;
      if (signe(a1))
      { /* lose one generator */
        E[1] = 2;
        gel(m,1) = a1;
        j = 2;
      }
      /* else lose both */
    }
    else
    {
      long v = Z_pvalrem(a, gen_2, &a);
      if (v) { E[1] -= v; E[2] = E[1]; primitive = 0; }
      gel(m,1) = a1;
      gel(m,2) = a;
      j = 3;
    }
  }
  l = lg(P);
  for (; i < l; i++)
  {
    GEN p = gel(P,i), a = gel(chi,i);
    /* image of g_i in Q/Z is a/cycg[i], cycg[i] = order(g_i) */
    if (!signe(a)) primitive = 0;
    else
    {
      long v = Z_pvalrem(a, p, &a);
      E[j] = E[i]; if (v) { E[j] -= v; primitive = 0; }
      gel(P,j) = gel(P,i);
      gel(m,j) = a; j++;
    }
  }
  setlg(m,j);
  setlg(P,j);
  setlg(E,j);
  if (pm) *pm = m; /* attached primitive  character */
  if (primitive)
  {
    q = bid_get_ideal(bid);
    if (mod4(q) == 2) primitive = 0;
  }
  if (!primitive)
  {
    if (e2)
    { /* remove duplicate p=2 row from factorization */
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
    E = zv_to_ZV(E);
    q = mkvec2(factorback2(P,E), mkmat2(P,E));
  }
  gerepileall(av, pm? 2: 1, &q, pm);
  return q;
}

GEN
zncharinduce(GEN G, GEN chi, GEN N)
{
  pari_sp av = avma;
  GEN q, faq, P, E, Pq, Eq, CHI;
  long i, j, l;
  int e2;

  if (!checkbidZ_i(G)) pari_err_TYPE("zncharinduce", G);
  if (!zncharcheck(G, chi)) pari_err_TYPE("zncharinduce", chi);
  q = bid_get_ideal(G);
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  if (checkbidZ_i(N))
  {
    GEN faN = bid_get_fact(N);
    P = gel(faN,1); l = lg(P);
    E = gel(faN,2);
    N = bid_get_ideal(N);
    if (l > 2 && equalii(gel(P,1),gel(P,2)))
    { /* remove duplicate 2 */
      l--;
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
  }
  else
  {
    GEN faN = check_arith_pos(N, "zncharinduce");
    if (!faN) faN = Z_factor(N);
    else
      N = (typ(N) == t_VEC)? gel(N,1): factorback(faN);
    P = gel(faN,1);
    E = gel(faN,2);
  }
  if (!dvdii(N,q)) pari_err_DOMAIN("zncharinduce", "N % q", "!=", gen_0, N);
  if (mod4(N) == 2)
  { /* remove 2 */
    if (lg(P) > 1 && absequaliu(gel(P,1), 2))
    {
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
    N = shifti(N,-1);
  }
  l = lg(P);
  /* q = N or q = 2N, N odd */
  if (cmpii(N,q) <= 0) return gerepilecopy(av, chi);
  /* N > 1 => l > 1*/
  if (typ(E) != t_VECSMALL) E = ZV_to_zv(E);
  e2 = (E[1] >= 3 && absequaliu(gel(P,1),2)); /* 2 generators at 2 mod N */
  if (ZV_equal0(chi))
  {
    avma = av;
    return equali1(N)? cgetg(1, t_COL): zerocol(l+e2 - 1);
  }

  faq = bid_get_fact(G);
  Pq = gel(faq,1);
  Eq = gel(faq,2);
  i = 1;
  CHI = cgetg(l+e2, t_COL);
  i = j = 1;
  if (e2)
  {
    i = 2; j = 3;
    if (absequaliu(gel(Pq,1), 2))
    {
      if (Eq[1] >= 3)
      { /* 2 generators at 2 mod q */
        gel(CHI,1) = gel(chi,1);
        gel(CHI,2) = shifti(gel(chi,2), E[1]-Eq[1]);
      }
      else if (Eq[1] == 2)
      { /* 1 generator at 2 mod q */
        gel(CHI,1) = gel(chi,1);
        gel(CHI,2) = gen_0;
      }
      else
        gel(CHI,1) = gel(CHI,2) = gen_0;
    }
    else
      gel(CHI,1) = gel(CHI,2) = gen_0;
  }
  for (; i < l; i++,j++)
  {
    GEN p = gel(P,i);
    long k = ZV_search(Pq, p);
    gel(CHI,j) = k? mulii(gel(chi,k), powiu(p, E[i]-Eq[k])): gen_0;
  }
  return gerepilecopy(av, CHI);
}

/* m a Conrey log [on the canonical primitive roots], cycg the primitive
 * roots orders */
GEN
znconreylog_normalize(GEN G, GEN m)
{
  GEN cycg = bidZ_get_cycg(G);
  long i, l;
  GEN d, M = cgetg_copy(m, &l);
  if (typ(cycg) != t_VEC || lg(cycg) != l)
    pari_err_TYPE("znconreylog_normalize",mkvec2(m,cycg));
  for (i = 1; i < l; i++) gel(M,i) = gdiv(gel(m,i), gel(cycg,i));
  /* m[i]: image of primroot generators g_i in Q/Z */
  M = Q_remove_denom(M, &d);
  return mkvec2(d? d: gen_1, M);
}

/* return normalized character on Conrey generators attached to chi: Conrey
 * label (t_INT), char on (SNF) G.gen* (t_VEC), or Conrey log (t_COL) */
GEN
znconrey_normalized(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: /* Conrey label */
      return znconreylog_normalize(G, znconreylog(G, chi));
    case t_COL: /* Conrey log */
      if (!RgV_is_ZV(chi)) break;
      return znconreylog_normalize(G, chi);
    case t_VEC: /* char on G.gen */
      if (!RgV_is_ZV(chi)) break;
      return znconreyfromchar_normalized(G, chi);
  }
  pari_err_TYPE("znchareval",chi);
  return NULL;/* not reached */
}

/* return 1 iff chi(-1) = -1, and 0 otherwise */
long
zncharisodd(GEN G, GEN chi)
{
  long i, l, s;
  GEN N;
  if (!checkbidZ_i(G)) pari_err_TYPE("zncharisodd", G);
  if (!zncharcheck(G, chi)) pari_err_TYPE("zncharisodd", chi);
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  N = bid_get_ideal(G);
  l = lg(chi);
  s = 0;
  if (!mod8(N))
  {
    s = mpodd(gel(chi,1));
    i = 3;
  }
  else
    i = 1;
  for (; i < l; i++) s += mpodd(gel(chi,i));
  return odd(s);
}

GEN
znchartokronecker(GEN G, GEN chi, long flag)
{
  pari_sp av = avma;
  long s;
  GEN F, o;

  if (flag && flag != 1) pari_err_FLAG("znchartokronecker");
  s = zncharisodd(G, chi)? -1: 1;
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  o = zncharorder(G, chi);
  if (cmpiu(o,2) > 0) { avma = av; return gen_0; }
  F = znconreyconductor(G, chi, NULL);
  if (typ(F) == t_INT)
  {
    if (s < 0) F = negi(F);
    return gerepileuptoint(av, F);
  }
  F = gel(F,1);
  F = (s < 0)? negi(F): icopy(F);
  if (!flag)
  {
    GEN MF = bid_get_fact(G), P = gel(MF,1);
    long i, l = lg(P);
    for (i = 1; i < l; i++)
    {
      GEN p = gel(P,i);
      if (!dvdii(F,p)) F = mulii(F,sqri(p));
    }
  }
  return gerepileuptoint(av, F);
}

/* G a bidZ, not stack clean */
GEN
znchareval(GEN G, GEN chi, GEN n, GEN z)
{
  GEN nchi, N = bid_get_ideal(G);
  /* avoid division by 0 */
  if (typ(n) == t_FRAC && !equali1(gcdii(gel(n,2), N))) return not_coprime(z);
  n = Rg_to_Fp(n, N);
  if (!equali1(gcdii(n, N))) return not_coprime(z);
  /* nchi: normalized character on Conrey generators */
  nchi = znconrey_normalized(G, chi);
  return chareval_i(nchi, znconreylog(G,n), z);
}

/* G is a bidZ, chi a Dirichlet character */
GEN
zncharconj(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: chi = znconreylog(G, chi); /* fall through */
    case t_COL: return charconj(bidZ_get_cycg(G), chi);
    case t_VEC: return charconj(bid_get_cyc(G), chi);
  }
  pari_err_TYPE("zncharconj",chi);
  return NULL; /*not reached*/
}

/* G is a bidZ, chi a Dirichlet character */
GEN
zncharorder(GEN G,  GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: chi = znconreylog(G, chi); /*fall through*/
    case t_COL: return charorder(bidZ_get_cycg(G), chi);
    case t_VEC: return charorder(bid_get_cyc(G), chi);
    default: pari_err_TYPE("zncharorder",chi);
             return NULL; /* not reached */
  }
}

/* G is a bidZ, chi a Dirichlet character */
GEN
zncharker(GEN G, GEN chi)
{
  if (typ(chi) != t_VEC) chi = znconreychar(G, chi);
  return charker(bid_get_cyc(G), chi);
}

/* G is a bidZ, 'a' and 'b' are Dirichlet character */
GEN
zncharmul(GEN G, GEN a, GEN b)
{
  long ta = typ(a), tb = typ(b);
  if (ta == tb) switch(ta)
  {
    case t_INT: return Fp_mul(a, b, bid_get_ideal(G));
    case t_VEC: return charmul(bid_get_cyc(G), a, b);
    case t_COL: return charmul(bidZ_get_cycg(G), a, b);
    default: pari_err_TYPE("zncharmul",a);
             return NULL; /* not reached */
  }
  if (ta != t_COL) a = znconreylog(G, a);
  if (tb != t_COL) b = znconreylog(G, b);
  return charmul(bidZ_get_cycg(G), a, b);
}

/* G is a bidZ, 'a' and 'b' are Dirichlet character */
GEN
znchardiv(GEN G, GEN a, GEN b)
{
  long ta = typ(a), tb = typ(b);
  if (ta == tb) switch(ta)
  {
    case t_INT: return Fp_div(a, b, bid_get_ideal(G));
    case t_VEC: return chardiv(bid_get_cyc(G), a, b);
    case t_COL: return chardiv(bidZ_get_cycg(G), a, b);
    default: pari_err_TYPE("znchardiv",a);
             return NULL; /* not reached */
  }
  if (ta != t_COL) a = znconreylog(G, a);
  if (tb != t_COL) b = znconreylog(G, b);
  return chardiv(bidZ_get_cycg(G), a, b);
}
