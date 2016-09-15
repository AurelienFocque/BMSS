/* Copyright (C) 2015  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**                 L-functions: Applications                      **/
/**                                                                **/
/********************************************************************/

#include "pari.h"
#include "paripriv.h"

static GEN
tag(GEN x, long t) { return mkvec2(mkvecsmall(t), x); }

/* v a t_VEC of length > 1 */
static int
is_tagged(GEN v)
{
  GEN T = gel(v,1);
  return (lg(T)==3 && typ(gel(T,1))==t_VECSMALL);
}
static void
checkldata(GEN ldata)
{
  GEN vga, w, N;
#if 0 /* assumed already checked and true */
  long l = lg(ldata);
  if (typ(ldata)!=t_VEC || l < 7 || l > 8 || !is_tagged(ldata))
    pari_err_TYPE("checkldata", ldata);
#endif
  vga = ldata_get_gammavec(ldata);
  if (typ(vga) != t_VEC) pari_err_TYPE("checkldata [gammavec]",vga);
  w = gel(ldata, 4); /* FIXME */
  if (typ(w) != t_INT) pari_err_TYPE("checkldata [weight]",w);
  N = ldata_get_conductor(ldata);
  if (typ(N) != t_INT) pari_err_TYPE("checkldata [conductor]",N);
}

/* data may be either an object (polynomial, elliptic curve, etc...)
 * or a description vector [an,sd,Vga,k,conductor,rootno,{poles}]. */
GEN
lfuncreate(GEN data)
{
  long lx = lg(data);
  if (typ(data)==t_VEC && (lx == 7 || lx == 8))
  {
    GEN ldata;
    if (is_tagged(data)) ldata = gcopy(data);
    else
    { /* tag first component as t_LFUN_GENERIC */
      ldata = gcopy(data);
      gel(ldata, 1) = tag(gel(ldata,1), t_LFUN_GENERIC);
      if (typ(gel(ldata, 2))!=t_INT)
        gel(ldata, 2) = tag(gel(ldata,2), t_LFUN_GENERIC);
    }
    checkldata(ldata); return ldata;
  }
  return lfunmisc_to_ldata(data);
}

/********************************************************************/
/**                     Simple constructors                        **/
/********************************************************************/

static GEN
vecan_conj(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  return gconj(p1);
}

static GEN
vecan_mul(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  return dirmul(p1, p2);
}

static GEN
lfunconvol(GEN a1, GEN a2)
{ return tag(mkvec2(a1, a2), t_LFUN_MUL); }

static GEN
vecan_div(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  return dirdiv(p1, p2);
}

static GEN
lfunconvolinv(GEN a1, GEN a2)
{ return tag(mkvec2(a1,a2), t_LFUN_DIV); }

static GEN
lfunconj(GEN a1)
{ return tag(mkvec(a1), t_LFUN_CONJ); }

static GEN
lfuncombdual(GEN fun(GEN, GEN), GEN ldata1, GEN ldata2)
{
  GEN a1 = ldata_get_an(ldata1), a2 = ldata_get_an(ldata2);
  GEN b1 = ldata_get_dual(ldata1), b2 = ldata_get_dual(ldata2);
  if (typ(b1)==t_INT && typ(b2)==t_INT)
    return utoi(signe(b1) && signe(b2));
  else
  {
    if (typ(b1)==t_INT) b1 = signe(b1) ? lfunconj(a1): a1;
    if (typ(b2)==t_INT) b2 = signe(b2) ? lfunconj(a2): a2;
    return fun(b1, b2);
  }
}

static GEN
lfunmulpoles(GEN ldata1, GEN ldata2, long bitprec)
{
  long k = ldata_get_k(ldata1), l, j;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1)
  {
    if (!r2) return NULL;
    r1 = lfunrtopoles(r2);
  }
  else
  {
    r1 = lfunrtopoles(r1);
    if (r2) r1 = setunion(r1, lfunrtopoles(r2));
  }
  l = lg(r1); r = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z1 = lfun(ldata1,be,bitprec), z2 = lfun(ldata2,be,bitprec);
    if (typ(z1) == t_SER && typ(z2) == t_SER)
    { /* pole of both, recompute to needed seriesprecision */
      long e = valp(z1) + valp(z2);
      GEN b = RgX_to_ser(deg1pol_shallow(gen_1, be, 0), 3-e);
      z1 = lfun(ldata1,b,bitprec);
      z2 = lfun(ldata2,b,bitprec);
    }
    gel(r,j) = mkvec2(be, gmul(z1, z2));
  }
  return r;
}

GEN
lfunmul(GEN ldata1, GEN ldata2, long bitprec)
{
  pari_sp ltop = avma;
  GEN r, N, Vga, eno, a1a2, b1b2, LD;
  long k;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfunmul [weight]",ldata1, ldata2);
  r = lfunmulpoles(ldata1, ldata2, bitprec);
  N = gmul(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  Vga = vecsort0(gconcat(ldata_get_gammavec(ldata1), ldata_get_gammavec(ldata2)), NULL, 0);
  eno = gmul(ldata_get_rootno(ldata1), ldata_get_rootno(ldata2));
  a1a2 = lfunconvol(ldata_get_an(ldata1), ldata_get_an(ldata2));
  b1b2 = lfuncombdual(lfunconvol, ldata1, ldata2);
  LD = mkvecn(7, a1a2, b1b2, Vga, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

static GEN
lfundivpoles(GEN ldata1, GEN ldata2, long bitprec)
{
  long k = ldata_get_k(ldata1), i, j, l;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1) return NULL;
  r1 = lfunrtopoles(r1);
  l = lg(r1); r = cgetg(l, t_VEC);
  r = cgetg(l, t_VEC);
  for (i = j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z = gdiv(lfun(ldata1,be,bitprec), lfun(ldata2,be,bitprec));
    if (valp(z) < 0) gel(r,i++) = mkvec2(be, z);
  }
  if (i == 1) return NULL;
  setlg(r, i); return r;
}

GEN
lfundiv(GEN ldata1, GEN ldata2, long bitprec)
{
  pari_sp ltop = avma;
  GEN r, N, v, v1, v2, eno, a1a2, b1b2, LD;
  long k, j, j1, j2, l1, l2;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfundiv [weight]",ldata1, ldata2);
  r = lfundivpoles(ldata1, ldata2, bitprec);
  N = gdiv(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  if (typ(N) != t_INT) pari_err_OP("lfundiv [conductor]",ldata1, ldata2);
  a1a2 = lfunconvolinv(ldata_get_an(ldata1), ldata_get_an(ldata2));
  b1b2 = lfuncombdual(lfunconvolinv, ldata1, ldata2);
  eno = gdiv(ldata_get_rootno(ldata1), ldata_get_rootno(ldata2));
  v1 = shallowcopy(ldata_get_gammavec(ldata1));
  v2 = ldata_get_gammavec(ldata2);
  l1 = lg(v1); l2 = lg(v2);
  for (j2 = 1; j2 < l2; j2++)
  {
    for (j1 = 1; j1 < l1; j1++)
      if (gel(v1,j1) && gequal(gel(v1,j1), gel(v2,j2)))
      {
        gel(v1,j1) = NULL; break;
      }
    if (j1 == l1) pari_err_OP("lfundiv [Vga]",ldata1, ldata2);
  }
  v = cgetg(l1-l2+1, t_VEC);
  for (j1 = j = 1; j1 < l1; j1++)
    if (gel(v1, j1)) gel(v,j++) = gel(v1,j1);

  LD = mkvecn(7, a1a2, b1b2, v, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

/*****************************************************************/
/*  L-series from closure                                        */
/*****************************************************************/
static GEN
localfactor(void *E, GEN p)
{
  GEN v = (GEN)E, L = gel(v,1), a = gel(v,2);
  return ginv(closure_callgen2(a, p, stoi(logint(L, p))));
}
static GEN
vecan_closure(GEN a, long L, GEN Sbad)
{
  long ta = typ(a), la, tv;
  GEN v;

  if (ta == t_CLOSURE) switch(closure_arity(a))
  {
    GEN gL;
    case 2:
      gL = stoi(L);
      return direuler_bad((void*)mkvec2(gL,a), localfactor, gen_2, gL,gL, Sbad);
    case 1:
      a = closure_callgen1(a, stoi(L));
      if (typ(a) != t_VEC) pari_err_TYPE("vecan_closure", a);
      return a;
    default: pari_err_TYPE("vecan_closure [wrong arity]", a);
  }
  la = lg(a);
  if (ta != t_VEC || la == 1) pari_err_TYPE("vecan_closure", a);
  v = gel(a,1); tv = typ(v);
  /* regular vector, return it */
  if (tv != t_CLOSURE && tv != t_VEC) return vecslice(a, 1, minss(L,la-1));
  /* vector [an, [p1, 1/L_{p1}], ..., [pk, 1/L_{pk}}]]: exceptional primes */
  if (la > 1) Sbad = vecslice(a, 2, la-1);
  return vecan_closure(v, L, Sbad);
}

/*****************************************************************/
/*  L-series of Dirichlet characters.                            */
/*****************************************************************/

static GEN
lfunzeta(void)
{
  GEN zet = mkvecn(7, NULL, gen_0, NULL, gen_1, gen_1, gen_1, gen_1);
  gel(zet,1) = tag(gen_1, t_LFUN_ZETA);
  gel(zet,3) = mkvec(gen_0);
  return zet;
}
static GEN
lfunzetainit(GEN dom, long der, long bitprec)
{ return lfuninit(lfunzeta(), dom, der, bitprec); }

static GEN
vecan_Kronecker(GEN D, long n)
{
  GEN v = cgetg(n+1, t_VEC);
  ulong Du = itou_or_0(D);
  long i, id, d = Du ? minuu(Du, n): n;
  for (i = 1; i <= d; i++) switch(krois(D,i))
  {
    case 1:  gel(v,i) = gen_1; break;
    case -1: gel(v,i) = gen_m1; break;
    default: gel(v,i) = gen_0; break;
  }
  for (id = i; i <= n; i++,id++) /* periodic mod d */
  {
    if (id > d) id = 1;
    gel(v, i) = gel(v, id);
  }
  return v;
}

static GEN
lfunchiquad(GEN D)
{
  GEN r;
  if (equali1(D)) return lfunzeta();
  if (!isfundamental(D)) pari_err_TYPE("lfunchiquad [not primitive]", D);
  r = mkvecn(6, NULL, gen_0, NULL, gen_1, NULL, gen_1);
  gel(r,1) = tag(icopy(D), t_LFUN_KRONECKER);
  gel(r,3) = mkvec(signe(D) < 0? gen_1: gen_0);
  gel(r,5) = mpabs(D);
  return r;
}

/* Begin Hecke characters. Here a character is assumed to be given by a
   vector on the generators of the ray class group clgp of CL_m(K).
   If clgp = [h,[d1,...,dk],[g1,...,gk]] with dk|...|d2|d1, a character chi
   is given by [a1,a2,...,ak] such that chi(gi)=\zeta_di^ai. */

/* Value of CHI on x, coprime to bnr.mod */
static GEN
chigeneval(GEN logx, GEN nchi, GEN z, long prec)
{
  pari_sp av = avma;
  GEN d = gel(nchi,1);
  GEN e = FpV_dotproduct(gel(nchi,2), logx, d);
  if (typ(z) != t_VEC)
    return gerepileupto(av, gpow(z, e, prec));
  else
  {
    ulong i = itou(e);
    avma = av; return gel(z, i+1);
  }
}

/* return x + yz; y != 0; z = 0,1 "often"; x = 0 "often" */
static GEN
gaddmul(GEN x, GEN y, GEN z)
{
  pari_sp av;
  if (typ(z) == t_INT)
  {
    if (!signe(z)) return x;
    if (equali1(z)) return gadd(x,y);
  }
  if (isintzero(x)) return gmul(y,z);
  av = avma;
  return gerepileupto(av, gadd(x, gmul(y,z)));
}

static GEN
vecan_chiZ(GEN an, long n, long prec)
{
  forprime_t iter;
  GEN bid = gel(an,1);
  GEN nchi = gel(an,2), gord = gel(nchi,1), z;
  GEN gp = cgetipos(3), v = vec_ei(n, 1);
  GEN N = bid_get_ideal(bid);
  long ord = itos_or_0(gord);
  ulong Nu = itou_or_0(N);
  long i, id, d = Nu ? minuu(Nu, n): n;
  ulong p;

  if (ord && n > (ord>>4))
    z = grootsof1(ord, prec);
  else
    z = char_rootof1(gord, prec);

  u_forprime_init(&iter, 2, d);
  while ((p = u_forprime_next(&iter)))
  {
    GEN ch;
    ulong k;
    if (!umodiu(N,p)) continue;
    gp[2] = p;
    ch = chigeneval(znconreylog(bid, gp), nchi, z, prec);
    gel(v, p)  = ch;
    for (k = 2*p; k <= (ulong)d; k += p)
      gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/p));
  }
  for (id = i = d+1; i <= n; i++,id++) /* periodic mod d */
  {
    if (id > d) id = 1;
    gel(v, i) = gel(v, id);
  }
  return v;
}

static GEN
vecan_chigen(GEN an, long n, long prec)
{
  forprime_t iter;
  GEN bnr = gel(an,1), nf = bnr_get_nf(bnr);
  GEN nchi = gel(an,2), gord = gel(nchi,1), z;
  GEN gp = cgetipos(3), v = vec_ei(n, 1);
  GEN N = gel(bnr_get_mod(bnr), 1), NZ = gcoeff(N,1,1);
  long ord = itos_or_0(gord);
  ulong p;

  if (ord && n > (ord>>4))
    z = grootsof1(ord, prec);
  else
    z = char_rootof1(gord, prec);

  if (nf_get_degree(nf) == 1)
  {
    ulong Nu = itou_or_0(NZ);
    long i, id, d = Nu ? minuu(Nu, n): n;
    u_forprime_init(&iter, 2, d);
    while ((p = u_forprime_next(&iter)))
    {
      GEN ch;
      ulong k;
      if (!umodiu(NZ,p)) continue;
      gp[2] = p;
      ch = chigeneval(isprincipalray(bnr,gp), nchi, z, prec);
      gel(v, p)  = ch;
      for (k = 2*p; k <= (ulong)d; k += p)
        gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/p));
    }
    for (id = i = d+1; i <= n; i++,id++) /* periodic mod d */
    {
      if (id > d) id = 1;
      gel(v, i) = gel(v, id);
    }
  }
  else
  {
    GEN BOUND = stoi(n);
    u_forprime_init(&iter, 2, n);
    while ((p = u_forprime_next(&iter)))
    {
      GEN L;
      long j;
      int check = !umodiu(NZ,p);
      gp[2] = p;
      L = idealprimedec_limit_norm(nf, gp, BOUND);
      for (j = 1; j < lg(L); j++)
      {
        GEN pr = gel(L, j), ch;
        ulong k, q;
        if (check && idealval(nf, N, pr)) continue;
        ch = chigeneval(isprincipalray(bnr,pr), nchi, z, prec);
        q = upr_norm(pr);
        gel(v, q) = gadd(gel(v, q), ch);
        for (k = 2*q; k <= (ulong)n; k += q)
          gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/q));
      }
    }
  }
  return v;
}

static GEN lfunzetak_i(GEN T);
static GEN
vec01(long r1, long r2)
{
  long d = r1+r2, i;
  GEN v = cgetg(d+1,t_VEC);
  for (i = 1; i <= r1; i++) gel(v,i) = gen_0;
  for (     ; i <= d;  i++) gel(v,i) = gen_1;
  return v;
}

/* bid has nftyp typ_BID */
static GEN
lfunchiZ(GEN bid, GEN chi)
{
  pari_sp av = avma;
  GEN sig = NULL;
  GEN N = bid_get_ideal(bid), nchi, r;
  int real;

  if (typ(N) != t_INT) pari_err_TYPE("lfunchiZ", bid);
  if (equali1(N)) return lfunzeta();
  if (typ(chi) != t_COL) chi = znconreylog(bid,chi);
  N = znconreyconductor(bid, chi, &chi);
  if (typ(N) != t_INT)
  {
    if (equali1(gel(N,1))) { avma = av; return lfunzeta(); }
    bid = ZNstar(N, nf_INIT);
    N = gel(N,1);
  }
  /* chi now primitive on bid */
  sig = mkvec( zncharisodd(bid, chi)? gen_1: gen_0 );
  nchi = znconreylog_normalize(bid, chi);
  real = abscmpiu(gel(nchi,1), 2) <= 0;
  r = mkvecn(6, tag(mkvec2(bid,nchi), t_LFUN_CHIZ),
                real? gen_0: gen_1, sig, gen_1, N, gen_0);
  return gerepilecopy(av, r);
}

static GEN
lfunchigen(GEN bnr, GEN CHI)
{
  pari_sp av = avma;
  GEN v;
  GEN N, sig, Ldchi, nf, nchi, NN;
  long r1, r2, n1;
  int real;

  if (nftyp(bnr) == typ_BID) return lfunchiZ(bnr, CHI);

  v = bnrconductor_i(bnr, CHI, 2);
  bnr = gel(v,2);
  CHI = gel(v,3); /* now CHI is primitive wrt bnr */

  nf = bnr_get_nf(bnr);
  N = bnr_get_mod(bnr);
  n1 = lg(vec01_to_indices(gel(N,2))) - 1; /* vecsum(N[2]) */
  N = gel(N,1);
  NN = mulii(idealnorm(nf, N), absi(nf_get_disc(nf)));
  if (equali1(NN)) return gerepileupto(av, lfunzeta());
  if (ZV_equal0(CHI)) return gerepilecopy(av, lfunzetak_i(bnr));
  nf_get_sign(nf, &r1, &r2);
  sig = vec01(r1+r2-n1, r2+n1);
  nchi = char_normalize(CHI, cyc_normalize(bnr_get_cyc(bnr)));
  real = abscmpiu(gel(nchi,1), 2) <= 0;
  Ldchi = mkvecn(6, tag(mkvec2(bnr, nchi), t_LFUN_CHIGEN),
                    real? gen_0: gen_1, sig, gen_1, NN, gen_0);
  return gerepilecopy(av, Ldchi);
}

/* Find all characters of clgp whose kernel contain group given by HNF H.
 * Set *pcnj[i] if chi[i] is not real */
static GEN
chigenkerfind(GEN bnr, GEN H, GEN *pcnj)
{
  GEN res, cnj, L = bnrchar(bnr, H, NULL), cyc = bnr_get_cyc(bnr);
  long i, k, l = lg(L);

  res = cgetg(l, t_VEC);
  *pcnj = cnj = cgetg(l, t_VECSMALL);
  for (i = k = 1; i < l; i++)
  {
    GEN chi = gel(L,i), c = charconj(cyc, chi);
    long fl = ZV_cmp(c, chi);
    if (fl < 0) continue; /* keep one char in pair of conjugates */
    gel(res, k) = chi;
    cnj[k] = fl; k++;
  }
  setlg(cnj, k);
  setlg(res, k); return res;
}

static GEN
lfunzetak_i(GEN T)
{
  GEN Vga, N, nf, bnf = checkbnf_i(T), r = gen_0/*unknown*/;
  long r1, r2;

  if (bnf)
    nf = bnf_get_nf(bnf);
  else
  {
    nf = checknf_i(T);
    if (!nf) nf = T = nfinit(T, DEFAULTPREC);
  }
  nf_get_sign(nf,&r1,&r2);
  N = absi(nf_get_disc(nf));
  if (bnf)
  {
    GEN h = bnf_get_no(bnf);
    GEN R = bnf_get_reg(bnf);
    long prec = nf_get_prec(nf);
    r = gdiv(gmul(mulir(shifti(h, r1+r2), powru(mppi(prec), r2)), R),
             mulur(bnf_get_tuN(bnf), gsqrt(N, prec)));
  }
  Vga = vec01(r1+r2,r2);
  return mkvecn(7, tag(T,t_LFUN_NF), gen_0, Vga, gen_1, N, gen_1, r);
}
static GEN
lfunzetak(GEN T)
{ pari_sp ltop = avma; return gerepilecopy(ltop, lfunzetak_i(T)); }

/* bnf = NULL: base field = Q */
GEN
lfunabelianrelinit(GEN nfabs, GEN bnf, GEN polrel, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN cond, chi, cnj, res, bnr, M, domain;
  long l, i;
  long v = -1;

  if (bnf) bnf = checkbnf(bnf);
  else
  {
    v = fetch_var();
    bnf = Buchall(pol_x(v), 0, nbits2prec(bitprec));
  }
  if (typ(polrel) != t_POL) pari_err_TYPE("lfunabelianrelinit", polrel);
  cond = rnfconductor(bnf, polrel);
  chi = chigenkerfind(gel(cond,2), gel(cond,3), &cnj);
  bnr = Buchray(bnf, gel(cond,1), nf_INIT|nf_GEN);
  l = lg(chi); res = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
  {
    GEN L = lfunchigen(bnr, gel(chi,i));
    gel(res, i) = lfuninit(L, dom, der, bitprec);
  }
  if (v >= 0) delete_var();
  M = mkvec3(res, const_vecsmall(l-1, 1), cnj);
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(ltop, lfuninit_make(t_LDESC_PRODUCT, lfunzetak_i(nfabs), M, domain));
}

/*****************************************************************/
/*                 Dedekind zeta functions                       */
/*****************************************************************/
static GEN
dirzetak0(GEN nf, ulong N)
{
  GEN vect, c, c2, T = nf_get_pol(nf), index = nf_get_index(nf);
  pari_sp av = avma, av2;
  const ulong SQRTN = usqrt(N);
  ulong i, p, lx;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  forprime_t S;

  (void)evallg(N+1);
  c  = cgetalloc(t_VECSMALL, N+1);
  c2 = cgetalloc(t_VECSMALL, N+1);
  c2[1] = c[1] = 1; for (i=2; i<=N; i++) c[i] = 0;
  u_forprime_init(&S, 2, N);
  av2 = avma;
  while ( (p = u_forprime_next(&S)) )
  {
    avma = av2;
    if (umodiu(index, p)) /* p does not divide index */
    {
      vect = gel(Flx_degfact(ZX_to_Flx(T,p), p),1);
      lx = lg(vect);
    }
    else
    {
      GEN P;
      court[2] = p; P = idealprimedec(nf,court);
      lx = lg(P); vect = cgetg(lx,t_VECSMALL);
      for (i=1; i<lx; i++) vect[i] = pr_get_f(gel(P,i));
    }
    if (p <= SQRTN)
      for (i=1; i<lx; i++)
      {
        ulong qn, q = upowuu(p, vect[i]); /* Norm P[i] */
        if (!q || q > N) break;
        memcpy(c2 + 2, c + 2, (N-1)*sizeof(long));
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (qn = q; qn <= N; qn *= q)
        {
          ulong k0 = N/qn, k, k2; /* k2 = k*qn */
          for (k = k0, k2 = k*qn; k > 0; k--, k2 -=qn) c2[k2] += c[k];
          if (q > k0) break; /* <=> q*qn > N */
        }
        swap(c, c2);
      }
    else /* p > sqrt(N): simpler */
      for (i=1; i<lx; i++)
      {
        ulong k, k2; /* k2 = k*p */
        if (vect[i] > 1) break;
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (k = N/p, k2 = k*p; k > 0; k--, k2 -= p) c[k2] += c[k];
      }
  }
  avma = av;
  pari_free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z, c;
  long n;

  if (typ(b) != t_INT) pari_err_TYPE("dirzetak",b);
  if (signe(b) <= 0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  n = itou_or_0(b); if (!n) pari_err_OVERFLOW("dirzetak");
  c = dirzetak0(nf, n);
  z = vecsmall_to_vec(c); pari_free(c); return z;
}

static GEN
linit_get_mat(GEN linit)
{
  if (linit_get_type(linit)==t_LDESC_PRODUCT)
    return lfunprod_get_fact(linit_get_tech(linit));
  else
    return mkvec3(mkvec(linit), mkvecsmall(1), mkvecsmall(0));
}

static GEN
lfunproduct(GEN ldata, GEN linit1, GEN linit2, GEN domain)
{
  GEN M1 = linit_get_mat(linit1);
  GEN M2 = linit_get_mat(linit2);
  GEN M3 = mkvec3(shallowconcat(gel(M1, 1), gel(M2, 1)),
                  vecsmall_concat(gel(M1, 2), gel(M2, 2)),
                  vecsmall_concat(gel(M1, 3), gel(M2, 3)));
  return lfuninit_make(t_LDESC_PRODUCT, ldata, M3, domain);
}

static GEN
lfunzetakinit_raw(GEN T, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN ldata = lfunzetak_i(T);
  return gerepileupto(ltop, lfuninit(ldata, dom, der, bitprec));
}

static GEN
lfunzetakinit_quotient(GEN nf, GEN polk, GEN dom, long der, long bitprec)
{
  pari_sp av = avma;
  GEN ak, an, nfk, Vga, ldata, N, Lk, LKk, domain;
  long r1k, r2k, r1, r2;

  nf_get_sign(nf,&r1,&r2);
  nfk = nfinit(polk, nbits2prec(bitprec));
  Lk = lfunzetakinit(nfk, dom, der, 0, bitprec); /* zeta_k */
  nf_get_sign(nfk,&r1k,&r2k);
  Vga = vec01((r1+r2) - (r1k+r2k), r2-r2k);
  N = absi(diviiexact(nf_get_disc(nf), nf_get_disc(nfk)));
  ak = nf_get_degree(nf)==1 ? tag(gen_1, t_LFUN_ZETA): tag(nfk, t_LFUN_NF);
  an = tag(mkvec2(tag(nf,t_LFUN_NF), ak), t_LFUN_DIV);
  ldata = mkvecn(6, an, gen_0, Vga, gen_1, N, gen_1);
  LKk = lfuninit(ldata, dom, der, bitprec); /* zeta_K/zeta_k */
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(av, lfunproduct(lfunzetak_i(nf), Lk, LKk, domain));
}

static GEN
subgroups_largestabelian(GEN S)
{
  long i, n = 0, l = lg (S);
  GEN M = NULL;
  for(i = 1; i < l; i++)
  {
    GEN Si = gel(S,i);
    long o = group_order(Si);
    if (o > n && group_isabelian(Si))
    {
      n = o;
      M = Si;
    }
  }
  return M;
}


/* If flag=0 (default), assume Artin conjecture */

static GEN
lfunzetakinit_Galois(GEN nf, GEN G, GEN dom, long der, long bitprec)
{
  GEN S, H, P, F, R, bnf;
  GEN T = nf_get_pol(nf);
  long v = varn(T);
  GEN grp = galois_group(G);
  if (group_isabelian(grp))
    return lfunabelianrelinit(nf, NULL, T, dom, der, bitprec);
  S = group_subgroups(grp);
  H = subgroups_largestabelian(S);
  if (v==0) { v=1; nf = gsubst(nf, 0, pol_x(v)); }
  else G = gsubst(G, v, pol_x(0));
  F = galoisfixedfield(G, H, 2, v);
  P = gel(F,1), R = gmael(F,3,1);
  setvarn(P, v);
  bnf = Buchall(P, 0, nbits2prec(bitprec));
  return lfunabelianrelinit(nf, bnf, R, dom, der, bitprec);
}

GEN
lfunzetakinit(GEN NF, GEN dom, long der, long flag, long bitprec)
{
  GEN nf = checknf(NF);
  GEN G, nfs, sbg;
  long lf, d = nf_get_degree(nf);
  if (d == 1) return lfunzetainit(dom, der, bitprec);
  G = galoisinit(nf, NULL);
  if (!isintzero(G))
    return lfunzetakinit_Galois(nf, G, dom, der, bitprec);
  nfs = nfsubfields(nf, 0); lf = lg(nfs)-1;
  sbg = gmael(nfs,lf-1,1);
  if (flag && d > 4*degpol(sbg))
    return lfunzetakinit_raw(nf, dom, der, bitprec);
  return lfunzetakinit_quotient(nf, sbg, dom, der, bitprec);
}

/***************************************************************/
/*             Elliptic Curves and Modular Forms               */
/***************************************************************/

static GEN
ellnf_get_normN(GEN e)
{
  GEN D = ell_get_disc(e), nf = ellnf_get_nf(e);
  GEN V, F = gel(idealfactor(nf,D),1);
  long i, l = lg(F);
  V = cgetg(l, t_VEC);
  for(i = 1; i < l; i++)
  {
    GEN P = gel(F,i), L = elllocalred(e,P);
    gel(V,i) = powii(pr_norm(P), gel(L,1));
  }
  return ZV_prod(V);
}

static GEN
lfunellnf(GEN e)
{
  pari_sp av = avma;
  GEN ldata;
  GEN nf = ellnf_get_nf(e);
  GEN d2, N;
  long n;
  d2 = sqri(nf_get_disc(nf));
  n = nf_get_degree(nf);
  N = ellnf_get_normN(e);
  ldata = cgetg(7, t_VEC);
  gel(ldata, 1) = tag(e, t_LFUN_ELL);
  gel(ldata, 2) = gen_0;
  gel(ldata, 3) = vec01(n, n);
  gel(ldata, 4) = gen_2;
  gel(ldata, 5) = mulii(d2,N);
  gel(ldata, 6) = gen_0;
  return gerepileupto(av, ldata);
}

static GEN
lfunellQ(GEN e)
{
  pari_sp av = avma;
  GEN ldata = cgetg(7, t_VEC);
  gel(ldata, 1) = tag(ellanal_globalred(e, NULL), t_LFUN_ELL);
  gel(ldata, 2) = gen_0;
  gel(ldata, 3) = mkvec2(gen_0, gen_1);
  gel(ldata, 4) = gen_2;
  gel(ldata, 5) = icopy(ellQ_get_N(e));
  gel(ldata, 6) = stoi(ellrootno_global(e));
  return gerepilecopy(av, ldata); /* ellanal_globalred not gerepile-safe */
}

static GEN
lfunell(GEN e)
{
  long t = ell_get_type(e);
  switch(t)
  {
    case t_ELL_Q:
      return lfunellQ(e);
    case t_ELL_NF:
      return lfunellnf(e);
  }
  pari_err_TYPE("lfun",e);
  return NULL; /*NOT REACHED*/
}

GEN
lfunmfspec(GEN lmisc, long bitprec)
{
  pari_sp ltop = avma;
  GEN Vga, linit, ldataf, veven, vodd, om, op, eps, dom;
  long k, k2, j;

  ldataf = lfunmisc_to_ldata_shallow(lmisc);
  k = ldata_get_k(ldataf);
  dom = mkvec3(dbltor(k/2.), dbltor((k-2)/2.), gen_0);
  if (is_linit(lmisc) && linit_get_type(lmisc) == t_LDESC_INIT
      && sdomain_isincl(k, dom, lfun_get_dom(linit_get_tech(lmisc))))
    linit = lmisc;
  else
    linit = lfuninit(ldataf, dom, 0, bitprec);
  Vga = ldata_get_gammavec(ldataf);
  if (!ldata_isreal(ldataf) || !gequal(Vga, mkvec2(gen_0,gen_1)))
    pari_err_TYPE("lfunmfspec", lmisc);
  if (odd(k)) pari_err_IMPL("odd weight in lfunmfspec");
  k2 = k/2;
  vodd = cgetg(k2+1, t_VEC);
  veven = cgetg(k2, t_VEC);
  for (j=1; j <= k2; ++j) gel(vodd,j) = lfunlambda(linit, stoi(2*j-1), bitprec);
  for (j=1; j < k2; ++j) gel(veven,j) = lfunlambda(linit, stoi(2*j), bitprec);
  if (k > 2)
  {
    om = gel(veven,1);
    veven = gdiv(veven, om);
    op = gel(vodd,2);
  }
  else
  { /* veven empty */
    om = gen_1;
    op = gel(vodd,1);
  }
  vodd = gdiv(vodd, op);
  eps = int2n(bitprec/4);
  veven= bestappr(veven, eps);
  vodd = bestappr(vodd, eps);
  return gerepilecopy(ltop, mkvec4(veven, vodd, om, op));
}

static long
ellsymsq_bad2(GEN c4, GEN c6, long e, long *pb2)
{
  switch (e)
  {
    case 2: *pb2 = 1; return 1;
    case 3: *pb2 = 2; return 0;
    case 5: *pb2 = 3; return 0;
    case 7: *pb2 = 4; return 0;
    case 8:
      if (dvdiu(c6,512)) { *pb2 = 4; return 0; }
      *pb2 = 3; return umodiu(c4,128)==32 ? 1 : -1;
    default: *pb2 = 0; return 0;
  }
}
static long
ellsymsq_bad3(GEN c4, GEN c6, long e, long *pb3)
{
  long c6_243, c4_81;
  switch (e)
  {
    case 2: *pb3 = 1; return 1;
    case 3: *pb3 = 2; return 0;
    case 5: *pb3 = 3; return 0;
    case 4: *pb3 = 2;
      c4_81 = umodiu(c4,81);
      if (c4_81 == 27) return -1;
      if (c4_81%27 != 9) return 1;
      c6_243 = umodiu(c6,243);
      return (c6_243==108 || c6_243==135)? -1: 1;
    default: *pb3 = 0; return 0;
  }
}
static int
c4c6_testp(GEN c4, GEN c6, GEN p)
{ GEN p2 = sqri(p); return (dvdii(c6,p2) && !dvdii(c4,p2)); }
/* assume e = v_p(N) >= 2 */
static long
ellsymsq_badp(GEN c4, GEN c6, GEN p, long e, long *pb)
{
  if (absequaliu(p, 2)) return ellsymsq_bad2(c4, c6, e, pb);
  if (absequaliu(p, 3)) return ellsymsq_bad3(c4, c6, e, pb);
  *pb = 1;
  switch(umodiu(p, 12UL))
  {
    case 1: return -1;
    case 5: return c4c6_testp(c4,c6,p)? -1: 1;
    case 7: return c4c6_testp(c4,c6,p)?  1:-1;
    default:return 1; /* p%12 = 11 */
  }
}
static GEN
ellsymsq(void *D, GEN p)
{
  GEN E = (GEN)D;
  GEN T, ap = sqri(ellap(E, p));
  long e = Z_pval(ellQ_get_N(E), p);
  if (e)
  {
    if (e == 1)
      T = deg1pol_shallow(negi(ap),gen_1,0);
    else
    {
      GEN c4 = ell_get_c4(E);
      GEN c6 = ell_get_c6(E);
      long junk, a = ellsymsq_badp(c4, c6, p, e, &junk);
      GEN pb = negi(mulis(p,a));
      GEN u1 = negi(addii(ap,pb));
      GEN u2 = mulii(ap,pb);
      T = mkpoln(3,u2,u1,gen_1);
    }
  }
  else
  {
    GEN u1 = subii(ap,p);
    GEN u2 = mulii(p,u1);
    GEN u3 = powiu(p,3);
    T = mkpoln(4,negi(u3),u2,negi(u1),gen_1);
  }
  return mkrfrac(gen_1,T);
}
static GEN
vecan_ellsymsq(GEN an, long n)
{ GEN nn = stoi(n); return direuler((void*)an, &ellsymsq, gen_2, nn, nn); }

static GEN
lfunellsymsqmintwist(GEN e)
{
  pari_sp av = avma;
  GEN B, N, Nfa, P, E, V, c4, c6, ld;
  long i, l, k;
  checkell_Q(e);
  e = ellminimalmodel(e, NULL);
  ellQ_get_Nfa(e, &N, &Nfa);
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  P = gel(Nfa,1); l = lg(P);
  E = gel(Nfa,2);
  V = cgetg(l, t_VEC);
  B = gen_1;
  for (i=k=1; i<l; i++)
  {
    GEN p = gel(P,i);
    long a, b, e = itos(gel(E,i));
    if (e == 1) { B = mulii(B, p); continue; }
    a = ellsymsq_badp(c4, c6, p, e, &b);
    B = mulii(B, powiu(p, b));
    gel(V,k++) = mkvec2(p, stoi(a));
  }
  setlg(V, k);
  ld = mkvecn(6, tag(e, t_LFUN_SYMSQ_ELL), gen_0,
                 mkvec3(gen_0, gen_0, gen_1), stoi(3), sqri(B), gen_1);
  return gerepilecopy(av, mkvec2(ld, V));
}

static GEN
mfpeters(GEN ldata2, GEN fudge, GEN N, long k, long bitprec)
{
  GEN t, L = greal(lfun(ldata2, stoi(k), bitprec));
  long prec = nbits2prec(bitprec);
  t = powrs(mppi(prec), k+1); shiftr_inplace(t, 2*k-1); /* Pi/2 * (4Pi)^k */
  return gmul(gdiv(gmul(mulii(N,mpfact(k-1)), fudge), t), L);
}

/* Assume E to be twist-minimal */
static GEN
lfunellmfpetersmintwist(GEN E, long bitprec)
{
  pari_sp av = avma;
  GEN symsq, veceuler, N = ellQ_get_N(E), fudge = gen_1;
  long j, k = 2;
  symsq = lfunellsymsqmintwist(E);
  veceuler = gel(symsq,2);
  for (j = 1; j < lg(veceuler); j++)
  {
    GEN v = gel(veceuler,j), p = gel(v,1), q = powis(p,1-k);
    long s = signe(gel(v,2));
    if (s) fudge = gmul(fudge, s==1 ? gaddsg(1, q): gsubsg(1, q));
  }
  return gerepileupto(av, mfpeters(gel(symsq,1),fudge,N,k,bitprec));
}

/* From Christophe Delaunay, http://delaunay.perso.math.cnrs.fr/these.pdf */
static GEN
elldiscfix(GEN E, GEN Et, GEN D)
{
  GEN N = ellQ_get_N(E), Nt = ellQ_get_N(Et);
  GEN P = gel(Z_factor(absi(D)), 1);
  GEN f = gen_1;
  long i, l = lg(P);
  for (i=1; i < l; i++)
  {
    GEN r, p = gel(P,i);
    long v = Z_pval(N, p), vt = Z_pval(Nt, p);
    if (v <= vt) continue;
    /* v > vt */
    if (absequaliu(p, 2))
    {
      if (vt == 0 && v >= 4)
        r = shifti(subsi(9, sqri(ellap(Et, p))), v-3);  /* 9=(2+1)^2 */
      else if (vt == 1)
        r = gmul2n(utoipos(3), v-3);  /* not in Z if v=2 */
      else if (vt >= 2)
        r = int2n(v-vt);
      else
        r = gen_1; /* vt = 0, 1 <= v <= 3 */
    }
    else if (vt >= 1)
      r = gdiv(subis(sqri(p), 1), p);
    else
      r = gdiv(mulii(subis(p, 1), subii(sqri(addis(p, 1)), sqri(ellap(Et, p)))), p);
    f = gmul(f, r);
  }
  return f;
}

GEN
lfunellmfpeters(GEN E, long bitprec)
{
  pari_sp ltop = avma;
  long prec = nbits2prec(bitprec);
  GEN D = ellminimaltwistcond(E);
  GEN Etr = ellinit(elltwist(E, D), NULL, prec);
  GEN Et = ellminimalmodel(Etr, NULL);
  GEN nor = lfunellmfpetersmintwist(Et, bitprec);
  GEN nor2 = gmul(nor, elldiscfix(E, Et, D));
  obj_free(Etr); obj_free(Et);
  return gerepilecopy(ltop, nor2);
}

/*************************************************************/
/*               genus 2 curves                              */
/*************************************************************/

static GEN
dirgenus2(void *E, GEN p)
{
  pari_sp av = avma;
  GEN Q = (GEN) E;
  GEN f = RgX_recip(hyperellcharpoly(gmul(Q,gmodulo(gen_1, p))));
  return gerepileupto(av, ginv(f));
}

static GEN
vecan_genus2(GEN an, long L)
{
  GEN Q = gel(an,1), bad = gel(an, 2);
  return direuler_bad((void*)Q, dirgenus2, gen_2, stoi(L), NULL, bad);
}

static GEN
genus2_redmodel(GEN P, GEN p)
{
  GEN M = FpX_factor(P, p);
  GEN F = gel(M,1), E = gel(M,2);
  long i, k, r = lg(F);
  GEN U = scalarpol(leading_coeff(P), varn(P));
  GEN G = cgetg(r, t_COL);
  for (i=1, k=0; i<r; i++)
  {
    if (E[i]>1)
      gel(G,++k) = gel(F,i);
    if (odd(E[i]))
      U = FpX_mul(U, gel(F,i), p);
  }
  setlg(G,++k);
  return mkvec2(G,U);
}

static GEN
oneminusxd(long d)
{
  return gsub(gen_1, monomial(gen_1, d, 0));
}

static GEN
ellfromeqncharpoly(GEN P, GEN Q, GEN p)
{
  long v;
  GEN E, F, t, y;
  v = fetch_var();
  y = pol_x(v);
  F = gsub(gadd(ZX_sqr(y), gmul(y, Q)), P);
  E = ellinit(ellfromeqn(F), p, DEFAULTPREC);
  delete_var();
  t = ellap(E, p);
  obj_free(E);
  return mkpoln(3, gen_1, negi(t), p);
}

static GEN
genus2_eulerfact(GEN P, GEN p)
{
  pari_sp av = avma;
  GEN Pp = FpX_red(P, p);
  GEN GU = genus2_redmodel(Pp, p);
  long d = 6-degpol(Pp), v = d/2, w = odd(d);
  GEN abe, tor;
  GEN ki, kp = pol_1(0), kq = pol_1(0);
  GEN F = gel(GU,1), Q = gel(GU,2);
  long dQ = degpol(Q), lF = lg(F)-1;

  abe = dQ >= 5 ? RgX_recip(hyperellcharpoly(gmul(Q,gmodulo(gen_1,p))))
      : dQ >= 3 ? RgX_recip(ellfromeqncharpoly(Q,gen_0,p))
                : pol_1(0);
  ki = dQ > 0 ? oneminusxd(1)
              : Fp_issquare(gel(Q,2),p) ? ZX_sqr(oneminusxd(1))
                                        : oneminusxd(2);
  if (lF)
  {
    long i;
    for(i=1; i <= lF; i++)
    {
      GEN Fi = gel(F, i);
      long d = degpol(Fi);
      GEN e = FpX_rem(Q, Fi, p);
      GEN kqf = lgpol(e)==0 ? oneminusxd(d):
                FpXQ_issquare(e, Fi, p) ? ZX_sqr(oneminusxd(d))
                                          : oneminusxd(2*d);
      kp = gmul(kp, oneminusxd(d));
      kq = gmul(kq, kqf);
    }
  }
  if (v)
  {
    GEN kqoo = w==1 ? oneminusxd(1):
               Fp_issquare(leading_coeff(Q), p)? ZX_sqr(oneminusxd(1))
                                              : oneminusxd(2);
    kp = gmul(kp, oneminusxd(1));
    kq = gmul(kq, kqoo);
  }
  tor = RgX_div(ZX_mul(oneminusxd(1), kq), ZX_mul(ki, kp));
  return gerepileupto(av, ZX_mul(abe, tor));
}

static GEN
F2x_genus2_find_trans(GEN P, GEN Q, GEN F)
{
  pari_sp av = avma;
  long i, d = F2x_degree(F), v = P[1];
  GEN M, C, V;
  M = cgetg(d+1, t_MAT);
  for (i=1; i<=d; i++)
  {
    GEN Mi = F2x_rem(F2x_add(F2x_shift(Q,i-1), monomial_F2x(2*i-2,v)), F);
    gel(M,i) = F2x_to_F2v(Mi, d);
  }
  C = F2x_to_F2v(F2x_rem(P, F), d);
  V = F2m_F2c_invimage(M, C);
  return gerepileuptoleaf(av, F2v_to_F2x(V, v));
}

static GEN
F2x_genus2_trans(GEN P, GEN Q, GEN H)
{
  return F2x_add(P,F2x_add(F2x_mul(H,Q), F2x_sqr(H)));
}

static GEN
F2x_genus_redoo(GEN P, GEN Q, long k)
{
  if (F2x_degree(P)==2*k)
  {
    long c = F2x_coeff(P,2*k-1), dQ = F2x_degree(Q);
    if ((dQ==k-1 && c==1) || (dQ<k-1 && c==0))
     return F2x_genus2_trans(P, Q, monomial_F2x(k, P[1]));
  }
  return P;
}

static GEN
F2x_pseudodisc(GEN P, GEN Q)
{
  GEN dP = F2x_deriv(P), dQ = F2x_deriv(Q);
  return F2x_gcd(Q, F2x_add(F2x_mul(P, F2x_sqr(dQ)), F2x_sqr(dP)));
}

static GEN
F2x_genus_red(GEN P, GEN Q)
{
  long dP, dQ;
  GEN F, FF;
  P = F2x_genus_redoo(P, Q, 3);
  P = F2x_genus_redoo(P, Q, 2);
  P = F2x_genus_redoo(P, Q, 1);
  dP = F2x_degree(P);
  dQ = F2x_degree(Q);
  FF = F = F2x_pseudodisc(P,Q);
  while(F2x_degree(F)>0)
  {
    GEN M = gel(F2x_factor(F),1);
    long i, l = lg(M);
    for(i=1; i<l; i++)
    {
      GEN R = F2x_sqr(gel(M,i));
      GEN H = F2x_genus2_find_trans(P, Q, R);
      P = F2x_div(F2x_genus2_trans(P, Q, H), R);
      Q = F2x_div(Q, gel(M,i));
    }
    F = F2x_pseudodisc(P, Q);
  }
  return mkvec4(P,Q,FF,mkvecsmall2(dP,dQ));
}

/* Number of solutions of x^2+b*x+c */
static long
F2xqX_quad_nbroots(GEN b, GEN c, GEN T)
{
  if (lgpol(b) > 0)
  {
    GEN d = F2xq_div(c, F2xq_sqr(b, T), T);
    return F2xq_trace(d, T)? 0: 2;
  }
  else
    return 1;
}

static GEN
genus2_redmodel2(GEN P)
{
  GEN Q = pol_0(varn(P));
  GEN P2 = ZX_to_F2x(P);
  while (F2x_issquare(P2))
  {
    GEN H = F2x_to_ZX(F2x_sqrt(P2));
    GEN P1 = ZX_sub(P, ZX_sqr(H));
    GEN Q1 = ZX_add(Q, ZX_mulu(H, 2));
    if ((signe(P1)==0 ||  ZX_lval(P1,2)>=2)
     && (signe(Q1)==0 ||  ZX_lval(Q1,2)>=1))
    {
      P = ZX_shifti(P1, -2);
      Q = ZX_shifti(Q1, -1);
      P2= ZX_to_F2x(P);
    } else break;
  }
  return mkvec2(P,Q);
}

static GEN
genus2_eulerfact2(GEN PQ)
{
  pari_sp av = avma;
  GEN V = F2x_genus_red(ZX_to_F2x(gel(PQ, 1)), ZX_to_F2x(gel(PQ, 2)));
  GEN P = gel(V, 1), Q = gel(V, 2);
  GEN F = gel(V, 3), v = gel(V, 4);
  GEN abe, tor;
  GEN ki, kp = pol_1(0), kq = pol_1(0);
  long dP = F2x_degree(P), dQ = F2x_degree(Q), d = maxss(dP, 2*dQ);
  if (!lgpol(F)) return pol_1(0);
  ki = dQ!=0 || dP>0 ? oneminusxd(1):
      dP==-1 ? ZX_sqr(oneminusxd(1)): oneminusxd(2);
  abe = d>=5? RgX_recip(hyperellcharpoly(gmul(PQ,gmodulss(1,2)))):
        d>=3? RgX_recip(ellfromeqncharpoly(F2x_to_ZX(P), F2x_to_ZX(Q), gen_2)):
        pol_1(0);
  if (lgpol(F))
  {
    GEN M = gel(F2x_factor(F), 1);
    long i, lF = lg(M)-1;
    for(i=1; i <= lF; i++)
    {
      GEN Fi = gel(M, i);
      long d = F2x_degree(Fi);
      long nb  = F2xqX_quad_nbroots(F2x_rem(Q, Fi), F2x_rem(P, Fi), Fi);
      GEN kqf = nb==1 ? oneminusxd(d):
                nb==2 ? ZX_sqr(oneminusxd(d))
                      : oneminusxd(2*d);
      kp = gmul(kp, oneminusxd(d));
      kq = gmul(kq, kqf);
    }
  }
  if (maxss(v[1],2*v[2])<5)
  {
    GEN kqoo = v[1]>2*v[2] ? oneminusxd(1):
               v[1]<2*v[2] ? ZX_sqr(oneminusxd(1))
                           : oneminusxd(2);
    kp = gmul(kp, oneminusxd(1));
    kq = gmul(kq, kqoo);
  }
  tor = RgX_div(ZX_mul(oneminusxd(1),kq), ZX_mul(ki, kp));
  return gerepileupto(av, ZX_mul(abe, tor));
}

GEN
lfungenus2(GEN G)
{
  pari_sp ltop = avma;
  GEN Ldata;
  GEN gr = genus2red(G, NULL);
  GEN N  = gel(gr, 1), M = gel(gr, 2), Q = gel(gr, 3), L = gel(gr, 4);
  GEN PQ = genus2_redmodel2(Q);
  GEN e;
  long i, lL = lg(L), ram2;
  ram2 = absequaliu(gmael(M,1,1),2);
  if (ram2 && equalis(gmael(M,2,1),-1))
    pari_warn(warner,"unknown valuation of conductor at 2");
  e = cgetg(lL+(ram2?0:1), t_VEC);
  gel(e,1) = mkvec2(gen_2, ram2 ? genus2_eulerfact2(PQ)
           : RgX_recip(hyperellcharpoly(gmul(PQ,gmodulss(1,2)))));
  for(i = ram2? 2: 1; i < lL; i++)
  {
    GEN Li = gel(L, i);
    GEN p = gel(Li, 1);
    gel(e, ram2 ? i: i+1) = mkvec2(p, genus2_eulerfact(Q,p));
  }
  Ldata = mkvecn(6, tag(mkvec2(Q,e), t_LFUN_GENUS2),
      gen_0, mkvec4(gen_0, gen_0, gen_1, gen_1), gen_2, N, gen_0);
  return gerepilecopy(ltop, Ldata);
}

/*************************************************************/
/*                        ETA QUOTIENTS                      */
/* An eta quotient is a matrix with 2 columns [m, r_m] with  */
/* m >= 1 representing f(\tau)=\prod_m\eta(m\tau)^{r_m}.     */
/*************************************************************/

static GEN
eta_inflate_ZXn(long m, long v)
{
  long n, k;
  GEN P = cgetg(m+2,t_POL);
  P[1] = 0;
  for(n = 0; n < m; n++) gel(P,n+2) = gen_0;
  for(n = 0;; n++)
  {
    k = v * (((3*n - 1) * n) >> 1);
    if (k >= m) break;
    gel(P, 2+k) = odd(n)? gen_m1: gen_1;
    k += n*v; /* v * (3*n + 1) * n / 2 */;
    if (k >= m) break;
    gel(P, 2+k) = odd(n)? gen_m1: gen_1;
  }
  return RgX_to_ser(P, m+2);
}

static GEN
vecan_eta(GEN eta, long L)
{
  GEN P, eq, divN = gel(eta, 1), RM = gel(eta, 2);
  long i, ld = lg(divN);
  P = gen_1; eq = gen_0;
  for (i = 1; i < ld; ++i)
  {
    GEN m, rm = gel(RM, i);
    if (!signe(rm)) continue;
    m = gel(divN, i); eq = addii(eq, mulii(m, rm));
    P = gmul(P, gpowgs(eta_inflate_ZXn(L, itos(m)), itos(rm)));
  }
  if (!equalis(eq, 24)) pari_err_IMPL("valuation != 1 in lfunetaquo");
  return gtovec0(P, L);
}

/* Check if correct eta quotient. Set canonical form columns */
static void
etaquocheck(GEN eta, GEN *pdivN, GEN *pRM, GEN *pN)
{
  GEN M, E, divN, RM, N;
  long lM, j;
  if (typ(eta) != t_MAT || lg(eta) != 3 || !RgM_is_ZM(eta))
    pari_err_TYPE("lfunetaquo", eta);
  eta = famat_reduce(eta);
  M = gel(eta, 1); lM = lg(M);
  E = gel(eta, 2);
  *pN = N = glcm0(M, NULL);
  *pdivN = divN = divisors(N);
  settyp(divN, t_COL);
  *pRM = RM = zerocol(lg(divN)-1);
  for (j = 1; j < lM; j++)
  {
    GEN m = gel(M,j), e = gel(E,j);
    long i = ZV_search(divN, m);
    gel(RM,i) = e;
  }
}

/* Return etaquotient type:
 * -1: nonholomorphic or not on gamma_0(N)
 * 0: holomorphic noncuspidal
 * 1: cuspidal
 * 2: selfdual noncuspidal
 * 3: selfdual cuspidal
 * Sets conductor, modular weight, canonical matrix */
static long
etaquotype(GEN eta, GEN *pN, long *pw, GEN *pcan)
{
  GEN divN, RM, S, T, U, N, M;
  long ld, i, j, fl;

  etaquocheck(eta, &divN, &RM, &N);
  *pcan = mkmat2(divN, RM);
  *pw = 0;
  *pN = gen_1;
  /* divN sorted in increasing order, N = last entry, divN[ld-i] = N/divN[i] */
  ld = lg(divN);
  S = gen_0; T = gen_0; U = gen_0;
  for (i = 1; i < ld; ++i)
  {
    GEN m = gel(divN,i), rm = gel(RM,i);
    if (!signe(rm)) continue;
    S = addii(S, mulii(m, rm));
    T = addii(T, rm);
    U = gadd(U, gdiv(rm, m));
  }
  if (umodiu(S, 24) || umodiu(T, 2)) return -1;
  *pw = itos(shifti(T,-1));
  *pN = M = lcmii(N, denom(gdivgs(U, 24)));
  for (i = 1, fl = 1; i < ld; i++)
  {
    GEN m = gel(divN, i), s = mulii(gel(RM,i), mulii(m,N));
    long t;
    for (j = 1; j < ld; ++j)
      if (j != i && signe(gel(RM,j)))
      {
        GEN mj = gel(divN, j), nj = gel(divN, ld-j); /* nj = N/mj */
        s = addii(s, mulii(mulii(gel(RM,j), sqri(gcdii(mj, m))), nj));
      }
    t = signe(s);
    if (t < 0) return -1;
    if (t == 0) fl = 0;
  }
  for (i = 1; i < ld; ++i)
  {
    GEN m = gel(divN, i), rm = gel(RM, i);
    if (!signe(rm)) continue;
    j = ZV_search(divN, divii(M,m));
    if (!j || !equalii(rm, gel(RM,j))) return fl;
  }
  return fl+2;
}

GEN
lfunetaquo(GEN eta)
{
  pari_sp ltop = avma;
  GEN Ldata, N, can;
  long k;
  switch(etaquotype(eta, &N, &k, &can))
  {
    case 3: break;
    case 2: pari_err_IMPL("noncuspidal eta quotient");
    default: pari_err_TYPE("lfunetaquo [non holomorphic]", eta);
  }
  Ldata = mkvecn(6, tag(can, t_LFUN_ETA),
                    gen_0, mkvec2(gen_0, gen_1), stoi(k), N, gen_1);
  return gerepilecopy(ltop, Ldata);
}

static GEN
vecan_qf(GEN Q, long L)
{ return gmul2n(gtovec(qfrep0(Q, utoi(L), 1)), 1); }

static long
qf_iseven(GEN M)
{
  long i, n = lg(M) - 1;
  for (i=1; i<=n; i++)
    if (mpodd(gcoeff(M,i,i))) return 0;
  return 1;
}

GEN
lfunqf(GEN M, long prec)
{
  pari_sp ltop = avma;
  long n, k;
  GEN D, d, Mi, cMi, detM, Ldata, poles, res0, res2, eno, dual;

  if (typ(M) != t_MAT) pari_err_TYPE("lfunqf", M);
  if (!RgM_is_ZM(M))   pari_err_TYPE("lfunqf [not integral]", M);
  n = lg(M)-1;
  if (odd(n)) pari_err_TYPE("lfunqf [odd dimension]", M);
  k = n >> 1;
  M = Q_primpart(M); detM = ZM_det(M);
  Mi = ZM_inv(M, detM); /* det(M) M^(-1) */
  if (is_pm1(detM)) cMi = NULL; else Mi = Q_primitive_part(Mi, &cMi);
  d = cMi? diviiexact(detM, cMi): detM; /* denom(M^(-1)) */
  if (!qf_iseven(M))
  {
    M = gmul2n(M, 1);
    d = shifti(d, 1);
    detM = shifti(detM,n);
  }
  if (!qf_iseven(Mi))
  {
    Mi = gmul2n(Mi, 1);
    d = shifti(d,1);
  }
  /* det(Mi) = d^n/det(M), D^2 = det(Mi)/det(M) */
  D = gdiv(powiu(d,k), detM);
  if (!issquareall(D, &eno)) eno = gsqrt(D, prec);
  dual = gequal1(D) ? gen_0: tag(Mi, t_LFUN_QF);
  res0 = RgX_to_ser(deg1pol_shallow(gen_m2, gen_0, 0), 3);
  setvalp(res0, -1);
  res2 = RgX_to_ser(deg1pol_shallow(gmulgs(eno,2), gen_0, 0), 3);
  setvalp(res2, -1);
  poles = mkcol2(mkvec2(stoi(k),res2), mkvec2(gen_0,res0));
  Ldata = mkvecn(7, tag(M, t_LFUN_QF), dual,
       mkvec2(gen_0, gen_1), stoi(k), d, eno, poles);
  return gerepilecopy(ltop, Ldata);
}

/********************************************************************/
/**  Artin L function, based on a GP script by Charlotte Euvrard   **/
/********************************************************************/

static GEN
artin_repfromgens(GEN G, GEN M)
{
  GEN R, V, ord = gal_get_orders(G), grp = gal_get_group(G);
  long i, j, k, n = lg(ord)-1, m = lg(grp)-1;

  if (lg(M)-1 != n) pari_err_DIM("lfunartin");
  R = cgetg(m+1, t_VEC);
  gel(R, 1) = matid(lg(gel(M, 1))-1);
  for (i = 1, k = 1; i <= n; ++i)
  {
    long c = k*(ord[i] - 1);
    gel(R, ++k) = gel(M, i);
    for (j = 2; j <= c; ++j) gel(R, ++k) = gmul(gel(R, j), gel(M, i));
  }
  V = cgetg(m+1, t_VEC);
  for (i = 1; i <= m; i++) gel(V, gel(grp, i)[1]) = gel(R, i);
  return V;
}

static GEN
galois_get_conj(GEN G)
{
  GEN grp = gal_get_group(G);
  long k, r = lg(grp)-1;
  for (k = 2; k <= r; ++k)
  {
    GEN g = gel(grp,k);
    if (g[g[1]]==1)
    {
      pari_sp av = avma;
      GEN F = galoisfixedfield(G, g, 1, -1);
      if (ZX_sturmpart(F, NULL) > 0) { avma = av; return g; }
      avma = av;
    }
  }
  pari_err_BUG("galois_get_conj");
  return NULL;
}

static GEN
artin_gamma(GEN N, GEN G, GEN R)
{
  long a, t, d = lg(gel(R,1))-1;
  GEN T;
  if (nf_get_r2(N) == 0) return vec01(d, 0);
  a = galois_get_conj(G)[1];
  T = lift_shallow( gtrace(gel(R,a)) );
  t = itos(simplify_shallow(T));
  return vec01((d+t) / 2, (d-t) / 2);
}

static GEN
artin_codim(GEN J, GEN R)
{
  pari_sp av = avma;
  long k, l, lJ = lg(J);
  GEN z, v = cgetg(lJ, t_VEC);

  for (l = 1; l < lJ; ++l) gel(v,l) = ker(gsubgs(gel(R, gel(J,l)[1]), 1));
  z = gel(v,1); for (k = 2; k < lJ; ++k) z = intersect(z, gel(v,k));
  return gerepilecopy(av, z);
}

static GEN
artin_ram(GEN N, GEN G, GEN pr, GEN ramg, GEN R, GEN ss)
{
  pari_sp av = avma;
  GEN c, S, Q;
  if (lg(ss)==1) return gen_1;

  Q = idealramfrobenius(N, G, pr, ramg);
  S = gel(R, Q[1]);
  c = RgX_recip(charpoly(gdiv(gmul(S, ss), ss), 0));
  return gerepilecopy(av, c);
}

/* [Artin conductor, vec of [p, Lp^(-1)]] */
static GEN
artin_badprimes(GEN N, GEN G, GEN R)
{
  pari_sp av = avma;
  long i, d = lg(gel(R,1))-1;
  GEN P = gel(absZ_factor(nf_get_disc(N)), 1);
  long lP = lg(P);
  GEN B = cgetg(lP, t_VEC), C = cgetg(lP, t_VEC);

  for (i = 1; i < lP; ++i)
  {
    GEN p = gel(P, i), pr = gel(idealprimedec(N, p), 1);
    GEN J = idealramgroups(N, G, pr);
    GEN G0 = gel(J,2); /* inertia group */
    long lJ = lg(J);
    GEN sdec = artin_codim(gel(G0,1), R);
    long ndec = group_order(G0);
    long j, v = ndec * (d + 1 - lg(sdec));
    for (j = 3; j < lJ; ++j)
    {
      GEN Jj = gel(J, j);
      GEN ss = artin_codim(gel(Jj, 1), R);
      v += group_order(Jj) * (d + 1 - lg(ss));
    }
    gel(C, i) = powiu(p, v/ndec);
    gel(B, i) = mkvec2(p, artin_ram(N, G, pr, J, R, sdec));
  }
  return gerepilecopy(av, mkvec2(ZV_prod(C), B));
}

struct dir_artin
{
  GEN N, G, V, aut;
};

static GEN
dirartin(void *E, GEN p)
{
  pari_sp av = avma;
  struct dir_artin *d = (struct dir_artin *) E;
  GEN N = d->N, pr, frob;
  /* pick one maximal ideal in the conjugacy class above p */
  if (!dvdii(nf_get_index(N), p))
  { /* simple case */
    GEN F = FpX_factor(nf_get_pol(N), p);
    GEN P = gel(F,1), E = gel(F,2);
    pr = idealprimedec_kummer(N, gel(P,1), E[1], p);
  }
  else /* wasteful but rare */
    pr = gel(idealprimedec(N,p), 1);
  frob = idealfrobenius_aut(N, d->G, pr, d->aut);
  return gerepileupto(av, ginv(gel(d->V, frob[1])));
}

static GEN
vecan_artin(GEN an, long L, long prec)
{
  struct dir_artin d;
  GEN A, Sbad = gel(an,5);
  long n = itos(gel(an,6));
  d.N = gel(an,1); d.G = gel(an,2); d.V = gel(an,3); d.aut = gel(an,4);
  A = lift_shallow(direuler_bad(&d, dirartin, gen_2, stoi(L), NULL, Sbad));
  return RgXV_RgV_eval(A, grootsof1(n, prec));
}

GEN
lfunartin(GEN N, GEN G, GEN M, long o)
{
  pari_sp av = avma;
  GEN bc, R, V, aut, Ldata;
  long i, l;
  N = checknf(N);
  checkgal(G);
  if (!is_vec_t(typ(M))) pari_err_TYPE("lfunartin",M);
  M = gmul(M, mkpolmod(gen_1, polcyclo(o, gvar(M))));
  R = artin_repfromgens(G,M);
  bc = artin_badprimes(N,G,R);
  l = lg(R); V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(V,i) = RgX_recip(charpoly(gel(R,i), 0));
  aut = nfgaloispermtobasis(N, G);
  Ldata = mkvecn(6, tag(mkcol6(N, G, V, aut, gel(bc, 2), stoi(o)), t_LFUN_ARTIN),
      gen_1, artin_gamma(N, G, R), gen_1, gel(bc,1), gen_0);
  return gerepilecopy(av, Ldata);
}

/********************************************************************/
/**                    High-level Constructors                     **/
/********************************************************************/
enum { t_LFUNMISC_POL, t_LFUNMISC_CHIQUAD, t_LFUNMISC_CHICONREY,
       t_LFUNMISC_CHIGEN, t_LFUNMISC_ELLINIT, t_LFUNMISC_ETAQUO };
static long
lfundatatype(GEN data)
{
  long l;
  switch(typ(data))
  {
    case t_INT: return t_LFUNMISC_CHIQUAD;
    case t_INTMOD: return t_LFUNMISC_CHICONREY;
    case t_POL: return t_LFUNMISC_POL;
    case t_VEC:
      if (checknf_i(data)) return t_LFUNMISC_POL;
      l = lg(data);
      if (l == 17) return t_LFUNMISC_ELLINIT;
      if (l == 3 && typ(gel(data,1)) == t_VEC) return t_LFUNMISC_CHIGEN;
      break;
  }
  return -1;
}
static GEN
lfunmisc_to_ldata_i(GEN ldata, long shallow)
{
  long lx;
  if (is_linit(ldata)) ldata = linit_get_ldata(ldata);
  lx = lg(ldata);
  if (typ(ldata)==t_VEC && (lx == 7 || lx == 8) && is_tagged(ldata))
  {
    if (!shallow) ldata = gcopy(ldata);
    checkldata(ldata); return ldata;
  }
  switch (lfundatatype(ldata))
  {
    case t_LFUNMISC_POL: return lfunzetak(ldata);
    case t_LFUNMISC_CHIQUAD: return lfunchiquad(ldata);
    case t_LFUNMISC_CHICONREY:
    {
      GEN G = ZNstar(gel(ldata,1), nf_INIT);
      return lfunchiZ(G, gel(ldata,2));
    }
    case t_LFUNMISC_CHIGEN: return lfunchigen(gel(ldata,1), gel(ldata,2));
    case t_LFUNMISC_ELLINIT: return lfunell(ldata);
  }
  pari_err_TYPE("lfunmisc_to_ldata",ldata);
  return NULL; /* NOT REACHED */
}

GEN
lfunmisc_to_ldata(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 0); }

GEN
lfunmisc_to_ldata_shallow(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 1); }

/********************************************************************/
/**                    High-level an expansion                     **/
/********************************************************************/
/* van is the output of ldata_get_an: return a_1,...a_L at precision prec */
GEN
ldata_vecan(GEN van, long L, long prec)
{
  GEN an = gel(van, 2);
  long t = mael(van,1,1);
  pari_timer ti;
  if (DEBUGLEVEL >= 1)
    err_printf("Lfun: computing %ld coeffs, prec %ld, type %ld\n", L, prec, t);
  if (DEBUGLEVEL >= 2) timer_start(&ti);
  switch (t)
  {
    long n;
    case t_LFUN_GENERIC:
      push_localprec(prec); an = vecan_closure(an, L, NULL); pop_localprec();
      n = lg(an)-1;
      if (n < L)
        pari_warn(warner, "#an = %ld < %ld, results may be imprecise", n, L);
      break;
    case t_LFUN_ZETA: an = const_vec(L, gen_1); break;
    case t_LFUN_NF:  an = dirzetak(an, stoi(L)); break;
    case t_LFUN_ELL: an = ellan(an, L); break;
    case t_LFUN_KRONECKER: an = vecan_Kronecker(an, L); break;
    case t_LFUN_CHIZ: an = vecan_chiZ(an, L, prec); break;
    case t_LFUN_CHIGEN: an = vecan_chigen(an, L, prec); break;
    case t_LFUN_ARTIN: an = vecan_artin(an, L, prec); break;
    case t_LFUN_ETA: an = vecan_eta(an, L); break;
    case t_LFUN_QF: an = vecan_qf(an, L); break;
    case t_LFUN_DIV: an = vecan_div(an, L, prec); break;
    case t_LFUN_MUL: an = vecan_mul(an, L, prec); break;
    case t_LFUN_CONJ: an = vecan_conj(an, L, prec); break;
    case t_LFUN_SYMSQ_ELL: an = vecan_ellsymsq(an, L); break;
    case t_LFUN_GENUS2: an = vecan_genus2(an, L); break;
    default: pari_err_TYPE("ldata_vecan", van);
  }
  if (DEBUGLEVEL >= 2) timer_printf(&ti, "ldata_vecan");
  return an;
}
