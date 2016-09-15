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
/*                       RAY CLASS FIELDS                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* increment y, which runs through [-d,d]^k. Return 0 when done. */
static int
increment(GEN y, long k, long d)
{
  long i = 0, j;
  do
  {
    if (++i > k) return 0;
    y[i]++;
  } while (y[i] > d);
  for (j = 1; j < i; j++) y[j] = -d;
  return 1;
}
static GEN
archstar_full_rk(GEN x, GEN bas, GEN v, GEN gen)
{
  long i, r, lgmat, N = lg(bas)-1, nba = nbrows(v);
  GEN lambda = cgetg(N+1, t_VECSMALL), mat = cgetg(nba+1,t_MAT);

  lgmat = lg(v); setlg(mat, lgmat+1);
  for (i = 1; i < lgmat; i++) gel(mat,i) = gel(v,i);
  for (     ; i <= nba; i++)  gel(mat,i) = cgetg(nba+1, t_VECSMALL);

  if (x) { x = ZM_lll(x, 0.75, LLL_INPLACE); bas = RgV_RgM_mul(bas, x); }

  for (r=1;; r++)
  { /* reset */
    (void)vec_setconst(lambda, (GEN)0);
    if (!x) lambda[1] = r;
    while (increment(lambda, N, r))
    {
      pari_sp av1 = avma;
      GEN a = RgM_zc_mul(bas, lambda), c = gel(mat,lgmat);
      for (i = 1; i <= nba; i++)
      {
        GEN t = gel(a,i);
        if (x) t = gaddgs(t, 1);
        c[i] = (gsigne(t) < 0)? 1: 0;
      }
      avma = av1; if (Flm_deplin(mat, 2)) continue;

      /* c independent of previous sign vectors */
      if (!x) a = zc_to_ZC(lambda);
      else
      {
        a = ZM_zc_mul(x, lambda);
        gel(a,1) = addiu(gel(a,1), 1);
      }
      gel(gen,lgmat) = a;
      if (lgmat++ == nba) {
        mat = Flm_inv(mat,2); /* full rank */
        settyp(mat, t_VEC); return mat;
      }
      setlg(mat,lgmat+1);
    }
  }
}

/* Faster than Buchray (because it can use nfsign_units: easier nfarchstar) */
GEN
buchnarrow(GEN bnf)
{
  GEN nf, cyc, gen, A, NO, GD, v, invpi, logs, R, basecl, met, u1, archp;
  long r1, j, ngen, t, RU;
  pari_sp av = avma;

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf); r1 = nf_get_r1(nf);

  if (!r1) return gcopy( bnf_get_clgp(bnf) );

  /* simplified version of nfsign_units; r1 > 0 so bnf.tu = -1 */
  archp = identity_perm(r1);
  A = bnf_get_logfu(bnf); RU = lg(A)+1;
  invpi = invr( mppi(nf_get_prec(nf)) );
  v = cgetg(RU,t_MAT); gel(v, 1) = const_vecsmall(r1, 1); /* nfsign(-1) */
  for (j=2; j<RU; j++) gel(v,j) = nfsign_from_logarch(gel(A,j-1), invpi, archp);
  /* up to here */

  cyc = bnf_get_cyc(bnf);
  gen = bnf_get_gen(bnf);
  v = Flm_image(v, 2);
  t = lg(v)-1;
  if (t == r1) { avma = av; return gcopy( bnf_get_clgp(bnf) ); }
  NO = shifti(bnf_get_no(bnf), r1-t);

  ngen = lg(gen)-1;
  gen = vec_lengthen(gen, r1 + (ngen-t));
  v = archstar_full_rk(NULL, nf_get_M(nf), v, gen + (ngen-t));
  v = rowslice(v, t+1, r1);

  logs = cgetg(ngen+1,t_MAT); GD = gmael(bnf,9,3);
  for (j=1; j<=ngen; j++)
  {
    GEN z = nfsign_from_logarch(gel(GD,j), invpi, archp);
    gel(logs,j) = zc_to_ZC( Flm_Flc_mul(v, z, 2) );
  }
  /* [ cyc  0 ]
   * [ logs 2 ] = relation matrix for Cl_f */
  R = shallowconcat(
    vconcat(diagonal_shallow(cyc), logs),
    vconcat(zeromat(ngen, r1-t), scalarmat(gen_2,r1-t))
  );
  met = ZM_snf_group(R,NULL,&u1);
  t = lg(met); basecl = cgetg(t,t_VEC);
  for (j=1; j<t; j++)
    gel(basecl,j) = Q_primpart( idealfactorback(nf,gen,gel(u1,j),0) );
  return gerepilecopy(av, mkvec3(NO, met, basecl));
}

/* x non-0 integral ideal in HNF, compute elements in 1+x (in x, if x = zk)
 * whose sign matrix is invertible. archp in 'indices' format */
GEN
nfarchstar(GEN nf, GEN x, GEN archp)
{
  long nba = lg(archp) - 1;
  GEN cyc, gen, mat;

  if (!nba)
    cyc = gen = mat = cgetg(1, t_VEC);
  else
  {
    GEN xZ = gcoeff(x,1,1), gZ;
    pari_sp av = avma;
    if (is_pm1(xZ)) x = NULL; /* x = O_K */
    gZ = x? subui(1, xZ): gen_m1; /* gZ << 0, gZ = 1 mod x */
    if (nba == 1)
    {
      gen = mkvec(gZ);
      mat = mkvec( mkvecsmall(1) );
    }
    else
    {
      GEN bas = nf_get_M(nf);
      if (lgcols(bas) > lg(archp)) bas = rowpermute(bas, archp);
      gen = cgetg(nba+1,t_VEC);
      gel(gen,1) = gZ;
      mat = archstar_full_rk(x, bas, mkmat(const_vecsmall(nba,1)), gen);
      gerepileall(av,2,&gen,&mat);
    }
    cyc = const_vec(nba, gen_2);
  }
  return mkvec4(cyc,gen,mat,archp);
}

/********************************************************************/
/**                                                                **/
/**                  REDUCTION MOD IDELE                           **/
/**                                                                **/
/********************************************************************/

static GEN
compute_fact(GEN nf, GEN u1, GEN gen)
{
  GEN G, basecl;
  long i, j, l = lg(u1), h = lgcols(u1); /* l > 1 */

  basecl = cgetg(l,t_VEC);
  G = cgetg(3,t_VEC);
  gel(G,2) = cgetg(1,t_MAT);

  for (j=1; j<l; j++)
  {
    GEN g,e, z = NULL;
    for (i=1; i<h; i++)
    {
      e = gcoeff(u1,i,j); if (!signe(e)) continue;

      g = gel(gen,i);
      if (typ(g) != t_MAT)
      {
        if (z)
          gel(z,2) = famat_mul(gel(z,2), to_famat_shallow(g, e));
        else
          z = mkvec2(NULL, to_famat_shallow(g, e));
        continue;
      }

      gel(G,1) = g;
      g = idealpowred(nf,G,e);
      z = z? idealmulred(nf,z,g): g;
    }
    gel(z,2) = famat_reduce(gel(z,2));
    gel(basecl,j) = z;
  }
  return basecl;
}

static int
too_big(GEN nf, GEN bet)
{
  GEN x = nfnorm(nf,bet);
  switch (typ(x))
  {
    case t_INT: return abscmpii(x, gen_1);
    case t_FRAC: return abscmpii(gel(x,1), gel(x,2));
  }
  pari_err_BUG("wrong type in too_big");
  return 0; /* not reached */
}

/* GTM 193: Algo 4.3.4. Reduce x mod divisor */
static GEN
idealmoddivisor_aux(GEN nf, GEN x, GEN f, GEN sarch)
{
  pari_sp av = avma;
  GEN a, A;

  if ( is_pm1(gcoeff(f,1,1)) ) /* f = 1 */
  {
    A = idealred(nf, mkvec2(x, gen_1));
    A = nfinv(nf, gel(A,2));
  }
  else
  {/* given coprime integral ideals x and f (f HNF), compute "small"
    * G in x, such that G = 1 mod (f). GTM 193: Algo 4.3.3 */
    GEN G = idealaddtoone_i(nf, x, f);
    GEN D = idealaddtoone_i(nf, idealdiv(nf,G,x), f);
    A = nfdiv(nf,D,G);
  }
  if (too_big(nf,A) > 0) { avma = av; return x; }
  a = set_sign_mod_divisor(nf, NULL, A, sarch);
  if (a != A && too_big(nf,A) > 0) { avma = av; return x; }
  return idealmul(nf, a, x);
}

GEN
idealmoddivisor(GEN bnr, GEN x)
{
  GEN nf = bnr_get_nf(bnr), bid = bnr_get_bid(bnr);
  return idealmoddivisor_aux(nf, x, bid_get_ideal(bid), bid_get_sarch(bid));
}

/* v_pr(L0 * cx) */
static long
fast_val(GEN nf,GEN L0,GEN cx,GEN pr)
{
  pari_sp av = avma;
  long v = typ(L0) == t_INT? 0: ZC_nfval(nf,L0,pr);
  if (cx)
  {
    long w = Q_pval(cx, pr_get_p(pr));
    if (w) v += w * pr_get_e(pr);
  }
  avma = av; return v;
}

/* x coprime to fZ, return y = x mod fZ, y integral */
static GEN
make_integral_Z(GEN x, GEN fZ)
{
  GEN d, y = Q_remove_denom(x, &d);
  if (d) y = FpC_Fp_mul(y, Fp_inv(d, fZ), fZ);
  return y;
}

/* p pi^(-1) mod f */
static GEN
get_pinvpi(GEN nf, GEN fZ, GEN p, GEN pi, GEN *v)
{
  if (!*v) {
    GEN invpi = nfinv(nf, pi);
    *v = make_integral_Z(RgC_Rg_mul(invpi, p), mulii(p, fZ));
  }
  return *v;
}
/* uniformizer pi for pr, coprime to F/p */
static GEN
get_pi(GEN F, GEN pr, GEN *v)
{
  if (!*v) *v = pr_uniformizer(pr, F);
  return *v;
}

static GEN
compute_raygen(GEN nf, GEN u1, GEN gen, GEN bid)
{
  GEN f, fZ, basecl, fa, pr, t, EX, sarch, cyc, F;
  GEN listpr, vecpi, vecpinvpi;
  long i,j,l,lp;

  if (lg(u1) == 1) return cgetg(1, t_VEC);

  /* basecl = generators in factored form */
  basecl = compute_fact(nf,u1,gen);

  cyc = bid_get_cyc(bid); EX = gel(cyc,1); /* exponent of (O/f)^* */
  f   = bid_get_ideal(bid); fZ = gcoeff(f,1,1);
  fa  = bid_get_fact(bid);
  sarch = bid_get_sarch(bid);
  listpr = gel(fa,1); F = prV_lcm_capZ(listpr);

  lp = lg(listpr);
  vecpinvpi = cgetg(lp, t_VEC);
  vecpi  = cgetg(lp, t_VEC);
  for (i=1; i<lp; i++)
  {
    pr = gel(listpr,i);
    gel(vecpi,i)    = NULL; /* to be computed if needed */
    gel(vecpinvpi,i) = NULL; /* to be computed if needed */
  }

  l = lg(basecl);
  for (i=1; i<l; i++)
  {
    GEN p, pi, pinvpi, dmulI, mulI, G, I, A, e, L, newL;
    long la, v, k;
    pari_sp av;
    /* G = [I, A=famat(L,e)] is a generator, I integral */
    G = gel(basecl,i);
    I = gel(G,1);
    A = gel(G,2); L = gel(A,1); e = gel(A,2);
    /* if no reduction took place in compute_fact, everybody is still coprime
     * to f + no denominators */
    if (!I) { gel(basecl,i) = famat_to_nf_moddivisor(nf, L, e, bid); continue; }
    if (lg(A) == 1) { gel(basecl,i) = I; continue; }

    /* compute mulI so that mulI * I coprime to f
     * FIXME: use idealcoprime ??? (Less efficient. Fix idealcoprime!) */
    dmulI = mulI = NULL;
    for (j=1; j<lp; j++)
    {
      pr = gel(listpr,j);
      v  = idealval(nf, I, pr);
      if (!v) continue;
      p  = pr_get_p(pr);
      pi = get_pi(F, pr, &gel(vecpi,j));
      pinvpi = get_pinvpi(nf, fZ, p, pi, &gel(vecpinvpi,j));
      t = nfpow_u(nf, pinvpi, (ulong)v);
      mulI = mulI? nfmuli(nf, mulI, t): t;
      t = powiu(p, v);
      dmulI = dmulI? mulii(dmulI, t): t;
    }

    /* make all components of L coprime to f.
     * Assuming (L^e * I, f) = 1, then newL^e * mulI = L^e */
    la = lg(e); newL = cgetg(la, t_VEC);
    for (k=1; k<la; k++)
    {
      GEN cx, LL = nf_to_scalar_or_basis(nf, gel(L,k));
      GEN L0 = Q_primitive_part(LL, &cx); /* LL = L0*cx (faster nfval) */
      for (j=1; j<lp; j++)
      {
        pr = gel(listpr,j);
        v  = fast_val(nf, L0,cx, pr); /* = val_pr(LL) */
        if (!v) continue;
        p  = pr_get_p(pr);
        pi = get_pi(F, pr, &gel(vecpi,j));
        if (v > 0)
        {
          pinvpi = get_pinvpi(nf, fZ, p, pi, &gel(vecpinvpi,j));
          t = nfpow_u(nf,pinvpi, (ulong)v);
          LL = nfmul(nf, LL, t);
          LL = RgC_Rg_div(LL, powiu(p, v));
        }
        else
        {
          t = nfpow_u(nf,pi,(ulong)(-v));
          LL = nfmul(nf, LL, t);
        }
      }
      LL = make_integral(nf,LL,f,listpr);
      gel(newL,k) = typ(LL) == t_INT? LL: FpC_red(LL, fZ);
    }

    av = avma;
    /* G in nf, = L^e mod f */
    G = famat_to_nf_modideal_coprime(nf, newL, e, f, EX);
    if (mulI)
    {
      G = nfmuli(nf, G, mulI);
      G = typ(G) == t_COL? ZC_hnfrem(G, ZM_Z_mul(f, dmulI))
                         : modii(G, mulii(fZ,dmulI));
    }
    G = set_sign_mod_divisor(nf,A,G,sarch);
    I = idealmul(nf,I,G);
    if (dmulI) I = ZM_Z_divexact(I, dmulI);
    /* more or less useless, but cheap at this point */
    I = idealmoddivisor_aux(nf,I,f,sarch);
    gel(basecl,i) = gerepilecopy(av, I);
  }
  return basecl;
}

/********************************************************************/
/**                                                                **/
/**                   INIT RAY CLASS GROUP                         **/
/**                                                                **/
/********************************************************************/
static GEN
check_subgroup(GEN bnr, GEN H, GEN *clhray)
{
  GEN cyc = bnr_get_cyc(bnr);
  *clhray = bnr_get_no(bnr);
  if (H && isintzero(H)) H = NULL;
  if (H) switch(typ(H))
  {
    case t_MAT:
      RgM_check_ZM(H, "check_subgroup");
      H = ZM_hnfmodid(H, cyc);
      break;
    case t_VEC:
      if (char_check(cyc, H)) { H = charker(cyc, H); break; }
    default: pari_err_TYPE("check_subgroup", H);
  }
  if (H)
  {
    GEN h = ZM_det_triangular(H);
    if (equalii(h, *clhray)) H = NULL; else *clhray = h;
  }
  return H;
}

static GEN
get_dataunit(GEN bnf, GEN bid)
{
  GEN D, cyc = bid_get_cyc(bid), U = bnf_build_units(bnf);
  GEN nf = bnf_get_nf(bnf);
  long i, l;
  zlog_S S; init_zlog_bid(&S, bid);
  D = nfsign_units(bnf, S.archp, 1); l = lg(D);
  for (i = 1; i < l; i++)
  {
    GEN v = zlog(nf, gel(U,i),gel(D,i), &S);
    gel(D,i) = vecmodii(ZM_ZC_mul(S.U, v), cyc);
  }
  return D;
}

GEN
Buchray(GEN bnf, GEN module, long flag)
{
  GEN nf, cyc, gen, Gen, u, clg, logs, p1, h, met, u1, u2, U, cycgen;
  GEN bid, cycbid, genbid, y, H, Hi, c1, c2, El;
  long RU, Ri, j, ngen, lh;
  const long add_gen = flag & nf_GEN;
  const long do_init = flag & nf_INIT;
  pari_sp av = avma;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  RU = lg(nf_get_roots(nf))-1; /* #K.fu */
  El = Gen = NULL; /* gcc -Wall */
  cyc = bnf_get_cyc(bnf);
  gen = bnf_get_gen(bnf); ngen = lg(cyc)-1;

  bid = checkbid_i(module);
  if (!bid) bid = Idealstar(nf,module,nf_GEN|nf_INIT);
  cycbid = bid_get_cyc(bid);
  genbid = bid_get_gen(bid);
  Ri = lg(cycbid)-1; lh = ngen+Ri;
  if (Ri || add_gen || do_init)
  {
    GEN fx = bid_get_fact(bid);
    El = cgetg(ngen+1,t_VEC);
    for (j=1; j<=ngen; j++)
    {
      p1 = idealcoprimefact(nf, gel(gen,j), fx);
      if (typ(p1) == t_COL && RgV_isscalar(p1)) p1 = gel(p1,1);
      gel(El,j) = p1;
    }
  }
  if (add_gen)
  {
    Gen = cgetg(lh+1,t_VEC);
    for (j=1; j<=ngen; j++) gel(Gen,j) = idealmul(nf, gel(El,j), gel(gen,j));
    for (   ; j<=lh; j++)   gel(Gen,j) = gel(genbid, j-ngen);
  }
  if (!Ri)
  {
    clg = cgetg(add_gen? 4: 3,t_VEC);
    if (add_gen) gel(clg,3) = Gen;
    gel(clg,1) = bnf_get_no(bnf);
    gel(clg,2) = cyc;
    if (!do_init) return gerepilecopy(av,clg);
    y = cgetg(7,t_VEC);
    gel(y,1) = bnf;
    gel(y,2) = bid;
    gel(y,3) = El;
    gel(y,4) = matid(ngen);
    gel(y,5) = clg;
    gel(y,6) = mkvec3(cgetg(1,t_MAT), matid(RU), gen_1);
    return gerepilecopy(av,y);
  }

  cycgen = bnf_build_cycgen(bnf);
  /* (log(Units)|D) * u = (0 | H) */
  if (do_init)
  {
    GEN D = shallowconcat(get_dataunit(bnf, bid), diagonal_shallow(cycbid));
    H = ZM_hnfall_i(D, do_init? &u: NULL, 1);
  }
  else
    H = ZM_hnfmodid(get_dataunit(bnf, bid), cycbid);
  logs = cgetg(ngen+1, t_MAT);
  /* FIXME: cycgen[j] is not necessarily coprime to bid, but it is made coprime
   * in famat_zlog using canonical uniformizers [from bid data]: no need to
   * correct it here. The same ones will be used in bnrisprincipal. Hence
   * modification by El is useless. */
  for (j=1; j<=ngen; j++)
  {
    p1 = gel(cycgen,j);
    if (typ(gel(El,j)) != t_INT) /* <==> != 1 */
    {
      GEN F = to_famat_shallow(gel(El,j), gel(cyc,j));
      p1 = famat_mul(F, p1);
    }
    gel(logs,j) = ideallog(nf, p1, bid); /* = log(Gen[j]) */
  }
  /* [ cyc  0 ]
   * [-logs H ] = relation matrix for Cl_f */
  h = shallowconcat(
    vconcat(diagonal_shallow(cyc), gneg_i(logs)),
    vconcat(zeromat(ngen, Ri), H)
  );
  met = ZM_snf_group(ZM_hnf(h), &U, add_gen? &u1: NULL);
  clg = cgetg(add_gen? 4: 3, t_VEC);
  gel(clg,1) = ZV_prod(met);
  gel(clg,2) = met;
  if (add_gen) gel(clg,3) = compute_raygen(nf,u1,Gen,bid);
  if (!do_init) return gerepilecopy(av, clg);

  u2 = cgetg(Ri+1,t_MAT);
  u1 = cgetg(RU+1,t_MAT);
  for (j=1; j<=RU; j++) { gel(u1,j) = gel(u,j); setlg(u[j],RU+1); }
  u += RU;
  for (j=1; j<=Ri; j++) { gel(u2,j) = gel(u,j); setlg(u[j],RU+1); }

  /* log(Units) U2 = H (mod D)
   * log(Units) U1 = 0 (mod D) */
  u1 = ZM_lll(u1, 0.99, LLL_INPLACE);
  Hi = Q_primitive_part(RgM_inv_upper(H), &c1);
  u2 = Q_primitive_part(ZM_mul(ZM_reducemodmatrix(u2,u1), Hi), &c2);
  c1 = mul_content(c1, c2);
  if (!c1)
    c2 = gen_1;
  else if (typ(c1) == t_INT)
  {
    if (!is_pm1(c1)) u2 = ZM_Z_mul(u2, c1);
    c2 = gen_1;
  }
  else /* t_FRAC */
  {
    c2 = gel(c1,2);
    c1 = gel(c1,1);
    if (!is_pm1(c1)) u2 = ZM_Z_mul(u2, c1);
  }
  y = cgetg(7,t_VEC);
  gel(y,1) = bnf;
  gel(y,2) = bid;
  gel(y,3) = El;
  gel(y,4) = U;
  gel(y,5) = clg;
  gel(y,6) = mkvec3(u2,u1,c2); /* u2/c2 = H^(-1) (mod Im u1) */
  return gerepilecopy(av,y);
}

GEN
bnrinit0(GEN bnf, GEN ideal, long flag)
{
  switch(flag)
  {
    case 0: flag = nf_INIT; break;
    case 1: flag = nf_INIT | nf_GEN; break;
    default: pari_err_FLAG("bnrinit");
  }
  return Buchray(bnf,ideal,flag);
}

GEN
bnrclassno(GEN bnf,GEN ideal)
{
  GEN h, D, bid, cycbid;
  pari_sp av = avma;

  bnf = checkbnf(bnf);
  h = bnf_get_no(bnf); /* class number */
  bid = checkbid_i(ideal);
  if (!bid) bid = Idealstar(bnf, ideal, nf_INIT);
  cycbid = bid_get_cyc(bid);
  if (lg(cycbid) == 1) { avma = av; return icopy(h); }
  D = get_dataunit(bnf, bid); /* (Z_K/f)^* / units ~ Z^n / D */
  D = ZM_hnfmodid(D,cycbid);
  return gerepileuptoint(av, mulii(h, ZM_det_triangular(D)));
}
GEN
bnrclassno0(GEN A, GEN B, GEN C)
{
  pari_sp av = avma;
  GEN h, H = NULL;
  /* adapted from ABC_to_bnr, avoid costly bnrinit if possible */
  if (typ(A) == t_VEC)
    switch(lg(A))
    {
      case 7: /* bnr */
        checkbnr(A); H = B;
        break;
      case 11: /* bnf */
        if (!B) pari_err_TYPE("bnrclassno [bnf+missing conductor]",A);
        if (!C) return bnrclassno(A, B);
        A = Buchray(A, B, nf_INIT); H = C;
        break;
      default: checkbnf(A);/*error*/
    }
  else checkbnf(A);/*error*/

  H = check_subgroup(A, H, &h);
  if (!H) { avma = av; return icopy(h); }
  return gerepileuptoint(av, h);
}

GEN
bnrisprincipal(GEN bnr, GEN x, long flag)
{
  pari_sp av = avma;
  GEN bnf, nf, bid, U, El, ep, L, idep, ex, cycray, cycbid, alpha;

  checkbnr(bnr);
  cycray = bnr_get_cyc(bnr);
  if (lg(cycray) == 1 && !(flag & nf_GEN)) return cgetg(1,t_COL);

  bnf = bnr_get_bnf(bnr); nf = bnf_get_nf(bnf);
  bid = bnr_get_bid(bnr);
  cycbid = bid_get_cyc(bid);
  El  = gel(bnr,3);
  U   = gel(bnr,4);

  if (typ(x) == t_VEC && lg(x) == 3)
  { idep = gel(x,2); x = gel(x,1); }  /* precomputed */
  else
    idep = bnfisprincipal0(bnf, x, nf_FORCE|nf_GENMAT);
  ep  = gel(idep,1);
  if (lg(cycbid) > 1)
  {
    GEN beta = gel(idep,2);
    long i, j = lg(ep);
    for (i=1; i<j; i++) /* modify beta as if gen -> El.gen (coprime to bid) */
      if (typ(gel(El,i)) != t_INT && signe(gel(ep,i))) /* <==> != 1 */
        beta = famat_mul(to_famat_shallow(gel(El,i), negi(gel(ep,i))), beta);
    ep = shallowconcat(ep, ideallog(nf,beta,bid));
  }
  ex = vecmodii(ZM_ZC_mul(U, ep), cycray);
  if (!(flag & nf_GEN)) return gerepileupto(av, ex);

  /* compute generator */
  L = isprincipalfact(bnf, x, bnr_get_gen(bnr), ZC_neg(ex),
                      nf_GENMAT|nf_GEN_IF_PRINCIPAL|nf_FORCE);
  if (L == gen_0) pari_err_BUG("isprincipalray");
  alpha = nffactorback(nf, L, NULL);
  if (lg(cycbid) > 1)
  {
    GEN v = gel(bnr,6), u2 = gel(v,1), u1 = gel(v,2), du2 = gel(v,3);
    GEN y = ZM_ZC_mul(u2, ideallog(nf, L, bid));
    if (!is_pm1(du2)) y = ZC_Z_divexact(y,du2);
    y = ZC_reducemodmatrix(y, u1);
    if (!ZV_equal0(y))
    {
      GEN U = bnf_build_units(bnf);
      alpha = nfdiv(nf, alpha, nffactorback(nf, U, y));
    }
  }
  return gerepilecopy(av, mkvec2(ex,alpha));
}

GEN
isprincipalray(GEN bnr, GEN x)
{
  return bnrisprincipal(bnr,x,0);
}

GEN
isprincipalraygen(GEN bnr, GEN x)
{
  return bnrisprincipal(bnr,x,nf_GEN);
}

/* N! / N^N * (4/pi)^r2 * sqrt(|D|) */
GEN
minkowski_bound(GEN D, long N, long r2, long prec)
{
  pari_sp av = avma;
  GEN c = divri(mpfactr(N,prec), powuu(N,N));
  if (r2) c = mulrr(c, powru(divur(4,mppi(prec)), r2));
  c = mulrr(c, gsqrt(absi(D),prec));
  return gerepileuptoleaf(av, c);
}

/* N = [K:Q] > 1, D = disc(K) */
static GEN
zimmertbound(GEN D, long N, long R2)
{
  pari_sp av = avma;
  GEN w;

  if (N > 20) w = minkowski_bound(D, N, R2, DEFAULTPREC);
  else
  {
    const double c[19][11] = {
{/*2*/  0.6931,     0.45158},
{/*3*/  1.71733859, 1.37420604},
{/*4*/  2.91799837, 2.50091538, 2.11943331},
{/*5*/  4.22701425, 3.75471588, 3.31196660},
{/*6*/  5.61209925, 5.09730381, 4.60693851, 4.14303665},
{/*7*/  7.05406203, 6.50550021, 5.97735406, 5.47145968},
{/*8*/  8.54052636, 7.96438858, 7.40555445, 6.86558259, 6.34608077},
{/*9*/ 10.0630022,  9.46382812, 8.87952524, 8.31139202, 7.76081149},
{/*10*/11.6153797, 10.9966020, 10.3907654,  9.79895170, 9.22232770, 8.66213267},
{/*11*/13.1930961, 12.5573772, 11.9330458, 11.3210061, 10.7222412, 10.1378082},
{/*12*/14.7926394, 14.1420915, 13.5016616, 12.8721114, 12.2542699, 11.6490374,
       11.0573775},
{/*13*/16.4112395, 15.7475710, 15.0929680, 14.4480777, 13.8136054, 13.1903162,
       12.5790381},
{/*14*/18.0466672, 17.3712806, 16.7040780, 16.0456127, 15.3964878, 14.7573587,
       14.1289364, 13.5119848},
{/*15*/19.6970961, 19.0111606, 18.3326615, 17.6620757, 16.9999233, 16.3467686,
       15.7032228, 15.0699480},
{/*16*/21.3610081, 20.6655103, 19.9768082, 19.2953176, 18.6214885, 17.9558093,
       17.2988108, 16.6510652, 16.0131906},

{/*17*/23.0371259, 22.3329066, 21.6349299, 20.9435607, 20.2591899, 19.5822454,
       18.9131878, 18.2525157, 17.6007672},

{/*18*/24.7243611, 24.0121449, 23.3056902, 22.6053167, 21.9113705, 21.2242247,
       20.5442836, 19.8719830, 19.2077941, 18.5522234},

{/*19*/26.4217792, 25.7021950, 24.9879497, 24.2793271, 23.5766321, 22.8801952,
       22.1903709, 21.5075437, 20.8321263, 20.1645647},
{/*20*/28.1285704, 27.4021674, 26.6807314, 25.9645140, 25.2537867, 24.5488420,
       23.8499943, 23.1575823, 22.4719720, 21.7935548, 21.1227537}
    };
    w = mulrr(dbltor(exp(-c[N-2][R2])), gsqrt(absi(D),DEFAULTPREC));
  }
  return gerepileuptoint(av, ceil_safe(w));
}

/* return \gamma_n^n if known, an upper bound otherwise */
static GEN
hermiteconstant(long n)
{
  GEN h,h1;
  pari_sp av;

  switch(n)
  {
    case 1: return gen_1;
    case 2: return mkfrac(utoipos(4), utoipos(3));
    case 3: return gen_2;
    case 4: return utoipos(4);
    case 5: return utoipos(8);
    case 6: return mkfrac(utoipos(64), utoipos(3));
    case 7: return utoipos(64);
    case 8: return utoipos(256);
  }
  av = avma;
  h  = powru(divur(2,mppi(DEFAULTPREC)), n);
  h1 = sqrr(ggamma(gdivgs(utoipos(n+4),2),DEFAULTPREC));
  return gerepileuptoleaf(av, mulrr(h,h1));
}

/* 1 if L (= nf != Q) primitive for sure, 0 if MAYBE imprimitive (may have a
 * subfield K) */
static long
isprimitive(GEN nf)
{
  long p, i, l, ep, N = nf_get_degree(nf);
  GEN D, fa;

  p = ucoeff(factoru(N), 1,1); /* smallest prime | N */
  if (p == N) return 1; /* prime degree */

  /* N = [L:Q] = product of primes >= p, same is true for [L:K]
   * d_L = t d_K^[L:K] --> check that some q^p divides d_L */
  D = nf_get_disc(nf);
  fa = gel(absZ_factor_limit(D,0),2); /* list of v_q(d_L). Don't check large primes */
  if (mod2(D)) i = 1;
  else
  { /* q = 2 */
    ep = itos(gel(fa,1));
    if ((ep>>1) >= p) return 0; /* 2 | d_K ==> 4 | d_K */
    i = 2;
  }
  l = lg(fa);
  for ( ; i < l; i++)
  {
    ep = itos(gel(fa,i));
    if (ep >= p) return 0;
  }
  return 1;
}

static GEN
dft_bound(void)
{
  if (DEBUGLEVEL>1) err_printf("Default bound for regulator: 0.2\n");
  return dbltor(0.2);
}

static GEN
regulatorbound(GEN bnf)
{
  long N, R1, R2, R;
  GEN nf, dK, p1, c1;

  nf = bnf_get_nf(bnf); N = nf_get_degree(nf);
  if (!isprimitive(nf)) return dft_bound();

  dK = absi(nf_get_disc(nf));
  nf_get_sign(nf, &R1, &R2); R = R1+R2-1;
  c1 = (!R2 && N<12)? int2n(N & (~1UL)): powuu(N,N);
  if (cmpii(dK,c1) <= 0) return dft_bound();

  p1 = sqrr(glog(gdiv(dK,c1),DEFAULTPREC));
  p1 = divru(gmul2n(powru(divru(mulru(p1,3),N*(N*N-1)-6*R2),R),R2), N);
  p1 = sqrtr(gdiv(p1, hermiteconstant(R)));
  if (DEBUGLEVEL>1) err_printf("Mahler bound for regulator: %Ps\n",p1);
  return gmax(p1, dbltor(0.2));
}

static int
is_unit(GEN M, long r1, GEN x)
{
  pari_sp av = avma;
  GEN Nx = ground( embed_norm(RgM_zc_mul(M,x), r1) );
  int ok = is_pm1(Nx);
  avma = av; return ok;
}

/* FIXME: should use smallvectors */
static double
minimforunits(GEN nf, long BORNE, ulong w)
{
  const long prec = MEDDEFAULTPREC;
  long n, r1, i, j, k, *x, cnt = 0;
  pari_sp av = avma;
  GEN r, M;
  double p, norme, normin;
  double **q,*v,*y,*z;
  double eps=0.000001, BOUND = BORNE * 1.00001;

  if (DEBUGLEVEL>=2)
  {
    err_printf("Searching minimum of T2-form on units:\n");
    if (DEBUGLEVEL>2) err_printf("   BOUND = %ld\n",BORNE);
    err_flush();
  }
  n = nf_get_degree(nf); r1 = nf_get_r1(nf);
  minim_alloc(n+1, &q, &x, &y, &z, &v);
  M = gprec_w(nf_get_M(nf), prec);
  r = gaussred_from_QR(nf_get_G(nf), prec);
  for (j=1; j<=n; j++)
  {
    v[j] = gtodouble(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = gtodouble(gcoeff(r,i,j));
  }
  normin = (double)BORNE*(1-eps);
  k=n; y[n]=z[n]=0;
  x[n] = (long)(sqrt(BOUND/v[n]));

  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
        z[l] = 0;
        for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
        p = (double)x[k] + z[k];
        y[l] = y[k] + p*p*v[k];
        x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
        p = (double)x[k] + z[k];
        if (y[k] + p*p*v[k] <= BOUND) break;
        k++; x[k]--;
      }
    }
    while (k>1);
    if (!x[1] && y[1]<=eps) break;

    if (DEBUGLEVEL>8){ err_printf("."); err_flush(); }
    if (++cnt == 5000) return -1.; /* too expensive */

    p = (double)x[1] + z[1]; norme = y[1] + p*p*v[1];
    if (is_unit(M, r1, x) && norme < normin)
    {
      /* exclude roots of unity */
      if (norme < 2*n)
      {
        GEN t = nfpow_u(nf, zc_to_ZC(x), w);
        if (typ(t) != t_COL || ZV_isscalar(t)) continue;
      }
      normin = norme*(1-eps);
      if (DEBUGLEVEL>=2) { err_printf("*"); err_flush(); }
    }
  }
  if (DEBUGLEVEL>=2){ err_printf("\n"); err_flush(); }
  avma = av;
  return normin;
}

#undef NBMAX
static int
is_zero(GEN x, long bitprec) { return (gexpo(x) < -bitprec); }

static int
is_complex(GEN x, long bitprec) { return !is_zero(imag_i(x), bitprec); }

/* assume M_star t_REAL
 * FIXME: what does this do ? To be rewritten */
static GEN
compute_M0(GEN M_star,long N)
{
  long m1,m2,n1,n2,n3,lr,lr1,lr2,i,j,l,vx,vy,vz,vM;
  GEN pol,p1,p2,p3,p4,p5,p6,p7,p8,p9,u,v,w,r,r1,r2,M0,M0_pro,S,P,M;
  GEN f1,f2,f3,g1,g2,g3,pg1,pg2,pg3,pf1,pf2,pf3,X,Y,Z;
  long bitprec = 24;

  if (N == 2) return gmul2n(sqrr(gacosh(gmul2n(M_star,-1),0)), -1);
  vx = fetch_var(); X = pol_x(vx);
  vy = fetch_var(); Y = pol_x(vy);
  vz = fetch_var(); Z = pol_x(vz);
  vM = fetch_var(); M = pol_x(vM);

  M0 = NULL; m1 = N/3;
  for (n1=1; n1<=m1; n1++) /* 1 <= n1 <= n2 <= n3 < N */
  {
    m2 = (N-n1)>>1;
    for (n2=n1; n2<=m2; n2++)
    {
      pari_sp av = avma; n3=N-n1-n2;
      if (n1==n2 && n1==n3) /* n1 = n2 = n3 = m1 = N/3 */
      {
        p1 = divru(M_star, m1);
        p4 = sqrtr_abs( mulrr(addsr(1,p1),subrs(p1,3)) );
        p5 = subrs(p1,1);
        u = gen_1;
        v = gmul2n(addrr(p5,p4),-1);
        w = gmul2n(subrr(p5,p4),-1);
        M0_pro=gmul2n(mulur(m1,addrr(sqrr(logr_abs(v)),sqrr(logr_abs(w)))), -2);
        if (DEBUGLEVEL>2)
        {
          err_printf("[ %ld, %ld, %ld ]: %.28Pg\n",n1,n2,n3,M0_pro);
          err_flush();
        }
        if (!M0 || gcmp(M0_pro,M0) < 0) M0 = M0_pro;
      }
      else if (n1==n2 || n2==n3)
      { /* n3 > N/3 >= n1 */
        long k = N - 2*n2;
        p2 = deg1pol_shallow(stoi(-n2), M_star, vx); /* M* - n2 X */
        p3 = gmul(powuu(k,k),
                  gpowgs(gsubgs(RgX_Rg_mul(p2, M_star), k*k), n2));
        pol = gsub(p3, RgX_mul(monomial(powuu(n2,n2), n2, vx),
                               gpowgs(p2, N-n2)));
        r = roots(pol, DEFAULTPREC); lr = lg(r);
        for (i=1; i<lr; i++)
        {
          GEN n2S;
          S = real_i(gel(r,i));
          if (is_complex(gel(r,i), bitprec) || signe(S) <= 0) continue;

          n2S = mulur(n2,S);
          p4 = subrr(M_star, n2S);
          P = divrr(mulrr(n2S,p4), subrs(mulrr(M_star,p4),k*k));
          p5 = subrr(sqrr(S), gmul2n(P,2));
          if (gsigne(p5) < 0) continue;

          p6 = sqrtr(p5);
          v = gmul2n(subrr(S,p6),-1);
          if (gsigne(v) <= 0) continue;

          u = gmul2n(addrr(S,p6),-1);
          w = gpow(P, gdivgs(utoineg(n2),k), 0);
          p6 = mulur(n2, addrr(sqrr(logr_abs(u)), sqrr(logr_abs(v))));
          M0_pro = gmul2n(addrr(p6, mulur(k, sqrr(logr_abs(w)))),-2);
          if (DEBUGLEVEL>2)
          {
            err_printf("[ %ld, %ld, %ld ]: %.28Pg\n",n1,n2,n3,M0_pro);
            err_flush();
          }
          if (!M0 || gcmp(M0_pro,M0) < 0) M0 = M0_pro;
        }
      }
      else
      {
        f1 = gsub(gadd(gmulsg(n1,X),gadd(gmulsg(n2,Y),gmulsg(n3,Z))), M);
        f2 =         gmulsg(n1,gmul(Y,Z));
        f2 = gadd(f2,gmulsg(n2,gmul(X,Z)));
        f2 = gadd(f2,gmulsg(n3,gmul(X,Y)));
        f2 = gsub(f2,gmul(M,gmul(X,gmul(Y,Z))));
        f3 = gsub(gmul(gpowgs(X,n1),gmul(gpowgs(Y,n2),gpowgs(Z,n3))), gen_1);
        /* f1 = n1 X + n2 Y + n3 Z - M */
        /* f2 = n1 YZ + n2 XZ + n3 XY */
        /* f3 = X^n1 Y^n2 Z^n3 - 1*/
        g1=resultant(f1,f2); g1=primpart(g1);
        g2=resultant(f1,f3); g2=primpart(g2);
        g3=resultant(g1,g2); g3=primpart(g3);
        pf1=gsubst(f1,vM,M_star); pg1=gsubst(g1,vM,M_star);
        pf2=gsubst(f2,vM,M_star); pg2=gsubst(g2,vM,M_star);
        pf3=gsubst(f3,vM,M_star); pg3=gsubst(g3,vM,M_star);
        /* g3 = Res_Y,Z(f1,f2,f3) */
        r = roots(pg3,DEFAULTPREC); lr = lg(r);
        for (i=1; i<lr; i++)
        {
          w = real_i(gel(r,i));
          if (is_complex(gel(r,i), bitprec) || signe(w) <= 0) continue;
          p1=gsubst(pg1,vz,w);
          p2=gsubst(pg2,vz,w);
          p3=gsubst(pf1,vz,w);
          p4=gsubst(pf2,vz,w);
          p5=gsubst(pf3,vz,w);
          r1 = roots(p1, DEFAULTPREC); lr1 = lg(r1);
          for (j=1; j<lr1; j++)
          {
            v = real_i(gel(r1,j));
            if (is_complex(gel(r1,j), bitprec) || signe(v) <= 0
             || !is_zero(gsubst(p2,vy,v), bitprec)) continue;

            p7=gsubst(p3,vy,v);
            p8=gsubst(p4,vy,v);
            p9=gsubst(p5,vy,v);
            r2 = roots(p7, DEFAULTPREC); lr2 = lg(r2);
            for (l=1; l<lr2; l++)
            {
              u = real_i(gel(r2,l));
              if (is_complex(gel(r2,l), bitprec) || signe(u) <= 0
               || !is_zero(gsubst(p8,vx,u), bitprec)
               || !is_zero(gsubst(p9,vx,u), bitprec)) continue;

              M0_pro =              mulur(n1, sqrr(logr_abs(u)));
              M0_pro = gadd(M0_pro, mulur(n2, sqrr(logr_abs(v))));
              M0_pro = gadd(M0_pro, mulur(n3, sqrr(logr_abs(w))));
              M0_pro = gmul2n(M0_pro,-2);
              if (DEBUGLEVEL>2)
              {
               err_printf("[ %ld, %ld, %ld ]: %.28Pg\n",n1,n2,n3,M0_pro);
               err_flush();
              }
              if (!M0 || gcmp(M0_pro,M0) < 0) M0 = M0_pro;
            }
          }
        }
      }
      if (!M0) avma = av; else M0 = gerepilecopy(av, M0);
    }
  }
  for (i=1;i<=4;i++) (void)delete_var();
  return M0? M0: gen_0;
}

static GEN
lowerboundforregulator(GEN bnf, GEN units)
{
  long i, N, R2, RU = lg(units)-1;
  GEN nf, M0, M, G, minunit;
  double bound;

  if (!RU) return gen_1;
  nf = bnf_get_nf(bnf);
  N = nf_get_degree(nf);
  R2 = nf_get_r2(nf);

  G = nf_get_G(nf);
  minunit = gnorml2(RgM_RgC_mul(G, gel(units,1))); /* T2(units[1]) */
  for (i=2; i<=RU; i++)
  {
    GEN t = gnorml2(RgM_RgC_mul(G, gel(units,i)));
    if (gcmp(t,minunit) < 0) minunit = t;
  }
  if (gexpo(minunit) > 30) return NULL;

  bound = minimforunits(nf, itos(gceil(minunit)), bnf_get_tuN(bnf));
  if (bound < 0) return NULL;
  if (DEBUGLEVEL>1) err_printf("M* = %Ps\n", dbltor(bound));
  M0 = compute_M0(dbltor(bound), N);
  if (DEBUGLEVEL>1) { err_printf("M0 = %.28Pg\n",M0); err_flush(); }
  M = gmul2n(divru(gdiv(powrs(M0,RU),hermiteconstant(RU)),N),R2);
  if (cmprr(M, dbltor(0.04)) < 0) return NULL;
  M = sqrtr(M);
  if (DEBUGLEVEL>1)
    err_printf("(lower bound for regulator) M = %.28Pg\n",M);
  return M;
}

/* upper bound for the index of bnf.fu in the full unit group */
static GEN
bound_unit_index(GEN bnf, GEN units)
{
  pari_sp av = avma;
  GEN x = lowerboundforregulator(bnf, units);
  if (!x) { avma = av; x = regulatorbound(bnf); }
  return gerepileuptoint(av, ground(gdiv(bnf_get_reg(bnf), x)));
}

/* Compute a square matrix of rank #beta attached to a family
 * (P_i), 1<=i<=#beta, of primes s.t. N(P_i) = 1 mod p, and
 * (P_i,beta[j]) = 1 for all i,j. nf = true nf */
static void
primecertify(GEN nf, GEN beta, ulong p, GEN bad)
{
  long lb = lg(beta), rmax = lb - 1;
  GEN M, vQ, L;
  ulong q;
  forprime_t T;

  if (p == 2)
    L = cgetg(1,t_VECSMALL);
  else
    L = mkvecsmall(p);
  (void)u_forprime_arith_init(&T, 1, ULONG_MAX, 1, p);
  M = cgetg(lb,t_MAT); setlg(M,1);
  while ((q = u_forprime_next(&T)))
  {
    GEN qq, gg, og;
    long lQ, i, j;
    ulong g, m;
    if (!umodiu(bad,q)) continue;

    qq = utoipos(q);
    vQ = idealprimedec_limit_f(nf,qq,1);
    lQ = lg(vQ); if (lQ == 1) continue;

    /* cf rootsof1_Fl */
    g = pgener_Fl_local(q, L);
    (void)u_lvalrem((q-1) / p, p, &m);
    gg = utoipos( Fl_powu(g, m, q) ); /* order p in (Z/q)^* */
    og = mkmat2(mkcol(utoi(p)), mkcol(gen_1)); /* order of g */

    if (DEBUGLEVEL>3) err_printf("       generator of (Zk/Q)^*: %lu\n", g);
    for (i = 1; i < lQ; i++)
    {
      GEN C = cgetg(lb, t_VECSMALL);
      GEN Q = gel(vQ,i); /* degree 1 */
      GEN modpr = zkmodprinit(nf, Q);
      long r;

      for (j = 1; j < lb; j++)
      {
        GEN t = nf_to_Fp_coprime(nf, gel(beta,j), modpr);
        t = utoipos( Fl_powu(t[2], m, q) );
        /* FIXME: implement Fl_log_Shanks */
        C[j] = itou( Fp_log(t, gg, og, qq) ) % p;
      }
      r = lg(M);
      gel(M,r) = C; setlg(M, r+1);
      if (Flm_rank(M, p) != r) { setlg(M,r); continue; }

      if (DEBUGLEVEL>2)
      {
        if (DEBUGLEVEL>3)
        {
          err_printf("       prime ideal Q: %Ps\n",Q);
          err_printf("       matrix log(b_j mod Q_i): %Ps\n", M);
        }
        err_printf("       new rank: %ld\n",r);
      }
      if (r == rmax) return;
    }
  }
  pari_err_BUG("primecertify");
}

struct check_pr {
  long w; /* #mu(K) */
  GEN mu; /* generator of mu(K) */
  GEN fu;
  GEN cyc;
  GEN cycgen;
  GEN bad; /* p | bad <--> p | some element occurring in cycgen */
};

static void
check_prime(ulong p, GEN nf, struct check_pr *S)
{
  pari_sp av = avma;
  long i,b, lc = lg(S->cyc), lf = lg(S->fu);
  GEN beta = cgetg(lf+lc, t_VEC);

  if (DEBUGLEVEL>1) err_printf("  *** testing p = %lu\n",p);
  for (b=1; b<lc; b++)
  {
    if (umodiu(gel(S->cyc,b), p)) break; /* p \nmid cyc[b] */
    if (b==1 && DEBUGLEVEL>2) err_printf("     p divides h(K)\n");
    gel(beta,b) = gel(S->cycgen,b);
  }
  if (S->w % p == 0)
  {
    if (DEBUGLEVEL>2) err_printf("     p divides w(K)\n");
    gel(beta,b++) = S->mu;
  }
  for (i=1; i<lf; i++) gel(beta,b++) = gel(S->fu,i);
  setlg(beta, b); /* beta = [cycgen[i] if p|cyc[i], tu if p|w, fu] */
  if (DEBUGLEVEL>3) {err_printf("     Beta list = %Ps\n",beta); err_flush();}
  primecertify(nf, beta, p, S->bad); avma = av;
}

static void
init_bad(struct check_pr *S, GEN nf, GEN gen)
{
  long i, l = lg(gen);
  GEN bad = gen_1;

  for (i=1; i < l; i++)
    bad = lcmii(bad, gcoeff(gel(gen,i),1,1));
  for (i = 1; i < l; i++)
  {
    GEN c = gel(S->cycgen,i);
    long j;
    if (typ(c) == t_MAT)
    {
      GEN g = gel(c,1);
      for (j = 1; j < lg(g); j++)
      {
        GEN h = idealhnf_shallow(nf, gel(g,j));
        bad = lcmii(bad, gcoeff(h,1,1));
      }
    }
  }
  S->bad = bad;
}

long
bnfcertify0(GEN bnf, long flag)
{
  pari_sp av = avma;
  long N;
  GEN nf, cyc, B, U;
  ulong bound, p;
  struct check_pr S;
  forprime_t T;

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  N = nf_get_degree(nf); if (N==1) return 1;
  B = zimmertbound(nf_get_disc(nf), N, nf_get_r2(nf));
  if (is_bigint(B))
    pari_warn(warner,"Zimmert's bound is large (%Ps), certification will take a long time", B);
  if (!is_pm1(nf_get_index(nf)))
  {
    GEN D = nf_get_diff(nf), L;
    if (DEBUGLEVEL>1) err_printf("**** Testing Different = %Ps\n",D);
    L = bnfisprincipal0(bnf, D, nf_FORCE);
    if (DEBUGLEVEL>1) err_printf("     is %Ps\n", L);
  }
  if (DEBUGLEVEL)
  {
    err_printf("PHASE 1 [CLASS GROUP]: are all primes good ?\n");
    err_printf("  Testing primes <= %Ps\n", B); err_flush();
  }
  bnftestprimes(bnf, B);
  if (flag) return 1;

  U = bnf_build_units(bnf);
  cyc = bnf_get_cyc(bnf);
  S.w = bnf_get_tuN(bnf);
  S.mu = gel(U,1);
  S.fu = vecslice(U,2,lg(U)-1);
  S.cyc = cyc;
  S.cycgen = bnf_build_cycgen(bnf);
  init_bad(&S, nf, bnf_get_gen(bnf));

  B = bound_unit_index(bnf, S.fu);
  if (DEBUGLEVEL)
  {
    err_printf("PHASE 2 [UNITS/RELATIONS]: are all primes good ?\n");
    err_printf("  Testing primes <= %Ps\n", B); err_flush();
  }
  bound = itou_or_0(B);
  if (!bound) pari_err_OVERFLOW("bnfcertify [too many primes to check]");
  if (u_forprime_init(&T, 2, bound))
    while ( (p = u_forprime_next(&T)) ) check_prime(p, nf, &S);
  if (lg(cyc) > 1)
  {
    GEN f = Z_factor(gel(cyc,1)), P = gel(f,1);
    long i;
    if (DEBUGLEVEL>1) { err_printf("  Primes dividing h(K)\n\n"); err_flush(); }
    for (i = lg(P)-1; i; i--)
    {
      p = itou(gel(P,i)); if (p <= bound) break;
      check_prime(p, nf, &S);
    }
  }
  avma = av; return 1;
}
long
bnfcertify(GEN bnf) { return bnfcertify0(bnf, 0); }

/*******************************************************************/
/*                                                                 */
/*        RAY CLASS FIELDS: CONDUCTORS AND DISCRIMINANTS           */
/*                                                                 */
/*******************************************************************/
/* \chi(gen[i]) = zeta_D^chic[i])
 * denormalize: express chi(gen[i]) in terms of zeta_{cyc[i]} */
GEN
char_denormalize(GEN cyc, GEN D, GEN chic)
{
  long i, l = lg(chic);
  GEN chi = cgetg(l, t_VEC);
  /* \chi(gen[i]) = e(chic[i] / D) = e(chi[i] / cyc[i])
   * hence chi[i] = chic[i]cyc[i]/ D  mod cyc[i] */
  for (i = 1; i < l; ++i)
  {
    GEN di = gel(cyc, i), t = diviiexact(mulii(di, gel(chic,i)), D);
    gel(chi, i) = modii(t, di);
  }
  return chi;
}
static GEN
bnrchar_i(GEN bnr, GEN g, GEN v)
{
  long i, h, l = lg(g);
  GEN CH, D, U, U2, H, cyc, cycD, dv, dchi;
  checkbnr(bnr);
  switch(typ(g))
  {
    GEN G;
    case t_VEC:
      G = cgetg(l, t_MAT);
      for (i = 1; i < l; i++) gel(G,i) = isprincipalray(bnr, gel(g,i));
      g = G; break;
    case t_MAT:
      if (RgM_is_ZM(g)) break;
    default:
      pari_err_TYPE("bnrchar",g);
  }
  cyc = bnr_get_cyc(bnr);
  H = ZM_hnfall_i(shallowconcat(g,diagonal_shallow(cyc)), v? &U: NULL, 1);
  dv = NULL;
  if (v)
  {
    GEN w = Q_remove_denom(v, &dv);
    if (typ(v)!=t_VEC || lg(v)!=l || !RgV_is_ZV(w)) pari_err_TYPE("bnrchar",v);
    if (!dv) v = NULL;
    else
    {
      U = rowslice(U, 1, l-1);
      w = FpV_red(ZV_ZM_mul(w, U), dv);
      for (i = 1; i < l; i++)
        if (signe(gel(w,i))) pari_err_TYPE("bnrchar [inconsistent values]",v);
      v = vecslice(w,l,lg(w)-1);
    }
  }
  /* chi defined on subgroup H, chi(H[i]) = e(v[i] / dv)
   * unless v = NULL: chi|H = 1*/
  h = itos( ZM_det_triangular(H) ); /* #(clgp/H) = number of chars */
  if (h == 1) /* unique character, H = Id */
  {
    if (v)
      v = char_denormalize(cyc,dv,v);
    else
      v = zerovec(lg(cyc)-1); /* trivial char */
    return mkvec(v);
  }

  /* chi defined on a subgroup of index h > 1; U H V = D diagonal,
   * Z^#H / (H) = Z^#H / (D) ~ \oplus (Z/diZ) */
  D = ZM_snfall_i(H, &U, NULL, 1);
  cycD = cyc_normalize(D); gel(cycD,1) = gen_1; /* cycD[i] = d1/di */
  dchi = gel(D,1);
  U2 = ZM_diag_mul(cycD, U);
  if (v)
  {
    GEN Ui = ZM_inv(U,gen_1); /* U^(-1) */
    GEN Z = hnf_solve(H, ZM_mul_diag(Ui, D));
    v = ZV_ZM_mul(ZV_ZM_mul(v, Z), U2);
    dchi = mulii(dchi, dv);
    U2 = ZM_Z_mul(U2, dv);
  }
  CH = cyc2elts(D);
  for (i = 1; i <= h; i++)
  {
    GEN c = zv_ZM_mul(gel(CH,i), U2);
    if (v) c = ZC_add(c, v);
    gel(CH,i) = char_denormalize(cyc, dchi, c);
  }
  return CH;
}
GEN
bnrchar(GEN bnr, GEN g, GEN v)
{
  pari_sp av = avma;
  return gerepilecopy(av, bnrchar_i(bnr,g,v));
}

/* Let bnr1 with generators, bnr2 be such that mod(bnr2) | mod(bnr1), compute
 * the matrix of the surjective map Cl(bnr1) ->> Cl(bnr2) */
GEN
bnrsurjection(GEN bnr1, GEN bnr2)
{
  long l, i;
  GEN M, gen = bnr_get_gen(bnr1);
  l = lg(gen); M = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(M,i) = isprincipalray(bnr2, gel(gen,i));
  return M;
}

/* Given normalized chi on bnr.clgp of conductor bnrc.mod,
 * compute primitive character chic on bnrc.clgp equivalent to chi,
 * still normalized wrt. bnr:
 *   chic(genc[i]) = zeta_C^chic[i]), C = cyc_normalize(bnr.cyc)[1] */
GEN
bnrchar_primitive(GEN bnr, GEN nchi, GEN bnrc)
{
  GEN Mc, U, M = bnrsurjection(bnr, bnrc);
  long l = lg(M);

  Mc = diagonal_shallow(bnr_get_cyc(bnrc));
  (void)ZM_hnfall_i(shallowconcat(M, Mc), &U, 1); /* identity */
  U = matslice(U,1,l-1, l,lg(U)-1);
  return char_simplify(gel(nchi,1), ZV_ZM_mul(gel(nchi,2), U));
}

/* s: <gen> = Cl_f --> Cl_f2 --> 0, H subgroup of Cl_f (generators given as
 * HNF on [gen]). Return subgroup s(H) in Cl_f2. bnr must include generators */
static GEN
imageofgroup(GEN bnr, GEN bnr2, GEN H)
{
  GEN H2, cyc2 = bnr_get_cyc(bnr2);
  if (!H) return diagonal_shallow(cyc2);
  H2 = ZM_mul(bnrsurjection(bnr, bnr2), H);
  return ZM_hnfmodid(H2, cyc2); /* s(H) in Cl_n */
}
static GEN
imageofchar(GEN bnr, GEN bnrc, GEN chi)
{
  GEN nchi = char_normalize(chi, cyc_normalize(bnr_get_cyc(bnr)));
  GEN DC = bnrchar_primitive(bnr, nchi, bnrc);
  return char_denormalize(bnr_get_cyc(bnrc), gel(DC,1), gel(DC,2));
}

/* convert A,B,C to [bnr, H] */
GEN
ABC_to_bnr(GEN A, GEN B, GEN C, GEN *H, int gen)
{
  if (typ(A) == t_VEC)
    switch(lg(A))
    {
      case 7: /* bnr */
        *H = B; return A;
      case 11: /* bnf */
        if (!B) pari_err_TYPE("ABC_to_bnr [bnf+missing conductor]",A);
        *H = C; return Buchray(A,B, gen? nf_INIT | nf_GEN: nf_INIT);
    }
  pari_err_TYPE("ABC_to_bnr",A);
  *H = NULL; return NULL; /* not reached */
}

GEN
bnrconductor0(GEN A, GEN B, GEN C, long flag)
{
  pari_sp av = avma;
  GEN H, bnr = ABC_to_bnr(A,B,C,&H, flag > 0);
  return gerepilecopy(av, bnrconductor_i(bnr, H, flag));
}

long
bnrisconductor0(GEN A,GEN B,GEN C)
{
  GEN H, bnr = ABC_to_bnr(A,B,C,&H, 0);
  return bnrisconductor(bnr, H);
}

/* return bnrisprincipal(bnr, (x)), assuming z = ideallog(x) */
static GEN
ideallog_to_bnr(GEN bnr, GEN z)
{
  GEN U = gel(bnr,4), divray = bnr_get_cyc(bnr);
  long j, l, lU, lz;
  int col;

  if (lg(z) == 1) return z;
  col = (typ(z) == t_COL); /* else t_MAT */
  lz = col? lg(z): lgcols(z);
  lU = lg(U);
  if (lz != lU)
  {
    if (lz == 1) return zerocol(nbrows(U)); /* lU != 1 */
    U = vecslice(U, lU-lz+1, lU-1); /* remove Cl(K) part */
  }
  if (col) {
    z = ZM_ZC_mul(U, z);
    z = vecmodii(z, divray);
  } else {
    z = ZM_mul(U, z); l = lg(z);
    for (j = 1; j < l; j++) gel(z,j) = vecmodii(gel(z,j), divray);
  }
  return z;
}
static GEN
bnr_log_gen_pr(GEN bnr, zlog_S *S, GEN nf, long e, long index)
{ return ideallog_to_bnr(bnr, log_gen_pr(S, index, nf, e)); }
static GEN
bnr_log_gen_arch(GEN bnr, zlog_S *S, long index)
{ return ideallog_to_bnr(bnr, log_gen_arch(S, index)); }

/* A \subset H ? Allow H = NULL = trivial subgroup */
static int
contains(GEN H, GEN A)
{ return H? (hnf_solve(H, A) != NULL): gequal0(A); }

/* (see also Discrayrel). Given a number field bnf=bnr[1], a ray class
 * group structure bnr (with generators if flag > 0), and a subgroup H of the
 * ray class group, compute the conductor of H if flag=0. If flag > 0, compute
 * furthermore the corresponding H' and output
 * if flag = 1: [[ideal,arch],[hm,cyc,gen],H']
 * if flag = 2: [[ideal,arch],newbnr,H'] */
GEN
bnrconductor_i(GEN bnr, GEN H0, long flag)
{
  long j, k, l;
  GEN bnf, nf, bid, ideal, archp, clhray, bnrc, e2, e, cond, H;
  int iscond0 = 1, iscondinf = 1, ischi;
  zlog_S S;

  checkbnr(bnr);
  bnf = bnr_get_bnf(bnr);
  bid = bnr_get_bid(bnr); init_zlog_bid(&S, bid);
  nf = bnf_get_nf(bnf);
  H = check_subgroup(bnr, H0, &clhray);

  archp = leafcopy(S.archp);
  e     = S.e; l = lg(e);
  e2 = cgetg(l, t_COL);
  for (k = 1; k < l; k++)
  {
    for (j = itos(gel(e,k)); j > 0; j--)
    {
      if (!contains(H, bnr_log_gen_pr(bnr, &S, nf, j, k))) break;
      iscond0 = 0;
    }
    gel(e2,k) = stoi(j);
  }
  l = lg(archp);
  for (k = 1; k < l; k++)
  {
    if (!contains(H, bnr_log_gen_arch(bnr, &S, k))) continue;
    archp[k] = 0;
    iscondinf = 0;
  }
  if (!iscondinf)
  {
    for (j = k = 1; k < l; k++)
      if (archp[k]) archp[j++] = archp[k];
    setlg(archp, j);
  }
  ideal = iscond0? bid_get_ideal(bid): factorbackprime(nf, S.P, e2);
  cond = mkvec2(ideal, indices_to_vec01(archp, nf_get_r1(nf)));
  if (!flag) return cond;

  /* character or subgroup ? */
  ischi = H0 && typ(H0) == t_VEC;
  if (iscond0 && iscondinf)
  {
    bnrc = bnr;
    if (ischi)
      H = H0;
    else if (!H)
      H = diagonal_shallow(bnr_get_cyc(bnr));
  }
  else
  {
    bnrc = Buchray(bnf, cond, nf_INIT | nf_GEN);
    if (ischi)
      H = imageofchar(bnr, bnrc, H0);
    else
      H = imageofgroup(bnr, bnrc, H);
  }

  if (flag == 1) bnrc = bnr_get_clgp(bnrc);
  return mkvec3(cond, bnrc, H);
}
GEN
bnrconductor(GEN bnr, GEN H0, long flag)
{
  pari_sp av = avma;
  return gerepilecopy(av, bnrconductor_i(bnr,H0,flag));
}

long
bnrisconductor(GEN bnr, GEN H0)
{
  pari_sp av = avma;
  long j, k, l;
  GEN bnf, nf, bid, archp, clhray, e, H;
  zlog_S S;

  checkbnr(bnr);
  bnf = bnr_get_bnf(bnr);
  bid = bnr_get_bid(bnr); init_zlog_bid(&S, bid);
  nf = bnf_get_nf(bnf);
  H = check_subgroup(bnr, H0, &clhray);

  archp = S.archp;
  e     = S.e; l = lg(e);
  for (k = 1; k < l; k++)
  {
    j = itos(gel(e,k));
    if (contains(H, bnr_log_gen_pr(bnr, &S, nf, j, k))) { avma = av; return 0; }
  }
  l = lg(archp);
  for (k = 1; k < l; k++)
    if (contains(H, bnr_log_gen_arch(bnr, &S, k))) { avma = av; return 0; }
  avma = av; return 1;
}

/* return the norm group corresponding to the relative extension given by
 * polrel over bnr.bnf, assuming it is abelian and the modulus of bnr is a
 * multiple of the conductor */
static GEN
rnfnormgroup_i(GEN bnr, GEN polrel)
{
  long i, j, degrel, degnf, k;
  GEN bnf, index, discnf, nf, G, detG, fa, gdegrel;
  GEN fac, col, cnd;
  forprime_t S;
  ulong p;

  checkbnr(bnr); bnf = bnr_get_bnf(bnr);
  nf = bnf_get_nf(bnf);
  cnd = gel(bnr_get_mod(bnr), 1);
  polrel = RgX_nffix("rnfnormgroup", nf_get_pol(nf),polrel,1);
  if (!gequal1(leading_coeff(polrel)))
    pari_err_IMPL("rnfnormgroup for non-monic polynomials");

  degrel = degpol(polrel);
  if (umodiu(bnr_get_no(bnr), degrel)) return NULL;
  /* degrel-th powers are in norm group */
  gdegrel = utoipos(degrel);
  G = FpC_red(bnr_get_cyc(bnr), gdegrel);
  for (i=1; i<lg(G); i++)
    if (!signe(gel(G,i))) gel(G,i) = gdegrel;
  detG = ZV_prod(G);
  k = abscmpiu(detG,degrel);
  if (k < 0) return NULL;
  if (!k) return diagonal(G);

  G = diagonal_shallow(G);
  discnf = nf_get_disc(nf);
  index  = nf_get_index(nf);
  degnf = nf_get_degree(nf);
  u_forprime_init(&S, 2, ULONG_MAX);
  while ( (p = u_forprime_next(&S)) )
  {
    long oldf, nfa;
    /* If all pr are unramified and have the same residue degree, p =prod pr
     * and including last pr^f or p^f is the same, but the last isprincipal
     * is much easier! oldf is used to track this */

    if (!umodiu(index, p)) continue; /* can't be treated efficiently */

    /* primes of degree 1 are enough, and simpler */
    fa = idealprimedec_limit_f(nf, utoipos(p), 1);
    nfa = lg(fa)-1;
    if (!nfa) continue;
    /* all primes above p included ? */
    oldf = (nfa == degnf)? -1: 0;
    for (i=1; i<=nfa; i++)
    {
      GEN pr = gel(fa,i), pp, T, polr, modpr;
      long f, nfac;
      /* if pr (probably) ramified, we have to use all (non-ram) P | pr */
      if (idealval(nf,cnd,pr)) { oldf = 0; continue; }
      modpr = zk_to_Fq_init(nf, &pr, &T, &pp); /* T = NULL, pp ignored */
      polr = nfX_to_FqX(polrel, nf, modpr); /* in Fp[X] */
      polr = ZX_to_Flx(polr, p);
      if (!Flx_is_squarefree(polr, p)) { oldf = 0; continue; }

      fac = gel(Flx_factor(polr, p), 1);
      f = degpol(gel(fac,1));
      if (f == degrel) continue; /* degrel-th powers already included */
      nfac = lg(fac)-1;
      /* check decomposition of pr has Galois type */
      for (j=2; j<=nfac; j++)
        if (degpol(gel(fac,j)) != f) return NULL;
      if (oldf < 0) oldf = f; else if (oldf != f) oldf = 0;

      /* last prime & all pr^f, pr | p, included. Include p^f instead */
      if (oldf && i == nfa && degrel == nfa*f && !umodiu(discnf, p))
        pr = utoipos(p);

      /* pr^f = N P, P | pr, hence is in norm group */
      col = bnrisprincipal(bnr,pr,0);
      if (f > 1) col = ZC_z_mul(col, f);
      G = ZM_hnf(shallowconcat(G, col));
      detG = ZM_det_triangular(G);
      k = abscmpiu(detG,degrel);
      if (k < 0) return NULL;
      if (!k) { cgiv(detG); return G; }
    }
  }
  return NULL;
}
GEN
rnfnormgroup(GEN bnr, GEN polrel)
{
  pari_sp av = avma;
  GEN G = rnfnormgroup_i(bnr, polrel);
  if (!G) { avma = av; return cgetg(1,t_MAT); }
  return gerepileupto(av, G);
}

GEN
nf_deg1_prime(GEN nf)
{
  GEN z, T = nf_get_pol(nf), D = nf_get_disc(nf), f = nf_get_index(nf);
  long degnf = degpol(T);
  forprime_t S;
  pari_sp av;
  ulong p;
  u_forprime_init(&S, degnf, ULONG_MAX);
  av = avma;
  while ( (p = u_forprime_next(&S)) )
  {
    ulong r;
    if (!umodiu(D, p) || !umodiu(f, p)) continue;
    r = Flx_oneroot(ZX_to_Flx(T,p), p);
    if (r != p)
    {
      z = utoi(Fl_neg(r, p));
      z = deg1pol_shallow(gen_1, z, varn(T));
      return idealprimedec_kummer(nf, z, 1, utoipos(p));
    }
    avma = av;
  }
  return NULL;
}

long
rnfisabelian(GEN nf, GEN pol)
{
  GEN modpr, pr, T, Tnf, pp, ro, nfL, C, a, sig, eq;
  long i, j, l, v;
  ulong p, k, ka;

  if (typ(nf) == t_POL)
    Tnf = nf;
  else {
    nf = checknf(nf);
    Tnf = nf_get_pol(nf);
  }
  v = varn(Tnf);
  pol = RgX_nffix("rnfisabelian",Tnf,pol,1);
  eq = nf_rnfeq(nf,pol); /* init L := K[x]/(pol), nf attached to K */
  C = gel(eq,1); setvarn(C, v); /* L = Q[t]/(C) */
  a = gel(eq,2); setvarn(a, v); /* root of K.pol in L */
  nfL = C;
  ro = nfroots_if_split(&nfL, QXX_QXQ_eval(pol, a, C));
  if (!ro) return 0;
  l = lg(ro)-1;
  /* small groups are abelian, as are groups of prime order */
  if (l < 6 || uisprime(l)) return 1;

  pr = nf_deg1_prime(nfL);
  modpr = nf_to_Fq_init(nfL, &pr, &T, &pp);
  p = itou(pp);
  k = umodiu(gel(eq,3), p);
  ka = (k * itou(nf_to_Fq(nfL, a, modpr))) % p;
  sig= cgetg(l+1, t_VECSMALL);
  /* image of c = ro[1] + k a [distinguished root of C] by the l automorphisms
   * sig[i]: ro[1] -> ro[i] */
  for (i = 1; i <= l; i++)
    sig[i] = Fl_add(ka, itou(nf_to_Fq(nfL, gel(ro,i), modpr)), p);
  ro = Q_primpart(ro);
  for (i=2; i<=l; i++) { /* start at 2, since sig[1] = identity */
    gel(ro,i) = ZX_to_Flx(gel(ro,i), p);
    for (j=2; j<i; j++)
      if (Flx_eval(gel(ro,j), sig[i], p)
       != Flx_eval(gel(ro,i), sig[j], p)) return 0;
  }
  return 1;
}

/* Given bnf and polrel defining an abelian relative extension, compute the
 * corresponding conductor and congruence subgroup. Return
 * [cond,bnr(cond),group] where cond=[ideal,arch] is the conductor. */
GEN
rnfconductor(GEN bnf, GEN polrel)
{
  pari_sp av = avma;
  GEN nf, module, bnr, group, den, D;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (typ(polrel) != t_POL) pari_err_TYPE("rnfconductor",polrel);
  den = Q_denom( RgX_to_nfX(nf, polrel) );
  if (!is_pm1(den)) polrel = RgX_rescale(polrel, den);
  (void)rnfallbase(nf,&polrel, &D, NULL, NULL);
  module = mkvec2(D, const_vec(nf_get_r1(nf), gen_1));
  bnr   = Buchray(bnf,module,nf_INIT | nf_GEN);
  group = rnfnormgroup_i(bnr,polrel);
  if (!group) { avma = av; return gen_0; }
  return gerepilecopy(av, bnrconductor_i(bnr,group,2));
}

/* Given a number field bnf=bnr[1], a ray class group structure bnr, and a
 * subgroup H (HNF form) of the ray class group, compute [n, r1, dk]
 * attached to H. If flcond = 1, abort (return gen_0) if
 * module is not the conductor If flrel = 0, compute only N(dk) instead of
 * the ideal dk proper */
static GEN
Discrayrel(GEN bnr, GEN H0, long flag)
{
  pari_sp av = avma;
  long j, k, l, nz, flrel = flag & rnf_REL, flcond = flag & rnf_COND;
  GEN bnf, nf, bid, ideal, archp, clhray, clhss, P, e, dlk;
  zlog_S S;

  checkbnr(bnr);
  bnf = bnr_get_bnf(bnr);
  bid = bnr_get_bid(bnr); init_zlog_bid(&S, bid);
  nf = bnf_get_nf(bnf);
  ideal= bid_get_ideal(bid);
  H0 = check_subgroup(bnr, H0, &clhray);
  if (!H0) H0 = diagonal_shallow(bnr_get_cyc(bnr));
  archp = S.archp;
  P     = S.P;
  e     = S.e; l = lg(e);
  dlk = flrel? idealpow(nf,ideal,clhray)
             : powii(ZM_det_triangular(ideal),clhray);
  for (k = 1; k < l; k++)
  {
    GEN pr = gel(P,k), sum = gen_0, H = H0;
    long ep = itos(gel(e,k));
    for (j = ep; j > 0; j--)
    {
      GEN z = bnr_log_gen_pr(bnr, &S, nf, j, k);
      H = ZM_hnf(shallowconcat(H, z));
      clhss = ZM_det_triangular(H);
      if (flcond && j==ep && equalii(clhss,clhray)) { avma = av; return gen_0; }
      if (is_pm1(clhss)) { sum = addis(sum, j); break; }
      sum = addii(sum, clhss);
    }
    dlk = flrel? idealdivpowprime(nf, dlk, pr, sum)
               : diviiexact(dlk, powii(pr_norm(pr),sum));
  }
  l = lg(archp); nz = nf_get_r1(nf) - (l-1);
  for (k = 1; k < l; k++)
  {
    if (!contains(H0, bnr_log_gen_arch(bnr, &S, k))) continue;
    if (flcond) { avma = av; return gen_0; }
    nz++;
  }
  return gerepilecopy(av, mkvec3(clhray, stoi(nz), dlk));
}

GEN
bnrdisc(GEN bnr, GEN H, long flag)
{
  pari_sp av = avma;
  long clhray, n, R1;
  GEN z, p1, D, dk, nf, dkabs;

  D = Discrayrel(bnr, H, flag);
  if ((flag & rnf_REL) || D == gen_0) return D;

  nf = checknf(bnr);
  dkabs = absi(nf_get_disc(nf));
  clhray = itos(gel(D,1)); p1 = powiu(dkabs, clhray);
  n = clhray * nf_get_degree(nf);
  R1= clhray * itos(gel(D,2));
  dk = gel(D,3);
  if (((n-R1)&3) == 2) dk = negi(dk); /* (2r2) mod 4 = 2 : r2(relext) is odd */
  z = cgetg(4,t_VEC);
  gel(z,1) = utoipos(n);
  gel(z,2) = stoi(R1);
  gel(z,3) = mulii(dk,p1); return gerepileupto(av, z);
}

GEN
bnrdisc0(GEN A, GEN B, GEN C, long flag)
{
  GEN H, bnr = ABC_to_bnr(A,B,C,&H, 0);
  return bnrdisc(bnr,H,flag);
}

/* Given a number field bnf=bnr[1], a ray class group structure bnr and a
 * vector chi representing a character on the generators bnr[2][3], compute
 * the conductor of chi. */
GEN
bnrconductorofchar(GEN bnr, GEN chi)
{
  pari_sp av = avma;
  GEN cyc, K;
  checkbnr(bnr);
  cyc = bnr_get_cyc(bnr);
  if (!char_check(cyc,chi)) pari_err_TYPE("bnrconductorofchar",chi);
  K = charker(cyc,chi); if (lg(K) == 1) K = NULL;
  return gerepilecopy(av, bnrconductor_i(bnr, K, 0));
}

/* t = [bid,U], h = #Cl(K) */
static GEN
get_classno(GEN t, GEN h)
{
  GEN bid = gel(t,1), m = gel(t,2), cyc = bid_get_cyc(bid);
  return mulii(h, ZM_det_triangular(ZM_hnfmodid(m, cyc)));
}

static void
chk_listBU(GEN L, const char *s) {
  if (typ(L) != t_VEC) pari_err_TYPE(s,L);
  if (lg(L) > 1) {
    GEN z = gel(L,1);
    if (typ(z) != t_VEC) pari_err_TYPE(s,z);
    if (lg(z) == 1) return;
    z = gel(z,1); /* [bid,U] */
    if (typ(z) != t_VEC || lg(z) != 3) pari_err_TYPE(s,z);
    checkbid(gel(z,1));
  }
}

/* Given lists of [bid, unit ideallogs], return lists of ray class
 * numbers */
GEN
bnrclassnolist(GEN bnf,GEN L)
{
  pari_sp av = avma;
  long i, j, lz, l = lg(L);
  GEN v, z, V, h;

  chk_listBU(L, "bnrclassnolist");
  if (l == 1) return cgetg(1, t_VEC);
  bnf = checkbnf(bnf); h = bnf_get_no(bnf);
  V = cgetg(l,t_VEC);
  for (i = 1; i < l; i++)
  {
    z = gel(L,i); lz = lg(z);
    gel(V,i) = v = cgetg(lz,t_VEC);
    for (j=1; j<lz; j++) gel(v,j) = get_classno(gel(z,j), h);
  }
  return gerepilecopy(av, V);
}

static GEN
Lbnrclassno(GEN L, GEN fac)
{
  long i, l = lg(L);
  for (i=1; i<l; i++)
    if (gequal(gmael(L,i,1),fac)) return gmael(L,i,2);
  pari_err_BUG("Lbnrclassno");
  return NULL; /* not reached */
}

static GEN
factordivexact(GEN fa1,GEN fa2)
{
  long i, j, k, c, l;
  GEN P, E, P1, E1, P2, E2, p1;

  P1 = gel(fa1,1); E1 = gel(fa1,2); l = lg(P1);
  P2 = gel(fa2,1); E2 = gel(fa2,2);
  P = cgetg(l,t_COL);
  E = cgetg(l,t_COL);
  for (c = i = 1; i < l; i++)
  {
    j = RgV_isin(P2,gel(P1,i));
    if (!j) { gel(P,c) = gel(P1,i); gel(E,c) = gel(E1,i); c++; }
    else
    {
      p1 = subii(gel(E1,i), gel(E2,j)); k = signe(p1);
      if (k < 0) pari_err_BUG("factordivexact [not exact]");
      if (k > 0) { gel(P,c) = gel(P1,i); gel(E,c) = p1; c++; }
    }
  }
  setlg(P, c);
  setlg(E, c); return mkmat2(P, E);
}
/* remove index k */
static GEN
factorsplice(GEN fa, long k)
{
  GEN p = gel(fa,1), e = gel(fa,2), P, E;
  long i, l = lg(p) - 1;
  P = cgetg(l, typ(p));
  E = cgetg(l, typ(e));
  for (i=1; i<k; i++) { P[i] = p[i]; E[i] = e[i]; }
  p++; e++;
  for (   ; i<l; i++) { P[i] = p[i]; E[i] = e[i]; }
  return mkmat2(P,E);
}
static GEN
factorpow(GEN fa, long n)
{
  if (!n) return trivial_fact();
  return mkmat2(gel(fa,1), gmulsg(n, gel(fa,2)));
}
static GEN
factormul(GEN fa1,GEN fa2)
{
  GEN p, pnew, e, enew, v, P, y = famat_mul_shallow(fa1,fa2);
  long i, c, lx;

  p = gel(y,1); v = indexsort(p); lx = lg(p);
  e = gel(y,2);
  pnew = vecpermute(p, v);
  enew = vecpermute(e, v);
  P = gen_0; c = 0;
  for (i=1; i<lx; i++)
  {
    if (gequal(gel(pnew,i),P))
      gel(e,c) = addii(gel(e,c),gel(enew,i));
    else
    {
      c++; P = gel(pnew,i);
      gel(p,c) = P;
      gel(e,c) = gel(enew,i);
    }
  }
  setlg(p, c+1);
  setlg(e, c+1); return y;
}


static long
get_nz(GEN bnf, GEN ideal, GEN arch, long clhray)
{
  GEN arch2, mod;
  long nz = 0, l = lg(arch), k, clhss;
  if (typ(arch) == t_VECSMALL)
    arch2 = indices_to_vec01(arch,nf_get_r1(bnf_get_nf(bnf)));
  else
    arch2 = leafcopy(arch);
  mod = mkvec2(ideal, arch2);
  for (k = 1; k < l; k++)
  { /* FIXME: this is wasteful. Use the same algorithm as bnrconductor */
    if (signe(gel(arch2,k)))
    {
      gel(arch2,k) = gen_0; clhss = itos(bnrclassno(bnf,mod));
      gel(arch2,k) = gen_1;
      if (clhss == clhray) return -1;
    }
    else nz++;
  }
  return nz;
}

static GEN
get_NR1D(long Nf, long clhray, long degk, long nz, GEN fadkabs, GEN idealrel)
{
  long n, R1;
  GEN dlk;
  if (nz < 0) mkvec3(gen_0,gen_0,gen_0); /*EMPTY*/
  n  = clhray * degk;
  R1 = clhray * nz;
  dlk = factordivexact(factorpow(Z_factor(utoipos(Nf)),clhray), idealrel);
  /* r2 odd, set dlk = -dlk */
  if (((n-R1)&3)==2) dlk = factormul(to_famat_shallow(gen_m1,gen_1), dlk);
  return mkvec3(utoipos(n),
                stoi(R1),
                factormul(dlk,factorpow(fadkabs,clhray)));
}

/* t = [bid,U], h = #Cl(K) */
static GEN
get_discdata(GEN t, GEN h)
{
  GEN bid = gel(t,1), fa = bid_get_fact(bid);
  GEN P = gel(fa,1), E = vec_to_vecsmall(gel(fa,2));
  return mkvec3(mkmat2(P, E), (GEN)itou(get_classno(t, h)), bid_get_mod(bid));
}
typedef struct _disc_data {
  long degk;
  GEN bnf, fadk, idealrelinit, V;
} disc_data;

static GEN
get_discray(disc_data *D, GEN V, GEN z, long N)
{
  GEN idealrel = D->idealrelinit;
  GEN mod = gel(z,3), Fa = gel(z,1);
  GEN P = gel(Fa,1), E = gel(Fa,2);
  long k, nz, clhray = z[2], lP = lg(P);
  for (k=1; k<lP; k++)
  {
    GEN pr = gel(P,k), p = pr_get_p(pr);
    long e, ep = E[k], f = pr_get_f(pr);
    long S = 0, norm = N, Npr = upowuu(p[2],f), clhss;
    for (e=1; e<=ep; e++)
    {
      GEN fad;
      if (e < ep) { E[k] = ep-e; fad = Fa; }
      else fad = factorsplice(Fa, k);
      norm /= Npr;
      clhss = (long)Lbnrclassno(gel(V,norm), fad);
      if (e==1 && clhss==clhray) { E[k] = ep; return cgetg(1, t_VEC); }
      if (clhss == 1) { S += ep-e+1; break; }
      S += clhss;
    }
    E[k] = ep;
    idealrel = factormul(idealrel, to_famat_shallow(p, utoi(f * S)));
  }
  nz = get_nz(D->bnf, gel(mod,1), gel(mod,2), clhray);
  return get_NR1D(N, clhray, D->degk, nz, D->fadk, idealrel);
}

/* Given a list of bids and attached unit log matrices, return the
 * list of discrayabs. Only keep moduli which are conductors. */
GEN
discrayabslist(GEN bnf, GEN L)
{
  pari_sp av = avma;
  long i, l = lg(L);
  GEN nf, V, D, h;
  disc_data ID;

  chk_listBU(L, "discrayabslist");
  if (l == 1) return cgetg(1, t_VEC);
  ID.bnf = bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  h = bnf_get_no(bnf);
  ID.degk = nf_get_degree(nf);
  ID.fadk = absZ_factor(nf_get_disc(nf));
  ID.idealrelinit = trivial_fact();
  V = cgetg(l, t_VEC);
  D = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN z = gel(L,i), v, d;
    long j, lz = lg(z);
    gel(V,i) = v = cgetg(lz,t_VEC);
    gel(D,i) = d = cgetg(lz,t_VEC);
    for (j=1; j<lz; j++) {
      gel(d,j) = get_discdata(gel(z,j), h);
      gel(v,j) = get_discray(&ID, D, gel(d,j), i);
    }
  }
  return gerepilecopy(av, V);
}

/* BIG VECTOR:
 * Interface: a container v whose length is arbitrary (< 2^30), bigel(v,i)
 * refers to the i-th component. It is an lvalue.
 *
 * Implementation: a vector v whose components have exactly 2^LGVINT entries
 * but for the last one which is allowed to be shorter. v[i][j]
 * (where j<=2^LGVINT) is understood as component number I = (i-1)*2^LGVINT+j
 * in a unique huge vector V. */
static const int SHLGVINT = 15;
static const long LGVINT = 1L << 15;
INLINE long vext0(ulong i) { return ((i-1)>>SHLGVINT) + 1; }
INLINE long vext1(ulong i) { return i & (LGVINT-1); }
#define bigel(v,i) gmael((v), vext0(i), vext1(i))

/* allocate an extended vector (t_VEC of t_VEC) for N _true_ components */
static GEN
bigcgetvec(long N)
{
  long i, nv = vext0(N);
  GEN v = cgetg(nv+1,t_VEC);
  for (i=1; i<nv; i++) gel(v,i) = cgetg(LGVINT+1,t_VEC);
  gel(v,nv) = cgetg(vext1(N)+1,t_VEC); return v;
}

/* a zsimp is [fa, cyc, U, v]
 * fa: vecsmall factorisation,
 * cyc: ZV (abelian group)
 * U: ZM (base change)
 * v: ZV (log of units) */
static GEN
zsimp(GEN bid, GEN embunit)
{
  GEN empty = cgetg(1, t_VECSMALL);
  return mkvec4(mkmat2(empty,empty), bid_get_cyc(bid), bid_get_U(bid), embunit);
}

/* fa a vecsmall factorization, append p^e */
static GEN
fasmall_append(GEN fa, long p, long e)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  retmkmat2(vecsmall_append(P,p), vecsmall_append(E,e));
}

static GEN
zsimpjoin(GEN b, GEN bid, GEN embunit, long prcode, long e)
{
  long l1, l2, nbgen;
  pari_sp av = avma;
  GEN fa, U, U1, U2, cyc1, cyc2, cyc;

  fa = gel(b,1);
  U1 = gel(b,3);       cyc1 = gel(b,2);         l1 = lg(cyc1);
  U2 = bid_get_U(bid); cyc2 = bid_get_cyc(bid); l2 = lg(cyc2);
  nbgen = l1+l2-2;
  if (nbgen)
  {
    cyc = ZV_snfall(shallowconcat(cyc1,cyc2), &U, NULL);
    ZM_snfclean(cyc, U, NULL);
    U = shallowconcat(
      l1==1   ? zeromat(nbgen, lg(U1)-1): ZM_mul(vecslice(U, 1,   l1-1), U1),
      l1>nbgen? zeromat(nbgen, lg(U2)-1): ZM_mul(vecslice(U, l1, nbgen), U2)
    );
  }
  else
  {
    U = zeromat(0, lg(U1)+lg(U2)-2);
    cyc = cgetg(1,t_VEC);
  }
  fa = fasmall_append(fa, prcode, e);
  return gerepilecopy(av, mkvec4(fa, cyc, U, vconcat(gel(b,4),embunit)));
}
/* B a zsimp */
static GEN
bnrclassnointern(GEN B, GEN h)
{
  long lx = lg(B), j;
  GEN L = cgetg(lx,t_VEC);
  for (j=1; j<lx; j++)
  {
    GEN b = gel(B,j), qm = ZM_mul(gel(b,3),gel(b,4));
    GEN m = ZM_det_triangular( ZM_hnfmodid(qm, gel(b,2)) );
    gel(L,j) = mkvec2(gel(b,1), mkvecsmall( itou( mulii(h, m) ) ));
  }
  return L;
}

static void
vecselect_p(GEN A, GEN B, GEN p, long init, long lB)
{
  long i; setlg(B, lB);
  for (i=init; i<lB; i++) B[i] = A[p[i]];
}
/* B := p . A = row selection according to permutation p. Treat only lower
 * right corner init x init */
static void
rowselect_p(GEN A, GEN B, GEN p, long init)
{
  long i, lB = lg(A), lp = lg(p);
  for (i=1; i<init; i++) setlg(B[i],lp);
  for (   ; i<lB;   i++) vecselect_p(gel(A,i),gel(B,i),p,init,lp);
}

static GEN
bnrclassnointernarch(GEN B, GEN h, GEN matU)
{
  long lx, nc, k, kk, j, r1, jj, nba, nbarch;
  GEN _2, b, qm, L, cyc, m, H, mm, rowsel;

  if (!matU) return bnrclassnointern(B,h);
  lx = lg(B); if (lx == 1) return B;

  r1 = nbrows(matU); _2 = const_vec(r1, gen_2);
  L = cgetg(lx,t_VEC); nbarch = 1L<<r1;
  for (j=1; j<lx; j++)
  {
    b = gel(B,j); qm = ZM_mul(gel(b,3),gel(b,4));
    cyc = gel(b,2); nc = lg(cyc)-1;
    /* [ qm   cyc 0 ]
     * [ matU  0  2 ] */
    m = ZM_hnfmodid(vconcat(qm, matU), shallowconcat(cyc,_2));
    mm = RgM_shallowcopy(m);
    H = cgetg(nbarch+1,t_VECSMALL);
    rowsel = cgetg(nc+r1+1,t_VECSMALL);
    for (k = 0; k < nbarch; k++)
    {
      nba = nc+1;
      for (kk=k,jj=1; jj<=r1; jj++,kk>>=1)
        if (kk&1) rowsel[nba++] = nc + jj;
      setlg(rowsel, nba);
      rowselect_p(m, mm, rowsel, nc+1);
      H[k+1] = itou( mulii(h, ZM_det_triangular(ZM_hnf(mm))) );
    }
    gel(L,j) = mkvec2(gel(b,1), H);
  }
  return L;
}

GEN
decodemodule(GEN nf, GEN fa)
{
  long n, nn, k;
  pari_sp av = avma;
  GEN G, E, id, pr;

  nf = checknf(nf);
  if (typ(fa)!=t_MAT || lg(fa)!=3)
    pari_err_TYPE("decodemodule [not a factorization]", fa);
  n = nf_get_degree(nf); nn = n*n; id = NULL;
  G = gel(fa,1);
  E = gel(fa,2);
  for (k=1; k<lg(G); k++)
  {
    long code = G[k], p = code / nn, j = (code%n)+1;
    GEN P = idealprimedec(nf, utoipos(p)), e = stoi(E[k]);
    if (lg(P) <= j) pari_err_BUG("decodemodule [incorrect hash code]");
    pr = gel(P,j);
    id = id? idealmulpowprime(nf,id, pr,e)
           : idealpow(nf, pr,e);
  }
  if (!id) { avma = av; return matid(n); }
  return gerepileupto(av,id);
}

/* List of ray class fields. Do all from scratch, bound < 2^30. No subgroups.
 *
 * Output: a "big vector" V (cf bigcgetvec). V[k] is a vector indexed by
 * the ideals of norm k. Given such an ideal m, the component is as follows:
 *
 * + if arch = NULL, run through all possible archimedean parts; archs are
 * ordered using inverse lexicographic order, [0,..,0], [1,0,..,0], [0,1,..,0],
 * Component is [m,V] where V is a vector with 2^r1 entries, giving for each
 * arch the triple [N,R1,D], with N, R1, D as in discrayabs; D is in factored
 * form.
 *
 * + otherwise [m,N,R1,D] */
GEN
discrayabslistarch(GEN bnf, GEN arch, ulong bound)
{
  int allarch = (arch==NULL), flbou = 0;
  long degk, j, k, l, nba, nbarch, r1, c;
  pari_sp av0 = avma,  av,  av1;
  GEN nf, p, Z, fa, bidp, matarchunit, Disc, U, sgnU, EMPTY, empty;
  GEN res, embunit, h, Ray, discall, idealrel, idealrelinit, fadkabs, BOUND;
  ulong i, ii, sqbou;
  forprime_t S;

  if (bound == 0)
    pari_err_DOMAIN("discrayabslistarch","bound","==",gen_0,utoi(bound));
  res = discall = NULL; /* -Wall */

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf); r1 = nf_get_r1(nf);
  degk = nf_get_degree(nf);
  fadkabs = absZ_factor(nf_get_disc(nf));
  h = bnf_get_no(bnf);
  U = bnf_build_units(bnf);
  sgnU = nfsign_units(bnf, NULL, 1);

  if (allarch) {
    arch = const_vec(r1, gen_1);
    bidp = Idealstar(nf, mkvec2(gen_1, arch), nf_INIT);
    matarchunit = zlog_units(nf, U, sgnU, bidp);
    bidp = Idealstar(nf, gen_1, nf_INIT);
    if (r1>15) pari_err_IMPL("r1>15 in discrayabslistarch");
    nba = r1;
  } else {
    bidp = Idealstar(nf, mkvec2(gen_1, arch), nf_INIT);
    matarchunit = NULL;
    for (nba=0,k=1; k<=r1; k++) if (signe(gel(arch,k))) nba++;
  }

  empty = cgetg(1,t_VEC);
  /* what follows was rewritten from Ideallist */
  BOUND = utoipos(bound);
  p = cgetipos(3);
  u_forprime_init(&S, 2, bound);
  av = avma;
  sqbou = (ulong)sqrt((double)bound) + 1;
  Z = bigcgetvec(bound);
  for (i=2; i<=bound; i++) bigel(Z,i) = empty;
  embunit = zlog_units(nf, U, sgnU, bidp);
  bigel(Z,1) = mkvec(zsimp(bidp,embunit));
  if (DEBUGLEVEL>1) err_printf("Starting zidealstarunits computations\n");
  /* The goal is to compute Ray (lists of bnrclassno). Z contains "zsimps",
   * simplified bid, from which bnrclassno is easy to compute.
   * Once p > sqbou, delete Z[i] for i > sqbou and compute directly Ray */
  Ray = Z;
  while ((p[2] = u_forprime_next(&S)))
  {
    if (!flbou && uel(p,2) > sqbou)
    {
      GEN z;
      flbou = 1;
      if (DEBUGLEVEL>1) err_printf("\nStarting bnrclassno computations\n");
      Z = gerepilecopy(av,Z); av1 = avma;
      Ray = bigcgetvec(bound);
      for (i=1; i<=bound; i++)
        bigel(Ray,i) = bnrclassnointernarch(bigel(Z,i),h,matarchunit);
      Ray = gerepilecopy(av1,Ray);
      z = bigcgetvec(sqbou);
      for (i=1; i<=sqbou; i++) bigel(z,i) = bigel(Z,i);
      Z = z;
    }
    fa = idealprimedec_limit_norm(nf,p,BOUND);
    for (j=1; j<lg(fa); j++)
    {
      GEN pr = gel(fa,j);
      long prcode, f = pr_get_f(pr);
      ulong q, Q = upowuu(p[2], f);

      /* p, f-1, j-1 as a single integer in "base degk" (f,j <= degk)*/
      prcode = (p[2]*degk + f-1)*degk + j-1;
      q = Q;
      for (l=1;; l++) /* Q <= bound */
      {
        ulong iQ;
        bidp = Idealstarprk(nf, pr, l, nf_INIT);
        embunit = zlog_units(nf, U, NULL, bidp);
        for (iQ = Q, i = 1; iQ <= bound; iQ += Q, i++)
        {
          GEN pz, p2, p1 = bigel(Z,i);
          long lz = lg(p1);
          if (lz == 1) continue;

          p2 = cgetg(lz,t_VEC); c = 0;
          for (k=1; k<lz; k++)
          {
            GEN z = gel(p1,k), v = gmael(z,1,1); /* primes in zsimp's fact. */
            long lv = lg(v);
            /* If z has a power of pr in its modulus, skip it */
            if (i != 1 && lv > 1 && v[lv-1] == prcode) break;
            gel(p2,++c) = zsimpjoin(z,bidp,embunit,prcode,l);
          }

          setlg(p2, c+1);
          pz = bigel(Ray,iQ);
          if (flbou) p2 = bnrclassnointernarch(p2,h,matarchunit);
          if (lg(pz) > 1) p2 = shallowconcat(pz,p2);
          bigel(Ray,iQ) = p2;
        }
        Q = itou_or_0( muluu(Q, q) );
        if (!Q || Q > bound) break;

      }
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"[1]: discrayabslistarch");
      gerepileall(av, flbou? 2: 1, &Z, &Ray);
    }
  }
  if (!flbou) /* occurs iff bound = 1,2,4 */
  {
    if (DEBUGLEVEL>1) err_printf("\nStarting bnrclassno computations\n");
    Ray = bigcgetvec(bound);
    for (i=1; i<=bound; i++)
      bigel(Ray,i) = bnrclassnointernarch(bigel(Z,i),h,matarchunit);
  }
  Ray = gerepilecopy(av, Ray);

  if (DEBUGLEVEL>1) err_printf("Starting discrayabs computations\n");
  if (allarch) nbarch = 1L<<r1;
  else
  {
    nbarch = 1;
    discall = cgetg(2,t_VEC);
  }
  EMPTY = mkvec3(gen_0,gen_0,gen_0);
  idealrelinit = trivial_fact();
  av1 = avma;
  Disc = bigcgetvec(bound);
  for (i=1; i<=bound; i++) bigel(Disc,i) = empty;
  for (ii=1; ii<=bound; ii++)
  {
    GEN sous, sousdisc;
    long ls;
    i = ii;
    sous = bigel(Ray,i);
    ls = lg(sous); bigel(Disc,ii) = sousdisc = cgetg(ls,t_VEC);
    for (j=1; j<ls; j++)
    {
      GEN b = gel(sous,j), clhrayall = gel(b,2), Fa = gel(b,1);
      GEN P = gel(Fa,1), E = gel(Fa,2);
      long lP = lg(P), karch;

      if (allarch) discall = cgetg(nbarch+1,t_VEC);
      for (karch=0; karch<nbarch; karch++)
      {
        long nz, clhray = clhrayall[karch+1];
        if (allarch)
        {
          long ka, k2;
          nba = 0;
          for (ka=karch,k=1; k<=r1; k++,ka>>=1)
            if (ka & 1) nba++;
          for (k2=1,k=1; k<=r1; k++,k2<<=1)
            if (karch&k2 && clhrayall[karch-k2+1] == clhray)
              { res = EMPTY; goto STORE; }
        }
        idealrel = idealrelinit;
        for (k=1; k<lP; k++) /* cf get_discray */
        {
          long e, ep = E[k], pf = P[k] / degk, f = (pf%degk) + 1, S = 0;
          ulong normi = i, Npr;
          p = utoipos(pf / degk);
          Npr = upowuu(p[2],f);
          for (e=1; e<=ep; e++)
          {
            long clhss;
            GEN fad;
            if (e < ep) { E[k] = ep-e; fad = Fa; }
            else fad = factorsplice(Fa, k);
            normi /= Npr;
            clhss = Lbnrclassno(bigel(Ray,normi),fad)[karch+1];
            if (e==1 && clhss==clhray) { E[k] = ep; res = EMPTY; goto STORE; }
            if (clhss == 1) { S += ep-e+1; break; }
            S += clhss;
          }
          E[k] = ep;
          idealrel = factormul(idealrel, to_famat_shallow(p, utoi(f * S)));
        }
        if (!allarch && nba)
          nz = get_nz(bnf, decodemodule(nf,Fa), arch, clhray);
        else
          nz = r1 - nba;
        res = get_NR1D(i, clhray, degk, nz, fadkabs, idealrel);
STORE:  gel(discall,karch+1) = res;
      }
      res = allarch? mkvec2(Fa, discall)
                   : mkvec4(Fa, gel(res,1), gel(res,2), gel(res,3));
      gel(sousdisc,j) = res;
      if (gc_needed(av1,1))
      {
        long jj;
        if(DEBUGMEM>1) pari_warn(warnmem,"[2]: discrayabslistarch");
        for (jj=j+1; jj<ls; jj++) gel(sousdisc,jj) = gen_0; /* dummy */
        Disc = gerepilecopy(av1, Disc);
        sousdisc = bigel(Disc,ii);
      }
    }
  }
  return gerepilecopy(av0, Disc);
}

int
subgroup_conductor_ok(GEN H, GEN L)
{ /* test conductor */
  long i, l = lg(L);
  for (i = 1; i < l; i++)
    if ( hnf_solve(H, gel(L,i)) ) return 0;
  return 1;
}
static GEN
conductor_elts(GEN bnr)
{
  GEN e, L, nf = bnf_get_nf( bnr_get_bnf(bnr) );
  long le, la, i, k;
  zlog_S S;

  init_zlog_bid(&S, bnr_get_bid(bnr));
  e = S.e; le = lg(e); la = lg(S.archp);
  L = cgetg(le + la - 1, t_VEC);
  i = 1;
  for (k = 1; k < le; k++)
    gel(L,i++) = bnr_log_gen_pr(bnr, &S, nf, itos(gel(e,k)), k);
  for (k = 1; k < la; k++)
    gel(L,i++) = bnr_log_gen_arch(bnr, &S, k);
  return L;
}

/* Let C a congruence group in bnr, compute its subgroups whose index is
 * described by bound (see subgrouplist) as subgroups of Clk(bnr).
 * Restrict to subgroups having the same conductor as bnr */
GEN
subgrouplist_cond_sub(GEN bnr, GEN C, GEN bound)
{
  pari_sp av = avma;
  long l, i, j;
  GEN D, Mr, U, T, subgrp, L, cyc = bnr_get_cyc(bnr);

  Mr = diagonal_shallow(cyc);
  D = ZM_snfall_i(hnf_solve(C, Mr), &U, NULL, 1);
  T = ZM_mul(C, RgM_inv(U));
  L = conductor_elts(bnr);
  subgrp  = subgrouplist(D, bound);
  l = lg(subgrp);
  for (i = j = 1; i < l; i++)
  {
    GEN H = ZM_hnfmodid(ZM_mul(T, gel(subgrp,i)), cyc);
    if (subgroup_conductor_ok(H, L)) gel(subgrp, j++) = H;
  }
  setlg(subgrp, j);
  return gerepilecopy(av, subgrp);
}

static GEN
subgroupcond(GEN bnr, GEN indexbound)
{
  pari_sp av = avma;
  GEN li = subgroupcondlist(bnr_get_cyc(bnr), indexbound, conductor_elts(bnr));
  if (indexbound && typ(indexbound) != t_VEC)
  { /* sort by increasing index if not single value */
    long i, l = lg(li);
    GEN D = cgetg(l,t_VEC);
    for (i=1; i<l; i++) gel(D,i) = ZM_det_triangular(gel(li,i));
    li = vecreverse( vecpermute(li, indexsort(D)) );
  }
  return gerepilecopy(av,li);
}

GEN
subgrouplist0(GEN bnr, GEN indexbound, long all)
{
  if (typ(bnr)!=t_VEC) pari_err_TYPE("subgrouplist",bnr);
  if (lg(bnr)!=1 && typ(gel(bnr,1))!=t_INT)
  {
    checkbnr(bnr);
    if (!all) return subgroupcond(bnr,indexbound);
    bnr = bnr_get_cyc(bnr);
  }
  return subgrouplist(bnr,indexbound);
}

GEN
bnrdisclist0(GEN bnf, GEN L, GEN arch)
{
  if (typ(L)!=t_INT) return discrayabslist(bnf,L);
  return discrayabslistarch(bnf,arch,itos(L));
}

/****************************************************************************/
/*                                Galois action on a BNR                    */
/****************************************************************************/

GEN
bnrautmatrix(GEN bnr, GEN aut)
{
  pari_sp av=avma;
  GEN gen, mat, nf;
  long i, l;
  nf = bnr_get_nf(bnr);
  gen = bnr_get_gen(bnr); l = lg(gen);
  aut = algtobasis(nf, aut);
  mat = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
    gel(mat, i) = bnrisprincipal(bnr,galoisapply(nf,aut,gel(gen,i)),0);
  return gerepilecopy(av, mat);
}

GEN
bnrgaloismatrix(GEN bnr, GEN aut)
{
  checkbnr(bnr);
  switch (typ(aut))
  {
    case t_POL:
    case t_COL:
      return bnrautmatrix(bnr, aut);
    case t_VEC:
    {
      long i, l = lg(aut);
      GEN V;
      if (l==9 && typ(gal_get_gen(aut))==t_VEC)
      {
        pari_sp av = avma;
        V = galoispermtopol(aut, gal_get_gen(aut));
        return gerepileupto(av, bnrgaloismatrix(bnr, V));
      }
      V = cgetg(l, t_VEC);
      for(i=1; i<l; i++)
        gel(V,i) = bnrautmatrix(bnr, gel(aut,i));
      return V;
    }
    default:
      pari_err_TYPE("bnrgaloismatrix", aut);
      return NULL; /*NOT REACHED*/
  }
}

GEN
bnrgaloisapply(GEN bnr, GEN mat, GEN x)
{
  pari_sp av=avma;
  GEN cyc;
  checkbnr(bnr);
  cyc = bnr_get_cyc(bnr);
  if (typ(mat)!=t_MAT || !RgM_is_ZM(mat))
    pari_err_TYPE("bnrgaloisapply",mat);
  if (typ(x)!=t_MAT || !RgM_is_ZM(x))
    pari_err_TYPE("bnrgaloisapply",x);
  return gerepileupto(av, ZM_hnfmodid(ZM_mul(mat, x), cyc));
}

static GEN
check_bnrgal(GEN bnr, GEN M)
{
  checkbnr(bnr);
  if (typ(M)==t_MAT)
    return mkvec(M);
  else if (typ(M)==t_VEC && lg(M)==9 && typ(gal_get_gen(M))==t_VEC)
  {
    pari_sp av = avma;
    GEN V = galoispermtopol(M, gal_get_gen(M));
    return gerepileupto(av, bnrgaloismatrix(bnr, V));
  }
  else if (!is_vec_t(typ(M)))
    pari_err_TYPE("bnrisgalois",M);
  return M;
}

long
bnrisgalois(GEN bnr, GEN M, GEN H)
{
  pari_sp av = avma;
  long i, l;
  if (typ(H)!=t_MAT || !RgM_is_ZM(H))
    pari_err_TYPE("bnrisgalois",H);
  M = check_bnrgal(bnr, M); l = lg(M);
  for (i=1; i<l; i++)
  {
    long res = ZM_equal(bnrgaloisapply(bnr,gel(M,i), H), H);
    if (!res) { avma = av; return 0; }
  }
  avma = av;
  return 1;
}
