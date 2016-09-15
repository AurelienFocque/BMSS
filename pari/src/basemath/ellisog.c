/* Copyright (C) 2014 The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"

/* Return 1 if the point Q is a Weierstrass (2-torsion) point of the
 * curve E, return 0 otherwise */
static long
ellisweierstrasspoint(GEN E, GEN Q)
{ return ell_is_inf(Q) || gequal0(ec_dmFdy_evalQ(E, Q)); }


/* Given an elliptic curve E = [a1, a2, a3, a4, a6] and t,w in the ring of
 * definition of E, return the curve
 *  E' = [a1, a2, a3, a4 - 5t, a6 - (E.b2 t + 7w)] */
static GEN
make_velu_curve(GEN E, GEN t, GEN w)
{
  GEN A4, A6, a1 = ell_get_a1(E), a2 = ell_get_a2(E), a3 = ell_get_a3(E);
  A4 = gsub(ell_get_a4(E), gmulsg(5L, t));
  A6 = gsub(ell_get_a6(E), gadd(gmul(ell_get_b2(E), t), gmulsg(7L, w)));
  return mkvec5(a1,a2,a3,A4,A6);
}

/* If phi = (f(x)/h(x)^2, g(x,y)/h(x)^3) is an isogeny, return the
 * variables x and y in a vecsmall */
INLINE void
get_isog_vars(GEN phi, long *vx, long *vy)
{
  *vx = varn(gel(phi, 1));
  *vy = varn(gel(phi, 2));
  if (*vy == *vx) *vy = gvar2(gel(phi,2));
}

static GEN
RgX_homogenous_evalpow(GEN P, GEN A, GEN B)
{
  pari_sp av = avma;
  long d, i, v;
  GEN s;
  if (typ(P)!=t_POL)
    return mkvec2(P, gen_1);
  d = degpol(P); v = varn(A);
  s = scalarpol_shallow(gel(P, d+2), v);
  for (i = d-1; i >= 0; i--)
  {
    s = gadd(gmul(s, A), gmul(gel(B,d+1-i), gel(P,i+2)));
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgX_homogenous_eval(%ld)",i);
      s = gerepileupto(av, s);
    }
  }
  s = gerepileupto(av, s);
  return mkvec2(s, gel(B,d+1));
}

/* Given isogenies F:E' -> E and G:E'' -> E', return the composite
 * isogeny F o G:E'' -> E */
static GEN
ellcompisog(GEN F, GEN G)
{
  pari_sp av = avma;
  GEN Fv, Gh, Gh2, Gh3, f, g, h, h2, h3, den, num;
  GEN K, K2, K3, F0, F1, g0, g1, Gp;
  long v, vx, vy, d;
  checkellisog(F);
  checkellisog(G);
  get_isog_vars(F, &vx, &vy);
  v = fetch_var_higher();
  Fv = shallowcopy(gel(F,3)); setvarn(Fv, v);
  Gh = gel(G,3); Gh2 = gsqr(Gh); Gh3 = gmul(Gh, Gh2);
  K = gmul(polresultant0(Fv, deg1pol(gneg(Gh2),gel(G,1), v), v, 0), Gh);
  delete_var();
  K = RgX_normalize(RgX_div(K, RgX_gcd(K,deriv(K,0))));
  K2 = gsqr(K); K3 = gmul(K, K2);
  F0 = polcoeff0(gel(F,2), 0, vy); F1 = polcoeff0(gel(F,2), 1, vy);
  d = maxss(maxss(degpol(gel(F,1)),degpol(gel(F,3))),maxss(degpol(F0),degpol(F1)));
  Gp = gpowers(Gh2, d);
  f  = RgX_homogenous_evalpow(gel(F,1), gel(G,1), Gp);
  g0 = RgX_homogenous_evalpow(F0, gel(G,1), Gp);
  g1 = RgX_homogenous_evalpow(F1, gel(G,1), Gp);
  h =  RgX_homogenous_evalpow(gel(F,3), gel(G,1), Gp);
  h2 = mkvec2(gsqr(gel(h,1)), gsqr(gel(h,2)));
  h3 = mkvec2(gmul(gel(h,1),gel(h2,1)), gmul(gel(h,2),gel(h2,2)));
  f  = gdiv(gmul(gmul(K2, gel(f,1)),gel(h2,2)), gmul(gel(f,2), gel(h2,1)));
  den = gmul(Gh3, gel(g1,2));
  num = gadd(gmul(gel(g0,1),den), gmul(gmul(gel(G,2),gel(g1,1)),gel(g0,2)));
  g = gdiv(gmul(gmul(K3,num),gel(h3,2)),gmul(gmul(gel(g0,2),den), gel(h3,1)));
  return gerepilecopy(av, mkvec3(f,g,K));
}

/* Given an isogeny phi from ellisogeny() and a point P in the domain of phi,
 * return phi(P) */
GEN
ellisogenyapply(GEN phi, GEN P)
{
  pari_sp ltop = avma;
  GEN f, g, h, img_f, img_g, img_h, img_h2, img_h3, img, tmp;
  long vx, vy;
  if (lg(P) == 4) return ellcompisog(phi,P);
  checkellisog(phi);
  checkellpt(P);
  if (ell_is_inf(P)) return ellinf();
  f = gel(phi, 1);
  g = gel(phi, 2);
  h = gel(phi, 3);
  get_isog_vars(phi, &vx, &vy);
  img_h = poleval(h, gel(P, 1));
  if (gequal0(img_h)) { avma = ltop; return ellinf(); }

  img_h2 = gsqr(img_h);
  img_h3 = gmul(img_h, img_h2);
  img_f = poleval(f, gel(P, 1));
  /* FIXME: This calculation of g is perhaps not as efficient as it could be */
  tmp = gsubst(g, vx, gel(P, 1));
  img_g = gsubst(tmp, vy, gel(P, 2));
  img = cgetg(3, t_VEC);
  gel(img, 1) = gdiv(img_f, img_h2);
  gel(img, 2) = gdiv(img_g, img_h3);
  return gerepileupto(ltop, img);
}

/* isog = [f, g, h] = [x, y, 1] = identity */
static GEN
isog_identity(long vx, long vy)
{ return mkvec3(pol_x(vx), pol_x(vy), pol_1(vx)); }

/* Returns an updated value for isog based (primarily) on tQ and uQ. Used to
 * iteratively compute the isogeny corresponding to a subgroup generated by a
 * given point. Ref: Equation 8 in Velu's paper.
 * isog = NULL codes the identity */
static GEN
update_isogeny_polys(GEN isog, GEN E, GEN Q, GEN tQ, GEN uQ, long vx, long vy)
{
  pari_sp ltop = avma, av;
  GEN xQ = gel(Q, 1), yQ = gel(Q, 2);
  GEN rt = deg1pol_shallow(gen_1, gneg(xQ), vx);
  GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E);

  GEN gQx = ec_dFdx_evalQ(E, Q);
  GEN gQy = ec_dFdy_evalQ(E, Q);
  GEN tmp1, tmp2, tmp3, tmp4, f, g, h, rt_sqr, res;

  /* g -= uQ * (2 * y + E.a1 * x + E.a3)
   *   + tQ * rt * (E.a1 * rt + y - yQ)
   *   + rt * (E.a1 * uQ - gQx * gQy) */
  av = avma;
  tmp1 = gmul(uQ, gadd(deg1pol_shallow(gen_2, gen_0, vy),
                       deg1pol_shallow(a1, a3, vx)));
  tmp1 = gerepileupto(av, tmp1);
  av = avma;
  tmp2 = gmul(tQ, gadd(gmul(a1, rt),
                       deg1pol_shallow(gen_1, gneg(yQ), vy)));
  tmp2 = gerepileupto(av, tmp2);
  av = avma;
  tmp3 = gsub(gmul(a1, uQ), gmul(gQx, gQy));
  tmp3 = gerepileupto(av, tmp3);

  if (!isog) isog = isog_identity(vx,vy);
  f = gel(isog, 1);
  g = gel(isog, 2);
  h = gel(isog, 3);
  rt_sqr = gsqr(rt);
  res = cgetg(4, t_VEC);
  av = avma;
  tmp4 = gdiv(gadd(gmul(tQ, rt), uQ), rt_sqr);
  gel(res, 1) = gerepileupto(av, gadd(f, tmp4));
  av = avma;
  tmp4 = gadd(tmp1, gmul(rt, gadd(tmp2, tmp3)));
  gel(res, 2) = gerepileupto(av, gsub(g, gdiv(tmp4, gmul(rt, rt_sqr))));
  av = avma;
  gel(res, 3) = gerepileupto(av, gmul(h, rt));
  return gerepileupto(ltop, res);
}

/* Given a point P on E, return the curve E/<P> and, if only_image is zero,
 * the isogeny pi: E -> E/<P>. The variables vx and vy are used to describe
 * the isogeny (ignored if only_image is zero) */
static GEN
isogeny_from_kernel_point(GEN E, GEN P, int only_image, long vx, long vy)
{
  pari_sp av = avma;
  GEN isog, EE, f, g, h, h2, h3;
  GEN Q = P, t = gen_0, w = gen_0;
  long c;
  if (!oncurve(E,P))
    pari_err_DOMAIN("isogeny_from_kernel_point", "point", "not on", E, P);
  if (ell_is_inf(P))
  {
    if (only_image) return E;
    return mkvec2(E, isog_identity(vx,vy));
  }

  isog = NULL; c = 1;
  for (;;)
  {
    GEN tQ, xQ = gel(Q,1), uQ = ec_2divpol_evalx(E, xQ);
    int stop = 0;
    if (ellisweierstrasspoint(E,Q))
    { /* ord(P)=2c; take Q=[c]P into consideration and stop */
      tQ = ec_dFdx_evalQ(E, Q);
      stop = 1;
    }
    else
      tQ = ec_half_deriv_2divpol_evalx(E, xQ);
    t = gadd(t, tQ);
    w = gadd(w, gadd(uQ, gmul(tQ, xQ)));
    if (!only_image) isog = update_isogeny_polys(isog, E, Q,tQ,uQ, vx,vy);
    if (stop) break;

    Q = elladd(E, P, Q);
    ++c;
    /* IF x([c]P) = x([c-1]P) THEN [c]P = -[c-1]P and [2c-1]P = 0 */
    if (gequal(gel(Q,1), xQ)) break;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"isogeny_from_kernel_point");
      gerepileall(av, isog? 4: 3, &Q, &t, &w, &isog);
    }
  }

  EE = make_velu_curve(E, t, w);
  if (only_image) return EE;

  if (!isog) isog = isog_identity(vx,vy);
  f = gel(isog, 1);
  g = gel(isog, 2);
  if ( ! (typ(f) == t_RFRAC && typ(g) == t_RFRAC))
    pari_err_BUG("isogeny_from_kernel_point (f or g has wrong type)");

  /* Clean up the isogeny polynomials f, g and h so that the isogeny
   * is given by (x,y) -> (f(x)/h(x)^2, g(x,y)/h(x)^3) */
  h = gel(isog, 3);
  h2 = gsqr(h);
  h3 = gmul(h, h2);
  f = gmul(f, h2);
  g = gmul(g, h3);
  if (typ(f) != t_POL || typ(g) != t_POL)
    pari_err_BUG("isogeny_from_kernel_point (wrong denominator)");
  return mkvec2(EE, mkvec3(f,g, gel(isog,3)));
}

/* Given a t_POL x^n - s1 x^{n-1} + s2 x^{n-2} - s3 x^{n-3} + ...
 * return the first three power sums (Newton's identities):
 *   p1 = s1
 *   p2 = s1^2 - 2 s2
 *   p3 = (s1^2 - 3 s2) s1 + 3 s3 */
static void
first_three_power_sums(GEN pol, GEN *p1, GEN *p2, GEN *p3)
{
  long d = degpol(pol);
  GEN s1, s2, ms3;

  *p1 = s1 = gneg(RgX_coeff(pol, d-1));

  s2 = RgX_coeff(pol, d-2);
  *p2 = gsub(gsqr(s1), gmulsg(2L, s2));

  ms3 = RgX_coeff(pol, d-3);
  *p3 = gadd(gmul(s1, gsub(*p2, s2)), gmulsg(-3L, ms3));
}


/* Let E and a t_POL h of degree 1 or 3 whose roots are 2-torsion points on E.
 * - if only_image != 0, return [t, w] used to compute the equation of the
 *   quotient by the given 2-torsion points
 * - else return [t,w, f,g,h], along with the contributions f, g and
 *   h to the isogeny giving the quotient by h. Variables vx and vy are used
 *   to create f, g and h, or ignored if only_image is zero */

/* deg h = 1; 2-torsion contribution from Weierstrass point */
static GEN
contrib_weierstrass_pt(GEN E, GEN h, long only_image, long vx, long vy)
{
  GEN p = ellbasechar(E);
  GEN a1 = ell_get_a1(E);
  GEN a3 = ell_get_a3(E);
  GEN x0 = gneg(constant_coeff(h)); /* h = x - x0 */
  GEN b = gadd(gmul(a1,x0), a3);
  GEN y0, Q, t, w, t1, t2, f, g;

  if (!equalis(p, 2L)) /* char(k) != 2 ==> y0 = -b/2 */
    y0 = gmul2n(gneg(b), -1);
  else
  { /* char(k) = 2 ==> y0 = sqrt(f(x0)) where E is y^2 + h(x) = f(x). */
    if (!gequal0(b)) pari_err_BUG("two_torsion_contrib (a1*x0+a3 != 0)");
    y0 = gsqrt(ec_f_evalx(E, x0), 0);
  }
  Q = mkvec2(x0, y0);
  t = ec_dFdx_evalQ(E, Q);
  w = gmul(x0, t);
  if (only_image) return mkvec2(t,w);

  /* Compute isogeny, f = (x - x0) * t */
  f = deg1pol_shallow(t, gmul(t, gneg(x0)), vx);

  /* g = (x - x0) * t * (a1 * (x - x0) + (y - y0)) */
  t1 = deg1pol_shallow(a1, gmul(a1, gneg(x0)), vx);
  t2 = deg1pol_shallow(gen_1, gneg(y0), vy);
  g = gmul(f, gadd(t1, t2));
  return mkvec5(t, w, f, g, h);
}
/* deg h =3; full 2-torsion contribution. NB: assume h is monic; base field
 * characteristic is odd or zero (cannot happen in char 2).*/
static GEN
contrib_full_tors(GEN E, GEN h, long only_image, long vx, long vy)
{
  GEN p1, p2, p3, half_b2, half_b4, t, w, f, g;
  first_three_power_sums(h, &p1,&p2,&p3);
  half_b2 = gmul2n(ell_get_b2(E), -1);
  half_b4 = gmul2n(ell_get_b4(E), -1);

  /* t = 3*(p2 + b4/2) + p1 * b2/2 */
  t = gadd(gmulsg(3L, gadd(p2, half_b4)), gmul(p1, half_b2));

  /* w = 3 * p3 + p2 * b2/2 + p1 * b4/2 */
  w = gadd(gmulsg(3L, p3), gadd(gmul(p2, half_b2),
                                gmul(p1, half_b4)));
  if (only_image) return mkvec2(t,w);

  /* Compute isogeny */
  {
    GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E), t1, t2;
    GEN s1 = gneg(RgX_coeff(h, 2));
    GEN dh = RgX_deriv(h);
    GEN psi2xy = gadd(deg1pol_shallow(a1, a3, vx),
                      deg1pol_shallow(gen_2, gen_0, vy));

    /* f = -3 (3 x + b2/2 + s1) h + (3 x^2 + (b2/2) x + (b4/2)) h'*/
    t1 = RgX_mul(h, gmulsg(-3, deg1pol(stoi(3), gadd(half_b2, s1), vx)));
    t2 = mkpoln(3, stoi(3), half_b2, half_b4);
    setvarn(t2, vx);
    t2 = RgX_mul(dh, t2);
    f = RgX_add(t1, t2);

    /* 2g = psi2xy * (f'*h - f*h') - (a1*f + a3*h) * h; */
    t1 = RgX_sub(RgX_mul(RgX_deriv(f), h), RgX_mul(f, dh));
    t2 = RgX_mul(h, RgX_add(RgX_Rg_mul(f, a1), RgX_Rg_mul(h, a3)));
    g = RgX_divs(gsub(gmul(psi2xy, t1), t2), 2L);

    f = RgX_mul(f, h);
    g = RgX_mul(g, h);
  }
  return mkvec5(t, w, f, g, h);
}

/* Given E and a t_POL T whose roots define a subgroup G of E, return the factor
 * of T that corresponds to the 2-torsion points E[2] \cap G in G */
INLINE GEN
two_torsion_part(GEN E, GEN T)
{ return RgX_gcd(T, elldivpol(E, 2, varn(T))); }

/* Return the jth Hasse derivative of the polynomial f = \sum_{i=0}^n a_i x^i,
 * i.e. \sum_{i=j}^n a_i \binom{i}{j} x^{i-j}. It is a derivation even when the
 * coefficient ring has positive characteristic */
static GEN
derivhasse(GEN f, ulong j)
{
  ulong i, d = degpol(f);
  GEN df;
  if (gequal0(f) || d == 0) return pol_0(varn(f));
  if (j == 0) return gcopy(f);
  df = cgetg(2 + (d-j+1), t_POL);
  df[1] = f[1];
  for (i = j; i <= d; ++i) gel(df, i-j+2) = gmul(binomialuu(i,j), gel(f, i+2));
  return normalizepol(df);
}

static GEN
non_two_torsion_abscissa(GEN E, GEN h0, GEN x)
{
  GEN mp1, dh0, ddh0, t, u, t1, t2, t3;
  long m = degpol(h0);
  mp1 = gel(h0, m + 1); /* negative of first power sum */
  dh0 = RgX_deriv(h0);
  ddh0 = RgX_deriv(dh0);
  t = ec_2divpol_evalx(E, x);
  u = ec_half_deriv_2divpol_evalx(E, x);
  t1 = RgX_sub(RgX_sqr(dh0), RgX_mul(ddh0, h0));
  t2 = RgX_mul(u, RgX_mul(h0, dh0));
  t3 = RgX_mul(RgX_sqr(h0),
               deg1pol_shallow(stoi(2*m), gmulsg(2L, mp1), varn(x)));
  /* t * (dh0^2 - ddh0*h0) - u*dh0*h0 + (2*m*x - 2*s1) * h0^2); */
  return RgX_add(RgX_sub(RgX_mul(t, t1), t2), t3);
}

static GEN
isog_abscissa(GEN E, GEN kerp, GEN h0, GEN x, GEN two_tors)
{
  GEN f0, f2, h2, t1, t2, t3;
  f0 = (degpol(h0) > 0)? non_two_torsion_abscissa(E, h0, x): pol_0(varn(x));
  f2 = gel(two_tors, 3);
  h2 = gel(two_tors, 5);

  /* Combine f0 and f2 into the final abcissa of the isogeny. */
  t1 = RgX_mul(x, RgX_sqr(kerp));
  t2 = RgX_mul(f2, RgX_sqr(h0));
  t3 = RgX_mul(f0, RgX_sqr(h2));
  /* x * kerp^2 + f2 * h0^2 + f0 * h2^2 */
  return RgX_add(t1, RgX_add(t2, t3));
}

static GEN
non_two_torsion_ordinate_char_not2(GEN E, GEN f, GEN h, GEN psi2)
{
  GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E);
  GEN df = RgX_deriv(f), dh = RgX_deriv(h);
  /* g = df * h * psi2/2 - f * dh * psi2
   *   - (E.a1 * f + E.a3 * h^2) * h/2 */
  GEN t1 = RgX_mul(df, RgX_mul(h, RgX_divs(psi2, 2L)));
  GEN t2 = RgX_mul(f, RgX_mul(dh, psi2));
  GEN t3 = RgX_mul(RgX_divs(h, 2L),
                   RgX_add(RgX_Rg_mul(f, a1), RgX_Rg_mul(RgX_sqr(h), a3)));
  return RgX_sub(RgX_sub(t1, t2), t3);
}

/* h = kerq */
static GEN
non_two_torsion_ordinate_char2(GEN E, GEN h, GEN x, GEN y)
{
  GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E), a4 = ell_get_a4(E);
  GEN b2 = ell_get_b2(E), b4 = ell_get_b4(E), b6 = ell_get_b6(E);
  GEN h2, dh, dh2, ddh, D2h, D2dh, H, psi2, u, t, alpha;
  GEN p1, t1, t2, t3, t4;
  long m, vx = varn(x);

  h2 = RgX_sqr(h);
  dh = RgX_deriv(h);
  dh2 = RgX_sqr(dh);
  ddh = RgX_deriv(dh);
  H = RgX_sub(dh2, RgX_mul(h, ddh));
  D2h = derivhasse(h, 2);
  D2dh = derivhasse(dh, 2);
  psi2 = deg1pol_shallow(a1, a3, vx);
  u = mkpoln(3, b2, gen_0, b6);
  setvarn(u, vx);
  t = deg1pol_shallow(b2, b4, vx);
  alpha = mkpoln(4, a1, a3, gmul(a1, a4), gmul(a3, a4));
  setvarn(alpha, vx);
  m = degpol(h);
  p1 = RgX_coeff(h, m-1); /* first power sum */

  t1 = gmul(gadd(gmul(a1, p1), gmulgs(a3, m)), RgX_mul(h,h2));

  t2 = gmul(a1, gadd(gmul(a1, gadd(y, psi2)), RgX_add(RgX_Rg_add(RgX_sqr(x), a4), t)));
  t2 = gmul(t2, gmul(dh, h2));

  t3 = gadd(gmul(y, t), RgX_add(alpha, RgX_Rg_mul(u, a1)));
  t3 = gmul(t3, RgX_mul(h, H));

  t4 = gmul(u, psi2);
  t4 = gmul(t4, RgX_sub(RgX_sub(RgX_mul(h2, D2dh), RgX_mul(dh, H)),
                        RgX_mul(h, RgX_mul(dh, D2h))));

  return gadd(t1, gadd(t2, gadd(t3, t4)));
}

static GEN
isog_ordinate(GEN E, GEN kerp, GEN kerq, GEN x, GEN y, GEN two_tors, GEN f)
{
  GEN g;
  if (! equalis(ellbasechar(E), 2L)) {
    /* FIXME: We don't use (hence don't need to calculate)
     * g2 = gel(two_tors, 4) when char(k) != 2. */
    GEN psi2 = ec_dmFdy_evalQ(E, mkvec2(x, y));
    g = non_two_torsion_ordinate_char_not2(E, f, kerp, psi2);
  } else {
    GEN h2 = gel(two_tors, 5);
    GEN g2 = gmul(gel(two_tors, 4), RgX_mul(kerq, RgX_sqr(kerq)));
    GEN g0 = non_two_torsion_ordinate_char2(E, kerq, x, y);
    g0 = gmul(g0, RgX_mul(h2, RgX_sqr(h2)));
    g = gsub(gmul(y, RgX_mul(kerp, RgX_sqr(kerp))), gadd(g2, g0));
  }
  return g;
}

/* Given an elliptic curve E and a polynomial kerp whose roots give the
 * x-coordinates of a subgroup G of E, return the curve E/G and,
 * if only_image is zero, the isogeny pi:E -> E/G. Variables vx and vy are
 * used to describe the isogeny (and are ignored if only_image is zero). */
static GEN
isogeny_from_kernel_poly(GEN E, GEN kerp, long only_image, long vx, long vy)
{
  long m;
  GEN b2 = ell_get_b2(E), b4 = ell_get_b4(E), b6 = ell_get_b6(E);
  GEN p1, p2, p3, x, y, f, g, two_tors, EE, t, w;
  GEN kerh = two_torsion_part(E, kerp);
  GEN kerq = RgX_divrem(kerp, kerh, ONLY_DIVIDES);
  if (!kerq) pari_err_BUG("isogeny_from_kernel_poly");
  /* isogeny degree: 2*degpol(kerp)+1-degpol(kerh) */
  m = degpol(kerq);

  kerp = RgX_Rg_div(kerp, leading_coeff(kerp));
  kerq = RgX_Rg_div(kerq, leading_coeff(kerq));
  kerh = RgX_Rg_div(kerh, leading_coeff(kerh));
  switch(degpol(kerh))
  {
  case 0:
    two_tors = mkvec5(gen_0, gen_0, pol_0(vx), pol_0(vx), pol_1(vx));
    break;
  case 1:
    two_tors = contrib_weierstrass_pt(E, kerh, only_image,vx,vy);
    break;
  case 3:
    two_tors = contrib_full_tors(E, kerh, only_image,vx,vy);
    break;
  default:
    two_tors = NULL;
    pari_err_DOMAIN("isogeny_from_kernel_poly", "kernel polynomial",
                    "does not define a subgroup of", E, kerp);
  }
  first_three_power_sums(kerq,&p1,&p2,&p3);
  x = pol_x(vx);
  y = pol_x(vy);

  /* t = 6 * p2 + b2 * p1 + m * b4, */
  t = gadd(gmulsg(6L, p2), gadd(gmul(b2, p1), gmulsg(m, b4)));

  /* w = 10 * p3 + 2 * b2 * p2 + 3 * b4 * p1 + m * b6, */
  w = gadd(gmulsg(10L, p3),
           gadd(gmul(gmulsg(2L, b2), p2),
                gadd(gmul(gmulsg(3L, b4), p1), gmulsg(m, b6))));

  EE = make_velu_curve(E, gadd(t, gel(two_tors, 1)),
                          gadd(w, gel(two_tors, 2)));
  if (only_image) return EE;

  f = isog_abscissa(E, kerp, kerq, x, two_tors);
  g = isog_ordinate(E, kerp, kerq, x, y, two_tors, f);
  return mkvec2(EE, mkvec3(f,g,kerp));
}

/* Given an elliptic curve E and a subgroup G of E, return the curve
 * E/G and, if only_image is zero, the isogeny corresponding
 * to the canonical surjection pi:E -> E/G. The variables vx and
 * vy are used to describe the isogeny (and are ignored if
 * only_image is zero). The subgroup G may be given either as
 * a generating point P on E or as a polynomial kerp whose roots are
 * the x-coordinates of the points in G */
GEN
ellisogeny(GEN E, GEN G, long only_image, long vx, long vy)
{
  pari_sp av = avma;
  GEN j, z;
  checkell(E);j = ell_get_j(E);
  if (vx < 0) vx = 0;
  if (vy < 0) vy = 1;
  if (varncmp(vx, vy) >= 0) pari_err_PRIORITY("ellisogeny", pol_x(vx), "<=", vy);
  if (varncmp(vy, gvar(j)) >= 0) pari_err_PRIORITY("ellisogeny", j, ">=", vy);
  switch(typ(G))
  {
  case t_VEC:
    checkellpt(G);
    if (!ell_is_inf(G))
    {
      GEN x =  gel(G,1), y = gel(G,2);
      if (varncmp(vy, gvar(x)) >= 0) pari_err_PRIORITY("ellisogeny", x, ">=", vy);
      if (varncmp(vy, gvar(y)) >= 0) pari_err_PRIORITY("ellisogeny", y, ">=", vy);
    }
    z = isogeny_from_kernel_point(E, G, only_image, vx, vy);
    break;
  case t_POL:
    if (varncmp(vy, gvar(constant_coeff(G))) >= 0)
      pari_err_PRIORITY("ellisogeny", constant_coeff(G), ">=", vy);
    z = isogeny_from_kernel_poly(E, G, only_image, vx, vy);
    break;
  default:
    z = NULL;
    pari_err_TYPE("ellisogeny", G);
  }
  return gerepilecopy(av, z);
}

static GEN
trivial_isogeny(void)
{
  return mkvec3(pol_x(0), scalarpol(pol_x(1), 0), pol_1(0));
}

static GEN
isogeny_a4a6(GEN E)
{
  GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E), b2 = ell_get_b2(E);
  retmkvec3(deg1pol(gen_1, gdivgs(b2, 12), 0),
            deg1pol(gdivgs(a1,2), deg1pol(gen_1, gdivgs(a3,2), 1), 0),
            pol_1(0));
}

static GEN
invisogeny_a4a6(GEN E)
{
  GEN a1 = ell_get_a1(E), a3 = ell_get_a3(E), b2 = ell_get_b2(E);
  retmkvec3(deg1pol(gen_1, gdivgs(b2, -12), 0),
            deg1pol(gdivgs(a1,-2),
              deg1pol(gen_1, gadd(gdivgs(a3,-2), gdivgs(gmul(b2,a1), 24)), 1), 0),
            pol_1(0));
}

static GEN
RgXY_eval(GEN P, GEN x, GEN y)
{
  return poleval(poleval(P,x), y);
}

static GEN
twistisogeny(GEN iso, GEN d)
{
  GEN d2 = gsqr(d), d3 = gmul(d, d2);
  return mkvec3(gdiv(gel(iso,1), d2), gdiv(gel(iso,2), d3), gel(iso, 3));
}

static GEN
ellisog_by_Kohel(GEN a4, GEN a6, long n, GEN ker, GEN kert, long flag)
{
  GEN E = ellinit(mkvec2(a4, a6), NULL, DEFAULTPREC);
  GEN F = isogeny_from_kernel_poly(E, ker, flag, 0, 1);
  GEN Et = ellinit(flag ? F: gel(F, 1), NULL, DEFAULTPREC);
  GEN c4t = ell_get_c4(Et), c6t = ell_get_c6(Et), jt = ell_get_j(Et);
  if (!flag)
  {
    GEN Ft = isogeny_from_kernel_poly(Et, kert, flag, 0, 1);
    GEN isot = twistisogeny(gel(Ft, 2), stoi(n));
    return mkvec5(c4t, c6t, jt, gel(F, 2), isot);
  }
  else return mkvec3(c4t, c6t, jt);
}

static GEN
ellisog_by_roots(GEN a4, GEN a6, long n, GEN z, long flag)
{
  return ellisog_by_Kohel(a4, a6, n, deg1pol(gen_1, gneg(z), 0),
                                  deg1pol(gen_1, gmulsg(n, z), 0), flag);
}

static GEN
a4a6_divpol(GEN a4, GEN a6, long n)
{
  switch(n)
  {
    case 2:
      return mkpoln(4, gen_1, gen_0, a4, a6);
    case 3:
      return mkpoln(5, utoi(3), gen_0, gmulgs(a4,6) , gmulgs(a6,12),
                       gneg(gsqr(a4)));
  }
  return NULL;
}

static GEN
ellisograph_Kohel_iso(GEN nf, GEN e, long n, GEN z, long flag)
{
  long i, r;
  GEN R, V;
  GEN c4 = gel(e,1), c6 = gel(e, 2);
  GEN a4 = gdivgs(c4, -48), a6 = gdivgs(c6, -864);
  GEN P = a4a6_divpol(a4, a6, n);
  R = nfroots(nf, z ? RgX_div_by_X_x(P, z, NULL): P);
  r = lg(R);
  V = cgetg(r, t_VEC);
  for (i=1; i < r; i++)
    gel(V, i) = ellisog_by_roots(a4, a6, n, gel(R, i), flag);
  return mkvec2(V, R);
}

static GEN
ellisograph_Kohel_r(GEN nf, GEN e, long n, GEN z, long flag)
{
  GEN W = ellisograph_Kohel_iso(nf, e, n, z, flag);
  GEN iso = gel(W, 1), R = gel(W, 2);
  long i, r = lg(iso);
  GEN V = cgetg(r, t_VEC);
  for (i=1; i < r; i++)
    gel(V, i) = ellisograph_Kohel_r(nf, gel(iso, i), n, gmulgs(gel(R, i), -n), flag);
  return mkvec2(e, V);
}

static GEN
corr(GEN c4, GEN c6)
{
  GEN c62 = gmul2n(c6, 1);
  return gadd(gdiv(gsqr(c4), c62), gdiv(c62, gmulgs(c4,3)));
}

static GEN
elkies98(GEN a4, GEN a6, long l, GEN s, GEN a4t, GEN a6t)
{
  GEN C, P, S;
  long i, n, d;
  d = l == 2 ? 1 : l>>1;
  C = cgetg(d+1, t_VEC);
  gel(C, 1) = gdivgs(gsub(a4, a4t), 5);
  if (d >= 2)
    gel(C, 2) = gdivgs(gsub(a6, a6t), 7);
  if (d >= 3)
    gel(C, 3) = gdivgs(gsub(gsqr(gel(C, 1)), gmul(a4, gel(C, 1))), 3);
  for (n = 3; n < d; ++n)
  {
    GEN s = gen_0;
    for (i = 1; i < n; i++)
      s = gadd(s, gmul(gel(C, i), gel(C, n-i)));
    gel(C, n+1) = gdivgs(gsub(gsub(gmulsg(3, s), gmul(gmulsg((2*n-1)*(n-1), a4), gel(C, n-1))), gmul(gmulsg((2*n-2)*(n-2), a6), gel(C, n-2))), (n-1)*(2*n+5));
  }
  P = cgetg(d+2, t_VEC);
  gel(P, 1 + 0) = stoi(d);
  gel(P, 1 + 1) = s;
  if (d >= 2)
    gel(P, 1 + 2) = gdivgs(gsub(gel(C, 1), gmulgs(gmulsg(2, a4), d)), 6);
  for (n = 2; n < d; ++n)
    gel(P, 1 + n+1) = gdivgs(gsub(gsub(gel(C, n), gmul(gmulsg(4*n-2, a4), gel(P, 1+n-1))), gmul(gmulsg(4*n-4, a6), gel(P, 1+n-2))), 4*n+2);
  S = cgetg(d+3, t_POL);
  S[1] = evalsigne(1) | evalvarn(0);
  gel(S, 2 + d - 0) = gen_1;
  gel(S, 2 + d - 1) = gneg(s);
  for (n = 2; n <= d; ++n)
  {
    GEN s = gen_0;
    for (i = 1; i <= n; ++i)
    {
      GEN p = gmul(gel(P, 1+i), gel(S, 2 + d - (n-i)));
      s = gadd(s, p);
    }
    gel(S, 2 + d - n) = gdivgs(s, -n);
  }
  return S;
}

static GEN
ellisog_by_jt(GEN c4, GEN c6, GEN jt, GEN jtp, GEN s0, long n, long flag)
{
  GEN jtp2 = gsqr(jtp), den = gmul(jt, gsubgs(jt, 1728));
  GEN c4t = gdiv(jtp2, den);
  GEN c6t = gdiv(gmul(jtp, c4t), jt);
  if (flag)
    return mkvec3(c4t, c6t, jt);
  else
  {
    GEN co  = corr(c4, c6);
    GEN cot = corr(c4t, c6t);
    GEN s = gmul2n(gmulgs(gadd(gadd(s0, co), gmulgs(cot,-n)), -n), -2);
    GEN a4  = gdivgs(c4, -48), a6 = gdivgs(c6, -864);
    GEN a4t = gmul(gdivgs(c4t, -48), powuu(n,4)), a6t = gmul(gdivgs(c6t, -864), powuu(n,6));
    GEN ker = elkies98(a4, a6, n, s, a4t, a6t);
    GEN st = gmulgs(s, -n);
    GEN a4tt = gmul(a4,powuu(n,4)), a6tt = gmul(a6,powuu(n,6));
    GEN kert = elkies98(a4t, a6t, n, st, a4tt, a6tt);
    return ellisog_by_Kohel(a4, a6, n, ker, kert, flag);
  }
}

/*
Based on
RENE SCHOOF
Counting points on elliptic curves over finite fields
Journal de Theorie des Nombres de Bordeaux,
tome 7, no 1 (1995), p. 219-254.
<http://www.numdam.org/item?id=JTNB_1995__7_1_219_0>
*/

static GEN
ellisog_by_j(GEN e, GEN jt, long n, GEN P, long flag)
{
  pari_sp av = avma;
  GEN c4  = gel(e,1), c6 = gel(e, 2), j = gel(e, 3);
  GEN Px = deriv(P, 0), Py = deriv(P, 1);
  GEN Pxj = RgXY_eval(Px, j, jt), Pyj = RgXY_eval(Py, j, jt);
  GEN Pxx  = deriv(Px, 0), Pxy = deriv(Py, 0), Pyy = deriv(Py, 1);
  GEN Pxxj = RgXY_eval(Pxx,j,jt);
  GEN Pxyj = RgXY_eval(Pxy,j,jt);
  GEN Pyyj = RgXY_eval(Pyy,j,jt);
  GEN c6c4 = gdiv(c6, c4);
  GEN jp = gmul(j, c6c4);
  GEN jtp = gdivgs(gmul(jp, gdiv(Pxj, Pyj)), -n);
  GEN jtpn = gmulgs(jtp, n);
  GEN s0 = gdiv(gadd(gadd(gmul(gsqr(jp),Pxxj),gmul(gmul(jp,jtpn),gmul2n(Pxyj,1))),
                gmul(gsqr(jtpn),Pyyj)),gmul(jp,Pxj));
  GEN et = ellisog_by_jt(c4, c6, jt, jtp, s0, n, flag);
  return gerepilecopy(av, et);
}

static GEN
ellisograph_iso(GEN nf, GEN e, ulong p, GEN P, GEN oj, long flag)
{
  long i, r;
  GEN Pj, R, V;
  GEN j = gel(e, 3);
  Pj = poleval(P, j);
  R = nfroots(nf,oj ? RgX_div_by_X_x(Pj, oj, NULL):Pj);
  r = lg(R);
  V = cgetg(r, t_VEC);
  for (i=1; i < r; i++)
    gel(V, i) = ellisog_by_j(e, gel(R, i), p, P, flag);
  return V;
}

static GEN
ellisograph_r(GEN nf, GEN e, ulong p, GEN P, GEN oj, long flag)
{
  GEN iso = ellisograph_iso(nf, e, p, P, oj, flag);
  GEN j = gel(e, 3);
  long i, r = lg(iso);
  GEN V = cgetg(r, t_VEC);
  for (i=1; i < r; i++)
    gel(V, i) = ellisograph_r(nf, gel(iso, i), p, P, j, flag);
  return mkvec2(e, V);
}

static GEN
ellisograph_a4a6(GEN E, long flag)
{
  GEN c4 = ell_get_c4(E), c6 = ell_get_c6(E), j = ell_get_j(E);
  return flag ? mkvec3(c4, c6, j):
                mkvec5(c4, c6, j, isogeny_a4a6(E), invisogeny_a4a6(E));
}

static GEN
ellisograph_dummy(GEN E, long n, GEN jt, GEN jtt, GEN s0, long flag)
{
  GEN c4 = ell_get_c4(E), c6 = ell_get_c6(E);
  GEN c6c4 = gdiv(c6, c4);
  GEN jtp = gmul(c6c4, gdivgs(gmul(jt, jtt), -n));
  GEN iso = ellisog_by_jt(c4, c6, jt, jtp, gmul(s0, c6c4), n, flag);
  GEN v = mkvec2(iso, cgetg(1, t_VEC));
  return mkvec2(ellisograph_a4a6(E, flag), mkvec(v));
}

static GEN
ellisograph_p(GEN nf, GEN E, ulong p, long flag)
{
  pari_sp av = avma;
  GEN iso, e = ellisograph_a4a6(E, flag);
  if (p > 3)
  {
    GEN P = polmodular_ZXX(p, 0, 0, 1);
    iso = ellisograph_r(nf, e, p, P, NULL, flag);
  }
  else
    iso = ellisograph_Kohel_r(nf, e, p, NULL, flag);
  return gerepilecopy(av, iso);
}

static long
etree_nbnodes(GEN T)
{
  GEN F = gel(T,2);
  long n = 1, i, l = lg(F);
  for (i = 1; i < l; i++)
    n += etree_nbnodes(gel(F, i));
  return n;
}

static long
etree_listr(GEN T, GEN V, long n, GEN u, GEN ut)
{
  GEN E = gel(T, 1), F = gel(T,2);
  long i, l = lg(F);
  GEN iso, isot = NULL;
  if (lg(E) == 6)
  {
    iso  = ellisogenyapply(gel(E,4), u);
    isot = ellisogenyapply(ut, gel(E,5));
    gel(V, n) = mkvec5(gel(E,1), gel(E,2), gel(E,3), iso, isot);
  } else
  {
    gel(V, n) = mkvec3(gel(E,1), gel(E,2), gel(E,3));
    iso = u;
  }
  for (i = 1; i < l; i++)
    n = etree_listr(gel(F, i), V, n + 1, iso, isot);
  return n;
}

static GEN
etree_list(GEN T)
{
  long n = etree_nbnodes(T);
  GEN V = cgetg(n+1, t_VEC);
  (void) etree_listr(T, V, 1, trivial_isogeny(), trivial_isogeny());
  return V;
}

static long
etree_distmatr(GEN T, GEN M, long n)
{
  GEN F = gel(T,2);
  long i, j, lF = lg(F), m = n + 1;
  GEN V = cgetg(lF, t_VECSMALL);
  mael(M, n, n) = 0;
  for(i = 1; i < lF; i++)
    V[i] = m = etree_distmatr(gel(F,i), M, m);
  for(i = 1; i < lF; i++)
  {
    long mi = i==1 ? n+1: V[i-1];
    for(j = mi; j < V[i]; j++)
    {
      mael(M,n,j) = 1 + mael(M, mi, j);
      mael(M,j,n) = 1 + mael(M, j, mi);
    }
    for(j = 1; j < lF; j++)
      if (i != j)
      {
        long i1, j1, mj = j==1 ? n+1: V[j-1];
        for (i1 = mi; i1 < V[i]; i1++)
          for(j1 = mj; j1 < V[j]; j1++)
            mael(M,i1,j1) = 2 + mael(M,mj,j1) + mael(M,i1,mi);
      }
  }
  return m;
}

static GEN
etree_distmat(GEN T)
{
  long i, n = etree_nbnodes(T);
  GEN M = cgetg(n+1, t_MAT);
  for(i = 1; i <= n; i++)
    gel(M,i) = cgetg(n+1, t_VECSMALL);
  (void)etree_distmatr(T, M, 1);
  return M;
}

static GEN
list_to_crv(GEN L)
{
  long i, l;
  GEN V = cgetg_copy(L, &l);
  for(i=1; i < l; i++)
  {
    GEN Li = gel(L, i);
    GEN e = mkvec2(gdivgs(gel(Li,1), -48), gdivgs(gel(Li,2), -864));
    gel(V, i) = lg(Li)==6 ? mkvec3(e, gel(Li,4), gel(Li,5)): e;
  }
  return V;
}

static GEN
distmat_pow(GEN E, ulong p)
{
  long i, j, n = lg(E)-1;
  GEN M = cgetg(n+1, t_MAT);
  for(i = 1; i <= n; i++)
  {
    gel(M,i) = cgetg(n+1, t_VEC);
    for(j = 1; j <= n; j++)
      gmael(M,i,j) = powuu(p,mael(E,i,j));
  }
  return M;
}

/* Assume there is a single p-isogeny */

static GEN
isomatdbl(GEN nf, GEN L, GEN M, ulong p, GEN T2, long flag)
{
  long i, j, n = lg(L) -1;
  GEN P = p > 3 ? polmodular_ZXX(p, 0, 0, 1): NULL;
  GEN V = cgetg(2*n+1, t_VEC);
  GEN N = cgetg(2*n+1, t_MAT);
  for(i=1; i <= n; i++)
    gel(V, i) = gel(L, i);
  for(i=1; i <= n; i++)
  {
    GEN e = gel(L, i);
    GEN F, E;
    if (i == 1)
      F = gmael(T2, 2, 1);
    else
    {
      if (p > 3)
        F = ellisograph_iso(nf, e, p, P, NULL, flag);
      else
        F = gel(ellisograph_Kohel_iso(nf, e, p, NULL, flag), 1);
      if (lg(F) != 2) pari_err_BUG("isomatdbl");
    }
    E = gel(F, 1);
    if (flag)
      gel(V, i+n) = mkvec3(gel(E,1), gel(E,2), gel(E,3));
    else
    {
      GEN iso = ellisogenyapply(gel(E,4), gel(e, 4));
      GEN isot = ellisogenyapply(gel(e,5), gel(E, 5));
      gel(V, i+n) = mkvec5(gel(E,1), gel(E,2), gel(E,3), iso, isot);
    }
  }
  for(i=1; i <= 2*n; i++)
    gel(N, i) = cgetg(2*n+1, t_COL);
  for(i=1; i <= n; i++)
    for(j=1; j <= n; j++)
    {
      gcoeff(N,i,j) = gcoeff(N,i+n,j+n) = gcoeff(M,i,j);
      gcoeff(N,i,j+n) = gcoeff(N,i+n,j) = muliu(gcoeff(M,i,j), p);
    }
  return mkvec2(list_to_crv(V), N);
}

INLINE GEN
mkfracss(long x, long y) { retmkfrac(stoi(x),stoi(y)); }

static ulong
ellQ_exceptional_iso(GEN j, GEN *jt, GEN *jtp, GEN *s0)
{
  *jt = j; *jtp = gen_1;
  if (typ(j)==t_INT)
  {
    long js = itos_or_0(j);
    GEN j37;
    if (js==-32768) { *s0 = mkfracss(-1156,539); return 11; }
    if (js==-121)
      { *jt = stoi(-24729001) ; *jtp = mkfracss(4973,5633);
        *s0 = mkfracss(-1961682050,1204555087); return 11;}
    if (js==-24729001)
      { *jt = stoi(-121); *jtp = mkfracss(5633,4973);
        *s0 = mkfracss(-1961682050,1063421347); return 11;}
    if (js==-884736)
      { *s0 = mkfracss(-1100,513); return 19; }
    j37 = negi(uu32toi(37876312,1780746325));
    if (js==-9317)
    {
      *jt = j37;
      *jtp = mkfracss(1984136099,496260169);
      *s0 = mkfrac(negi(uu32toi(457100760,4180820796UL)),
                        uu32toi(89049913, 4077411069UL));
      return 37;
    }
    if (equalii(j, j37))
    {
      *jt = stoi(-9317);
      *jtp = mkfrac(utoi(496260169),utoi(1984136099UL));
      *s0 = mkfrac(negi(uu32toi(41554614,2722784052UL)),
                        uu32toi(32367030,2614994557UL));
      return 37;
    }
    if (js==-884736000)
    { *s0 = mkfracss(-1073708,512001); return 43; }
    if (equalii(j, negi(powuu(5280,3))))
    { *s0 = mkfracss(-176993228,85184001); return 67; }
    if (equalii(j, negi(powuu(640320,3))))
    { *s0 = mkfrac(negi(uu32toi(72512,1969695276)), uu32toi(35374,1199927297));
      return 163; }
  } else
  {
    GEN j1 = mkfracss(-297756989,2);
    GEN j2 = mkfracss(-882216989,131072);
    if (gequal(j, j1))
    {
      *jt = j2; *jtp = mkfracss(1503991,2878441);
      *s0 = mkfrac(negi(uu32toi(121934,548114672)),uu32toi(77014,117338383));
      return 17;
    }
    if (gequal(j, j2))
    {
      *jt = j1; *jtp = mkfracss(2878441,1503991);
      *s0 = mkfrac(negi(uu32toi(121934,548114672)),uu32toi(40239,4202639633UL));
      return 17;
    }
  }
  return 0;
}

static GEN
mkisomat(ulong p, GEN T)
{
  pari_sp av = avma;
  GEN L = list_to_crv(etree_list(T));
  GEN M = distmat_pow(etree_distmat(T), p);
  return gerepilecopy(av, mkvec2(L, M));
}

static GEN
mkisomatdbl(ulong p, GEN T, ulong p2, GEN T2, long flag)
{
  GEN L = etree_list(T);
  GEN M = distmat_pow(etree_distmat(T), p);
  return isomatdbl(NULL, L, M, p2, T2, flag);
}

/*
See
M.A Kenku
On the number of Q-isomorphism classes of elliptic curves in each Q-isogeny class
Journal of Number Theory
Volume 15, Issue 2, October 1982, Pages 199-202
http://www.sciencedirect.com/science/article/pii/0022314X82900257
*/

static GEN
ellQ_isomat(GEN E, long flag)
{
  GEN K = NULL;
  GEN T2, T3, T5, T7, T13;
  long n2, n3, n5, n7, n13;
  GEN jt, jtp, s0;
  GEN c4 = ell_get_c4(E), c6 = ell_get_c6(E), j = ell_get_j(E);
  long l = ellQ_exceptional_iso(j, &jt, &jtp, &s0);
  if (l)
  {
#if 1
      return mkisomat(l, ellisograph_dummy(E, l, jt, jtp, s0, flag));
#else
      return mkisomat(l, ellisograph_p(K, E, l), flag);
#endif
  }
  T2 = ellisograph_p(K, E, 2, flag);
  n2 = etree_nbnodes(T2);
  if (n2>4 || gequalgs(j, 1728) || gequalgs(j, 287496))
    return mkisomat(2, T2);
  T3 = ellisograph_p(K, E, 3, flag);
  n3 = etree_nbnodes(T3);
  if (n3>1 && n2==2) return mkisomatdbl(3,T3,2,T2, flag);
  if (n3==2 && n2>1)  return mkisomatdbl(2,T2,3,T3, flag);
  if (n3>2 || gequal0(j)) return mkisomat(3, T3);
  T5 = ellisograph_p(K, E, 5, flag);
  n5 = etree_nbnodes(T5);
  if (n5>1 && n2>1) return mkisomatdbl(2,T2,5,T5, flag);
  if (n5>1 && n3>1) return mkisomatdbl(3,T3,5,T5, flag);
  if (n5>1) return mkisomat(5, T5);
  T7 = ellisograph_p(K, E, 7, flag);
  n7 = etree_nbnodes(T7);
  if (n7>1 && n2>1) return mkisomatdbl(2,T2,7,T7, flag);
  if (n7>1 && n3>1) return mkisomatdbl(3,T3,7,T7, flag);
  if (n7>1) return mkisomat(7,T7);
  if (n2>1) return mkisomat(2,T2);
  if (n3>1) return mkisomat(3,T3);
  T13 = ellisograph_p(K, E, 13, flag);
  n13 = etree_nbnodes(T13);
  if (n13>1) return mkisomat(13,T13);
  if (flag)
    retmkvec2(list_to_crv(mkvec(mkvec3(c4, c6, j))), matid(1));
  else
    retmkvec2(list_to_crv(mkvec(mkvec5(c4, c6, j, isogeny_a4a6(E), invisogeny_a4a6(E)))), matid(1));
}

GEN
ellisomat(GEN E, long flag)
{
  pari_sp av = avma;
  GEN LM;
  checkell_Q(E);
  if (flag < 0 || flag > 1) pari_err_FLAG("ellisomat");
  LM = ellQ_isomat(E, flag);
  return gerepilecopy(av, LM);
}