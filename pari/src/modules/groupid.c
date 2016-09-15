/* Copyright (C) 2003  The PARI group.

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

static long
groupelts_sumorders(GEN S)
{
  long i, s = 0;
  for(i=1; i < lg(S); i++) s += perm_order(gel(S,i));
  return s;
}

static long
vecgroup_sumorders(GEN L)
{
  long i, s = 0;
  for(i=1; i<lg(L); i++) s += group_order(gel(L,i));
  return s;
}

static int
indexgroupsubgroup(GEN L, long order, const long *good, const long *bad)
{
  long i;
  for(i=1; i<lg(L); i++)
  {
    GEN G=gel(L,i);
    long idx;
    const long *p;
    if (group_order(G)!=order) continue;
    idx = group_ident(G,NULL);
    for(p=good; *p; p++)
      if (*p==idx) return 1;
    for(p=bad; *p; p++)
      if (*p==idx) return 0;
  }
  return 0;
}

static int
indexgroupcentre(GEN G, GEN Z, const long *good, const long *bad)
{
  long i;
  for(i=1;i<lg(Z);i++)
  {
    GEN z=gel(Z,i);
    if (perm_order(z)==2)
    {
      pari_sp btop=avma;
      GEN H = cyclicgroup(z,2);
      GEN C = group_quotient(G,H);
      GEN Q = quotient_group(C,G);
      const long *p;
      long idx=group_ident(Q,NULL);
      avma=btop;
      for(p=good;*p;p++)
        if (*p==idx) return 1;
      for(p=bad;*p;p++)
        if (*p==idx) return 0;
    }
  }
  return 0;
}

static GEN
vecgroup_idxlist(GEN L, long order)
{
  pari_sp ltop=avma;
  GEN V;
  long i,j,n;
  for (n=0,i=1; i<lg(L); i++)
    if (group_order(gel(L,i))==order)
      n++;
  V=cgetg(n+1,t_VECSMALL);
  for(i=1,j=1; j<=n; i++)
    if (group_order(gel(L,i))==order)
      V[j++]=group_ident(gel(L,i),NULL);
  return gerepileupto(ltop,vecsmall_uniq(V));
}

/* Group identification code.
 * The group data are taken from GAP 4 and the SMALL GROUPS LIBRARY by  Hans
 * Ulrich Besche, Bettina Eick and Eamonn O'Brien.
 */

static long
group_ident_i(GEN G, GEN S)
{
  long n = group_order(G);
  long s;
  GEN F,p,e;
  if (n==1) return 1;
  if (!S) S = group_elts(G,group_domain(G));
  s = groupelts_sumorders(S);/*This is used as a hash value*/
  F = factoru(n);
  p = gel(F,1);
  e = gel(F,2);
  switch(lg(p)-1)
  {
  case 1:/*prime power*/
    switch (e[1])
    {
    case 1: /* p */
      return 1;
    case 2: /* p^2 */
      return (s == 1 - p[1] + n*p[1])? 2: 1; /* pxp || p^2 */
    case 3: /* p^3 */
      {
        GEN H = group_abelianSNF(G, S);
        if (H) /*G is abelian*/
        {
          long l = lg(H)-1;
          return (l==3)?5: l; /*pxpxp || p^3 or p^2xp*/
        } /*G is not abelian*/
        if (p[1] == 2)
          return (s == 19)? 3: 4; /*D8 || Q8*/
        else
        {
          long q = p[1]*p[1];
          q *= q;
          return (s == q - p[1] + 1)?3 :4; /* pxp:p || p^2:p */
        }
      }
    }
    break;
  case 2:
    switch(e[1]+e[2])
    {
    case 2: /*pq*/
      return (p[2]%p[1]!=1)?1:1+group_isabelian(G); /*pq || pq or p:q*/
    case 3:
      if (p[1]==2 && e[1]==2) /* 4p */
      {
        long q = p[2], q2 = q*q, pmq2 = (q%4 == 1 || q==3);
        if (s==3+5*q+3*q2) return 1; /* 2p.2 */
        if (s==11-11*q+11*q2) return 2; /* 4p */
        if (s==3+q+3*q2) return 3+pmq2; /* D4p */
        if (s==7-7*q+7*q2) return 4+pmq2; /* 2px2 */
        return 3; /*A4 or p:4 */
      }
      else if (p[1]==2 && e[1]==1) /*2p^2*/
      {
        long q = p[2], q2 = q*q, q3 = q*q2, q4 = q*q3;
        if (s==1-q+3*q2-q3+q4) return 1; /* p^2:2 */
        if (s==3-3*q+3*q2-3*q3+3*q4) return 2; /* 2p^2 */
        if (s==1+q-2*q2+3*q3) return 3; /* D2pxp */
        if (s==1-q+2*q2+q3) return 4; /* p:2+p:2 */
        return 5;   /* 2pxp */
      }
      else if (p[1]==3 && e[1]==2) /*9p, p>3*/
      {
        long q= p[2], q2 = q*q, p3 = (q%3 == 1), p9 = (q%9 == 1);
        if (s==7+47*q+7*q2) return 1; /* 3p.3 */
        if (s==61-61*q+61*q2) return 1+p3; /* 9p */
        if (s==1+59*q+q2) return 3; /* p:9 */
        if (s==7+11*q+7*q2) return 3+p9; /* p:3x3 */
        return 2+2*p3+p9; /* 3^2xp */
      }
      break;
    }
  case 3:
    switch(e[1]+e[2]+e[3])
    {
    case 3: /*pqr*/
      if (p[1]==2)  /*2qr*/
      {
        long q = p[2],q2 = q*q, qc = 1-q+q2, qd = 1+q+q2;
        long r = p[3],r2 = r*r, rc = 1-r+r2, rd = 1+r+r2;
        long pmq = (r%q==1)? 2: 0;
        if (pmq && s==3*r*(q2-q)+rd) return 1; /* r:2q */
        if (pmq && s==3*(r2+(q2-q-1)*r+1)) return 2; /* r:qx2 */
        if (s==qd*rc) return 1+pmq; /* D2qxr */
        if (s==rd*qc) return 2+pmq; /* D2rxq */
        if (s==3*qc*rc) return 4+pmq; /* 2qr */
        return 3+pmq; /* q:2+r:2 */
      }
      break;
    }
  }
  {
    const long tab[]={
    24, 173, 301, 99, 125, 113, 101, 97, 85, 161, 133, 189, 67, 87, 73, 105, -1,
    36, 255, 671, 265, 219, 427, 243, 147, 275, 115, 127, 121, 159, 111, 175,
       -1,
    40, 391, 903, 263, 311, 291, 271, 227, 207, 483, 399, 567, 163, 187, 315,
       -1,
    56, 697, 1849, 585, 557, 529, 413, 385, 989, 817, 1161, 351, 357, 645, -1,
    60, 945, 721, 561, 1617, 211, 497, 337, 373, 651, 581, 693, 501, 1029, -1,
    75, 3647, 271, 847, -1,
    84, 647, 935, 1935, 1295, 1071, 3311, 451, 699, 595, 1333, 469, 1099, 1419,
        987, 2107, -1,
    88, 1573, 4773, 1397, 1353, 1309, 953, 909, 2553, 2109, 2997, 865, 1665, -1,
    90, 1659, 1891, 1371, 3843, 775, 1407, 735, 903, 615, 1575, -1,
    104, 2143, 6751, 991, 1935, 1883, 1831, 1307, 1255, 3611, 2983, 4239, 731,
         1203, 2355, -1,
    105, 1785, 6321, -1,
    126, 1533, 2037, 3397, 3477, 2749, 7869, 777, 937, 721, 1281, 1425, 2881,
         1369, 1849, 1201, 3225, -1,
      -1};
      long i;
      const long *t;
      for(t=tab;*t!=-1;t++)
      {
        if (t[0]==n)
        {
          for(i=1; t[i] != -1; i++)
            if (t[i]==s) return i;
          return -1;
        }
        while (*t>=0) t++;
      }
  }
  {
    const long tab[]={
      16, 1710031, 550075, 70099, 70075, 870059, 110059, 30079, 30071, 30063,
470131, 70155, 70107, 110115, 310307, -1,
      32, 6830063, 150323, 1830171, /*230171*/0, 230227, 30283, 30251, 30203,
/*70267*/0, 70219, 110227, /*230171*/0, /*70187*/0, /*70187*/0, 110155,
3430123, 430123, 30191, 30175, 30159, 1110387, 150563, 150387, 230323, 230411,
230299, 70619, 70467, 70355, /*70379*/0, /*70379*/0, /*70267*/0, 70291, 70555,
70331, 1750291, 230291, 430275, 70411, 70363, 70315, 110331, 30371, 30323,
950819, 150995, 150643, 230691, 30747, 30635, 632451, -1,
      48, 430156, 11970124, 10219, 430324, 110324, 30396, 30444, 30348, 230300,
110300, 230396, /*70396*/0, /*70396*/0, 70540, 30412, 30364, 30380, 30332,
70492, 3850300, 490396, 490300, 6090236, 770236, 210316, 210284, 210252, 30299,
30371, 30363, 110299, 70311, 110271, 70588, 230732, 70876, 110636, 30868,
30628, 30596, 30644, 150684, 70828, 3290524, 490620, 490428, 770460, 30627,
70571, 10643, 151740, 2171228, -1,
      54, 10256, 16410120, 70292, 610232, 10373, 10292, 10616, 70517, 5610228,
210309, 210228, 250448, 70616, 11696, 2370552, -1,
      /*64*/
      72, 110307, 26230195, 210272, 30523, 110631, 30739, 70575, 30683,
14030351, 1830403, 1830299, 770346, 110586, 10750330, 10620, 210420, 71223,
9150663, 30426, 30858, 30978, 30954, 31074, 30762, 210452, 210538, 770634,
210730, 490626, 210722, 31018, 111234, 31450, 71106, 31322, 5750594, 750682,
750506, 10346, 10826, 10490, 70620, 11124, 10716, 30786, 31746, 210636, 491202,
72402, 3751122, -1,
      80, 430250, 35910186, 110282, 430530, 110530, 30650, 30730, 30570,
230482, 110482, 230642, /*70642*/0, /*70642*/0, 70882, 30666, 30586, 30618,
30538, 70786, 11550450, 1470594, 1470450, 18270354, 2310354, 630474, 630426,
630378, 110562, 30562, 110722, 30722, 70546, 30546, 30946, 70962, 231202,
71442, 111042, 31426, 31026, 30978, 31058, 151106, 71346, 9870786, 1470930,
1470642, 2310690, 10467, 71266, 152866, 6511842, -1,
      81,49210121, 6730319, 250427, 250319, 16450238, 610238, 70454, 70346,
70400, 70319, 5650670, 250994, 250670, 610589, 2412452, -1,
      /*96*/
      100, 30393, 57310217, 10481, 30693, 36470341, 630408, 30968, 13310392,
210416, 10576, 11256, 10856, 11096, 630648, 31768, 8470616, -1,
      108, 30552, 60170280, 610359, 30984, 38290440, 210660, 1830540, 30849,
30660, 31308, 211137, 20570532, 770721, 770532, 70769, 11636, 11813, 610647,
70647, 250674, 70674, 70890, 211092, 1830852, 31389, 31092, 32388, 211965,
13090836, 491133, 490836, 751080, 211416, 33576, 8691288, 70904, 11048, 71720,
13688, 12344, 251538, 751608, 212280, 36600, 5532024,-1,
      112, 430344, 73530248, 430736, 110736, 30904, 31016, 30792, 230664,
110664, 230888, 0/*70888*/, 0/*70888*/, 71224, 30920, 30808, 30856, 30744,
71080, 23650600, 3010792, 3010600, 37410472, 4730472, 1290632, 1290568,
1290504, 71336, 231672, 72008, 111448, 31984, 31424, 31360, 31472, 151528,
71864, 20211048, 3011240, 3010856, 4730920, 30643, 153992, 13332456,-1,
      120,2310456, 770488, 110648, 63210360, 30763, 210552, 30712, 31256,
31240, 31336, 31400, 31496, 31480, 31096, 630498, 210808, 770968, 211128,
490904, 211064, 630744, 2310888, 631032, 1470840, 630984, 31128, 111368, 31608,
71224, 31464, 33810648, 4410744, 4410552, 11211, 31263, 11416, 210858, 11290,
11090, 211032, 31352, 32600, 630738, 491864, 1471704, 72664, 22051224, -1,
      -1};
    long i;
    const long *t;
    GEN Z = groupelts_center(S), L = group_subgroups(G);
    long scenter = groupelts_sumorders(Z), svecgroup = vecgroup_sumorders(L);
    long u = svecgroup+10000*scenter; /*This is used as a hash value*/

    for(t=tab; *t!=-1; t++)
    {
      if (t[0]==n)
      {
        for(i=1; t[i] != -1; i++)
          if (t[i]==u) return i;
        switch(n)
        {
        case 32:
          switch(u)
          {
          case 230171:
            {
              const long good[]={2,0}, bad[]={4,5,0};
              return indexgroupcentre(G,Z,good,bad)? 4: 12;
            }
          case 70267:
            if (s==135) return 9;
            return 32;
          case 70187:
            {
              const long good[]={8,0}, bad[]={7,9,0};
              return indexgroupcentre(G,Z,good,bad)? 13: 14;
            }
          case 70379:
            {
              const long good[]={4,0},bad[]={0};
              return indexgroupsubgroup(L,8,good,bad)? 31: 30;
            }
          }
          break;
        case 48: case 80:
          {
            const long good[]={5,8,0},bad[]={6,7,0};
            return indexgroupcentre(G,Z,good,bad)? 12: 13;
          }
        case 112:
          {
            const long good[]={7,4,0},bad[]={5,6,0};
            return indexgroupcentre(G,Z,good,bad)? 11: 12;
          }
        }
        return -1;
      }
      while (*t!=-1) t++;
    }
    {
      const long tab[]={ 64, 1270001, /*4270003*/0, /*4270003*/0, 8190072,
 6430073, 6670445, 5550446, 8190278, 7070279, 6350071, 5230072, 8110154,
 /*5870155*/0, /*5870155*/0, /*4270042*/0, /*4270042*/0, 7710246, 7390277,
 6750037, 8032377, 8670266, 6750397, 11390022, 7710267, 7070277, /*3630046*/0,
 /*3630046*/0, 3630057, 4830196, 4830207, 4671808, 9070697, 6670700, 8750094,
 6990091, 6350111, 5870115, 6671599, 5711601, 5551702, 5871512, 6351709,
 5391711, /*3630046*/0, 3630047, 4111467, /*4430156*/0, /*4430156*/0, 3790166,
 /*2510026*/0, /*2510026*/0, 4470028, 4150300, 3830030, 13470021, 20350065,
 10910041, 16514365, /*12190433*/0, 34110271, /*16514475*/0, 15230465,
 /*10910433*/0, 9630041, 13470233, /*16514475*/0, 20834696, /*10910433*/0,
 13954343, /*12190433*/0, 19553542, 13474377, 25790466, 15870467, 18914476,
 14110477, /*14590443*/0, 13310443, 11550043, /*14590443*/0, 10270043, 8990002,
 8990546, 8990646, 8993647, 8356896, 13310905, 13310915, 12039018, 16990866,
 12670888, 15071116, 11551217, 12038218, 16031739, 12512740, 12353138, 12993048,
 15391849, 11872850, 12993551, 12353851, 8991446, 8991447, 8354830, 9951566,
 9951666, 8674709, 9317039, 8031897, 8030187, 7713641, 7714641, 7074743,
 9236585, 9236415, 9236586, 10990821, 9879066, 8751833, 9873399, 8751766,
 10990754, 8593054, 8593087, 6830446, 6833546, 17472434, 13953445, 14432313,
 16352544, 12833555, 13313423, 15635143, 13234877, 13874853, 12755287, 17870919,
 14190949, 13075209, 11955310, 10835253, 9715354, 11312124, 10193135, 11074927,
 12197529, 9957664, 11074970, 12196539, 9956674, 9958907, 10439497, 9479551,
 9554015, 8433958, 9553915, 8434058, 8918081, 7798421, 10110856, 10110756,
 9476648, 8991757, 8991857, 8356682, 10994275, 8750435, 8590474, 9230510,
 10355254, 8115355, 13556790, 15790679, 11310691, 12275539, 14035061, 11795172,
 8750465, 7474472, 8750475, 8114920, 6110196, 6111806, 5951808, 10191819,
 9238364, 8271841, 8590736, 9390959, 8432079, 25470255, 41792701, 25470275,
 20355344, 27233751, 18593673, 19717567, 23394762, 17312707, 19717633, 46115277,
 31557088, 22917189, 24677288, 24039835, 24676366, 16032362, 17793529, 17153269,
 38432486, 21153763, 23393635, 16037076, 27710971, 27074338, 20995174, 23396204,
 20193482, 17157790, 19550231, 14751475, 17153832, 19070249, 16038080, 33391110,
 25875097, 22197835, 22195018, 21070221, 24590112, 18999456, 15952565, 18356361,
 17237769, 18359003, 15951169, 14832955, 16110295, 18350268, 21392354, 22030301,
 18353365, 15955257, 13550032, 18430405, 18434015, 17150260, 17154128, 27234036,
 23710639, 20194057, 21157900, 24198470, 20679613, 21158141, 22435065, 21318520,
 20197076, 67390501, 83715011, 51070497, 54590283, 58915129, 50275230, 52035340,
 263870051, -1,
      -1};
      long i;
      const long *t;
      GEN V=vecgroup_idxlist(L,32);
      long idxlist=vecsmall_pack(V,10,9967);
      long w=10000*svecgroup+idxlist; /*This is used as a hash value*/
      for(t=tab; *t!=-1; t++)
      {
        if (t[0]==n)
        {
          for(i=1; t[i] != -1; i++)
            if (t[i]==w) return i;
          switch(n)
          {
          case 64:
            switch(w)
            {
            case 4270003:
              return (scenter==439)? 2: 3;
            case 5870155:
              {
                const long good[]={8,9,0},bad[]={7,0};
                return indexgroupcentre(G,Z,good,bad)? 13: 14;
              }
            case 4270042:
              {
                const long good[]={13,0},bad[]={14,0};
                return indexgroupcentre(G,Z,good,bad)? 15: 16;
              }
            case 4430156:
              {
                const long good[]={18,20,0},bad[]={19,0};
                return indexgroupcentre(G,Z,good,bad)? 47: 48;
              }
            case 2510026:
              return scenter==1367? 50: 51;
            case 12190433:
              return scenter==47? 59: 70;
            case 16514475:
              {
                const long good[]={22,24,28,0},bad[]={23,25,27,30,0};
                return indexgroupcentre(G,Z,good,bad)? 61: 66;
              }
            case 10910433:
              {
                const long good[]={23,31,0},bad[]={25,26,29,30,33,0};
                return indexgroupcentre(G,Z,good,bad)? 63: 68;
              }
            case 14590443:
              {
                const long good[]={28,33,0},bad[]={30,34,0};
                return indexgroupcentre(G,Z,good,bad)? 77: 80;
              }
            case 3630046:
              {
                const long good[]={3,0},bad[]={12,16,0};
                if (scenter==695) return 26;
                return indexgroupcentre(G,Z,good,bad)? 27: 44;
              }
            }
            break;
          }
          return -1;
        }
        while (*t!=-1) t++;
      }
    }
    {
      const long tab[]={ 96, 316010002, 252010002, 707020000, 676160124,
    676170124, 87180027, 988190278, 892200028, 876030110, 876040110, 876120110,
    215111237, 503062153, 972141052, 972131052, 455091156, 167101154, 620160033,
    620170033, 908031033, 908121033, 908041033, 199101564, 7130153, 7140153,
    812150123, 247051165, 487091566, 812151024, 391071276, 103081274, 247111377,
    988180195, 892190205, 924190197, 828200207, 103050134, 679020464, 295091075,
    199070145, 391060235, 103101076, 7080146, 135111157, 295020044, 684030223,
    684040223, 908050274, 135060255, 7070285, 812080286, 71092475, 876102476,
    908112287, 684120223, 748130243, 748140243, 620150254, 492160043, 492170043,
    764180045, 700190477, 636200047, 963110003, 779050031, 935100032, 799110033,
    819210003, 791260032, 246270050, 723330003, 987340003, 651360031, 623380033,
    647263930, 839351534, 455321350, 178211335, 791244031, 322256848, 189340236,
    130316409, 599331360, 743244548, 935295937, 551333907, 189222029, 274255883,
    525275609, 82306043, 610289391, 82315641, 82307025, 647262487, 839353950,
    0/*455322385*/, 0/*455322385*/, 178233588, 791245051, 322256982, 130307015,
    658286619, 983297004, 983297037, 599333858, 631365165, 631376165, 535386399,
    66408676, 354390966, 871428265, 775411064, 631376407, 535386309, 114430028,
    823441008, 314398920, 74437993, 831420054, 42405827, 90439425, 799440830,
    847426805, 767410275, 815440314, 863429143, 487360134, 487371044, 66211564,
    66231664, 871295713, 66231764, 679242567, 125228724, 210253894, 18306803,
    546288536, 162390938, 919437378, 871401018, 162255761, 967304398, 967313318,
    413274329, 498283470, 498288163, 29345108, 967401139, 727449579, 679411219,
    775352619, 583261276, 919295225, 66312839, 423381047, 2437470, 759424560,
    711448550, 770222372, 109272382, 551210244, 258222592, 551230264, 295242430,
    647254411, 199262266, 482272602, 871283751, 423293752, 519303751, 519312662,
    71320222, 167332232, 226340245, 327352266, 167360274, 167372584, 103382587,
    647392595, 455406162, 263412616, 327428742, 487438955, 295440098, 358290331,
    622253358, 886280358, 322410312, 754400322, 394443122, 282440313, 354423123,
    522430323, 726220349, 990273529, 470450359, 742460359, 522470032, 198470031,
    282480353, 290490033, 274500353, 414470000, 614490000, 605473864, 664459790,
    723464091, 893482714, 675465704, 845486215, 184493728, 653478045, 941489155,
    605501588, 925482982, 264492577, 589502601, 312450472, 371466994, 285450492,
    989464902, 578470486, 770489139, 994490497, 546500507, 604460529, 65270050,
    684510049, 468510050, 134510562, 831510052, -1
        -1};
      long i;
      const long *t;
      GEN V=vecgroup_idxlist(L,48);
      long idx48=vecsmall_pack(V,10,9967);
      long idx32=vecgroup_idxlist(L,32)[1];
      long w=1000000*(svecgroup%997)+10000*idx32+idx48;
      /*This is used as a hash value*/
      for(t=tab; *t!=-1; t++)
      {
        if (t[0]==n)
        {
          for(i=1; t[i] != -1; i++)
            if (t[i]==w) return i;
          switch(n)
          {
          case 96:
            switch(w)
            {
            case 455322385:
              {
                const long good[]={37,40,0},bad[]={34,41,0};
                return indexgroupcentre(G,Z,good,bad)? 96: 97;
              }
            }
            break;
          }
          return -1;
        }
        while (*t!=-1) t++;
      }
    }
  }
  return 0;
}

long
group_ident(GEN G, GEN S)
{
  pari_sp av = avma;
  long idx = group_ident_i(G, S);
  if (idx < 0) pari_err_TYPE("group_ident [not a group]", G);
  if (!idx) pari_err_IMPL("galoisidentify for groups of order > 127");
  avma = av; return idx;
}

long
group_ident_trans(GEN G, GEN S)
{
  const long tab[]={
        4, 1, 2, -1,
        6, 2, 1, -1,
        8, 1, 2, 4, 5, 3, -1,
        9, 1, 2, -1,
        10, 2, 1, -1,
        12, 5, 1, 4, 3, 2, -1,
        14, 2, 1, -1,
        15, 1, -1,
        16, 1, 4, 10, 8, 5, 6, 13, 12, 14, 2, 9, 7, 11, 3, -1,
        18, 5, 1, 3, 4, 2, -1,
        20, 2, 1, 5, 4, 3, -1,
        21, 2, 1, -1,
        22, 2, 1, -1,
        24, 8, 1, 7, 5, 12, 13, 6, 14, 2, 15, 4, 10, 9, 11, 3, -1,
        25, 1, 2, -1,
        26, 2, 1, -1,
        27, 1, 2, 3, 5, 4, -1,
        28, 3, 1, 4, 2, -1,
        30, 2, 4, 3, 1, -1,
        -1};
  long n = group_order(G), s;
  const long *t;
  if (n == 1) return 1;
  /* N.B. known up to 32 (Cannon-Holt) */
  if (n > 30) pari_err_IMPL("group_ident_trans [n > 30]");
  if (uisprime(n)) return 1;
  s = group_ident(G,S);
  for(t=tab;*t>=0;t++)
  {
    if (t[0]==n) return t[s];
    while (*t>=0) t++;
  }
  return 0; /*NOT REACHED*/
}
