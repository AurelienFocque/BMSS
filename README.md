# BMSS
fast algorithm for computing isogenies using PARIGP framework (v 2.8)

v1.c is a source code for BMSS and Lercier Sirvent that works without any modification in PARI library.

If you want to modify PARI library in order to add it this code, you can find in "fichiers modifiés" the files you need to change.

Most of the functions added in FpX.c are necessary for ellsea.c.

List of changes:

In FpX.c:

-FqX_halfgcd now works in average caracteristic.
-FqXn_mul recoded from the begining, using optimal cutoff (0.7) and suitable for Fq.
-Some functions (FqX_mulup..) for upper and middle product.
-Newton inverse iteration and operations on formal series (FqXn_inv, FqXn_sqrt, FqXn_exp, FqXn_log)


In ellsea.c:
BMSSPREC is a macro standing for the number of extra coefficients you want to calculate in order to check the kernel polynomial.
In the previous version, the division polynomial was calculated to check the result, but it's very slow.

-new function Zq_div_safe, because either the existing function didn't work or I didn't manage to make it work correctly.
Anyway the previous code with find_kernel didn't work in small caracteristic.

-two functions find_kernel_BMSS and find_kernel_LS, the first one is about 10 times quicker than the second but only works if pp>l. (both are quasi linear, one uses half gcd reconstruction whereas the second uses fast reconstruction from powersums).

-in find_isogenous, I modified the bound to switch to p-adics. More over, it seems like my algorithm has no/few p-adic lose, so that e=3 has always worked in my tests whereas Lercier Sirvent exemples needed 10 or more.

-in order to check my implementation I modified find_isogenous_from_Atkin, in order to avoid zero divisions (returning NULL in pathologic cases of Hensel Lemma, or avoiding the calculation of pp1 when using p-adics), but I think the 3 functions need to be reviewed.

NB: in some rare cases in low caracteristic, the algorithm didn't end switching between mt_pathological and mt_atkin.
