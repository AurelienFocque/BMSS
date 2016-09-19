
#include "pari/pari.h"
#include "pari/paripriv.h"
#include <time.h>

static clock_t temps_total;
static clock_t temps_kernel;
static clock_t temps_equadiff;
static clock_t temps_euclide;
static clock_t temps_comp;
GEN Fq_ui(int k,GEN T,GEN p)
{
  if(T==NULL)
    return mkintn(1,k);
  else 
    return mkpoln(1,mkintn(1,k));
}

int main()
{	
  pari_init(10000000000,2);

  temps_kernel=clock();
  temps_equadiff=clock();
  temps_euclide=clock();
  temps_comp=clock();
  temps_total=clock();
  GEN T=RgX_shift(mkpoln(1,gen_1),53);
  T=RgX_add(T,mkpoln(2,gneg(mkintn(1,1)),gneg(mkintn(1,1))));
  GEN p=mkintn(1,53);	
  GEN a4=Fq_ui(10,T,p);
  GEN a6=Fq_ui(4,T,p);
  clock_t tmp=clock();
  pari_printf("%Ps\n",Fq_ellcard_SEA(a4,a6,gpowgs(p,53),T,p,0));
  temps_total=clock()-tmp;
  printf("temps kernel :%f\ntemps equadiff :%f\n",(double)temps_kernel/CLOCKS_PER_SEC,(double)temps_equadiff/CLOCKS_PER_SEC);
  printf("temps euclide :%f\ntemps comp :%f\n",(double)temps_euclide/CLOCKS_PER_SEC,(double)temps_comp/CLOCKS_PER_SEC);
  printf("temps total:%f\n",(double)temps_total/CLOCKS_PER_SEC);
  return 0;
  }
