
#include "pari/pari.h"
#include "pari/paripriv.h"


static 
GEN Fq_ui(int k,GEN T,GEN p)
{
  if(T==NULL)
    return mkintn(1,k);
  else 
    return mkpoln(1,mkintn(1,k));
}
// Calculate the number of points of the elliptic curve defined by y^2=x^3+10x+4 over GF(53^53) using SEA.
// to get the kernel polynomial it uses successively BMSS and Lercier Sirvent algorithms.
int main()
{	
	pari_init(10000000000,2);
 	GEN T=RgX_shift(mkpoln(1,gen_1),53);
	T=RgX_add(T,mkpoln(2,gneg(mkintn(1,1)),gneg(mkintn(1,1))));
	GEN p=mkintn(1,53);	
	GEN a4=Fq_ui(10,T,p);
	GEN a6=Fq_ui(4,T,p);
	pari_printf("%Ps\n",Fq_ellcard_SEA(a4,a6,gpowgs(p,53),T,p,0));
	return 0;
}
