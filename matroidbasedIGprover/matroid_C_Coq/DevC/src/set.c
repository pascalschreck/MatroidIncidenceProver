#include "set.h"

// Variables globales 
// attention surtout avec dim
// (avant, c'était un define (pas terrible non plus))
unsigned dim = 2; // default  
const unsigned sizemyType = 64;
unsigned realSizemyType = 60; // default


myType setIByte(myType e, int i) {
	myType mask = 1ull << (i-1);
	myType result = e | mask;
	return result;
}

myType unsetIByte(myType e, int i) {
	myType mask = ~(1ull << (i-1));
	myType result = e & mask;
	return result;
}

int getBytes(myType e, int i) {
	int result = e >> (i-1) & 0x1;
	return result;
}

myType getIBytes(myType e, int i) {
	myType mask,res;
	int j = 0;
	while(i != 0 && j <= sizemyType -1)
	{
		mask = 1ull << j;
		res = e & mask;
		if(res)
		{
			i--;
		}
		j++;
	}
	return res;
}

int countBytes(myType e) {
	return __builtin_popcount(e);
}

myType initSet() {
	myType e;
	e = 0x0;
	return e;
}

myType DecToBin(int i) { // c'est assez compliqué pour coder l'identité !
	/*
	int j;
	int cpt=1;
	myType res = 0x0;
	
	while(i > 0)
	{
		j = i%2;
		
		if(j == 1)
		{
			res = setIByte(res,cpt);
		}
		i=i/2;
		cpt++;
	}
	
	
	return res;
	*/
	return i;
}

myType initRanks(myType e) {
	
	int bits = countBytes(e);
	if(dim == 7)
	{
		if(bits >= 8)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-1);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 7)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 6)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 5)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 4)
		{
			e = setIByte(e,sizemyType-1);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 3)
		{
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-2);
		}
	}
	else if(dim == 6)
	{
		if(bits >= 7)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 6)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 5)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 4)
		{
			e = setIByte(e,sizemyType-1);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 3)
		{
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-2);
		}
	}
	else if(dim == 5)
	{
		if(bits >= 6)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 5)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 4)
		{
			e = setIByte(e,sizemyType-1);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 3)
		{
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-2);
		}
	}
	else if(dim == 4)
	{
		if(bits >= 5)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 4)
		{
			e = setIByte(e,sizemyType-1);
			e = setIByte(e,sizemyType-2);
		}
		else if(bits == 3)
		{
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-2);
		}
	}
	else if(dim == 3)
	{
		if(bits >= 4)
		{
			e = setIByte(e,sizemyType);
			e = setIByte(e,sizemyType-1);
		}
		else if(bits == 3)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-1);
		}
	}
	else if(dim == 2)
	{
		if(bits >= 3)
		{
			e = setIByte(e,sizemyType);
		}
		else if(bits == 2)
		{
			e = setIByte(e,sizemyType-1);
		}
	}
	else if(dim == 1)
	{
		if(bits >= 2)
		{
			e = setIByte(e,sizemyType-1);
		}
	}
	else
	{
		fprintf(stderr,"Erreur sur la dimension sélectionné ?? \n");
		exit(1);
	}
		
	return e;
}

int rankMax(myType e) {
	int i;
	int k,l,m;
	
	i = sizemyType-1;
	
	if(dim >= 4)
	{
		k = (e >> i & 0x1) == 1;
		l = (e >> (i-1) & 0x1) == 1;
		m = (e >> (i-2) & 0x1) == 1;
	}
	else
	{
		k = 0;
		l = (e >> i & 0x1) == 1;
		m = (e >> (i-1) & 0x1) == 1;
	}
	
	if(k == 1)
	{
		if(l == 1)
		{
			if(m == 1)
			{
				return 8;
			}
			else
			{
				return 7;
			}
		}
		else
		{
			if(m == 1)
			{
				return 6;
			}
			else
			{
				return 5;
			}
		}
	}
	else
	{
		if(l == 1)
		{
			if(m == 1)
			{
				return 4;
			}
			else
			{
				return 3;
			}
		}
		else
		{
			if(m == 1)
			{
				return 2;
			}
			else
			{
				return 1;
			}
		}
	}
}

myType setMax(myType e, int i) {
	
	if(i > (dim +1))
	{
		fprintf(stderr,"Erreur dans les dimensions des hypothèses\n");
		exit(1);
	}
	else if(dim >= 4)
	{
		if(i == 8)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0xE000000000000000;
		}
		else if(i == 7)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0xC000000000000000;
		}
		else if(i == 6)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0xA000000000000000;
		}
		else if(i == 5)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0x8000000000000000;
		}
		else if(i == 4)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0x6000000000000000;
		}
		else if(i == 3)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0x4000000000000000;
		}
		else if(i == 2)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF) | 0x2000000000000000;
		}
		else if(i == 1)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF);
		}
	}
	else
	{
		if(i == 4)
		{
			e = (e & 0x3FFFFFFFFFFFFFFF) | 0xC000000000000000;
		}
		else if(i == 3)
		{
			e = (e & 0x3FFFFFFFFFFFFFFF) | 0x8000000000000000;
		}
		else if(i == 2)
		{
			e = (e & 0x3FFFFFFFFFFFFFFF) | 0x4000000000000000;
		}
		else if(i == 1)
		{
			e = (e & 0x1FFFFFFFFFFFFFFF);
		}
	}
	
	return e;	
}

int rankMin(myType e) {
	int i;
	int o,p,q;
	
	if(dim >= 4)
	{
		i = sizemyType-4;
		o = (e >> i & 0x1) == 1;
		p = (e >> (i-1) & 0x1) == 1;
		q = (e >> (i-2) & 0x1) == 1;
	}
	else
	{
		i = sizemyType-3;
		o = 0;
		p = (e >> i & 0x1) == 1;
		q = (e >> (i-1) & 0x1) == 1;
	}

	if(o == 1)
	{
		if(p == 1)
		{
			if(q == 1)
			{
				return 8;
			}
			else
			{
				return 7;
			}
		}
		else
		{
			if(q == 1)
			{
				return 6;
			}
			else
			{
				return 5;
			}
		}
	}
	else
	{
		if(p == 1)
		{
			if(q == 1)
			{
				return 4;
			}
			else
			{
				return 3;
			}
		}
		else
		{
			if(q == 1)
			{
				return 2;
			}
			else
			{
				return 1;
			}
		}
	}
}

myType setMin(myType e, int i) {
	
	if(i > (dim + 1))
	{
		fprintf(stderr,"Erreur dans les dimensions des hypothèses\n");
		exit(1);
	}
	else if(dim >=4)
	{
		if(i == 8)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x1C00000000000000;
		}
		else if(i == 7)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x1800000000000000;
		}
		else if(i == 6)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x1400000000000000;
		}
		else if(i == 5)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x1000000000000000;
		}
		else if(i == 4)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0xC00000000000000;
		}
		else if(i == 3)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x800000000000000;
		}
		else if(i == 2)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF) | 0x400000000000000;
		}
		else if(i == 1)
		{
			e = (e & 0xE3FFFFFFFFFFFFFF);
		}
	}
	else
	{
		if(i == 4)
		{
			e = (e & 0xCFFFFFFFFFFFFFFF) | 0x3000000000000000;
		}
		else if(i == 3)
		{
			e = (e & 0xCFFFFFFFFFFFFFFF) | 0x2000000000000000;
		}
		else if(i == 2)
		{
			e = (e & 0xCFFFFFFFFFFFFFFF) | 0x1000000000000000;
		}
		else if(i == 1)
		{
			e = (e & 0xCFFFFFFFFFFFFFFF);
		}
	}
	
	return e;	
}

myType setMinMax(myType e, int i, int j) {
	
	if(j < i)
	{
		fprintf(stderr,"Erreur dans les dimensions des hypothèses\n");
		exit(1);
	}
	e = setMin(e,i);
	e = setMax(e,j);
	return e;
}

int rankMinMaxEqual(myType e, int value) {
	int min = rankMin(e);
	int max = rankMax(e);
	
	if(min == value && max == value)
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

int incl(myType e1, myType e2) {
	if(((e1 & 0x03FFFFFFFFFFFFFF) & (e2 & 0x03FFFFFFFFFFFFFF)) == (e1 & 0x03FFFFFFFFFFFFFF))
	{
		return 1;
	}
	else
	{
		return 0;
	}
}

void printSet(myType e) {
	printBytesAsRank(e);printBytes(e);printBytesAsNumber(e);
}

void printBytes(myType e) {
	int i;
	myType mask;
	for(i = sizemyType-1; i >= 0; i--)
	{
		mask = 1ull << i;
		if(e & mask)
		{
			printf("%d",1);
		}
		else
		{
			printf("%d",0);
		}
	}
}

void printBytesAsNumber(myType e) {
	int i,j;
	int first = 1;
	j = realSizemyType;
	printf("  "); // blank for printSet
	printf("{");
	for(i = realSizemyType-1; i >= 0; i--)
	{
		if(first)
		{
			if(((e >> i) & 0x1) == 1)
			{
				printf("%d",j);
				first = 0;
			}
		}
		else
		{
			if(((e >> i) & 0x1) == 1)
			{
				printf(",%d",j);
			}
		}
		j--;
	}
	printf("}");
	printf("\n");
}

void printBytesAsRank(myType e) {
	int i;
	int k,l,m,o,p,q;
	
	i = sizemyType-1;
	if(dim >= 4)
	{
		k = (e >> i & 0x1) == 1;
		l = (e >> (i-1) & 0x1) == 1;
		m = (e >> (i-2) & 0x1) == 1;
	}
	else
	{
		k = 0;
		l = (e >> i & 0x1) == 1;
		m = (e >> (i-1) & 0x1) == 1;
	}
	
	if(dim >= 4)
	{
		i = sizemyType-4;
		o = (e >> i & 0x1) == 1;
		p = (e >> (i-1) & 0x1) == 1;
		q = (e >> (i-2) & 0x1) == 1;
	}
	else
	{
		i = sizemyType-3;
		o = 0;
		p = (e >> i & 0x1) == 1;
		q = (e >> (i-1) & 0x1) == 1;
	}
	
	if(k == 1)
	{
		if(l == 1)
		{
			if(m == 1)
			{
				printf("Rank max : 8, ");
			}
			else
			{
				printf("Rank max : 7, ");
			}
		}
		else
		{
			if(m == 1)
			{
				printf("Rank max : 6, ");
			}
			else
			{
				printf("Rank max : 5, ");
			}
		}
	}
	else
	{
		if(l == 1)
		{
			if(m == 1)
			{
				printf("Rank max : 4, ");
			}
			else
			{
				printf("Rank max : 3, ");
			}
		}
		else
		{
			if(m == 1)
			{
				printf("Rank max : 2, ");
			}
			else
			{
				printf("Rank max : 1, ");
			}
		}
	}
	
	if(o == 1)
	{
		if(p == 1)
		{
			if(q == 1)
			{
				printf("Rank min : 8, ");
			}
			else
			{
				printf("Rank min : 7, ");
			}
		}
		else
		{
			if(q == 1)
			{
				printf("Rank min : 6, ");
			}
			else
			{
				printf("Rank min : 5, ");
			}
		}
	}
	else
	{
		if(p == 1)
		{
			if(q == 1)
			{
				printf("Rank min : 4, ");
			}
			else
			{
				printf("Rank min : 3, ");
			}
		}
		else
		{
			if(q == 1)
			{
				printf("Rank min : 2, ");
			}
			else
			{
				printf("Rank min : 1, ");
			}
		}
	}
}
	
/*--------------------------------------------------------*
*   cardinal d'un ensemble ... attention, j'ai limité à 28
*---------------------------------------------------------*/
int cardinal(myType e)
{
	int nb_points = 0;
	int point = 0;
	for(; point < 28; point++)
		nb_points += e>>point & 1;
	
	return nb_points;

}
	
