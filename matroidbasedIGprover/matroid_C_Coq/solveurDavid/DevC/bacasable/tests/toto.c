#include<stdio.h>
#include<math.h>
#define myType unsigned long long

unsigned long long setIByte(myType e, int i) {
	myType mask = 1ull << (i-1);
	myType result = e | mask;
	return result;
}
unsigned long long DecToBin(int i) { // c'est assez compliqué pour coder l'identité !
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
}
int main()
{
     // printf("%g et %ld\n", (double)(2u<<10) - pow(2,10), (2u<<10) - (long)pow(2,10));
     int i = 347;
     unsigned long long j = DecToBin(i);
     printf("%d %llu %llu\n", i, (unsigned long long)i, j);
}