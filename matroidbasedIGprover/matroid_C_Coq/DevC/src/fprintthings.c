
// fichier fprinthings.c
// créé par Pascal (PS)
// modification des fonctions initiales de sortie sur le flux stadard
// en ajoutant un flux quelconques
// c'est la reprise de fonctions de David trouvées à droite et à gauche
// qui permettent de faire une sortie sans preuve dans un fichier
// ce fichier peut ensuit être étudié, par exemple lorsqu'on la conclusion
// comporte plusieurs buts
#include<stdio.h>
#include "fprintthings.h"

// ajwp_out
// sortie dans un fichier


void fprintNode(FILE *wp_out, node n) {
	if(n != NULL)
	{
		fprintSet(wp_out, n->e);
	}
}
void fprintLineGraphWithoutProof (FILE *wp_out, graph g, int i) {
	fprintf(wp_out, "Ligne %d | ", i); fprintNode(wp_out, g.tab[i]);
}

void fprintGraphWithoutProof(FILE *wp_out, graph g) {
	int i;
	for(i = 0; i < g.size; i++)
	{
		fprintLineGraphWithoutProof(wp_out, g,i);
	}
}

void fprintSet(FILE *wp_out, myType e) {
	fprintBytesAsRank(wp_out, e);fprintBytes(wp_out, e);fprintBytesAsNumber(wp_out, e);
}

void fprintBytes(FILE *wp_out, myType e) {
	int i;
	myType mask;
	for(i = sizemyType-1; i >= 0; i--)
	{
		mask = 1ull << i;
		if(e & mask)
		{
			fprintf(wp_out,"%d",1);
		}
		else
		{
			fprintf(wp_out,"%d",0);
		}
	}
}

void fprintBytesAsNumber(FILE *wp_out, myType e) {
	int i,j;
	int first = 1;
	j = realSizemyType;
	fprintf(wp_out,"  "); // blank for printSet
	fprintf(wp_out,"{");
	for(i = realSizemyType-1; i >= 0; i--)
	{
		if(first)
		{
			if(((e >> i) & 0x1) == 1)
			{
				fprintf(wp_out,"%d",j);
				first = 0;
			}
		}
		else
		{
			if(((e >> i) & 0x1) == 1)
			{
				fprintf(wp_out,",%d",j);
			}
		}
		j--;
	}
	fprintf(wp_out,"}");
	fprintf(wp_out,"\n");
}

void fprintBytesAsRank(FILE *wp_out, myType e) {
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
				fprintf(wp_out,"Rank max : 8, ");
			}
			else
			{
				fprintf(wp_out,"Rank max : 7, ");
			}
		}
		else
		{
			if(m == 1)
			{
				fprintf(wp_out,"Rank max : 6, ");
			}
			else
			{
				fprintf(wp_out,"Rank max : 5, ");
			}
		}
	}
	else
	{
		if(l == 1)
		{
			if(m == 1)
			{
				fprintf(wp_out,"Rank max : 4, ");
			}
			else
			{
				fprintf(wp_out,"Rank max : 3, ");
			}
		}
		else
		{
			if(m == 1)
			{
				fprintf(wp_out,"Rank max : 2, ");
			}
			else
			{
				fprintf(wp_out,"Rank max : 1, ");
			}
		}
	}
	
	if(o == 1)
	{
		if(p == 1)
		{
			if(q == 1)
			{
				fprintf(wp_out,"Rank min : 8, ");
			}
			else
			{
				fprintf(wp_out,"Rank min : 7, ");
			}
		}
		else
		{
			if(q == 1)
			{
				fprintf(wp_out,"Rank min : 6, ");
			}
			else
			{
				fprintf(wp_out,"Rank min : 5, ");
			}
		}
	}
	else
	{
		if(p == 1)
		{
			if(q == 1)
			{
				fprintf(wp_out,"Rank min : 4, ");
			}
			else
			{
				fprintf(wp_out,"Rank min : 3, ");
			}
		}
		else
		{
			if(q == 1)
			{
				fprintf(wp_out,"Rank min : 2, ");
			}
			else
			{
				fprintf(wp_out,"Rank min : 1, ");
			}
		}
	}
}