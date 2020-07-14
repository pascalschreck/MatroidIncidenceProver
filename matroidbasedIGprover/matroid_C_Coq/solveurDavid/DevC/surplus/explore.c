
#include "statement.h"
#include "set.h"
#include "parties.h"
#include "fprintthings.h"
#include <string.h>


void clean_input(char *buffer, unsigned size)
{ for(int i=0; i<size; i++)
    if(buffer[i]==10 || buffer[i]==13) buffer[i]='\0';
}

int main(int argc, char * argv[])
{


// lecture d'un énoncé
	char filestate[64], fileout[64], buff[256];
    unsigned long long set = 0ull;
    if(argc != 3) {printf("Usage %s + énoncé + sortie à explorer\n",argv[0]); exit(1);}
    strcpy(filestate,argv[1]);
    strcpy(fileout,argv[2]);
    FILE *stat = fopen(filestate,"r");
    statement st = st_read(stat);
	// On ne considère que des énoncés avec une seule couche ...
    
	 
	FILE *wp_out = fopen(fileout,"r");
   printf("entrez la liste des points terminée par ';' (ou 'halt')\n");
   fscanf(stdin," %s ",buff);
   while(strcmp(buff,"halt")){
        set = 0ull;
        while(strcmp(buff,";"))
        {
            int ref = find_ref(buff,st);
            if(ref==-1){printf("erreur : %s point non reconnu", buff); exit(2);}
            set = set | 1ull << ref;
            printf("point lu %s, set : %llu\n",buff,set);
            fscanf(stdin,"%s",buff);
        }

       if(strcmp(buff,";")) {printf("syntax error : ':' expected\n"), exit(1);}
        rewind(wp_out); // on revient à 0 parce qu'on est pas sûr que tous les suppléments sont
		                    // rangés dans un ordre croissant
        // 
		for(unsigned long j=0ul; j < set; j++) fgets(buff, 255, wp_out);
			printf(" ligne %llu : %s\n", set, buff);	
        fflush(stdin);
        printf("entrez la liste des points terminée par ';' (ou 'halt')\n");
        fscanf(stdin,"%s",buff);
   }
printf("bye\n");

}

/*
int main(int argc, char * argv[]) {
	
	allocSize sizeTab;
	graph g1,g2,g3;
	int res = 8247;
	
	int nbp;

	FILE* file = NULL;
	file = fopen(filename,"w");
	
	fprintf(stderr,"-------------- initialisation\n\n");
	
	//~ sizeTab = allocSizeTab(1,2);
	//~ nbp = 15;
	//~ g1 = allocGraph(nbp);
	
	sizeTab = allocSizeTab(3,2);
	nbp = 9;
	g1 = allocGraph(nbp);
	nbp = 16;
	g2 = allocGraph(nbp);
	nbp = 19;
	g3 = allocGraph(nbp);
	

	//~ fprintf(stderr,"-------------- convergence\n\n");
	
	//~ g1 = example_nico(g1);
	//~ sizeTab.tab[0][0] = g1.effectiveAllocPow;
	//~ sizeTab.tab[0][1] = g1.effectiveSize;
	//~ g1 = convergenceParties(g1,res);
	//~ 
	//~ printGraphWithoutProof(g1);
	
	fprintf(stderr,"-------- convergence 1\n");
	g1 = dg_part1(g1);
	sizeTab.tab[0][0] = g1.effectiveAllocPow;
	sizeTab.tab[0][1] = g1.effectiveSize;
	g1 = convergenceParties(g1,res);
	
	copyGraph(g1,g2,res);
	fprintf(stderr,"-------- convergence 2\n");
	
	g2 = dg_part2(g2);
	sizeTab.tab[1][0] = g2.effectiveAllocPow;
	sizeTab.tab[1][1] = g2.effectiveSize;
	g2 = convergenceParties(g2,res);

	copyGraph(g2,g3,res);
	fprintf(stderr,"-------- convergence 3\n");

	g3 = dg_part3(g3);
	sizeTab.tab[2][0] = g3.effectiveAllocPow;
	sizeTab.tab[2][1] = g3.effectiveSize;
	g3 = convergenceParties(g3,res);

	printGraphWithoutProof(g3);
	
	fprintf(stderr,"--------------- reconstruction\n\n");
	
	int i;
	
	preMark(g3.tab[res]);

	for(i = 0; i < g2.effectiveSize; i++)
	{
		if(g3.tab[i]->mark == 1 && i != res)
		{
			preMark(g2.tab[i]);
		}
	}
	
	for(i = 0; i < g1.effectiveSize; i++)
	{
		if(g2.tab[i]->mark == 1 && i != res)
		{
			preMark(g1.tab[i]);
			constructLemma(file, g1, g1.tab[i]);
			constructIntro(file, g1);
			constructProof(file,g1.tab[i], sizeTab, 1);
			g1.tab[i]->mark = 4;
			unMark(g1.tab[i]);
		}
	}
	
	for(i = g1.effectiveSize; i < g2.effectiveSize; i++)
	{
		if(g3.tab[i]->mark == 1 && i != res)
		{
			preMark(g2.tab[i]);
			constructLemma(file, g2, g2.tab[i]);
			constructIntro(file, g2);
			constructProof(file,g2.tab[i], sizeTab, 1);
			g2.tab[i]->mark = 4;
			unMark(g2.tab[i]);
		}
	}
	
	constructLemma(file, g3, g3.tab[res]);
	constructIntro(file, g3);
	constructProof(file, g3.tab[res], sizeTab, 1);

	//~ preMark(g1.tab[res]);
	//~ constructLemma(file, g1, g1.tab[res]);
	//~ constructIntro(file, g1);
	//~ constructProof(file, g1.tab[res], sizeTab, 1);
	
	fclose(file);
	
	return 0;
}

*/
