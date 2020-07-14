// fichier main.c
#include "statement.h"
#include "set.h"
#include "parties.h"
#include "fprintthings.h"
#include "globals.h"		// on définit ici des constantes et des variables globales
#include <string.h>

void read_comd_line(int argc, char *argv[]);
// variables globales
 char        statement_name[255],
             rankoutput_name[255],
             coqoutput_name[255],
             newrules_name[255];


int main(int argc, char * argv[])
{
	// on commence par lire la ligne de commande et par attribuer les
	// différents noms des fichiers d'entrée et de sortie.
	read_comd_line(argc, argv);
	
	// les deux déclarations suivantes seront à régler lorsqu'on fera
	// du multicouche : il faudra un graphe par couche
	// et sizetab sera défini par
	// sizeTab = allocSizeTab(n,2); *** n = nbre de couches
	// g[i] = allocGraph(nbp[i]);  *** nbp[i] = nbre de points pour la couche i  
	allocSize sizeTab;
	graph g;

// lecture d'un énoncé dans un fichier qui est soit le nom par défaut (dft_statement.txt)
// soit le nom donné sur la ligne de commande rangé dans la variable statement_name
    FILE *stat = fopen(statement_name,"r");
    statement st = st_read(stat);			// lecture de l'énoncé pour remplir la structure statement
											// Dans un premier temps, 
											// on ne considère que des énoncés avec une seule couche ...
    fclose(stat);
											// mise à jour de deux variables globales
	dim = st->sdim; 						// !!!! variable globale
	realSizemyType = (dim >= 4) ? 58 : 60; 	// !!!!! variable globale
	// affichage pour vérification
	st_print(st);

   
	int nbp = st-> nbp;						// nombre de points (lu dans l'énoncé)
	int res = st->conclusion.set;			// conclusion lue dans l'énoncé

	// on ouvre ensuite le fichier de sortie pour la preuve coq
	// c'est soit le fichier standard, soit celui lu à la ligne de commande
	FILE* file = fopen(coqoutput_name,"w");				
											
	
	fprintf(stderr,"-------------- initialisation\n\n");

	sizeTab = allocSizeTab(1,2); // 1 : il n'y a qu'une couche et 2 : c'est toujours 2 (tableau à 2 colonnes)
	g = allocGraph(nbp); 

    g.effectiveAllocPow = nbp;    
    g.effectiveSize = (1u<<nbp)-1;  

  	for(int i=0; i<st->nbr; i++)
  	{
		rang r = st->hypoth[i];
		int set = r.set;
		g.tab[set]-> e = setMinMax(g.tab[set]->e,r.rk,r.rk);
		g.tab[set]->color = -1;
  	}
  
    // printGraphWithoutProof(g);
    // éventuellement : free(st);
	fprintf(stderr,"-------- convergence 1\n");

	sizeTab.tab[0][0] = g.effectiveAllocPow;
	sizeTab.tab[0][1] = g.effectiveSize;
	g = convergenceParties(g,res);
	 
	// fin de la preuve, sortie des rangs dans un fichier dont le nom est prédéfini
	// on peut changer ça avec des options sur la ligne de commande
	FILE *wp_out = fopen(rankoutput_name,"w+");
	fprintGraphWithoutProof(wp_out, g);				// écriture dans le fichier 
	
	// exploration simple du fichier : on cherche le rang corrspondant à la conclusion et
	// les rangs des lignes supplémentaires
	rewind(wp_out);
	long long unsigned nw_line = st->conclusion.set;
	int srk = st->conclusion.rk;
	char buf[255];
	for(int j=0; j <= nw_line; j++) fgets(buf, 255, wp_out);
	printf("conclusion (ligne %lld), rang attendu %d\n  %s\n", nw_line, srk, buf);

	for(int i=0;i< st->nbs; i++) // nbs : nombre de lignes supplémentaires
		{	rewind(wp_out); 	// on revient à 0 parce qu'on est pas sûr que tous les suppléments sont
		                    	// rangés dans un ordre croissant
			nw_line = st->supp[i].set;
			srk = st->supp[i].rk;
			for(int j=0; j <= nw_line; j++) fgets(buf, 255, wp_out);
			printf("supplément (ligne %lld) rang attendu %d\n  %s\n", nw_line, srk, buf);	
		}
  fclose(wp_out);
}


// lecture et analyse de la ligne de commande
// pour donner ouvrir les bons fichiers d'entrée et de sortie
void read_comd_line(int argc, char *argv[])
{
	strcpy(statement_name,dft_statement_name);		// nom par défaut
    strcpy(rankoutput_name,dft_rankoutput_name);	// nom par défaut
    strcpy(coqoutput_name,dft_coqoutput_name);		// nom par défaut
    strcpy(newrules_name,dft_newrules_name);		// nom par défaut

    unsigned opt_flag = 0;

    if (argc == 1) { printf("Erreur il faut au moins un argument\n"); exit(1);}
    if (argc == 2 && strcmp(argv[1],"-h")) 
        { 
            printf("L'unique argument (%s) est pris ecomme un énoncé\n", argv[1]);
        } // mais on contrôle rien de plus
    else
    {
        int i = 1;
        while(i<argc)
        {
            if(!strcmp(argv[i],"-h")) 
                { 
                    printf("Affichage du message d'aide :\n");
					printf("   -s <statement> pour spécifier le fichier contenant l'énoncé\n");
					printf("   -ro <rankfile> pour spécifier le fichier de sortie pour la liste des rangs\n");
					printf("   -co <coqproof> pour spécifier le fichier de sortie pour la preuve Coq\n");
					printf("   -n <newrules> pour spécifier le fichier contenant de nouvelles règles\n");
                    exit(0);
                }
            else if (!strcmp(argv[i],"-s"))
                {
                    if(opt_flag & stat_flag) { printf("l'option -s a déjà été lue\n"); exit(2);}
                    opt_flag |= stat_flag;
                    i++;    // on attends alors le nom d'un fichier
                            // mais on ne fait pas d'ouverture ni de test pour le moment
                    printf("Enoncé contenu dans le fichier : %s\n",argv[i]); 
                    strcpy(statement_name,argv[i]);
                }
            else if (!strcmp(argv[i],"-ro"))
                {
                    if(opt_flag & rank_flag) { printf("l'option -ro a déjà été lue\n"); exit(2);}
                    opt_flag |= rank_flag;
                    i++;    // on attends alors le nom d'un fichier
                            // mais on ne fait pas d'ouverture ni de test pour le moment
                    printf("output : la liste des rang sera contenue dans le fichier : %s\n",argv[i]); 
                    strcpy(rankoutput_name,argv[i]);
                }
            else if (!strcmp(argv[i],"-co"))
                {
                    if(opt_flag & coq_flag) { printf("l'option -co a déjà été lue\n"); exit(2);}
                    opt_flag |= coq_flag;
                    i++;    // on attends alors le nom d'un fichier
                            // mais on ne fait pas d'ouverture ni de test pour le moment
                    printf("output : la preuve coq sera contenue dans le fichier : %s\n",argv[i]); 
                    strcpy(coqoutput_name,argv[i]);
                }
            else if (!strcmp(argv[i],"-n"))
                {
                    if(opt_flag & rule_flag) { printf("l'option -n a déjà été lue\n"); exit(2);}
                    opt_flag |= rule_flag;
                    i++;    // on attends alors le nom d'un fichier
                            // mais on ne fait pas d'ouverture ni de test pour le moment
                    printf("De nouvelles règles contenues dans le fichier : %s seront utilisées\n",argv[i]); 
                    strcpy(newrules_name,argv[i]);
                }
            else { printf("Option non reconnue %s -- arrêt\n", argv[i]); exit(3);}
            // incrémentation automatique de l'indice des arguments
            i++;
        }
    }

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
