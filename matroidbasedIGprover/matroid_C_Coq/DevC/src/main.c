// fichier main.c
// créé par David
// modifié par PS pour prendre en compte l'utilisation d'énoncés codés
// dans un fichier plutôt que codés en dur dans ce fichier
#include "statement.h"          // ajouté par PS
#include "set.h"
#include "parties.h"
#include "fprintthings.h"       // ajouté par PS
#include "globals.h"		    // ajouté par PS constantes et des variables globales
#include <string.h>

// fonctions locales
void read_comd_line(int argc, char *argv[]);
        // lecture et analyse de la ligne de commande
        // pour donner ouvrir les bons fichiers d'entrée et de sortie

// variables globales : ce sont les noms de fichier d'E/S utilisés
 char        statement_name[255],
             rankoutput_name[255],
             coqoutput_name[255],
             newrules_name[255];


//----------------------------------------------------
//  main
//----------------------------------------------------
int main(int argc, char * argv[])
{
	// on commence par lire la ligne de commande et par attribuer les
	// différents noms des fichiers d'entrée et de sortie.
	read_comd_line(argc, argv);
    // lecture d'un énoncé dans un fichier qui est soit le nom par défaut (dft_statement.txt)
    // soit le nom donné sur la ligne de commande rangé dans la variable statement_name
    FILE *stat = fopen(statement_name,"r");
    statement st = st_read(stat);			// lecture de l'énoncé pour remplir la structure statement
    fclose(stat);
											// mise à jour de deux variables globales
	dim = st->sdim; 						// !!!! variable globale
	realSizemyType = (dim >= 4) ? 58 : 60; 	// !!!!! variable globale
	// affichage de l'énoncé pour vérification
	st_print(st);

    int nb_layers = st->nb_layers;          // en principe < MAX_LAYERS

    int nbp=0;          // nombre de points pour la couche courante
    int res;            // conclusion pour la couche courante
	allocSize sizeTab = allocSizeTab(nb_layers,2);
	graph g[MAX_LAYERS];
    layer cly;      // couche courante
    int iocl=0;
    /*-------------------------------------------------*/
    // traitement en avant de la couche 0
    /*-------------------------------------------------*/
        cly = st->layers[iocl];
        fprintf(stderr,"-------------- initialisation couche %d (%s)\n\n",iocl,cly->name);
        nbp = cly->nbp;
        res = cly->conclusion.set;
        g[iocl] = allocGraph(nbp);
        g[iocl].effectiveAllocPow = nbp;    
        g[iocl].effectiveSize = (1u<<nbp)-1;  
        for(int i=0; i<cly->nbr; i++)
  	    {
		    rang r = cly->hypoth[i];
		    int set = r.set;
		    g[iocl].tab[set]-> e = setMinMax(g[iocl].tab[set]->e,r.rk,r.rk);
		    g[iocl].tab[set]->color = -1;
  	    }
    fprintf(stderr,"-------- convergence couche 0 \n");
	sizeTab.tab[iocl][0] = g[iocl].effectiveAllocPow;
	sizeTab.tab[iocl][1] = g[iocl].effectiveSize;
	g[iocl] = convergenceParties(g[iocl],res);  // Saturation
    /*-------------------------------------------------*/
    //    traitement des autres couches
    /*-------------------------------------------------*/
    for(iocl=1; iocl < nb_layers; iocl++)
    {
        cly = st->layers[iocl];
        fprintf(stderr,"-------------- initialisation couche %d (%s)\n\n",iocl,cly->name);
        nbp = cly->nbp;
        res = cly->conclusion.set;
        g[iocl] = allocGraph(nbp);
        g[iocl].effectiveAllocPow = nbp;    
        g[iocl].effectiveSize = (1u<<nbp)-1;  

        copyGraph(g[iocl-1],g[iocl],res);

       for(int i=0; i<cly->nbr; i++)
  	    {
		    rang r = cly->hypoth[i];
		    int set = r.set;
		    g[iocl].tab[set]-> e = setMinMax(g[iocl].tab[set]->e,r.rk,r.rk);
		    g[iocl].tab[set]->color = -1;
  	    }
        fprintf(stderr,"-------- convergence couche %d \n", iocl);
	    sizeTab.tab[iocl][0] = g[iocl].effectiveAllocPow;
	    sizeTab.tab[iocl][1] = g[iocl].effectiveSize;
	    g[iocl] = convergenceParties(g[iocl],res); // Saturation

    }
			

	 
	// fin de la preuve, sortie des rangs dans un fichier dont le nom est donné sur la lc
	FILE *wp_out = fopen(rankoutput_name,"w+");
	fprintGraphWithoutProof(wp_out, g[nb_layers-1]);				// écriture dans le fichier 


	// exploration simple du fichier : on cherche le rang correspondant à la conclusion et
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



  	// on ouvre ensuite le fichier de sortie pour la preuve coq
	// c'est soit le fichier standard, soit celui lu à la ligne de commande
	FILE* file = fopen(coqoutput_name,"w");	

    fprintf(stderr,"--------------- reconstruction\n\n");
	
    /*________________________________________________________
        TODO : la suite est à vérifier
    ----------------------------------------------------------*/
	int i, last = nb_layers-1;
	
	preMark(g[last].tab[res]);  // marque tous les prédecesseurs de res dans 
                                // le dernier graphe (qui contient tout les points) 

    // rétro-propagation du prémarquage dans les graphes correspondant à chacune de couches
    for(iocl=last-1; iocl >= 0; iocl--)
    {
        for(i=0; i < g[iocl].effectiveSize;i++)
            if(g[iocl+1].tab[i]->mark == 1 && i != res) preMark(g[iocl].tab[i]);
    }
    
    // construcion en avant de la preuve
    iocl = 0;
    i=0;

    for(; iocl < last; iocl++)  // la dernière couche est exclue
    {
        for(; i < g[iocl].effectiveSize;i++)
        {   
        // ajout dans la condition suivante (à la fin) :
        // test sur la cardinalité du noeud à montrer : l'ens. doit avoir plus d'UN élément
            if(g[iocl+1].tab[i]->mark == 1 && i != res && cardinal(g[iocl].tab[i]->e)!=1)
            {
                if(constructLemma(file,g[iocl],g[iocl].tab[i],iocl)) // retourne faux si le lemme n'est pas écrit
                {
                    constructIntro(file, g[iocl]);
			        constructProof(file,g[iocl].tab[i], sizeTab, 1);
			        g[iocl].tab[i]->mark = 4;
			        unMark(g[iocl].tab[i]);
                }
            }
            
        }
    }

    // traitement de la dernière couche :
    if(constructLemma(file, g[last], g[last].tab[res],last))
    {
	    constructIntro(file, g[last]);
	    constructProof(file, g[last].tab[res], sizeTab, 1);
    }

	
	fclose(file);
	
	return 0;
}
// fin de la fonction main





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
            printf("L'unique argument (%s) est pris comme un énoncé\n", argv[1]);
            opt_flag = stat_flag;
            strcpy(statement_name,argv[1]);
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
if(!(opt_flag & coq_flag))
    {
        strcpy(coqoutput_name,statement_name); strcat(coqoutput_name,".v");
    }
if(!(opt_flag & rank_flag))
    {
        strcpy(rankoutput_name,statement_name); strcat(rankoutput_name,".out");
    }
}





