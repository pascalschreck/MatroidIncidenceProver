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
// et plus généralement des variables relatives à la lecture de la ligne de commande
 char        statement_name[255],   // contient le nom du fichier où est écrit l'énoncé
             rankoutput_name[255],  // contient le nom du fichier où se fait l'affichage des rangs après saturation
             coqoutput_name[255],   // contient le nom du fichier où est écriture de la peuve Coq
             newrules_name[255],    // pour utiliser un fichier avec de nouvelles règles (pas d'actualité en oct 2020)
             traced_set_name[255];  // nom de l'ensemble tracé (par exemple "O A B" (il faut les double-quotes)) avec l'option trace
 
 FILE *debug_file = NULL;           // structure FILE partagée par tous les fichiers - déclaration extern dans globals.h
 bool debug_mode = false;           // booléen partagé pas tout les fichiers - déclaration extern dans global.h
 bool trace = false;                // idem pour le mode trace (a priori, il faut que le mode debug soit activé)
 myType traced = 0llu;              // ensemble tracé

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
        if(stat==NULL){ printf("le fichier %s n'existe pas\n", statement_name); exit(2);}
    // ouvrir le fichier de déboggage
    if(debug_mode)
        debug_file = fopen("debug.log","w");

    statement st = st_read(stat);			// lecture de l'énoncé pour remplir la structure statement
    fclose(stat);
        /*----------------------traçage-----------------------------*/
            if(trace)
            {
                char buff[32];  // on limite le nom d'un point à 31 caractères
                char *pos = traced_set_name;
                int nbp;
                pos = strtok(traced_set_name," ,");
                for(nbp = 0; nbp < 30 && pos; nbp++)
                    {
                    int ref;
                    strcpy(buff,pos);
                    ref  = find_ref(buff,st);
                    if(ref==-1){printf("error in tracing set : %s unknown point",buff); exit(2);}
                    traced = traced | (1ull << ref);  // !!!!  mise à jour de la variable globale
                    // printf("test : point courant  %s et ensemble courant %llu\n", buff, traced);
                    pos = strtok(NULL," ,");
                    }
                traced = traced;
                printf(" Traced set : %llu\n", traced);
            }
        //--------------------------------fin de traitement de la trace dans main


    //------------------------------------ mise à jour de deux variables globales
	dim = st->sdim; 						// !!!! variable globale
	realSizemyType = (dim >= 4) ? 58 : 60; 	// !!!!! variable globale
	
    // affichage de l'énoncé pour vérification
	st_print(st);
    // pourrait être commenté

    // initialisation de variables liées à l'énoncé
    int nb_layers = st->nb_layers;              // nombre de couche en principe < MAX_LAYERS
    int nbp=0;                                  // nombre de points pour la couche courante
    unsigned long long res;                     // conclusion pour la couche courante
    unsigned long long resf=st->conclusion.set; // conclusion finale

	allocSize sizeTab = allocSizeTab(nb_layers,2); // tableau de structures pour gérer les couches
	graph g[MAX_LAYERS];                           // tableau de graphe (rangés hiérarchiquement)
    layer cly;                                     // couche courante
    int iocl=0;                                    // numéro de la couche courante
    /////////////////////////////////////////////////////////////////////////////////////////////
    /////////////////// Calcul de la preuve
    ///////////////////////////////////////////////////////////////////////////////////////////
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

        copyGraph(g[iocl-1],g[iocl],resf);

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
    resf = nw_line;
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
	long long unsigned int i ;
    int last = nb_layers-1;
	
    // resf = codage de l'ensemble dans la conclusion finale
            if(debug_mode)
        {
            NL;
            DEB_PS("********************************************");NL;NL;
            TAB; fprintf(debug_file," marquage dans la (dernière) couche %d\n", last);
            NL; DEB_PS("********************************************");NL;NL;
        }
	
    /*--------*/
    //          marquage de la dernière couche
    /*---------*/
    preMark(g[last].tab[resf]);  // marque tous les prédecesseurs de resf dans 
                                // le dernier graphe (qui contient tout les points) 

    /*--------*/
    //          marquage des autres couches
    /*---------*/
    // rétro-propagation du prémarquage d'une couche dans la précédente
    // 
    for(iocl=last-1; iocl >= 0; iocl--)
    {
        if(debug_mode)
        {
            NL;
            DEB_PS("********************************************");NL;NL;
            TAB; fprintf(debug_file," marquage dans la couche %d\n", iocl);
            NL; DEB_PS("********************************************");NL;NL;
        }
        for(i=0; i < g[iocl].effectiveSize;i++)
            if(g[iocl+1].tab[i]->mark == 1 && i != resf) preMark(g[iocl].tab[i]);
    }
    
    // construction en avant de la preuve
    iocl = 0;
    i = 0ull;

    for(; iocl < last; iocl++)  // la dernière couche est exclue
    {
        for(; i < g[iocl].effectiveSize;i++)
        {   
         // TODO : lorsque l'on n'écrit pas un lemme (soit parce que le cardinal de la conculusion est un, 
         // soit parce que la conclusion est dans la hypothèse), il faut peut-être quand même nettoyer le graphe
         // et faire attention que la preuve soit bien correcte
         // pour le moment, il manque des lemmes semble-t-il (étude de Nicolas)
        // ajout dans la condition suivante (à la fin) :
        // test sur la cardinalité du noeud à montrer : l'ens. doit avoir plus d'UN élément
        // TENTION : la suite e été un peu modifiée (avec aussi la fonction constructionLemma) 
        // pour conserver l'ancien fonctionnement où même les lemmes "bidons" sont écrits
            if(g[iocl+1].tab[i]->mark == 1 && i != resf /* && cardinal(g[iocl].tab[i]->e)!=1 */ )  // TENTION ne teste pas si la conclusion est sur un singleton
            // i.e si le lemme est marqué dans la couche suivante, c'est qu'on en a besoin
            // comme c'est on agit de lanière ascendante dans les couches, c'est la première occurence
            // on en fait un lemme
            {
                // if(constructLemma(file,g[iocl],g[iocl].tab[i],iocl)) // retourne faux si le lemme n'est pas écrit
                {
                    constructLemma(file,g[iocl],g[iocl].tab[i],iocl);  // à commenter après test
                    constructIntro(file, g[iocl]);
			        constructProof(file,g[iocl].tab[i], sizeTab, 1); // le dernier argument correspond à previousconstruct, c'est toujours 1 ?
			        g[iocl].tab[i]->mark = 4;
                    g[iocl+1].tab[i]->mark = 4;     // ajout dans la couche suivante pour que le lemme soit pris en compte
			        unMark(g[iocl].tab[i]);
                }
               
            }
            
        }
    }

    // traitement de la dernière couche :
    // ATTENTION : tab[res]
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // TODO
    // C'est ici qu'on pourrait prendre en compte plusieurs conclusion 
    // seule la conclusion <res> est traitée !
    // 
    // if(constructLemma(file, g[last], g[last].tab[resf],last))  // devrait être toujours vrai
    {
        constructLemma(file, g[last], g[last].tab[resf],last);  // à commenter après test
	    constructIntro(file, g[last]);
	    constructProof(file, g[last].tab[resf], sizeTab, 1);
    }

	
	fclose(file);
    if(debug_mode) fclose(debug_file);
	
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
            else if (!strcmp(argv[i],"-debug") || !strcmp(argv[i],"--debug"))
                {
                    printf("exécution en mode deboggage \n");
                    debug_mode = true;
                }
            else if (!strcmp(argv[i],"-trace") || !strcmp(argv[i],"--trace"))
                {
                    if(trace) { printf("l'option -trace ou --trace a déjà été lue\n"); exit(2);}
                    trace = true;
                    i++;
                    printf("ensemble tracé : %s\n", argv[i]);
                    strcpy(traced_set_name,argv[i]);
                    // traced sera mis à jour après lecture de l'ennoncé
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





