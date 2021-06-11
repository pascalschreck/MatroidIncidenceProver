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

statement STATEMENT;

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
    STATEMENT = st;                         // STATEMENT procure un accès global à l'énoncé (c'est une variable globale à tout le projet)
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
    int nb_layers = st->nb_layers;                  // nombre de couche en principe < MAX_LAYERS
    int nbp=0;                                      // nombre de points pour la couche courante
    unsigned long long res;                        // conclusion pour la couche courante
    unsigned long long resf=st->conclusion[0].set; // 1er terme de la conclusion finale (compatibilité)

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
        res = cly->conclusion.set;                  // n'est pas utilisé en fait
        g[iocl] = allocGraph(nbp);
        g[iocl].effectiveAllocPow = nbp;    
        g[iocl].effectiveSize = (1u<<nbp)-1;  
        for(int i=0; i<cly->nbr; i++)
  	    {
		    rang r = cly->hypoth[i];
		    int set = r.set;
		    g[iocl].tab[set]-> e = setMinMax(g[iocl].tab[set]->e,r.rk,r.rk);  // hypothèses (rang) de l'énoncé
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
		    g[iocl].tab[set]-> e = setMinMax(g[iocl].tab[set]->e,r.rk,r.rk);    // hypothèses (rang) de l'énoncé
		    g[iocl].tab[set]->color = -1;
  	    }
        fprintf(stderr,"-------- convergence couche %d \n", iocl);
	    sizeTab.tab[iocl][0] = g[iocl].effectiveAllocPow;
	    sizeTab.tab[iocl][1] = g[iocl].effectiveSize;
	    g[iocl] = convergenceParties(g[iocl],res); // Saturation

    }
			

	 
	// fin de la preuve, sortie des rangs dans un fichier dont le nom est donné sur la ligne de commande
	FILE *wp_out = fopen(rankoutput_name,"w+");
	fprintGraphWithoutProof(wp_out, g[nb_layers-1]);				// écriture dans le fichier 


	// exploration simple du fichier : on cherche le rang correspondant à la conclusion et
	// les rangs des lignes supplémentaires

    // modification juin 2021
    // la conclusion est un ensemble de termes
    for(int i=0; i < st->nbconc; i++)
    {
        rewind(wp_out);
        long long unsigned nw_line = st->conclusion[i].set;
        resf = nw_line;
        int srk = st->conclusion[i].rk;
        char buf[255];
        for(int j=0; j <= nw_line; j++) fgets(buf, 255, wp_out);
        printf("conclusion (ligne %lld), rang attendu %d\n  %s\n", nw_line, srk, buf);
    }

	for(int i=0;i< st->nbs; i++) // nbs : nombre de lignes supplémentaires
		{	rewind(wp_out); 	// on revient à 0 parce qu'on est pas sûr que tous les suppléments sont
		                    	// rangés dans un ordre croissant
			nw_line = st->supp[i].set;
			srk = st->supp[i].rk;
			for(int j=0; j <= nw_line; j++) fgets(buf, 255, wp_out);
			printf("supplément (ligne %lld) rang attendu %d\n  %s\n", nw_line, srk, buf);	
		}
  fclose(wp_out);



// TODO 
// la conclusion est maintenant un ensemble de termes 
// la suite n'a pas encore été traitée.
//
//

  	// on ouvre ensuite le fichier de sortie pour la preuve coq
	// c'est soit le fichier standard, soit celui lu à la ligne de commande
	FILE* file = fopen(coqoutput_name,"w");	
    fprintf(file, "Require Import lemmas_automation_g.\n\n\n");

    fprintf(stderr,"--------------- reconstruction\n\n");
	
    /*________________________________________________________
        TODO : la suite est à vérifier
    ----------------------------------------------------------*/

    /*


        Deux cas différents : 
            - multi-couches (.e. nb_layers > 1) : on applique la méthode de David, 
                * dans toutes les couches sauf la dernière, tous les sommets marqués sont transcrits 
                  en Coq par des lemmes
                * dans la dernière couche seul le noeud correspondant à l'ensemble resf  donne lieu à
                  un lemme
                Issues : 
                    * je (PS) ne sais pas bien comment se propage le marquage. Avec ma reprise du code
                    il y a des problèmes de bout de preuves qui ne sont pas produits (les causes possibles sont
                    la recopie de graphe qui ne reporte pas les listes ante et succ, le marquage qui pourrait ne
                    pas bien traverser les couches (par exemple, j'ai corrigé le passage des marks 4 correspondant
                    à une preuve déjà faite))
                    * je ne pense pas que fabriquer des couches soit intéressant.
                    *
            - mono-couches où j'ai opéré le changment suivant : tous les sommets marqués donnent lieu à
                des lemmes. On a ainsi des lemmes peu intéressants pour lesquels j'ai fait des filtres
                qui sont pour le moment désactivés car ils semblent perturber l'écriture de la preuve
        Dans la suite, on distingue les deux cas pour voir.

        Remarque : j'ai aussi fait des changement dans la reconstruction de la preuve : on n'écrit pas un lemme
            sans qu'un certain nombre de lemmes intermédiaires n'aient pas eux-mêmes été écrits. On n'utilise un lemme
            dans une preuve que s'il a effectivement été écrit. Il reste cependant des cas identifiés dans lequels la preuve
            d'une pémisse qui aurait pu faire l'objet d'un lemme, reste locale à une preuve.
    */
    if(nb_layers==1) 
    // ==========================
    // cas monocouche 
    // ==========================
    {
        long long unsigned int i ;
        int last = 0;
        
        // resf = codage de l'ensemble dans la conclusion finale
                if(debug_mode)
            {
                NL;
                DEB_PS("********************************************");NL;NL;
                TAB; fprintf(debug_file," marquage dans la (dernière) couche %d\n", last);
                NL; DEB_PS("********************************************");NL;NL;
            }
         
        // marquage en arrière à partir de resf
        preMark(g[last].tab[resf]);  
        // construction en avant de la preuve (les filtres ne sont pas écrits)
        i = 0ull;

        
        for(; i < g[last].effectiveSize;i++)
        {   
            if(g[last].tab[i]->mark == U_NOT_WRITTEN_IN_PROOF && i != resf) 
            {
                constructLemma(file,g[last],g[last].tab[i],sizeTab, last);  
                // la fonction constructLemma a été revisitée : elle examine tous les noeuds qui sont requis
                // pour écrire la preuve et en fait des lemmes. Les deux fonctions dont les appels sont commentés
                // ci-dessous sont faits dans la fonction constructctLemma ainsi, on peut mieux contrôler l'écriture
                // dans le fichier.
                // constructIntro(file, g[last]);
                // constructProof(file,g[last].tab[i], sizeTab, 1); 
                g[last].tab[i]->mark = PROOF_ALREADY_DONE; // 4
               unMark(g[last].tab[i]);   // on remet à 1 () les noeuds qui ont été mis à 5
            }
            
        }
        
        
        constructLemma(file, g[last], g[last].tab[resf],sizeTab, last); 
        // constructIntro(file, g[last]);
        // constructProof(file, g[last].tab[resf], sizeTab, 1);
        

        
        fclose(file);
        if(debug_mode) fclose(debug_file);
    }
    else  
    // ======================================
    // cas multi-couches 
    // ... contient encore des bugs
    // =====================================
    {
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

                if(g[iocl+1].tab[i]->mark == 1 && i != resf ) 
                // i.e si le lemme est marqué dans la couche suivante, c'est qu'on en a besoin
                // comme c'est on agit de lanière ascendante dans les couches, c'est la première occurence
                // on en fait un lemme
                {
                        constructLemma(file,g[iocl],g[iocl].tab[i],sizeTab, iocl);
                        g[iocl].tab[i]->mark = 4;
                        g[iocl+1].tab[i]->mark = 4;     // ajout dans la couche suivante pour que le lemme soit pris en compte
                
                }
                
            }
        }

        constructLemma(file, g[last], g[last].tab[resf],sizeTab, last); 
        
        fclose(file);
        if(debug_mode) fclose(debug_file);
    }
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
                    // le petit bout de code suivant fait que le nom du fichier est celui entré jusqu'au séparateur '.'
                    // et complété par ".v"
                        char *pt = argv[i], *ptt = coqoutput_name;
                        for(;*pt && *pt != '.'; pt++, ptt++) *ptt = *pt ;
                        *ptt++ ='.'; *ptt++='v'; *ptt='\0';
                    printf("output : la preuve coq sera contenue dans le fichier : %s\n",coqoutput_name); 
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
        // le petit bout de code suivant fait que le nom du fichier est celui entré jusqu'au séparateur '.'
        // et complété par ".v"
            char *pt = statement_name, *ptt = coqoutput_name;
            for(;*pt && *pt != '.'; pt++, ptt++) *ptt = *pt ;
            *ptt++ ='.'; *ptt++='v'; *ptt='\0';
        // strcpy(coqoutput_name,statement_name); strcat(coqoutput_name,".v");
    }
if(!(opt_flag & rank_flag))
    {
        strcpy(rankoutput_name,statement_name); strcat(rankoutput_name,".out");
    }
}





