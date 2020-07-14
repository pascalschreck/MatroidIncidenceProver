// fichier testLC.c
// petit essai sur la lecture de la ligne de commande
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include "../include/globals.h"

 char        statement_name[255],
             rankoutput_name[255],
             coqoutput_name[255],
             newrules_name[255];


int main(int argc, char * argv[])
{
    strcpy(statement_name,dft_statement_name);
    strcpy(rankoutput_name,dft_rankoutput_name);
    strcpy(coqoutput_name,dft_coqoutput_name);
    strcpy(newrules_name,dft_newrules_name);

    unsigned opt_flag = 0;

    if (argc == 1) { printf("Erreur il faut au moins un argument\n"); exit(1);}
    if (argc == 2) 
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
                    printf("Affichage du message d'aide\n");
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
    

    printf("OK\n\n");
    printf("énoncé : %s \n liste des rangs : %s \n sortie coq : %s \n nouvelles règles %s \n ", 
            statement_name,
            rankoutput_name,
            coqoutput_name,
            newrules_name);
}