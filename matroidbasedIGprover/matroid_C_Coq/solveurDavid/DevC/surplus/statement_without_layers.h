// fichier statement.h
#ifndef __STATEMENT_H__
#define __STATEMENT_H__
#define MAX_POINTS 64
#define MAX_RANKS 256
#define NAME_SIZE 16
#define MAX_PPR 32
#include<stdio.h>

typedef struct s_rg {
    int points[MAX_PPR];                    // entiers désignant les points impliqués
    unsigned long long set;                 // ensemble des points impliqués codé par un entier
    int nbp;                                // nombre de points impliqués
    int rk;                                 // rang (imposé ou trouvé) de l'ensemble 'set'
} rang;                                     // structure rang

typedef struct s_statement {
    unsigned sdim;                          // dimension donnée par l'énoncé
    char p_names[MAX_POINTS][NAME_SIZE];    // nom des points donnés par l'énoncé
    int nbp;                                // nombre de points
    rang hypoth[MAX_RANKS];                 // tableau des rangs codant les hypothèses du thm à prouver      
    int nbr;                                // nombre de ces hypothèses
    rang conclusion;                        // rang codant la conclusion
    rang supp[MAX_RANKS];                   // rang supplémentaires à afficher à la fin
    int nbs;                                // nombre de ces "conclusion" supplémentaires
                                            // ces "conclusions" ne sont pas passées au solveur
                                            // je ne sais pas si il gère plusieurs conclusions
} struct_st, *statement;                    // un énoncé est un pointeur sur une telle structure

// pre : ?
// post : retourne la référence (un entier) correspondant à un nom de point de l'énoncé
//        c'est en fait son indice dans le tableau 'St->p_names'
// effet de bord : aucun
int find_ref(char *p_name, statement St);

// pre : FILE != NULL et l'énoncé est correctemt posé (voir la syntaxe plus bas)
// post : lit un énoncé à partir d'un fichier (en fait une struct? FILE ouverte ailleurs)
// effet de bord : reserve de la place pour un énoncé (struct_st) et le remplit
statement st_read(FILE *stat_name);

// pre : ?
// post : ne retourne rien
// effet de bord : affichage de l'enoncé
void st_print(statement st);

/*----------------------------syntaxe-----------------*
*
*       TODO
*
*-----------------------------------------------------*/


#endif