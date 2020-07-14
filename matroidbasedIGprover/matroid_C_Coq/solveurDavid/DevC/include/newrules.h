// fichier newrules.h
// créé par PS
#ifndef __NEWRULES_H__
#define __NEWRULES_H__
// Nous allons réutiliser les structures de l'énoncé car
// la formulation d'un règle ressemble à celle d'un énoncé
// par ailleurs, 
// nous allons utiliser la notion de couche pour ajouter des points
// c'est la même idée, il faudra alors faire attention à ce que l'allocation
// correspondantes aux couches suivantes soient retardées pour garder des 
// puissances de 2 consécutives pour numéroter les points
#include "statement.h"

#define MAX_ADD 4   // nombre max de points ajoutés par une règle
#define MAX_RANKS_PR 32

typedef struct s_conclusion {
    char add_names[MAX_ADD][NAME_SIZE];
    int nbadd;              // en pratique on ajoute 1 point (double la taille du graphe)
                            // si nbadd != 0 prévoir une nouvelle couche (layer)
                            // cette couche devra être ajoutée à la fin des autres
    rang maxR[MAX_RANKS_PR];
    int nbMaxr;
    rang minR[MAX_RANKS_PR];
    int nbMinr;
} str_conclusion, *conclusion;

 typedef struct s_rule {
     unsigned rdim;
     char up_names[MAX_POINTS][NAME_SIZE];          // univ. quantifiés
     int nbup;                                      // nb. points univ.
     char ep_names[MAX_POINTS][NAME_SIZE];          // exist. quantifiés
     int nbep;                                      // nb. points exist.
     rang hypoth[MAX_RANKS_PR];
     int nbhy;
     rang guards[MAX_RANKS_PR];
     int nbg;
     conclusion conlusions[MAX_RANKS_PR]
 } str_rule; *rule;

#endif