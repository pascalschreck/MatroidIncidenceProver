// fichier statement.h
#ifndef __STATEMENT_H__
#define __STATEMENT_H__
#define MAX_POINTS 64
#define MAX_RANKS 64
#define NAME_SIZE 16
#define MAX_PPR 32
#include<stdio.h>

typedef struct s_rg {
    int points[MAX_PPR];
    unsigned long long set;                // ensemble des points impliqués codé par un entier
    int nbp;
    int rk;
} rang;

typedef struct s_statement {
    char p_names[MAX_POINTS][NAME_SIZE];
    int nbp;
    rang hypoth[MAX_RANKS];         
    int nbr;
    rang conclusion;

} struct_st, *statement;

int find_ref(char *p_name, statement St);
statement st_read(FILE *stat_name);
void st_print(statement st);

#endif