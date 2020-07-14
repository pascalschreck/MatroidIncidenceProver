// fichier statement.c
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include "statement.h"


int find_ref(char *p_name, statement St)
{
    int ref = St->nbp-1;
    for(;ref>=0 && strcmp(p_name,St->p_names[ref]);ref--){};
    return ref;
}

statement st_read(FILE *stat_name)
{
    char buff[256];
    statement st = (statement)malloc(sizeof(struct_st));



// reading declaration of points
    fscanf(stat_name,"%s\n",buff);
    while(!strcmp(buff,"#"))
    {
        fgets(buff,255,stat_name);
        fscanf(stat_name,"%s\n",buff);
    }

    if(strcmp(buff,"points")) {printf("syntax error : 'points' expected\n"), exit(1);}
    fscanf(stat_name,"%s ",buff);
    for(st->nbp=0; st->nbp < MAX_POINTS && strcmp(buff,"rangs"); st->nbp++)
    {
         strcpy(st->p_names[st->nbp],buff);
         fscanf(stat_name,"%s ",buff);
    }
    if(strcmp(buff,"rangs")) {printf("syntax error : 'rangs' expected\n"), exit(1);}

// reading hypthesis ranks
    fscanf(stat_name, "%s ",buff);
    if(!strcmp(buff,":")) {printf("syntax error : point name or fin expected\n"), exit(1);}
    for(st->nbr=0; st->nbr < MAX_RANKS && strcmp(buff,"conclusion"); st->nbr++)
    {   int rk, nbp_rk;
        unsigned long long set = 0ull;
        for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
        {
            int ref = find_ref(buff,st);
            if(ref==-1){printf("erreur %s point non reconnu",buff); exit(2);}
            st->hypoth[st->nbr].points[nbp_rk] = ref;
            set = set | 1ull << ref;
            fscanf(stat_name,"%s ",buff);
        }
        if(strcmp(buff,":")) {printf("syntax error : ':' expected\n"), exit(1);}
        fscanf(stat_name,"%d\n",&rk); 
        if(rk > nbp_rk) {printf("syntax error : %d rank is too big in %d \n",rk, st->nbr), exit(1);}
        st->hypoth[st->nbr].nbp = nbp_rk;
        st->hypoth[st->nbr].set = set-1;
        st->hypoth[st->nbr].rk = rk;
        fscanf(stat_name,"%s ",buff);
    }
    
    if(strcmp(buff,"conclusion")) {printf("syntax error : 'conclusion' expected\n"), exit(1);}

    // reading conclusion
    fscanf(stat_name,"%s ",buff);
    if(!strcmp(buff,":")) {printf("syntax error : point name expected\n"), exit(1);}
    { int rk, nbp_rk;
      unsigned long long set = 0ull;
        for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
        {
            int ref = find_ref(buff,st);
            if(ref==-1){printf("erreur %s point non reconnu",buff); exit(2);}
            st->conclusion.points[nbp_rk] = ref;
            set = set | 1ull << ref;
            fscanf(stat_name,"%s ",buff);
        }
        if(strcmp(buff,":")) {printf("syntax error : ':' expected\n"), exit(1);}
        fscanf(stat_name,"%d\n",&rk); 
        if(rk > nbp_rk) {printf("syntax error : %d rank is too big in %d \n",rk, st->nbr), exit(1);}
        st->conclusion.nbp = nbp_rk;
        st->conclusion.set = set - 1;
        st->conclusion.rk = rk;
    }

    return st;
}


void st_print(statement st)
{
    printf("nombre de points %d\n", st->nbp);
    for(int i=0; i< st->nbp; i++) printf("%s ", st->p_names[i]);
    putchar('\n');
    
    printf("nombre de rangs imposés : %d\n", st->nbr);
    for(int i=0; i< st->nbr; i++)
    {
        rang r = st->hypoth[i];
        printf("%d (%d points) ensemble %llu: ", i, r.nbp, r.set);
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" a pour rang %d\n", r.rk);
    }
    putchar('\n');

    rang r = st->conclusion;
    printf("conclusion (ensemble %llu): \n",r.set);   
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" devrait avoir pour rang %d\n", r.rk);
    putchar('\n');
}

/*
int main(int argc, char * argv[])
{
    char filename[64];
    if(argc != 2) {printf("Usage %s + nom de fichier (et c'est tout\n",argv[0]); exit(1);}
    strcpy(filename,argv[1]);

    FILE *stat = fopen(filename,"r");
    statement st = st_read(stat);
    fclose(stat);

    st_print(st);
    putchar('\n');
}

*/