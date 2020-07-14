// fichier sscanf.c
#include<stdio.h>
#include<string.h>
#include<stdlib.h>

#define MAX_POINTS 64
#define MAX_RANKS 64
#define NAME_SIZE 16
#define MAX_PPR 32

typedef struct s_rg {
    int points[MAX_PPR];
    int nbp;
    int rk;
} rang;

int find_ref(char *p_name, char t_points[][NAME_SIZE], int bs)
{
    int ref = bs-1;
    for(;ref>=0 && strcmp(p_name,t_points[ref]);ref--){};
    return ref;
}
int main()
{
    char points[MAX_POINTS][NAME_SIZE], buff[256];
    rang ranks[MAX_RANKS];
    int nbp, nbr;


    scanf("%s\n",buff);
    if(strcmp(buff,"points")) {printf("syntax error : 'points' expected\n"), exit(1);}
    scanf("%s ",buff);
    for(nbp=0; nbp < MAX_POINTS && strcmp(buff,"rangs"); nbp++)
    {
         strcpy(points[nbp],buff);
         scanf("%s ",buff);
    }
    printf("nombre de points %d\n", nbp);
    for(int i=0; i< nbp; i++) printf("%s ", points[i]);
    
    if(strcmp(buff,"rangs")) {printf("syntax error : 'rangs' expected\n"), exit(1);}

    scanf("%s ",buff);
    if(!strcmp(buff,":")) {printf("syntax error : point name or fin expected\n"), exit(1);}
    for(nbr=0; nbr < MAX_RANKS && strcmp(buff,"fin"); nbr++)
    {   int rk, nbp_rk;
        for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
        {
            int ref = find_ref(buff,points,nbp);
            if(ref==-1){printf("erreur %s point non reconnu",buff); exit(2);}
            ranks[nbr].points[nbp_rk] = ref;
            scanf("%s ",buff);
        }
        if(strcmp(buff,":")) {printf("syntax error : ':' expected\n"), exit(1);}
        scanf("%d\n",&rk); 
        if(rk > nbp_rk) {printf("syntax error : %d rank is too big in %d \n",rk, nbr), exit(1);}
        ranks[nbr].nbp = nbp_rk;
        ranks[nbr].rk = rk;
        scanf("%s ",buff);
    }

    printf("nombre de rangs imposés : %d\n", nbr);
    for(int i=0; i< nbr; i++)
    {
        rang r = ranks[i];
        printf("%d (%d points): ", i, r.nbp);
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", points[r.points[j]], r.points[j]);
        printf(" a pour rang %d\n", r.rk);
    }

    putchar('\n');
}