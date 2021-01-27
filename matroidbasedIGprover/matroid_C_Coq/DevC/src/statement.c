// fichier statement.c
// créé par PS
// dernière modif : 11 juillet 2020
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include<stdbool.h>
#include "statement.h"
#include "parties.h"


bool notin(int x, int *tab, int max)
{
    int i=0;
    for(;i<max && tab[i]!=x;i++);
    return i==max;
}

/*--------------------------------------------------------------------------
    fonctions pour sauter les commentaires
    un commentaire commence par # (corrigé :pas forcément suivi d'un espace)
    le commentaire va jusqu'à la fin de la ligne
*---------------------------------------------------------------------------*/
char * st_comment(FILE *file, char *buff)
{
        // while(!strcmp(buff,"#") || !strcmp(buff,""))
        while(!strcmp(buff,"") || buff[0]=='#')
    {
        fgets(buff,255,file);
        fscanf(file,"%s\n",buff);   // fscanf s'arrête au premier espace
    }
    return buff;
}


/*----------------------------------------------------------------------
    recherche de l'indice d'un point dans le tableau de points
    Remarque : on un tableau de points global pour tout l'énoncé
    les points d'une couches correspondent à des tranches de ce tableau
*-----------------------------------------------------------------------*/
int find_ref(char *p_name, statement St)
{
    int ref = St->nbp-1;
    for(;ref>=0 && strcmp(p_name,St->p_names[ref]);ref--){};
    return ref;
}


/*------------------------------------------------------------------
    lecture d'un énoncé
    .... cette fonction
*--------------------------------------------------------------------*/

statement st_read(FILE *stat_name)
{
    char buff[256];
    statement st = (statement)malloc(sizeof(struct_st));
    st->nbp=0;

    // lecture du contexte
    fscanf(stat_name,"%s\n",buff);  st_comment(stat_name, buff);
    if(strcmp(buff,"context")) 
        {printf("syntax error : 'context' expected instead of %s\n",buff); exit(1);}            // context

    fscanf(stat_name,"%s\n",buff); st_comment(stat_name, buff);
    if(strcmp(buff,"dimension")) 
        {printf("syntax error : 'dimension' expected instead of %s\n",buff); exit(1);}        // dimension
    
    fscanf(stat_name,"%d\n",&(st->sdim));st_comment(stat_name, buff);
    if(st->sdim <2 || st->sdim > 7) {printf("error : 'dimension' not in [2..7]\n"); exit(1);}
    
    fscanf(stat_name,"%s\n",buff); st_comment(stat_name, buff);
    if(strcmp(buff,"layers")) 
        {printf("syntax error : 'layers' expected instead of %s\n",buff); exit(1);}              // layers
    fscanf(stat_name,"%d\n",&(st->nb_layers));st_comment(stat_name, buff);
    if(st->nb_layers > MAX_LAYERS) 
        {printf("error : 'nb of layers' should be < %d\n",MAX_LAYERS); exit(1);}
    
    fscanf(stat_name,"%s\n",buff);st_comment(stat_name, buff);
    if(strcmp(buff,"endofcontext"))                                                                 // endofcontext
        {printf("syntax error : 'endofcontext' expected instead of %s\n",buff); exit(1);}
    
    //-----------------------------------lecture des couches------------------------------------------
    int iocl = 0;
    for(;iocl < st->nb_layers; iocl++)
    {   // read one layer
        layer cly = (layer)malloc(sizeof(struct_ly));
        st->layers[iocl] = cly;
        cly->nbp = 0;
        cly->nbr = 0;
        cly->nbs = 0;
        cly->nb_slices = 0;

        fscanf(stat_name,"%s\n",buff); st_comment(stat_name, buff);
        if(strcmp(buff,"layer"))                                                                 // layer
            {printf("syntax error : 'layer' expected instead of %s\n",buff), exit(1);}
        fscanf(stat_name,"%s\n",cly->name);st_comment(stat_name, buff);

        fscanf(stat_name,"%s\n",buff); st_comment(stat_name, buff);
        if(strcmp(buff,"points"))                                                               // points
            {printf("syntax error : 'points' expected instead of %s\n",buff), exit(1);}
        fscanf(stat_name,"%s ",buff); st_comment(stat_name, buff);
        while(!strcmp(buff, "layer"))                                   // import des points d'autres layers
        {
            char name_ly[NAME_SIZE]; 
            int ref_ly;
            int j;
            fscanf(stat_name,"%s\n",name_ly);st_comment(stat_name, buff);

            for(ref_ly=0;ref_ly < iocl && strcmp(name_ly,st->layers[ref_ly]->name); ref_ly++){}
            if(ref_ly==iocl) 
                {printf("réference au layer %s non trouvée",name_ly); exit(1); }

            for(j=0; j<st->layers[ref_ly]->nb_slices;j++)
                {
                  if(notin(st->layers[ref_ly]->start_slices[j],cly->start_slices,cly->nb_slices))
                    {
                    cly->start_slices[cly->nb_slices] = st->layers[ref_ly]->start_slices[j];
                    cly->end_slices[cly->nb_slices] = st->layers[ref_ly]->end_slices[j];
                    cly->nbp += cly->end_slices[cly->nb_slices] - cly->start_slices[cly->nb_slices];
                    cly->nb_slices++;
                    }
                }
            fscanf(stat_name,"%s\n",buff); st_comment(stat_name, buff);
        }   // fin du traitement de l'import des points des layers précédents
            // l'inclusion des layers est transitive
    // addition des nouveaux points
        cly->start_slices[cly->nb_slices] = st->nbp;
        while(st->nbp < MAX_POINTS && strcmp(buff,"hypotheses"))
        {
        if(find_ref(buff,st) == -1)
            {
            strcpy(st->p_names[st->nbp],buff);
            fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
            st->nbp++;          // on augmente le nombre de points total
            cly->nbp++;         // on augmente le nombre de points de la couche
            }
        else
            {
            printf("layer %s : point %s déjà dans défini, il n'a pas été rajouté\n",cly->name, buff);
            exit(1);
            }
        
        }
    cly->end_slices[cly->nb_slices] = st->nbp;    // attention : l'indice de fin pointe sur le premier élt en dehors
    cly->nb_slices++;

    // lecture des rangs
        if(strcmp(buff,"hypotheses"))                                               // hypotheses
                {printf("syntax error : 'hypotheses' expected instead of %s\n",buff); exit(1);}
    // reading hypotheses ranks
        fscanf(stat_name, "%s ",buff); st_comment(stat_name, buff);// traitement des commentaires
        if(!strcmp(buff,":")) 
            {printf("syntax error : point name or fin expected instead of %s\n", buff); exit(1);}
        for(cly->nbr=0; cly->nbr < MAX_RANKS && strcmp(buff,"conclusion"); cly->nbr++)
        {   int rk, nbp_rk;
            unsigned long long set = 0ull;
            for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
            {
                int ref = find_ref(buff,st);
                if(ref==-1){printf("erreur in hypoth. %d : %s point non reconnu",cly->nbr, buff); exit(2);}
                cly->hypoth[cly->nbr].points[nbp_rk] = ref;
                set = set | 1ull << ref;
                fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
            }
            if(strcmp(buff,":"))                                                    // lecture des :
                { printf("syntax error : ':' expected instead of %s\n", buff); exit(1); }
            fscanf(stat_name,"%d\n",&rk); st_comment(stat_name, buff);
            if(rk > nbp_rk) 
                {
                printf("error in hypoth: %d rank is too big in %d (layer %d) \n",rk, cly->nbr, iocl);
                exit(1);
                }
            cly->hypoth[cly->nbr].nbp = nbp_rk;
            cly->hypoth[cly->nbr].set = set-1;
            cly->hypoth[cly->nbr].rk = rk;
            fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
        } // fin de la lecture des hypothèses pour une couche

        if(strcmp(buff,"conclusion")) 
            {printf("syntax error : 'conclusion' expected instead of %s\n",buff); exit(1);}
        // reading conclusion
        fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
        if(strcmp(buff,"None") && strcmp(buff,"none"))
        {
            if(!strcmp(buff,":")) 
                {printf("syntax error : point name expected instead of %s\n",buff); exit(1);}
            { int rk, nbp_rk;
            unsigned long long set = 0ull;
                for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
                {
                    int ref = find_ref(buff,st);
                    if(ref==-1)
                        {printf("error in conclusion %s unkown point",buff); exit(2);}
                    cly->conclusion.points[nbp_rk] = ref;
                    set = set | 1ull << ref;
                    fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
                }
                if(strcmp(buff,":")) 
                    {printf("syntax error : ':' expected instead of %s\n",buff); exit(1);}
                fscanf(stat_name,"%d\n",&rk); st_comment(stat_name, buff);
                if(rk > nbp_rk) 
                    {printf("error in conclusion of layer %d: %d rank is too big\n",iocl, rk), exit(1);}
                cly->conclusion.nbp = nbp_rk;
                cly->conclusion.set = set - 1;
                cly->conclusion.rk = rk;
            }
        }
        fscanf(stat_name,"%s\n",buff);st_comment(stat_name, buff);
        // reading supplement ranks
        if(!strcmp(buff,"supplements"))
        {
            fscanf(stat_name, "%s ",buff);st_comment(stat_name, buff);
            if(!strcmp(buff,":")) 
                {printf("syntax error : point name or fin expected instead of %s\n",buff); exit(1);}
            for(cly->nbs=0; cly->nbs < MAX_RANKS && strcmp(buff,"endoflayer"); cly->nbs++)
            {   int rk, nbp_rk;
                unsigned long long set = 0ull;
                for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
                {
                int ref = find_ref(buff,st);
                if(ref==-1)
                    {printf("erreur in suppl. %s point non reconnu",buff); exit(2);}
                cly->supp[cly->nbs].points[nbp_rk] = ref;
                set = set | 1ull << ref;
                fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
                }
                if(strcmp(buff,":")) 
                    {printf("syntax error : ':' expected instead of %s\n",buff); exit(1);}
                fscanf(stat_name,"%d\n",&rk); st_comment(stat_name, buff);
                if(rk > nbp_rk) 
                {
                  printf("syntax error in supplements : %d rank is too big in %d of layer %d\n",rk, cly->nbs, iocl);
                  exit(1);
                }
                cly->supp[cly->nbs].nbp = nbp_rk;
                cly->supp[cly->nbs].set = set-1;
                cly->supp[cly->nbs].rk = rk;
                fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
            }
        }
        else if(strcmp(buff,"endoflayer")) 
            {printf("syntax error : 'endoflayer' or supplements expected instead of %s\n",buff); exit(1);}
        else printf("end of layer %d\n",iocl);
    } // fin de la boucle de l'acquisition d'une couche


//---------------------------------------------------------------------------- suite pas touchée
// cela correspond à la saisie de la conclusion générale
// et aux suppléments généraux
    fscanf(stat_name,"%s\n",buff);st_comment(stat_name, buff);
    if(strcmp(buff,"conclusion")) 
        {printf("syntax error : 'conclusion' expected instead of %s\n", buff); exit(1);}

    // reading conclusion
    fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
    if(!strcmp(buff,":")) 
        {printf("syntax error : point name expected instead of %s\n",buff); exit(1);}
    { int rk, nbp_rk;
      unsigned long long set = 0ull;
        for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
        {
            int ref = find_ref(buff,st);
            if(ref==-1){printf("erreur in conclusion %s point non reconnu",buff); exit(2);}
            st->conclusion.points[nbp_rk] = ref;
            set = set | 1ull << ref;
            fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
        }
        if(strcmp(buff,":")) 
            {printf("syntax error : ':' expected instead of %s\n", buff); exit(1);}
        fscanf(stat_name,"%d\n",&rk); st_comment(stat_name, buff);
        if(rk > nbp_rk) {printf("error in conclusion : %d rank is too big in conclusion \n",rk), exit(1);}
        st->conclusion.nbp = nbp_rk;
        st->conclusion.set = set - 1;
        st->conclusion.rk = rk;
    }
fscanf(stat_name,"%s\n",buff);st_comment(stat_name, buff);
// if(strcmp(buff,"supplements")) 
//    {printf("syntax error : 'supplements' expected instead of %s\n",buff); exit(1);}
if(!strcmp(buff,"supplements"))
    {
// reading supplemnts ranks
      fscanf(stat_name, "%s ",buff);st_comment(stat_name, buff);
      if(!strcmp(buff,":")) 
        {printf("syntax error : point name or end expected instead of %s\n",buff); exit(1);}
      for(st->nbs=0; st->nbs < MAX_RANKS && strcmp(buff,"end"); st->nbs++)
        {   int rk, nbp_rk;
            unsigned long long set = 0ull;
            for(nbp_rk = 0; nbp_rk < MAX_PPR && strcmp(buff,":"); nbp_rk++)
            {
            int ref = find_ref(buff,st);
            if(ref==-1){printf("erreur in suppl. %s point non reconnu",buff); exit(2);}
            st->supp[st->nbs].points[nbp_rk] = ref;
            set = set | 1ull << ref;
            fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
            }
            if(strcmp(buff,":")) 
                {printf("syntax error : ':' expected instead of %s\n",buff); exit(1);}
            fscanf(stat_name,"%d\n",&rk); st_comment(stat_name, buff);
            if(rk > nbp_rk) {printf("syntax error in supplements : %d rank is too big in %d \n",rk, st->nbs), exit(1);}
            st->supp[st->nbs].nbp = nbp_rk;
            st->supp[st->nbs].set = set-1;
            st->supp[st->nbs].rk = rk;
            fscanf(stat_name,"%s ",buff);st_comment(stat_name, buff);
        }
    }
    else if(strcmp(buff,"end")) 
            {printf("syntax error : 'end' or supplements expected instead of %s\n",buff); exit(1);}
        else printf("end\n");
    
//    if(strcmp(buff,"end")) 
//        {printf("syntax error : 'end' expected instead of %s\n",buff); exit(1);}

    return st;
}


///////////////////////////////////////////////////////////////////////////
//          affichage
///////////////////////////////////////////////////////////////////////////

void st_print(statement st)
{
    // printf("dimension de l'énoncé %d (solveur : %d)\n",st->sdim, dim);
    printf("dimension de l'énoncé %d \n",st->sdim);
    printf("nombre de points %d\n", st->nbp);
    for(int i=0; i< st->nbp; i++) printf("%s ", st->p_names[i]);
    putchar('\n');
    printf("nombre de couches : %d\n", st->nb_layers);
    for(int iocl=0; iocl < st->nb_layers;iocl++)
    {
      layer cly = st->layers[iocl];
        printf("------------------------------------\n");
        printf("couche %d, nom : %s\n", iocl, cly->name);
        printf("nombre de points dans la couche : %d\n", cly->nbp);
        printf("nombre de tranches : %d\n", cly->nb_slices);
        for(int i=0; i< cly->nb_slices; i++)
            printf("tranche %d : \n\t début %d \n\t fin %d\n", i, cly->start_slices[i],cly->end_slices[i]);
        printf("nombre de rangs imposés : %d\n", cly->nbr);
        for(int i=0; i< cly->nbr; i++)
        {
        rang r = cly->hypoth[i];
        printf("%d (%d points) ensemble %llu: ", i, r.nbp, r.set);
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" a pour rang %d\n", r.rk);
        }
      putchar('\n');

      rang r = cly->conclusion;
      printf("conclusion (ensemble %llu): \n",r.set);   
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" devrait avoir pour rang %d\n", r.rk);
      putchar('\n');

      printf("supplements : %d\n", cly->nbs);
     for(int i=0; i< cly->nbs; i++)
        {
        rang r = cly->supp[i];
        printf("%d (%d points) ensemble %llu: ", i, r.nbp, r.set);
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" devrait avoir pour rang %d\n", r.rk);
        }
      putchar('\n');
    }
    printf("--------------------------------------------\n");
    printf("fin des couches\n");
    
    rang r = st->conclusion;
      printf("conclusion (ensemble %llu): \n",r.set);   
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" devrait avoir pour rang %d\n", r.rk);
      putchar('\n');

      printf("supplements : %d\n", st->nbs);
     for(int i=0; i< st->nbs; i++)
        {
        rang r = st->supp[i];
        printf("%d (%d points) ensemble %llu: ", i, r.nbp, r.set);
        for(int j=0; j < r.nbp; j++) printf("%s(%d) ", st->p_names[r.points[j]], r.points[j]);
        printf(" devrait avoir pour rang %d\n", r.rk);
        }
      putchar('\n');

}

/*-----------------------------------------------------------------------

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

------------------------------------------------------------------------*/

