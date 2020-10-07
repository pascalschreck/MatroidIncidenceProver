// fichier parties.c
// créé par David Braun
// modification mineures par PS
#include "parties.h"

/*______________________________________________________________________________

## allocSizeTab() gestion de l'allocation mémoire pour les couches
________________________________________________________________________________*/
allocSize allocSizeTab (int n, int m) {
	int i,j;
	allocSize p;
	
	p.size = n;
	p.tab = (int **)malloc(sizeof(int *)*n);
	
	for(i = 0; i < p.size; i++)
	{
		p.tab[i] = (int *)malloc(sizeof(int)*m);
	}
	
	for(i = 0; i < p.size; i++)
	{
		for(j = 0; j < m; j++)
		{
			p.tab[i][j] = 0;
		}
	}
	
	return p;
}

/*______________________________________________________________________________

## allocGraph() gestion de l'allocation mémoire
________________________________________________________________________________*/
graph allocGraph (int n) {
	int i;
	graph g;
	myType init = 0x0;
	// char s[255]; // debug : juste pour le sget()

	// printf("nombre de points dans allocGraph : %d\n", n);
	g.size =  (1 << n); 
	g.effectiveSize = 0;
	g.allocPow = n;
	g.effectiveAllocPow = 0;
	
	node * tab = (node *)malloc(sizeof(node)*g.size);
	
	for(i = 0; i < g.size; i++)
	{
		init = i+1 ;  // DecToBin(i+1);  /* hum ... pourquoi faire compliqué ? c'est juste i+1  */
		init = initRanks(init);
		tab[i] = createNode(init);
	}
	
	g.tab = tab;
	// printf("sortie de l'alloc safely\n"); // debug
    // fgets(s, 255, stdin);				 // debug
	return g;
}

/*______________________________________________________________________________

## copyGraph() recopie de graphes
________________________________________________________________________________*/
graph copyGraph(graph g1, graph g2, int res) {
	int i;
	
	for (i = 0; i < g1.effectiveSize; i++)
	{
		if(i != res && rankMax(g1.tab[i]->e) == rankMin(g1.tab[i]->e))
		{
			g2.tab[i] = createNode(g1.tab[i]->e);
			g2.tab[i]->color = g1.tab[i]->color;
		}
	}
	return g2;
}

//**************************************************************************
/*---------------------------------------------------------------*
*
*	convergenceParties(g, res) :
* modifie le graphe g par effet de bord en mettant à jour minRank 
* et maxRank par application des règles issue du matroïde 
*
*_________________________________________________________________*/
graph convergenceParties (graph g, int res) {
	
	int debug = 0;
	int print = 0;
	
	int i, j;
		
	myType partA, partB, partAiB, partAuB, partAe, partBe, partAiBe, partAuBe;
	int rankMinA, rankMaxA, rankMinB, rankMaxB, rankMinAiB, rankMaxAiB, rankMinAuB, rankMaxAuB;
	
	int convergenceValue = 1;
	int * convergence = &convergenceValue;
	int variation = 1;
	int loopNumber = 0;
	int pappusNumber = 0;
	int computeM3 = -1;
	int decr = 0;
	int sub = 0;
	
	int colori, colorj;

	list l;
	node n;
		
	//~ // convergence
	while(*convergence == 1)
	{
		*convergence = 0;

		while(variation == 1)
		{
			variation = 0;
			/*-------------------------------------------------*/
			// une boucle de l'algo. de saturation
			// On parcours toutes les paires (i,j) de sommets 
			// du graphe
			
			for(i = 0; i < g.effectiveSize; i++) 			// boucle sur un sommet
			{
				colori = g.tab[i]->color;
				
				for(j = i+1; j < g.effectiveSize; j++)		// boucle sur le deuxième sommet
				{	
					colorj = g.tab[j]->color;
					if(colori >= loopNumber+1 || colorj >= loopNumber+1 || colori == -1 || colorj == -1)
					{
					
						// sets
						partA = g.tab[i]->e;
						partB = g.tab[j]->e;
						
						partAe = g.tab[i]->e & 0x3FFFFFFFFFFFFFF;
						partBe = g.tab[j]->e & 0x3FFFFFFFFFFFFFF;
						partAiBe = partAe & partBe;
						partAuBe = partAe | partBe;
						
						if(partAiBe != 0x0)
						{
							partAiB = g.tab[partAiBe-1]->e;	
						}
						partAuB = g.tab[partAuBe-1]->e;
						
						// ranks			
						rankMinA = rankMin(g.tab[i]->e);
						rankMaxA = rankMax(g.tab[i]->e);
						rankMinB = rankMin(g.tab[j]->e);
						rankMaxB = rankMax(g.tab[j]->e);
						
						if(partAiBe != 0x0)
						{
							rankMinAiB = rankMin(g.tab[partAiBe-1]->e);
							rankMaxAiB = rankMax(g.tab[partAiBe-1]->e);
						}
						else
						{
							rankMinAiB = 0;
							rankMaxAiB = 0;
						}
						rankMinAuB = rankMin(g.tab[partAuBe-1]->e);
						rankMaxAuB = rankMax(g.tab[partAuBe-1]->e);
						
						//rules
						
						if(incl(partA,partB) && rankMinA > rankMinB)
						{
							if(rankMinA > rankMaxB)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partAe-1]);
							l = addList(l,g.tab[partBe-1]);
							n = addNode(l,setMin(partB,rankMinA),5);
							g.tab[partBe-1] = n;
							g.tab[partBe-1]->color = loopNumber+2;
							
							//~ rankMinB = rankMin(g.tab[partBe-1]->e);
							//~ rankMinAuB = rankMin(g.tab[partAuBe-1]->e);
							//~ if(partAiBe != 0x0)
							//~ {
								//~ rankMinAiB = rankMin(g.tab[partAiBe-1]->e);
							//~ }
							
							variation = 1;
							decr++;
							
							if(debug)
							printf("rule 5 : incl(partA,partB) && rankMinA > rankMinB ! i : %d j : %d \n",i,j);
							
						}
						
						if(incl(partA,partB) && rankMaxB < rankMaxA)
						{
							if(rankMaxB < rankMinA)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partBe-1]);
							l = addList(l,g.tab[partAe-1]);
							n = addNode(l,setMax(partA,rankMaxB),6);
							g.tab[partAe-1] = n;
							g.tab[partAe-1]->color = loopNumber+2;
							
							//~ rankMaxA = rankMax(g.tab[partAe-1]->e);
							//~ rankMaxAuB = rankMax(g.tab[partAuBe-1]->e);
							//~ if(partAiBe != 0x0)
							//~ {
								//~ rankMaxAiB = rankMax(g.tab[partAiBe-1]->e);
							//~ }
							
							variation = 1;
							decr++;

							if(debug)
							printf("rule 6 : incl(partA,partB) && rankMaxB < rankMaxA ! i : %d j : %d \n",i,j);
							
						}
						
						computeM3 = rankMaxA + rankMaxB - rankMinAiB;
						if(rankMaxAuB > computeM3)
						{
							if(computeM3 < rankMinAuB)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partAe-1]);
							l = addList(l,g.tab[partBe-1]);
							if(partAiBe != 0x0)
							{
								l = addList(l,g.tab[partAiBe-1]);
							}
							l = addList(l,g.tab[partAuBe-1]);
							n = addNode(l,setMax(partAuB,computeM3),1);
							g.tab[partAuBe-1] = n;
							g.tab[partAuBe-1]->color = loopNumber+2;
							
							//~ rankMaxA = rankMax(g.tab[partAe-1]->e);
							//~ rankMaxB = rankMax(g.tab[partBe-1]->e);
							//~ rankMaxAuB = rankMax(g.tab[partAuBe-1]->e);
							//~ if(partAiBe != 0x0)
							//~ {
								//~ rankMaxAiB = rankMax(g.tab[partAiBe-1]->e);
							//~ }
							
							variation = 1;
							sub++;

							if(debug)
							printf("rule 1 : rankMaxA + rankMaxB - rankMinAiB ! i : %d j : %d \n",i,j);
							
						}
						
						computeM3 = rankMinAuB + rankMinAiB - rankMaxB;	
						if(rankMinA < computeM3)
						{
							if(computeM3 > rankMaxA)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partAuBe-1]);
							if(partAiBe != 0x0)
							{
								l = addList(l,g.tab[partAiBe-1]);
							}
							l = addList(l,g.tab[partBe-1]);
							l = addList(l,g.tab[partAe-1]);
							n = addNode(l,setMin(partA,computeM3),2);
							g.tab[partAe-1] = n;
							g.tab[partAe-1]->color = loopNumber+2;

							//~ rankMinA = rankMin(g.tab[partAe-1]->e);
							//~ rankMinAuB = rankMin(g.tab[partAuBe-1]->e);
							//~ if(partAiBe != 0x0)
							//~ {
								//~ rankMinAiB = rankMin(g.tab[partAiBe-1]->e);
							//~ }
							
							variation = 1;
							sub++;

							if(debug)
							printf("rule 2 : rankMinAuB + rankMinAiB - rankMaxB ! i : %d j : %d \n",i,j);
			
						}
						
						computeM3 = rankMaxA + rankMaxB - rankMinAuB;
						if(rankMaxAiB > computeM3)
						{
							if(computeM3 < rankMinAiB)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							if(partAiBe != 0x0)
							{
								
								l = createList(g.tab[partAe-1]);
								l = addList(l,g.tab[partBe-1]);
								l = addList(l,g.tab[partAuBe-1]);
								l = addList(l,g.tab[partAiBe-1]);
								n = addNode(l,setMax(partAiB,computeM3),3);
								g.tab[partAiBe-1] = n;
								g.tab[partAiBe-1]->color = loopNumber+2;
								
								//~ rankMinA = rankMin(g.tab[partAe-1]->e);
								//~ rankMinB = rankMin(g.tab[partBe-1]->e);
								//~ rankMinAuB = rankMin(g.tab[partAuBe-1]->e);
								//~ if(partAiBe != 0x0)
								//~ {
									//~ rankMinAiB = rankMin(g.tab[partAiBe-1]->e);
								//~ }
								
								variation = 1;
								sub++;

								if(debug)
								printf("rule 3 : rankMaxA + rankMaxB - rankMinAuB ! i : %d j : %d \n",i,j);
										
							}	
						}
						
						computeM3 = rankMinAuB + rankMinAiB - rankMaxA;
						if(rankMinB < computeM3)
						{	
							if(computeM3 > rankMaxB)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partAuBe-1]);
							if(partAiBe != 0x0)
							{
								l = addList(l,g.tab[partAiBe-1]);
							}
							l = addList(l,g.tab[partAe-1]);
							l = addList(l,g.tab[partBe-1]);
							n = addNode(l,setMin(partB,computeM3),4);
							g.tab[partBe-1] = n;
							g.tab[partBe-1]->color = loopNumber+2;
							
							//~ rankMinB = rankMin(g.tab[partBe-1]->e);
							//~ rankMinAuB = rankMin(g.tab[partAuBe-1]->e);
							//~ if(partAiBe != 0x0)
							//~ {
								//~ rankMinAiB = rankMin(g.tab[partAiBe-1]->e);
							//~ }
							
							variation = 1;
							sub++;

							if(debug)
							printf("rule 4 : rankMinAuB + rankMinAiB - rankMaxA ! i : %d j : %d \n",i,j);
							
						}
						
						//~ g = applyPappusParties(g,i,j,convergence,loopNumber);
						//~ 
						//~ if(*convergence == 1) variation = 1;
						//~ 
						//~ *convergence = 0;

						//~ if(incl(partB,partA) && rankMinB > rankMinA)
						//~ {
							//~ l = createList(g.tab[partBe-1]);
							//~ l = addList(l,g.tab[partAe-1]);
							//~ n = addNode(l,setMin(partA,rankMinB),7);
							//~ g.tab[partAe-1] = n;
							//~ g.tab[partAe-1]->color = loopNumber+2;
							//~ 
							//~ variation = 1;
							//~ 
							//~ if(debug)
							//~ printf("rule 7 : incl(partB,partA) && rankMinB > rankMinA ! i : %d j : %d \n",i,j);
							//~ 
						//~ }

						//~ if(incl(partB,partA) && rankMaxA < rankMaxB)
						//~ {
							//~ l = createList(g.tab[partAe-1]);
							//~ l = addList(l,g.tab[partBe-1]);
							//~ n = addNode(l,setMax(partB,rankMaxA),8);
							//~ g.tab[partBe-1] = n;
							//~ g.tab[partBe-1]->color = loopNumber+2;
							//~ 
							//~ variation = 1;
							//~ 
							//~ if(debug)
							//~ printf("rule 8 : incl(partB,partA) && rankMaxA < rankMaxB ! i : %d j : %d \n",i,j);
							//~ 
						//~ }
					}
				}
			}
			
			if(print)
			{
				printGraphWithoutProof(g);
				printf("\n");
			}
			
			loopNumber++;
			fprintf(stderr,"Loop number : %d\n",loopNumber);
		}
		
		//~ if(rankMax(g.tab[res]->e)==rankMin(g.tab[res]->e))
		//~ {
			//~ return g;
		//~ }

		// g = applyPappus(g,convergence,loopNumber);

		// pappusNumber++;
		// fprintf(stderr,"Pappus test : %d\n",pappusNumber);
		
		if(*convergence == 1) variation = 1;
	}
	
	fprintf(stderr,"Decr vs Sub : %d %d\n",decr,sub);
	
	return g;
}

/*----------------------------------------------------------------------------------------------*
*																								*
*	Gestion de la règle de Pappus :																*
*  La gestion de la règle de Pappus dont l'application se fait en dehors des boucles d'			*
*  actualisation des rangs avec essentiellement les règles d'inclusion et de sous-modularité,	*
*  est fondée sur les 4 fonctions suivantes :													*
*																								*
*     - graph applyPappusParties (graph g, int i, int j, int * convergence, int loopNumber)		*
*																								*
*     - graph applyPappus (graph g, int * convergence, int loopNumber)							*
*																								*
*      - myType existPappusConfiguration														*
*                (graph g, myType e1, myType e2, myType e3, myType e4, myType e5, myType e6)	*
*																								*
*																								*
*      - myType existIntersectPoint(graph g, myType e1, myType e2)								*
* les fonctions plus bas recensent tous les cas possibles ... elles sont très longues			*
*																								*
*_______________________________________________________________________________________________*/



graph applyPappusParties (graph g, int i, int j, int * convergence, int loopNumber) {

	myType partI,partJ,partIuJ,partIiJ;
	myType e1,e2,e3,e4,e5,e6;
	myType conf = 0x0;
	myType i1,i2,i3,tmp;
	
	list l;
	node n;
	
	partI = g.tab[i]->e & 0x3FFFFFFFFFFFFFF;
	if(countBytes(partI) == 3 && rankMinMaxEqual(g.tab[i]->e,2))
	{

		partJ = g.tab[j]->e & 0x3FFFFFFFFFFFFFF;
		partIiJ = partI & partJ;
		partIuJ = partI | partJ;
		if(countBytes(partJ) == 3 && rankMinMaxEqual(g.tab[j]->e,2) && partIiJ == 0x0 && rankMin(g.tab[partIuJ-1]->e) >= 3)
		{
			e1 = getIBytes(partI,1);
			e2 = getIBytes(partI,2);
			e3 = getIBytes(partI,3);
			e4 = getIBytes(partJ,1);
			e5 = getIBytes(partJ,2);
			e6 = getIBytes(partJ,3);
			
			// Configuration 1 
			i1 = existIntersectPoint(g,(e1|e5),(e2|e4));
			i2 = existIntersectPoint(g,(e1|e6),(e3|e4));
			i3 = existIntersectPoint(g,(e2|e6),(e3|e5));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e5 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e4 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e6 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e6 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
					
			// Configuration 2 
			i1 = existIntersectPoint(g,(e1|e6),(e2|e4));
			i2 = existIntersectPoint(g,(e1|e5),(e3|e4));
			i3 = existIntersectPoint(g,(e2|e5),(e3|e6));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e6 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e4 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e5 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e5 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
					
			// Configuration 3 
			i1 = existIntersectPoint(g,(e1|e4),(e2|e5));
			i2 = existIntersectPoint(g,(e1|e6),(e3|e5));
			i3 = existIntersectPoint(g,(e2|e6),(e3|e4));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e4 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e6 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e6 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
					
			// Configuration 4 
			i1 = existIntersectPoint(g,(e1|e6),(e2|e5));
			i2 = existIntersectPoint(g,(e1|e4),(e3|e5));
			i3 = existIntersectPoint(g,(e2|e4),(e3|e6));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e6 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e4 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e4 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
					
			// Configuration 5
			i1 = existIntersectPoint(g,(e1|e4),(e2|e6));
			i2 = existIntersectPoint(g,(e1|e5),(e3|e6));
			i3 = existIntersectPoint(g,(e2|e5),(e3|e4));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e4 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e5 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e5 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
					
			// Configuration 6 
			i1 = existIntersectPoint(g,(e1|e5),(e2|e6));
			i2 = existIntersectPoint(g,(e1|e4),(e3|e6));
			i3 = existIntersectPoint(g,(e2|e4),(e3|e5));
			
			if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
			{
				conf = i1 | i2 | i3;
			}
			if(conf != 0x0)
			{
				if(!rankMinMaxEqual(g.tab[conf-1]->e,2))
				{
					*convergence = 1;
					
					l = createList(g.tab[partI-1]);
					l = addList(l,g.tab[partJ-1]);
					
					tmp = e1 | e5 | i1;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6 | i1;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e4 | i2;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6 | i2;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e2 | e4 | i3;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6 | i3;
					l = addList(l,g.tab[tmp-1]);
					
					tmp = e1 | e2;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e3;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e4;
					l = addList(l,g.tab[tmp-1]);	
					tmp = e1 | e5;
					l = addList(l,g.tab[tmp-1]);			
					tmp = e1 | e6;
					l = addList(l,g.tab[tmp-1]);				
					tmp = e2 | e3;
					l = addList(l,g.tab[tmp-1]);							
					tmp = e2 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e2 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e4;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e3 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e5;
					l = addList(l,g.tab[tmp-1]);
					tmp = e4 | e6;
					l = addList(l,g.tab[tmp-1]);
					tmp = e5 | e6;
					l = addList(l,g.tab[tmp-1]);
					
					n = addNode(l,setMinMax(conf,2,2),9);
					g.tab[conf-1] = n;
					g.tab[conf-1]->color = loopNumber+1;	
		
				}
			}
		}
	}
	return g;
}


/*______________________________________________________________________________


##  fonction applyPappus(graph g, int * convergence, int loopNumber)

________________________________________________________________________________*/
graph applyPappus (graph g, int * convergence, int loopNumber) {
	
	int i, j;
	
	myType partI,partJ,partIuJ,partIiJ;
	
	for(i = 0; i < g.effectiveSize; i++)
	{
		partI = g.tab[i]->e & 0x3FFFFFFFFFFFFFF;
		if(countBytes(partI) == 3 && rankMinMaxEqual(g.tab[i]->e,2))
		{
			for(j = i+1; j < g.effectiveSize; j++)
			{
				partJ = g.tab[j]->e & 0x3FFFFFFFFFFFFFF;
				partIiJ = partI & partJ;
				partIuJ = partI | partJ;
				if(countBytes(partJ) == 3 && rankMinMaxEqual(g.tab[j]->e,2) && partIiJ == 0x0 && rankMin(g.tab[partIuJ-1]->e) >= 3)
				{
					applyPappusParties(g,i,j,convergence,loopNumber);
				}
			}
		}
	}
	return g;
}

/*______________________________________________________________________________


##  fonction existPappusConfiguration()

________________________________________________________________________________*/
myType existPappusConfiguration(graph g, myType e1, myType e2, myType e3, myType e4, myType e5, myType e6) {
	myType i1,i2,i3;
	myType i = 0x0;
	
	i1 = existIntersectPoint(g,(e1|e5),(e2|e4));
	i2 = existIntersectPoint(g,(e1|e6),(e3|e4));
	i3 = existIntersectPoint(g,(e2|e6),(e3|e5));
	
	if(i1 != 0x0 && i2 != 0x0 && i3 != 0x0)
	{
		i = i1 | i2 | i3;
	}
	
	return i;
}


/*______________________________________________________________________________


##  fonction existIntersectPoint()

________________________________________________________________________________*/
myType existIntersectPoint(graph g, myType e1, myType e2) {
	int i;
	myType mask, res = 0x0;
	myType me1,me2;
	int rke1,rke2;
	
	for(i = realSizemyType-1; i >= 0 && res == 0x0; i--)
	{
		if(i <= g.effectiveAllocPow-1)
		{
			mask = 1ull << i;
			if(((e1 | e2) & mask) == 0x0)
			{
				me1 = e1 | mask;
				me2 = e2 | mask;
				
				rke1 = rankMinMaxEqual(g.tab[me1-1]->e,2);
				rke2 = rankMinMaxEqual(g.tab[me2-1]->e,2);
				
				if(rke1 & rke2)
				{
					res = mask;
				}
			}
		}
	}
	return res;
}


/*************************************************************************************************/

/*__________________________________fin Pappus___________________________________________________*/

/*************************************************************************************************/




/*----------------------------------------------------------------------------------------------*
* ## Section sur la construction du graphe de déduction											*
*  Celle-ci comprend les fonctions suivantes													*
*																								*
	- void preMark(node n)																		*
	- void unMark(node n)																		*
	- void constructLemma(FILE* file, graph g, node n)											*
	- void constructIntro(FILE* file, graph g)													*
	- void constructProof (FILE* file, node n, allocSize stab, int previousConstruct)			*
	- void constructProofaux 																	*
			(FILE* file, node n, myType res, allocSize stab, int previousConstruct)				*
*																								*
*_______________________________________________________________________________________________*/
/************************************************************************************************/

void preMark(node n) {
	if(n->mark == 0)
	{
		n->mark = 1;
	}
	if(n->ante != NULL)
	{
		list tmp = n->ante;
		while(tmp != NULL)
		{
			//~ if(tmp->n->mark == 0)
			//~ {
				preMark(tmp->n);
			//~ }
			tmp = tmp->next;
		}
	}
}

void unMark(node n) {
	if(n->mark <= 3)
	{
		n->mark = 0;
	}
	if(n->ante != NULL)
	{
		list tmp = n->ante;
		while(tmp != NULL)
		{
			//~ if(tmp->n->mark != 0)
			//~ {
				unMark(tmp->n);
			//~ }
			tmp = tmp->next;
		}
	}
}


/*----------------------------------------------------------------------------------*
*           construcLemma                                    						*
*     g est le graphe correspondant à une couche             						*
*																					*
*    modifications :																*
*   (1) PS 27/09/20 pour filtrer les lemmes inutiles								*
*     la modification consiste à écrire temporairment dans une chaîne				*
*     de caractères (local_buffer) pour contrôler si 								*
*      - la conclusion ne contient le rang que d'un seul point						*
*      - la conclusion est comprise dans les hypothèses								*
*     la fonction renvoie maintenant un booléen :									*
*      - s'il est vrai, on a effectivement écrit l'énoncé du lemme					*
*      - s'il est faux, on n'a rien écrit : il ne faut pas écrire de preuve			*
*		(ce qui est fait dans une autre fonction)									*
*___________________________________________________________________________________*/
bool constructLemma(FILE* file, graph g, node n, int couche) {
	int i;
	int cpt = 0;
	myType partA, partAe, partB, partBe;
	int rankMinA, rankMaxA, rankB;
	// modif PS : 27 septembre 2020
	char *local_buffer = (char *)calloc(5000,sizeof(char));
	char *pos = local_buffer;
	// <--PS
	partA = n->e;
	partAe = partA & 0x3FFFFFFFFFFFFFF;

	rankMinA = rankMin(partA);
	rankMaxA = rankMax(partA);
	if(rankMin(partA) != rankMax(partA))
	{
		fprintf(stderr,"Attention rangs non identiques pour le résultat\n");
	}
	pos += sprintf(pos,"Lemma L"); // modif 27/09/20 : avant il y avait un fprintf()
	pos = printHypSetString(pos, partAe);   //  idem PS 27/09/20
											//  la fonction printHypStFile a été réécrite plus bas
	pos += sprintf(pos," : forall ");	    //  idem PS 27/09/20
	//<--PS
	for(i = 0; i < g.effectiveAllocPow; i++)
	{
		pos += sprintf(pos,"P%d ",i+1);		// idem PS 27/09/20
	}
												// Ainsi, 
	pos += sprintf(pos,",\n");					// tous les points du graphe sont quantifiés universellement
	
	for(i = 0; i < g.effectiveSize; i++)
	{
		if(g.tab[i]->color == -1)
		{			
			cpt++;
			
			if (g.tab[i]->e == n->e) { 	// idem PS 27/09/20 : brutal !		
				// si g.tab[i]->e == n->e, il n'est pas utile d'écrire
				// le lemme ni la preuve
				fprintf(file,"(* Lemme pas écrit (couche %d) *) \n", couche);	// TODO : couche
				free(local_buffer);
				return 0;             
			}
		// sinon, on continue l'écriture dans le buffer tant que la boucle n'est pas finie
			partB = g.tab[i]->e;		 
			                            
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			rankB = rankMin(partB);
			
			if(rankMin(partB) != rankMax(partB))
			{
				fprintf(stderr,"Reconstruction impossible rangs des hypothèses non identiques\n");
				exit(1);
			}
			
			pos += sprintf(pos,"rk(");			// idem PS 27/09/20
			pos = printSetString(pos,partBe);  // idem PS 27/09/20
			if(cpt == 3)
			{
				pos += sprintf(pos," nil) = %d ->\n",rankB);
				cpt = 0;
			}
			else
			{
				pos += sprintf(pos," nil) = %d -> ",rankB);
			}
		}
	}
	*pos = '\n'; // pour finir la chaîne ... ça aurait du être fait pas sprintf(...) 
	 //--------------------------------------------------------------------------
	 // écriture effective du lemme dans le fichier
	// PS 29/09/20 : si on arrive jusqu'ici, on écrit tout le buffer
	//               dans le fichier <file>
	//               et l'écriture se continuera dans ce fichier
	fprintf(file,"%s",local_buffer); 
	//<--PS

	if(rankMinA == rankMaxA)
	{
		fprintf(file,"rk(");
		printSetFile(file,partAe);
		fprintf(file," nil) = %d.\n",rankMinA);
	}
	else
	{
		if(dim >=4)
		{
			fprintf(stderr,"Reconstruction impossible rangs non identiques pour le résultat en dimension 4+\n");
			exit(1);
		}
		
		fprintf(file,"rk(");
		printSetFile(file,partAe);
		fprintf(file," nil) >= %d",rankMinA);
		fprintf(file,"/\\");
		fprintf(file,"rk(");
		printSetFile(file,partAe);
		fprintf(file," nil) <= %d.\n",rankMaxA);
	}
	free(local_buffer); 
	return 1;
}	

/*______________________________________________________________________________


##  fonction constructIntro()

________________________________________________________________________________*/
void constructIntro(FILE* file, graph g) {
	int i;
	int cpt = 0;
	myType partA, partAe;
	
	fprintf(file,"Proof.\n\nintros ");
	
	for(i = 0; i < g.effectiveAllocPow; i++)
	{
		fprintf(file,"P%d ",i+1);
	}
	
	fprintf(file,"\n");
	
	for(i = 0; i < g.effectiveSize; i++)
	{
		if(g.tab[i]->color == -1)
		{
			cpt++;
			partA = g.tab[i]->e;
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			
			fprintf(file,"H");
			printHypSetFile(file,partAe);
			
			if(cpt == 10)
			{
				fprintf(file,"eq\n");
				cpt = 0;
			}
			else
			{
				fprintf(file,"eq ");
			}
		}
	}
	
	fprintf(file,".\n");;
}

/*______________________________________________________________________________


##  fonction constructProof()
	construit la preuve d'un lemme dont l'énoncé a été écrit dans 
	un fichier par les fonctions précédentes
________________________________________________________________________________*/
void constructProof (FILE* file, node n, allocSize stab, int previousConstruct) {
	myType res = n->e & 0x3FFFFFFFFFFFFFF;
	constructProofaux(file, n, res, stab, previousConstruct);
	
	myType partA, partAe;
	int rankMinA, rankMaxA;
	
	partA = n->e;
	partAe = partA & 0x3FFFFFFFFFFFFFF;
	rankMinA = rankMin(partA);
	rankMaxA = rankMax(partA);
	
	if(dim == 3)
	{
		if(countBytes(partAe) < dim + 1)
		{
			fprintf(file,"\nassert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"M : rk(");
			printSetFile(file,partAe);
			fprintf(file," nil) <= %d) by (solve_hyps_max H",countBytes(partAe));
			printHypSetFile(file,partAe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d).\n",countBytes(partAe));
		}
		else
		{
			fprintf(file,"\nassert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"M : rk(");
			printSetFile(file,partAe);
			fprintf(file," nil) <= 4) by (apply rk_upper_dim).\n");
		}
	}
	else
	{
		fprintf(file,"\nassert(H");
		printHypSetFile(file,partAe);
		fprintf(file,"M : rk(");
		printSetFile(file,partAe);
		fprintf(file," nil) <= %d) by (solve_hyps_max H",countBytes(partAe));
		printHypSetFile(file,partAe);
		fprintf(file,"eq H");
		printHypSetFile(file,partAe);
		fprintf(file,"M%d).\n",countBytes(partAe));
	}
	
	fprintf(file,"assert(H");
	printHypSetFile(file,partAe);
	fprintf(file,"m : rk(");
	printSetFile(file,partAe);
	fprintf(file," nil) >= %d) by (solve_hyps_min H",1);
	printHypSetFile(file,partAe);
	fprintf(file,"eq H");
	printHypSetFile(file,partAe);
	fprintf(file,"m%d).\n",1);
	
	if(rankMinA == rankMaxA)
	{
		fprintf(file,"intuition.\nQed.\n\n");
	}
	else
	{
		fprintf(file,"split. intuition. intuition. \nQed.\n\n");
	}
}

/*______________________________________________________________________________


##  fonction constructProofaux()

________________________________________________________________________________*/
void constructProofaux (FILE* file, node n, myType res, allocSize stab, int previousConstruct) {
	
	int i,j;
	int stabb = 1;
	myType partA, partB, partAiB, partAuB, partAe, partBe, partAiBe, partAuBe;
	int rankMinA, rankMaxA, rankMinB, rankMaxB, rankMinAiB, rankMaxAiB, rankMinAuB, rankMaxAuB;
	int freeA, freeB, freeAuB, freeAiB;
	
	if(n->ante != NULL)
	{
		list tmp = n->ante;
		while(tmp != NULL)
		{
			if(tmp->n->mark == 1)
			{
				tmp->n->mark = 2;
				constructProofaux(file, tmp->n, res, stab, previousConstruct);
			}
			tmp = tmp->next;
		}
		
		n->mark = 3;
		
		if(n->rule == 1)
		{
			//sets + ranks
			
			partAuB = n->e;
			partA = n->ante->n->e;
			freeA = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			partB = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			
			if(n->ante->next->next->next !=NULL)
			{
				partAiB = n->ante->next->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeAuB = checkGenealogie(n->ante->next->next->next->n); //checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				//oldPart = n->ante->next->next->n->e;
				freeAuB = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
			}
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			if(n->ante->next->next->next !=NULL)
			{
				partAiBe = partAiB & 0x3FFFFFFFFFFFFFF;
			}
			else
			{
				partAiBe = 0x0;
			}
			partAuBe = partAuB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			if(partAiB != 0x0)
			{
				rankMinAiB = rankMin(partAiB);
				rankMaxAiB = rankMax(partAiB);
			}
			else
			{
				rankMinAiB = 0;
				rankMaxAiB = 0;
			}
			rankMinAuB = rankMin(partAuB);
			rankMaxAuB = rankMax(partAuB);
			//oldRankMax = rankMax(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"M%d : rk(",rankMaxAuB);
			printSetFile(file,partAuBe);
			fprintf(file,"nil) <= %d).\n",rankMaxAuB);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}	
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
			printHypSetFile(file,partAe); 
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d).\n",rankMaxA);
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}	

			fprintf(file,"\tassert(H");
			printHypSetFile(file,partBe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
			printHypSetFile(file,partBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d).\n",rankMaxB);

			if(partAiB != 0x0)
			{
				if(previousConstruct)
				{
					fprintf(file,"\ttry assert(H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) = %d) by (apply L",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file," with ");
					
					for(j = 0; j < stab.size && stabb; j++)
					{
						if(partAiBe <= stab.tab[j][1])
						{
							for(i = 0; i < stab.tab[j][0]; i++)
							{
								fprintf(file,"(P%d := P%d) ",i+1,i+1);
							}
							fprintf(file,";try assumption).\n");
							stabb = 0;
						}
					}
					stabb = 1;
				}	
				
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAiBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m%d).\n",rankMinAiB);
			}
			else
			{
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				fprintf(file,"nil) >= %d) by (solve_hyps_min Hnul",0);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m).\n");
			}
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) (list_inter (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (repeat clear_all_rk;my_inO).\n");
			
			fprintf(file,"\tassert(HT1 : equivlist (");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (clear_all_rk;my_inO).\n");
						
			fprintf(file,"\tassert(HT2 : equivlist (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil) ((");
			printSetFile(file,partAe);
			fprintf(file,"nil) ++ (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (clear_all_rk;my_inO).\n");

			fprintf(file,"\tassert(HT := rule_1 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) %d %d %d H",rankMaxA,rankMaxB,rankMinAiB);
			printHypSetFile(file,partAe);
			fprintf(file,"Mtmp H");
			printHypSetFile(file,partBe);
			fprintf(file,"Mtmp H");
			printHypSetFile(file,partAiBe);
			fprintf(file,"mtmp Hincl);\n");
			fprintf(file,"\trewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAiB == 1 && partAiBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAuB == 1 && partAuBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 2)
		{
			//sets + ranks
			partA = n->e;
			partAuB = n->ante->n->e;
			freeAuB = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			if(n->ante->next->next->next !=NULL)
			{
				partAiB = n->ante->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
				partB = n->ante->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeA = checkGenealogie(n->ante->next->next->next->n); //checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				partB = n->ante->next->n->e;
				freeB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
				//oldPart = n->ante->next->next->n->e;
				freeA = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
			}
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			if(n->ante->next->next->next !=NULL)
			{
				partAiBe = partAiB & 0x3FFFFFFFFFFFFFF;
			}
			else
			{
				partAiBe = 0x0;
			}
			partAuBe = partAuB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			if(partAiB != 0x0)
			{
				rankMinAiB = rankMin(partAiB);
				rankMaxAiB = rankMax(partAiB);
			}
			else
			{
				rankMinAiB = 0;
				rankMaxAiB = 0;
			}
			rankMinAuB = rankMin(partAuB);
			rankMaxAuB = rankMax(partAuB);
			//oldRankMin = rankMin(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"m%d : rk(",rankMinA);
			printSetFile(file,partAe);
			fprintf(file,"nil) >= %d).\n",rankMinA);
			fprintf(file,"{\n");

			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}

			fprintf(file,"\tassert(H");
			printHypSetFile(file,partBe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
			printHypSetFile(file,partBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d).\n",rankMaxB);
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) = %d) by (apply L",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAuBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAuBe); 
			fprintf(file,"mtmp : rk(");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
			printHypSetFile(file,partAuBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"m%d).\n",rankMinAuB);
			
			if(partAiB != 0x0)
			{
				if(previousConstruct)
				{
					fprintf(file,"\ttry assert(H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) = %d) by (apply L",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file," with ");
					
					for(j = 0; j < stab.size && stabb; j++)
					{
						if(partAiBe <= stab.tab[j][1])
						{
							for(i = 0; i < stab.tab[j][0]; i++)
							{
								fprintf(file,"(P%d := P%d) ",i+1,i+1);
							}
							fprintf(file,";try assumption).\n");
							stabb = 0;
						}
					}
					stabb = 1;
				}
				
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAiBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m%d).\n",rankMinAiB);
			}
			else
			{
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				fprintf(file,"nil) >= %d) by (solve_hyps_min Hnul",0);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m).\n");
			}
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) (list_inter (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (repeat clear_all_rk;my_inO).\n");
			
			fprintf(file,"\tassert(HT1 : equivlist (");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (clear_all_rk;my_inO).\n");
						
			fprintf(file,"\tassert(HT2 : equivlist (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil) ((");
			printSetFile(file,partAe);
			fprintf(file,"nil) ++ (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (clear_all_rk;my_inO).\n");
			
			fprintf(file,"\ttry rewrite HT1 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp;try rewrite HT2 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp.\n");
			
			fprintf(file,"\tassert(HT := rule_2 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) %d %d %d H",rankMinAuB,rankMinAiB,rankMaxB);
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp H");
			printHypSetFile(file,partAiBe);
			fprintf(file,"mtmp H");
			printHypSetFile(file,partBe);
			fprintf(file,"Mtmp Hincl);apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAiB == 1 && partAiBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAuB == 1 && partAuBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 3)
		{	
			//sets + ranks 
			partAiB = n->e;
			partA = n->ante->n->e;
			freeA = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			partB = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			partAuB = n->ante->next->next->n->e;
			freeAuB = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
			if(n->ante->next->next->next !=NULL)
			{
				//oldPart = n->ante->next->next->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->next->next->n); //checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				freeAiB = 0;
			}
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			partAuBe = partAuB & 0x3FFFFFFFFFFFFFF;
			partAiBe = partAiB & 0x3FFFFFFFFFFFFFF;

			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			rankMinAiB = rankMin(partAiB);
			rankMaxAiB = rankMax(partAiB);
			rankMinAuB = rankMin(partAuB);
			rankMaxAuB = rankMax(partAuB);
			if(n->ante->next->next->next !=NULL)
			{
				//oldRankMax = rankMax(oldPart);
			}
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAiBe);
			fprintf(file,"M%d : rk(",rankMaxAiB);
			printSetFile(file,partAiBe);
			fprintf(file,"nil) <= %d).\n",rankMaxAiB);
			fprintf(file,"{\n");
		
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}

			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
			printHypSetFile(file,partAe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d).\n",rankMaxA);
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partBe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
			printHypSetFile(file,partBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d).\n",rankMaxB);
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) = %d) by (apply L",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAuBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}

			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAuBe); 
			fprintf(file,"mtmp : rk(");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
			printHypSetFile(file,partAuBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"m%d).\n",rankMinAuB);

			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) (list_inter (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (repeat clear_all_rk;my_inO).\n");
			
			fprintf(file,"\tassert(HT1 : equivlist (");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (clear_all_rk;my_inO).\n");
						
			fprintf(file,"\tassert(HT2 : equivlist (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil) ((");
			printSetFile(file,partAe);
			fprintf(file,"nil) ++ (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (clear_all_rk;my_inO).\n");
			
			fprintf(file,"\ttry rewrite HT1 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp;try rewrite HT2 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp.\n");
			
			fprintf(file,"\tassert(HT := rule_3 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) %d %d %d H",rankMaxA,rankMaxB,rankMinAuB);
			printHypSetFile(file,partAe);
			fprintf(file,"Mtmp H");
			printHypSetFile(file,partBe);
			fprintf(file,"Mtmp H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp Hincl);apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAiB == 1 && partAiBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAuB == 1 && partAuBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 4)
		{
			//sets + ranks 
			partB = n->e;
			partAuB = n->ante->n->e;
			freeAuB = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			
			if(n->ante->next->next->next !=NULL)
			{
				partAiB = n->ante->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
				partA = n->ante->next->next->n->e;
				freeA = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->next->n); //checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				partA = n->ante->next->n->e;
				freeA = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
				//oldPart = n->ante->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->n); //checkSuccList(n->ante->next->next->n->succ);
			}
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			if(n->ante->next->next->next !=NULL)
			{
				partAiBe = partAiB & 0x3FFFFFFFFFFFFFF;
			}
			else
			{
				partAiBe = 0x0;
			}
			partAuBe = partAuB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			if(partAiB != 0x0)
			{
				rankMinAiB = rankMin(partAiB);
				rankMaxAiB = rankMax(partAiB);
			}
			else
			{
				rankMinAiB = 0;
				rankMaxAiB = 0;
			}
			rankMinAuB = rankMin(partAuB);
			rankMaxAuB = rankMax(partAuB);
			//oldRankMin = rankMin(oldPart);
			
			// export
			fprintf(file,"\n");

			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"m%d : rk(",rankMinB);
			printSetFile(file,partBe);
			fprintf(file,"nil) >= %d).\n",rankMinB);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}

			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
			printHypSetFile(file,partAe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d).\n",rankMaxA);
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) = %d) by (apply L",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAuBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAuBe); 
			fprintf(file,"mtmp : rk(");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
			printHypSetFile(file,partAuBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"m%d).\n",rankMinAuB);
			
			if(partAiB != 0x0)
			{
				if(previousConstruct)
				{
					fprintf(file,"\ttry assert(H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) = %d) by (apply L",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file," with ");
					
					for(j = 0; j < stab.size && stabb; j++)
					{
						if(partAiBe <= stab.tab[j][1])
						{
							for(i = 0; i < stab.tab[j][0]; i++)
							{
								fprintf(file,"(P%d := P%d) ",i+1,i+1);
							}
							fprintf(file,";try assumption).\n");
							stabb = 0;
						}
					}
					stabb = 1;
				}
				
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAiBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m%d).\n",rankMinAiB);
			}
			else
			{
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAiBe); 
				fprintf(file,"mtmp : rk(");
				fprintf(file,"nil) >= %d) by (solve_hyps_min Hnul",0);
				printHypSetFile(file,partAiBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAiBe);
				fprintf(file,"m).\n");;
			}
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) (list_inter (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (repeat clear_all_rk;my_inO).\n");
			
			fprintf(file,"\tassert(HT1 : equivlist (");
			printSetFile(file,partAuBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (clear_all_rk;my_inO).\n");
						
			fprintf(file,"\tassert(HT2 : equivlist (");
			printSetFile(file,partAe);
			printSetFile(file,partBe);
			fprintf(file,"nil) ((");
			printSetFile(file,partAe);
			fprintf(file,"nil) ++ (");
			printSetFile(file,partBe);
			fprintf(file,"nil))) by (clear_all_rk;my_inO).\n");
			
			fprintf(file,"\ttry rewrite HT1 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp;try rewrite HT2 in H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp.\n");
			
			fprintf(file,"\tassert(HT := rule_4 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAiBe);
			fprintf(file,"nil) %d %d %d H",rankMinAuB,rankMinAiB,rankMaxA);
			printHypSetFile(file,partAuBe);
			fprintf(file,"mtmp H");
			printHypSetFile(file,partAiBe);
			fprintf(file,"mtmp H");
			printHypSetFile(file,partAe);
			fprintf(file,"Mtmp Hincl); apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAiB == 1 && partAiBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAiBe);fprintf(file,"eq. ");
				}
			}
			
			if(freeAuB == 1 && partAuBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAuBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 5)
		{
			//sets + ranks 
			partB = n->e;
			partA = n->ante->n->e;
			freeA = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			//oldRankMin = rankMin(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"m%d : rk(",rankMinA);
			printSetFile(file,partBe);
			fprintf(file,"nil) >= %d).\n",rankMinA);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) = %d) by (apply L",rankMinA);
				printHypSetFile(file,partAe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
		
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAe); 
			fprintf(file,"mtmp : rk(");
			printSetFile(file,partAe);
			fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinA);
			printHypSetFile(file,partAe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"m%d).\n",rankMinA);
			
			fprintf(file,"\tassert(Hcomp : ");
			fprintf(file,"%d <= %d",rankMinA,rankMinB);
			fprintf(file,") by (repeat constructor).\n");
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (repeat clear_all_rk;my_inO).\n");
		
			fprintf(file,"\tassert(HT := rule_5 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) %d %d H",rankMinA,rankMinB);
			printHypSetFile(file,partAe);
			fprintf(file,"mtmp Hcomp Hincl);apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 6)
		{
			//sets + ranks 
			partA = n->e;
			partB = n->ante->n->e;
			freeB = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeA = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			//oldRankMax = rankMax(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d : rk(",rankMaxB);
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d).\n",rankMaxB);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partBe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
			printHypSetFile(file,partBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d).\n",rankMaxB);
			
			fprintf(file,"\tassert(Hcomp : ");
			fprintf(file,"%d <= %d",rankMaxB,rankMaxA);
			fprintf(file,") by (repeat constructor).\n");

			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil)) by (repeat clear_all_rk;my_inO).\n");
		
			fprintf(file,"\tassert(HT := rule_6 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) %d %d H",rankMaxA,rankMaxB);
			printHypSetFile(file,partBe);
			fprintf(file,"Mtmp Hcomp Hincl);apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 7)
		{
			//sets + ranks 
			partA = n->e;
			partB = n->ante->n->e;
			freeB = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeA = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			//oldRankMin = rankMin(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"m%d : rk(",rankMinB);
			printSetFile(file,partAe);
			fprintf(file,"nil) >= %d).\n",rankMinB);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partBe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) = %d) by (apply L",rankMinB);
				printHypSetFile(file,partBe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partBe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
						
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partBe); 
			fprintf(file,"mtmp : rk(");
			printSetFile(file,partBe);
			fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinB);
			printHypSetFile(file,partBe);
			fprintf(file,"eq H");
			printHypSetFile(file,partBe);
			fprintf(file,"m%d).\n",rankMinB);

			fprintf(file,"\tassert(Hcomp : ");
			fprintf(file,"%d >= %d",rankMinB,rankMinA);
			fprintf(file,") by (repeat constructor).\n");
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			fprintf(file,"nil)) by (repeat clear_all_rk;my_inO).\n");
		
			fprintf(file,"\tassert(HT := rule_7 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) %d %d H",rankMinA,rankMinB);
			printHypSetFile(file,partBe);
			fprintf(file,"mtmp Hcomp Hincl); apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			fprintf(file,"\n");
		}
		else if (n->rule == 8)
		{
			//sets + ranks 
			partB = n->e;
			partA = n->ante->n->e;
			freeA = checkGenealogie(n->ante->n); //checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); //checkSuccList(n->ante->next->n->succ);
			
			// sets
			partAe = partA & 0x3FFFFFFFFFFFFFF;
			partBe = partB & 0x3FFFFFFFFFFFFFF;
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			//oldRankMax = rankMax(oldPart);
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d : rk(",rankMaxA);
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d).\n",rankMaxA);
			fprintf(file,"{\n");
			
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,partAe);
				fprintf(file,"eq : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) = %d) by (apply L",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(partAe <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
			
			fprintf(file,"\tassert(H");
			printHypSetFile(file,partAe); 
			fprintf(file,"Mtmp : rk(");
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
			printHypSetFile(file,partAe);
			fprintf(file,"eq H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d).\n",rankMaxA);
			
			fprintf(file,"\tassert(Hcomp : ");
			fprintf(file,"%d <= %d",rankMaxA,rankMaxB);
			fprintf(file,") by (repeat constructor).\n");
			
			fprintf(file,"\tassert(Hincl : incl (");
			printSetFile(file,partBe);
			fprintf(file,"nil) (");
			printSetFile(file,partAe);
			fprintf(file,"nil)) by (repeat clear_all_rk;my_inO).\n");
		
			fprintf(file,"\tassert(HT := rule_8 (");
			printSetFile(file,partAe);
			fprintf(file,"nil) (");
			printSetFile(file,partBe);
			fprintf(file,"nil) %d %d H",rankMaxA,rankMaxB);
			printHypSetFile(file,partAe);
			fprintf(file,"Mtmp Hcomp Hincl); apply HT.\n");
			fprintf(file,"}\n");
			
			if(freeA == 1 && partAe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partAe);fprintf(file,"eq. ");
				}
			}
			
			if(freeB == 1 && partBe != res)
			{
				int tmpRankM = 1;
				while(tmpRankM <= 3)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
					tmpRankM++;
				}
				if(dim >= 4)
				{
					while(tmpRankM <= 7)
					{
						fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"M%d. ",tmpRankM);
						tmpRankM++;
					}
				}
				
				int tmpRankm;
				if(dim >= 4)
				{
					tmpRankm = 7;
				}
				else
				{
					tmpRankm = 4;
				}
				
				while(tmpRankm >= 1)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"m%d. ",tmpRankm);
					tmpRankm--;
				}
				if(!previousConstruct)
				{
					fprintf(file,"try clear H");printHypSetFile(file,partBe);fprintf(file,"eq. ");
				}
			}
			fprintf(file,"\n");
		}
		else if(n->rule == 9)
		{
			myType partP, partPe, partL1, partL1e, partL2, partL2e;
			myType partE1, partE1e, partE2, partE2e, partE3, partE3e, partE4, partE4e, partE5, partE5e, partE6, partE6e;
			myType tmp, e1,e2,e3,e4,e5,e6,e7,e8,e9;
	
			//sets + ranks 
			partP = n->e;
			partL1 = n->ante->n->e;
			partL2 = n->ante->next->n->e;
			partE1 = n->ante->next->next->n->e;
			partE2 = n->ante->next->next->next->n->e;
			partE3 = n->ante->next->next->next->next->n->e;
			partE4 = n->ante->next->next->next->next->next->n->e;
			partE5 = n->ante->next->next->next->next->next->next->n->e;
			partE6 = n->ante->next->next->next->next->next->next->next->n->e;
			
			partPe = partP & 0x3FFFFFFFFFFFFFF;
			partL1e = partL1 & 0x3FFFFFFFFFFFFFF;
			partL2e = partL2 & 0x3FFFFFFFFFFFFFF;
			partE1e = partE1 & 0x3FFFFFFFFFFFFFF;
			partE2e = partE2 & 0x3FFFFFFFFFFFFFF;
			partE3e = partE3 & 0x3FFFFFFFFFFFFFF;
			partE4e = partE4 & 0x3FFFFFFFFFFFFFF;
			partE5e = partE5 & 0x3FFFFFFFFFFFFFF;
			partE6e = partE6 & 0x3FFFFFFFFFFFFFF;
			
			e1 = getIBytes(partL1e,1);
			e2 = getIBytes(partL1e,2);
			e3 = getIBytes(partL1e,3);
			e4 = getIBytes(partL2e,1);
			e5 = getIBytes(partL2e,2);
			e6 = getIBytes(partL2e,3);
			e7 = getIBytes(partPe,1);
			e8 = getIBytes(partPe,2);
			e9 = getIBytes(partPe,3);
			
			partPe = partP & 0x3FFFFFFFFFFFFFF;
			
			// export
			fprintf(file,"\n");
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partPe);
			fprintf(file,"eq : rk(");
			printSetFile(file,partPe);
			fprintf(file,"nil) = 2).\n");
			fprintf(file,"{\n");
			
			tmp = e1 | e2;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e1 | e3;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e1 | e4;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e1 | e5;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e1 | e6;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e2 | e3;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e2 | e4;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e2 | e5;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e2 | e6;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e3 | e4;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e3 | e5;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e3 | e6;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e4 | e5;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e4 | e6;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = e5 | e6;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partL1e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partL2e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE1e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE2e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE3e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE4e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE5e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
			
			tmp = partE6e;
			if(previousConstruct)
			{
				fprintf(file,"\ttry assert(H");
				printHypSetFile(file,tmp);
				fprintf(file,"eq : rk(");
				printSetFile(file, tmp);
				fprintf(file," nil) = 2) by (apply L");
				printHypSetFile(file,tmp);
				fprintf(file," with ");
				
				for(j = 0; j < stab.size && stabb; j++)
				{
					if(tmp <= stab.tab[j][1])
					{
						for(i = 0; i < stab.tab[j][0]; i++)
						{
							fprintf(file,"(P%d := P%d) ",i+1,i+1);
						}
						fprintf(file,";try assumption).\n");
						stabb = 0;
					}
				}
				stabb = 1;
			}
	
			fprintf(file,"\ttry assert(H");
			printHypSetFile(file,tmp);
			fprintf(file,"eq : rk(");
			printSetFile(file, tmp);
			fprintf(file," nil) = 2) by (intuition).\n");
		
			fprintf(file,"\tassert(HT : rk(");
			printSetFile(file,partPe);
			fprintf(file," nil) = 2);\n");
			fprintf(file,"\tapply (rk_pappus ");
			printHypSetFile(file,e1);
			fprintf(file," ");
			printHypSetFile(file,e2);
			fprintf(file," ");
			printHypSetFile(file,e3);
			fprintf(file," ");
			printHypSetFile(file,e4);
			fprintf(file," ");
			printHypSetFile(file,e5);
			fprintf(file," ");
			printHypSetFile(file,e6);
			fprintf(file," ");
			printHypSetFile(file,e7);
			fprintf(file," ");
			printHypSetFile(file,e8);
			fprintf(file," ");
			printHypSetFile(file,e9);
			fprintf(file,");rk_couple_triple.\n");
			fprintf(file,"}\n");
			
			fprintf(file,"\n");
		}
	}
}
//*******************************************************************************
/*______________________________________________________________________________*


##  fin de la fonction constructProofaux()
	
________________________________________________________________________________*/
//*******************************************************************************




/********************************************************************************/
/*------------------------------------------------------------------------------*
*																				*
*    Fonction auxilliaires pour l'impression dans un fichier					*
*						des fonctions d'impression								*
*																				*
*_______________________________________________________________________________*/

void printSetFile (FILE* file, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if(((e >> i) & 0x1) == 1)
		{
				fprintf(file,"P%d :: ",j);
		}
		j++;
	}
}

char *printSetString (char *s, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if(((e >> i) & 0x1) == 1)
		{
				s += sprintf(s,"P%d :: ",j);
		}
		j++;
	}
	return s;
}

// remarque : c'est la même fonction que printSetFile() à un " ::" près ...
void printHypSetFile (FILE* file, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if(((e >> i) & 0x1) == 1)
		{
				fprintf(file,"P%d",j);
		}
		j++;
	}
}

char *printHypSetString (char *s, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if(((e >> i) & 0x1) == 1)
		{
				s += sprintf(s,"P%d",j);
		}
		j++;
	}
	return s;
}

void printLineGraph (graph g, int i) {
	printf("Ligne %d | ", i);printNodes(g.tab[i],1);
}

void printLineGraphWithoutProof (graph g, int i) {
	printf("Ligne %d | ", i);printNode(g.tab[i]);
}

void printGraph (graph g) {
	int i;
	for(i = 0; i < g.size; i++)
	{
		printLineGraph(g,i);
	}
}

void printGraphWithoutProof(graph g) {
	int i;
	for(i = 0; i < g.size; i++)
	{
		printLineGraphWithoutProof(g,i);
	}
}

