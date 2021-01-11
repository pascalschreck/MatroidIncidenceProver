// fichier parties.c
// créé par David Braun
// modification mineures par PS
#include "parties.h"
#include "globals.h"


/*______________________________________________________________________________

## allocSizeTab() gestion de l'allocation mémoire pour les couches
________________________________________________________________________________*/
allocSize allocSizeTab (int n, int m) {
	int i,j;
	allocSize p;
	
	p.size = n;
	p.tab = (int **)malloc(sizeof(int *)*n);
		if(p.tab == 0) {printf("erreur d'allocation dans allocSizeTab()"); exit(2);}
	
	for(i = 0; i < p.size; i++)
	{
		p.tab[i] = (int *)malloc(sizeof(int)*m);
			if(p.tab[i] == 0) {printf("erreur d'allocation dans allocSizeTab()"); exit(2);}
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
	unsigned long long i;
	graph g;
	myType init = 0x0;

	g.size =  (1ull << n); 
	g.effectiveSize = 0;
	g.allocPow = n;
	g.effectiveAllocPow = 0;
	
	node * tab = (node *)malloc(sizeof(node)*g.size);
		if(tab == 0) { printf("erreur d'allocation dans allocGraph"); exit(2);}
	
	for(i = 0; i < g.size; i++)
	{
		init = initRanks(i+1);
		tab[i] = createNode(init);
	}
	
	g.tab = tab;

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
			g2.tab[i] = createNode(g1.tab[i]->e);						//   Attention : on ne copie pas l'historique d'application des règles
																		// je ne sais pas si c'est utile ou si on retrouve les lemmes qu'il faut ....
																		// faire un copyNode() ?
			g2.tab[i]->color = g1.tab[i]->color;						// je pense que dans l'esprit de David,
		}																// quand on traverse une couche, tous ces noeuds
	}																	// ont été transcrits dans des lemmes
	return g2;															// ils n'ont plus a être mis à jour et peuvent être
	}																	// utilisés comme prémisses
																		// il faut donc faire attention dans la conception
																		// des couches que les points soient bien définis
																		// avant de passer à la couche supérieure.
																		// Peut-être qu'un copy node(avec partage des noeuds ?)
																		// pourrait rendre les choses plus robustes.

//**************************************************************************
/*---------------------------------------------------------------*
*
*	convergenceParties(g, res) :
* modifie le graphe g par effet de bord en mettant à jour minRank 
* et maxRank par application des règles issue du matroïde 
*
*_________________________________________________________________*/
graph convergenceParties (graph g, int res) {  // normalement, pour être cohérent res devrait ête de type ull

#ifdef DEBUG	
	bool debug = debug_mode ;	// par défaut, on est dans le mode donné par l'utilisateur
#endif


	bool print = false;	// mettre à 1 si ????
	
	unsigned long long i, j;    // pour correspondre au type
		
	myType partA, partB, partAiB, partAuB, partAe, partBe, partAiBe, partAuBe;
	int rankMinA, rankMaxA, rankMinB, rankMaxB, rankMinAiB, rankMaxAiB, rankMinAuB, rankMaxAuB;
	
	int convergenceValue = 1;
	int * convergence = &convergenceValue;
	int variation = 1;
	int loopNumber = 0;
	//  PS octobre 2020 : a priori, on ne va plus se servir de la règle de Pappus
	// j'ai donc commenté la déclaration suivante qui provoquait un message par le compilateur
	// .... message que j'en avais assez de voir !
	// int pappusNumber = 0;
	int computeM3 = -1;
	int decr = 0;
	int sub = 0;
	
	int colori, colorj;

	list l; // l est variable de liste qui sert à divers endroits plutôt comme varaiable temporaire
	node n; // idem pour n
		
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
			
			for(i = 0ull; i < g.effectiveSize; i++) 			// boucle sur un sommet
			{
				colori = g.tab[i]->color;
				
				for(j = i+1ull ; j < g.effectiveSize; j++)		// boucle sur le deuxième sommet
				{	
					colorj = g.tab[j]->color;
					if(colori >= loopNumber+1 || colorj >= loopNumber+1 || colori == -1 || colorj == -1)
					{
					
						// sets
						partA = g.tab[i]->e;
						partB = g.tab[j]->e;
						
						partAe = SetFrom(g.tab[i]->e);
						partBe = SetFrom(g.tab[j]->e) ;
						partAiBe = partAe & partBe;
						partAuBe = partAe | partBe;
						
						if(partAiBe != 0x0)
						{
							partAiB = g.tab[partAiBe-1]->e;		// Attention décalage pour gagner une ligne dans tab ....
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
						
						/*-----------------------------------------------------------

								règle 5
						
						-------------------------------------------------------------*/
						if(incl(partA,partB) && rankMinA > rankMinB)
						{
							if(rankMinA > rankMaxB)
							{
								fprintf(stderr,"Erreur rang minimum > rang maximum  \n");
								exit(1);
							}
							l = createList(g.tab[partAe-1]);				// 
							l = addList(l,g.tab[partBe-1]);
							n = addNode(l,setMin(partB,rankMinA),5);		// addition au titre de la règle 5
							g.tab[partBe-1] = n;
							g.tab[partBe-1]->color = loopNumber+2;
							
						
							variation = 1;
							decr++;
							#ifdef DEBUG
							if(debug){
								// printf("rule 5 : incl(partA,partB) && rankMinA > rankMinB ! i : %llu j : %llu \n",i,j);
								DEB_PS("rule 5 : incl(partA,partB) && rankMinA > rankMinB avec : ");
								NL; TAB;
								DEB_PS(" A : ");
								printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB;
								DEB_PS(" B "); 
								printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
								NL;
							}
							#endif
							
						}
						/*-----------------------------------------------------------

								règle 6
						
						-------------------------------------------------------------*/
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
							
							
							variation = 1;
							decr++;

							#ifdef DEBUG
							if(debug){
							// printf("rule 6 : incl(partA,partB) && rankMaxB < rankMaxA ! i : %llu j : %llu \n",i,j);
								DEB_PS("rule 6 : incl(partA,partB) && rankMaxB < rankMaxA avec : ");
								NL; TAB;
								DEB_PS(" A : ");
								printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB;
								DEB_PS(" B : ");
								printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
								NL;
							}
							#endif
						}
						
						computeM3 = rankMaxA + rankMaxB - rankMinAiB;
						/*-----------------------------------------------------------

								règle 1
						
						-------------------------------------------------------------*/
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
							
							
							variation = 1;
							sub++;

							#ifdef DEBUG
							if(debug){
							// printf("rule 1 : rankMaxA + rankMaxB - rankMinAiB ! i : %llu j : %llu \n",i,j);
								DEB_PS("rule 1 : rankMaxA + rankMaxB - rankMinAiB  ! i ! i (A) et j (B) : ");
								NL; TAB;
								DEB_PS(" A : ");
								printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB;
								DEB_PS(" B : ");
								printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
								NL;
							}
							#endif
						}
						
						computeM3 = rankMinAuB + rankMinAiB - rankMaxB;	
						/*-----------------------------------------------------------

								règle 2
						
						-------------------------------------------------------------*/
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


							variation = 1;
							sub++;

							#ifdef DEBUG
							if(debug){
							// printf("rule 2 : rankMinAuB + rankMinAiB - rankMaxB ! i : %llu j : %llu \n",i,j);
								DEB_PS("rule 2 : rankMinAuB + rankMinAiB - rankMaxB  ! i ! i (A) et j (B) : ");
								NL; TAB;
								DEB_PS(" A : ");
								printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB; 
								DEB_PS(" B : ");
								printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
								NL;
							}
							#endif
						}
						
						computeM3 = rankMaxA + rankMaxB - rankMinAuB;
						/*-----------------------------------------------------------

								règle 3
						
						-------------------------------------------------------------*/
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
								
								
								variation = 1;
								sub++;

								#ifdef DEBUG
								if(debug){
								// printf("rule 3 : rankMaxA + rankMaxB - rankMinAuB ! i : %llu j : %llu \n",i,j);
									DEB_PS("rule 3 : rankMaxA + rankMaxB - rankMinAuB ! i ! i (A) et j (B) : ");
									NL; TAB;
									DEB_PS(" A : ");
									printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB;
									DEB_PS(" B : ");
									printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
									NL;	
								}	
								#endif								
							}	
						}
						
						computeM3 = rankMinAuB + rankMinAiB - rankMaxA;
						/*-----------------------------------------------------------

								règle 4
						
						-------------------------------------------------------------*/
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
							
							
							variation = 1;
							sub++;

							#ifdef DEBUG
							if(debug){
							// printf("rule 4 : rankMinAuB + rankMinAiB - rankMaxA ! i : %llu j : %llu \n",i,j);
								DEB_PS("rule 4 : rankMinAuB + rankMinAiB - rankMaxA  ! i ! i (A) et j (B) : ");
								NL; TAB;
								DEB_PS(" A : ");
								printSetFile(debug_file,(myType)i); DEB_PS("nil"); TAB; 
								DEB_PS(" B : ");
								printSetFile(debug_file,(myType)j); DEB_PS("nil"); TAB;
								NL;		
							}	
							#endif			
						}
				
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
		
		
		if(*convergence == 1) variation = 1;
	}
	
	fprintf(stderr,"Decr vs Sub : %d %d\n",decr,sub);
	
	return g;
}


/*______________________________________________________________________________


##  fonction existIntersectPoint()
	conservée, mais je ne sais pas encore pourquoi
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

/*----------------------------------------------------------------------------------------------*/
//                    void preMark(node n)
// 
// marquage récursifs des antécédents d'un noeud par l'application des règles
//		tous les noeuds qui précédent dans le sens de la dépendence de la preuve
// 		le noeud <n> donné en argument sont marqués à U_NOT_WRITTEN_IN_PROOF
//  	(y compris le noeud en argument), ce qui signifie que ces noeuds sont
// 		utiles à la preuve.
//
/*----------------------------------------------------------------------------------------------*/
void preMark(node n) {		
	myType partA, partAe;
	partA = n->e;
	partAe = SetFrom(partA);

	if(n->mark == UNUSED)
	{
		n->mark = U_NOT_WRITTEN_IN_PROOF;
			//     DEBUG ---->
			if(debug_mode) {
				DEB_PS("marqué : ");
				printSetFile(debug_file,partAe); DEB_PS("nil"); NL;
			}
			//<-----DEBUG	
	}
	if(n->ante != NULL)			// à enlever lorsque la situation sera stabilisée. 
	{							// Je ne sais pas pourquoi David a écrit ça
		list tmp = n->ante;
		while(tmp != NULL)
		{
			preMark(tmp->n);	// appel récursif : tous les antécédents du résultat sont marqués
			tmp = tmp->next;
		}
	}
}

/*----------------------------------------------------------------------------------------------*/
//																								*
//     fonction unMark()																		*
// 																								*
//		Les noeuds qui ont été utilisés à l'intérieur de le démontration d'un lemme donné 		*
//		ont été marqués avec PROOF_WRITTEN_in_Lemma pour éviter que les assertiond				*
//  	d'hypothèses du style HP1P2P4P5P8eq (par exemple) se fasse plusieurs fois dans cette	*
//  	preuve locale. Cependant, ils restent éligigbles (au moins dans le cas mono-couche) à	*
//  	l'écriture de la preuve d'autres lemmes, voire à être eux-mêmes écrits comme lemmes,	*
//		ils sont donc marqués avec l'étiquette U_NOT_WRITTEN_IN_PROOF (1) par cette fonction	*
//																								*
/*----------------------------------------------------------------------------------------------*/
void unMark(node n) {		// démarquage des antécédents
	if(n->mark == PROOF_WRITTEN_in_Lemma) 
	{
		n->mark = U_NOT_WRITTEN_IN_PROOF;
	}
	if(n->ante != NULL)
	{
		list tmp = n->ante;
		while(tmp != NULL)
		{
			unMark(tmp->n);
			tmp = tmp->next;
		}
	}
}


/*------------------------------------------------------------------------------------------*
*           construcLemma                                    								*
*     g est le graphe correspondant à une couche             								*
*																							*
*    modifications :																		*
*   (1) PS 27/09/20 pour filtrer les lemmes inutiles										*
*     la modification consiste à écrire temporairment dans une chaîne						*
*     de caractères (local_buffer) pour contrôler si 										*
*      - la conclusion ne contient le rang que d'un seul point								*
*      - la conclusion est comprise dans les hypothèses										*
*     la fonction renvoie maintenant un booléen :											*
*      - s'il est vrai, on a effectivement écrit l'énoncé du lemme							*
*      - s'il est faux, on n'a rien écrit : il ne faut pas écrire de preuve					*
*		(ce qui est fait dans une autre fonction)											*
*   (2) les modifications du (1) ci-dessous sont commentées car pour qu'elles soient		*
*		utilisables il faudrait en tenir compte dans toute l'écriture de la preuve			*
*		ce qui n'a pas (encore) été fait.													*
*	(3) la fonction s'appelle récursivement pour permettre une meilleure décomposition		*
*		en lemmes, mais cela nécessite de regarder soigneusement ce qui peut être			*
*       un lemme préliminaire ou non														*
*		En particulier, le premier antécédent d'un noeud (qui correspond à la première		*
*		prémisse de la règle appliquée) est un noeud correspondant au même ensemble que		*
*       le noeud en cours de traitment mais avec un intervalle de rangs plus grand : 		*
*		c'est l'étape précédente de réduction d'intervalle de cet ensemble. En l'état, 		*
*		noeuds ne peuvent pas donner lieu à des lemmes car									*
*		  - le lemmes sont nommés d'après l'ensemble et on aurait donc plusieurs			*
*			lemmes avec le même nom															*
*		  - on aurait des lemmes avec pour conlusion un intervalle de rangs possibles		*
*			c'était autorisé par David (pour passer les couches), mais ça me paraît plus	*
*			dur à gérer avec la systématisation des lemmes.									*
*		Ces noeuds correspondants au même ensemble que le noeud courant sont appelés		*
*		les premiers fils du noeud courants à cause de la manière de coder l'arbre des		*
*		déductions pour ce noeud. Les premiers fils sont traités dans la preuve du lemme	*
*		courant par la fonction constructProofaux qui écrit leur preuve à l'aide de 		*
*		"assert" de sous-buts avec une preuve locale. Il en est de même pour tous les		*
*       antécédents des premiers fils qui auraient peut être eux mérités un lemme : ce		*
*       n'est pas fait pour le moment par peur de liens transversaux, mais je 				*
*		m'interroge encore. 																*
*	(4) on interdit explicitement l'écriture d'un lemme où le rang n'est pas défini			*
*		à la fin. De tels lemmes seront prouvés à local à chaque fois que ce sera			*
*		nécessaire. Attention, cela risque peut-être de poser des problèmes avec			*
*		l'implantation actuelle du multicouche car la fonction copyGraph() ne recopie		*
*		pas les arbres de déduction attachés aux noeuds avec l'idée qu'une couche doit		*
*		être complétement saturée avant de passer à la suivante (avec la rustine de			*
*		pouvoir utiliser des lemmes avec des intervalles de rangs en conclusion)			*
*	(5) Cette fonction appelle maintenant les deux fonctions qui dépendent d'elles			*
*		   - constructIntro() qui est un peu une constante									*
*		   - constructProof() qui écrit la preuve notamment en appelant						*
*		   	 constructProofaux() qui est la fonction la plus imporante dans cette tâche		*
*	(6) Un nouveau statut a été défini pour les noeuds :									*
*        PROOF_WRITTEN_in_Lemma (qui vaut 5) pour indiquer les noeuds qui ont donné lieu	*
*		 à une preuve locale dans un lemme, ces noeuds seront démarqués par unMark()		*
*		 qui a été modifiée dans ce sens.													*
*		 Le demarquage est appelé à la fin de la fonction constructLemma(), avant il était	*
*		 à la sortie de cette fonction mais cela a occasionné des bugs.						*
*___________________________________________________________________________________________*/

bool constructLemma(FILE* file, graph g, node n,  allocSize   sizeTab, int couche) {
	// on écrit de code dans le fichier <file>, l'énoncé correspondant qu noeud n du graphe g
	// la mention de la <couche> sert uniquement à faire des sorties informatives 



	int i;
	int cpt = 0;
	myType partA, partAe, partB, partBe;
	int rankMinA, rankMaxA, rankB;

	partA = n->e;
	partAe = SetFrom(partA);
	rankMinA = rankMin(partA);
	rankMaxA = rankMax(partA);
	// PS 26 octobre 2020-----------------------------------------------------------------------*
	// On filtre le lemmes qui n'ont pas pour conclusion une égalité de rang 					*
	// 		(au passage ça doit aussi fltrer les premiers fils)									*
	// la possibilité laissée par David pour avoir des lemmes où le rang n'est pas complément	*
	// déterminé peut être justifié par les aspects x-couches : il n'y a plus de lemmes			*
	// écrit dans la dernière couche et on ne devrait plus risquer de télescopage				*
	if(rankMinA != rankMaxA)
		{
			fprintf(stderr,"Attention rangs non identiques pour le résultat de %llu  rang min %d et rang max %d \n", 
							partAe, rankMinA, rankMaxA);
			printSetFile(stderr, partAe),
			fprintf(stderr,"\n Le traitement de la preuve en tant que Lemme n'est pas considérée.\n");
			return false;
		}
	// fin du filtrage des lemmes---------------------------------------------------------------*

	// modif PS : 27 septembre 2020	 -----------------------------------------------------------*
	// pour le moment (21 oct 2020) les deux buffers suivants ne sont pas utilisés				*
	// les pointeurs en dessous non plus. L'écriture différée de l'énoncé du Lemme				*
	// sera peut-être utiliséesi on veut éviter les lemmes triviaux								*
	// et si la nouvelle organisation ne permet pas de retader l'écriture de l'énoncé			*
	/*
	char *local_buffer = (char *)calloc(5000,sizeof(char));
	char *debug_info = (char *)calloc(500,sizeof(char));
	char *pos = local_buffer, *pos_debug = debug_info;
	*/

        /*-------------------------------------------PS-ajout-----------------------------------*/
		// on traite les sous-buts associés aux noeud antécédents comme pouvant donner lieu		*
		// à des lemmes réutilisables plus tard plutôt que des "assert" locales					*
        list tmp = n->ante;	
		n->mark = U_WAITING_FOR_PREVIOUS_PROOF;
        if(tmp != NULL)		// test conservé pour éventuellement traiter le 1er fils
		{
			// traitement du premier fils différent des autres ?								*
			// ça permettrait d'écrire plus de lemmes, mais ça semble moins robuste				*
			//constructLemma(file, g, tmp->n, sizeTab, couche, false);   
			//tmp = tmp->next;
            while(tmp != NULL)
            {
                if(tmp->n->mark == U_NOT_WRITTEN_IN_PROOF && SetFrom(tmp->n->e) != SetFrom(n->e)) 
                {   // uniquement les noeuds utiles non utilisés localement et dont l'ens. est diff. de l'ens. courant
					fprintf(file,"(* dans constructLemma(), requis par L");
					printHypSetFile(file, partAe);fprintf(file," *)\n");
                    constructLemma(file, g, tmp->n, sizeTab, couche); 
                }
                tmp = tmp->next;
            }
		}
		/*-----------------------------------------fin de l'ajout--------------------------------*/


	//////////////////////////////////////////////////////////////////////////////////////////////
	//////					Début de l'écriture du Lemme                               		  ////
	//////    on ne doit plus écrire de lemme avant la fin de la preuve    					  ////
	//////	  du lemme courant.											   					  ////
	///// 																					  ////
	//////////////////////////////////////////////////////////////////////////////////////////////
		
		// les sprintf() commentés à la suite ont été utilisés pour faire une écriture différée dans le fichier
		// Coq au moment de filtrer les Lemmes triviaux où la conclusion était dans les hypothèses
		// cela posait des problèmes dans la réutilistion de lemmes et c'est commenté pour le moment.
		//pos += sprintf(pos, "(* dans la couche %d *)\n", couche); 
		fprintf(file, "(* dans la couche %d *)\n", couche);
		// pos += sprintf(pos,"Lemma L"); // modif 27/09/20 : avant il y avait un fprintf()
		fprintf(file,"Lemma L");
		// pos_debug += sprintf(pos_debug,"Lemma L");
		// pos = printHypSetString(pos, partAe);   //  idem PS 27/09/20
		printHypSetFile(file, partAe);

					/*--------------------------------------trace---------------------------------*/
						if(trace && (partAe == traced)) {
							DEB_PS("\n\n----------------début trace------------------------------\n\n");
							fprintf(debug_file, "---> dans la couche %d : \n", couche);
							fprintf(debug_file,"Lemma L");
							printHypSetFile(debug_file, partAe);
							DEB_PS("\n----------------------------------------------\n");
						}
					/*-------------------------------------------------------------------------------*/
		
		//pos_debug = printHypSetString(pos_debug, partAe);										
		//pos += sprintf(pos," : forall ");	    		//  idem PS 27/09/20
		fprintf(file," : forall ");

		// boucle pour écrire la quantification universelle de toutes les variables 
		// (en fait, fermeture universelle par tous les points)
		for(i = 0; i < g.effectiveAllocPow; i++)
		{
			// pos += sprintf(pos,"P%d ",i+1);			// idem PS 27/09/20
			// fprintf(file,"%s ",STATEMENT->p_names[i]);  // version A B C, i au lieu de i+1
			fprintf(file,"P%d ",i+1);						// version Pi
		} 
														// Ainsi, 
		// pos += sprintf(pos,",\n");					// tous les points du graphe sont quantifiés universellement
		fprintf(file,",\n");

		// boucle pour mettre en prémisse toutes les hypothèses donnée
		// dans l'énoncé (éventuellement réduit à la couche courante)
		for(i = 0; i < g.effectiveSize; i++)
		{
			if(g.tab[i]->color == -1)
			{			
				cpt++;
			/*------------------------------------ 			élim. d'un lemme trivial (commenté)---------*
			// 							non-écriture dans le fichier et sortie de constructLemma()		*
			if (g.tab[i]->e == n->e) { 	// idem PS 27/09/20 : brutal !									*		
										// si g.tab[i]->e == n->e, il n'est pas utile d'écrire			*
										// le lemme ni la preuve										*
				*pos_debug = '\n';		//																*
				fprintf(file,"(* Lemme %s pas écrit (couche %d) *) \n", debug_info, couche);  //		*
				free(local_buffer);		//																*
				free(debug_info);		//																*
				return false;     		//																*        
			}							//																*
            --------------------------------------------------------------------------------------------*/
			// sinon, on continue l'écriture dans le buffer tant que la boucle n'est pas finie
				partB = g.tab[i]->e;		 
											
				partBe = SetFrom(partB);
				rankB = rankMin(partB);
				
				if(rankMin(partB) != rankMax(partB))
				{
					fprintf(stderr,"Reconstruction impossible rangs des hypothèses non identiques\n");
					exit(1);
				}
				// pos += sprintf(pos,"rk(");			// idem PS 27/09/20
				fprintf(file,"rk(");
				// pos = printSetString(pos,partBe);  	// idem PS 27/09/20
				printSetFile(file,partBe);
				if(cpt == 3)
				{
					//pos += sprintf(pos," nil) = %d ->\n",rankB);	// idem PS 27/09/20
					fprintf(file," nil) = %d ->\n",rankB);
					cpt = 0;
				}
				else
				{
					// pos += sprintf(pos," nil) = %d -> ",rankB);	// idem PS 27/09/20
					fprintf(file," nil) = %d -> ",rankB);

				}
			}
		}

		// *pos = '\n'; // pour finir la chaîne 	// idem PS 27/09/20
		//--------------------------------------------------------------------------
		// écriture effective du lemme dans le fichier
		// PS 29/09/20 : si on arrive jusqu'ici, on écrit tout le buffer
		//               dans le fichier <file>
		//               et l'écriture se continuera dans ce fichier
		// fprintf(file,"%s",local_buffer); 
		// free(local_buffer);
		// free(debug_info);
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
		


		// construction de la preuve proprement dite
		// on reste au marquage U_WAITING_FOR_PREVIOUS_PROOF pour le noeud courant
		// car d'autres hypothèses concernant le noeud courant sont encore à démontrer
		// ça sera fait dans constructProofaux()
		
		constructIntro(file, g);
		constructProof(file, n, sizeTab, 1);
		// tout s'est bien passé et le lemme a été écrit avec sa preuve ... en principe
		n->mark = PROOF_ALREADY_DONE;
		unMark(n);			// on remet à 1 () les noeuds qui ont été mis à 5
							// j'ai mis le démarquage ici comme ça on n'est sûr de ne pas l'oublier
										
	return 1;
}	

/*______________________________________________________________________________


##  fonction constructIntro()
	Remarque cette intro est très générique et ne nécessite que les données de l'énoncé
	(en principe dans le graphe)
	- tous les points sont introduits
	- toutes les hyptothèses sont introduites
________________________________________________________________________________*/
void constructIntro(FILE* file, graph g) {
	int i;
	int cpt = 0;
	myType partA, partAe;
	
	fprintf(file,"Proof.\n\nintros ");
	
	for(i = 0; i < g.effectiveAllocPow; i++)
	{
		// fprintf(file,"%s ",STATEMENT->p_names[i]);   // i pas i+1 !!!
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
	un fichier par les fonctions précédentes.
	En fait, c'est constructProofaux() qui fasse tout le boulot (appelée au début)
	la majeur partie du code suivant est une espèce de filet de sécurité qui observe
	les valeurs initiales (d'où les preuves pour le rg d'un singleton ou lorsque la concl. est
	dans les hypothèses (qui concernent les rangs donnés au départ))
________________________________________________________________________________*/
void constructProof (FILE* file, node n, allocSize stab, int previousConstruct) {
	myType res = SetFrom(n->e);
	bool print_trace = false;

		if(trace && traced == (n->e & res)) {
		fprintf(debug_file," ------------\n\n\t trace pour %llu\n\n", traced);
		print_trace = true;
		}
	
	// appel à la vraie construction de la preuve 
	constructProofaux(file, n, res, stab, previousConstruct, print_trace);
	
	
	//----------------------------
	//
	// La suite ne traite que l'ensemble A sans faire appel à d'autres ensembles
	// on se fonde soit sur l'intialisation (min 1 et max = dim espace + 1)
	// soit sur les hypothèses
	//
	//-----------------------------------------
	myType partA, partAe;
	int rankMinA, rankMaxA;
	
	partA = n->e;
	partAe = SetFrom(partA);
	rankMinA = rankMin(partA);
	rankMaxA = rankMax(partA);
	
	if(dim >= 3)	//---------------> modifié, avant c'était dim==3 sans doute pour distinguer le cas où dim == 2 je pense 
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
			fprintf(file," nil) <= %d) by (apply rk_upper_dim).\n",dim+1); // <---------- modif par PS : la dimension n'était pas prise en compte
																		// ancienne version à la ligne ci-dessous (commentée)
			// fprintf(file," nil) <= 4) by (apply rk_upper_dim).\n");
		}
	}
	else	//-------------------------------------------------------> les dimensions > 3 ne semblent pas être bien prises en compte
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
// le marque à PROOF_ALREADY_DONE (4) sera fait au retour dans constructLemma() si
// c'est bien cette fonction qui a appelé constructProof()
}
 
/*______________________________________________________________________________


##  fonction constructProofaux()
    C'est ici que la preuve relative à l'application des règles est rédigée
________________________________________________________________________________*/
void constructProofaux (FILE* file, node n, myType res, allocSize stab, int previousConstruct, bool print_trace) {
	
	int i,j;
	int stabb = 1;	// utilité ?
	myType partA, partB, partAiB, partAuB, partAe, partBe, partAiBe, partAuBe;
	int rankMinA, rankMaxA, rankMinB, rankMaxB, rankMinAiB, rankMaxAiB, rankMinAuB, rankMaxAuB;
	int freeA, freeB, freeAuB, freeAiB;
	list tmp = n->ante;					/* la liste ante correspond aux étapes précédentes de réduction d'intervalle */



	if(tmp != NULL)	
		{
		/* debogage   */

				if(print_trace || (SetFrom(n->e)==traced && trace))
				{
					fprintf(debug_file," \t\t trace pour %llu (règle %d)", SetFrom(n->e),n->rule);
					printHypSetFile(debug_file,SetFrom(n->e));
					DEB_PS("\n\nliste ante :\n");
					printListFile (debug_file, tmp); NL;
					DEB_PS("fin de la liste.\n");
					printListFile (debug_file, tmp->n->ante); NL;
					DEB_PS("fin de la liste.\n");
					print_trace = true;
				}
		/*   fin debogage 		*/
		n->mark = U_WAITING_FOR_PREVIOUS_PROOF;
		while(tmp != NULL)
		{

			if(tmp->n->mark == U_NOT_WRITTEN_IN_PROOF)
			{
				if(print_trace)
				{
					fprintf(debug_file,"étape précédent marquée : ensemble %llu\n",SetFrom(tmp->n->e));
				}
				// tmp->n->mark = U_WAITING_FOR_PREVIOUS_PROOF;  // fait avant d'entrer dans la boucle
				/*-------------------------------------
						appel récusrif  :
					c'est ici que l'on traite les différentes étapes de la preuve
					chaque étape correspondant à une réduction de l'intervalle des rangs
					pour l'ensemble considéré.(et sans écrire de Lemme puisque le lemme
					en question est justement en train d'être écrit), cependant ces noeuds
					font intervenir des noeuds marqués dont on voudra la preuve ... mais celle-ci
					ne pourra pas donner lieu à un lemme.

					Remarque importante :
					On a déjà fait ce type de travail dans constructLemma() mais en ne traitant
					pas les noeuds correspondants à l'ensemble concerné par le Lemme (ces noeuds
					correspondent au même ensemble mais avec un intervalle de rang plus grand)
					C'est ici qu ces noeud dit premiers fils sont traités 
				
				-----------------------------------------*/
				fprintf(file,"\n(* dans constructProofaux(), preuve de %d <= rg <= %d pour ", rankMin(tmp->n->e), rankMax(tmp->n->e)); 
				printHypSetFile(file, SetFrom(tmp->n->e));
				fprintf(file, " requis par la preuve de (?)");
				printHypSetFile(file, SetFrom(n->e));fprintf(file," pour la règle %d  *)",n->rule);
				constructProofaux(file, tmp->n, res, stab, previousConstruct, print_trace);
			}
			tmp = tmp->next;
		}
		print_trace = false;
		n->mark = U_PROOF_BEING_WRITTEN;
		
		/*_______________________________________________________________

				règle 1 == règle 5 de la thèse
		__________________________________________________________________*/
		if(n->rule == 1) 
		{
			//sets + ranks
			
			partAuB = n->e;							// on en déduit quelque chose sur AuB (règle 5 de la thèse ?)
			// partA = n->ante->n->e;
			partA = R_FIRST(n)->e;
			freeA = checkGenealogie(n->ante->n); 	// ancienne version dessous
			//freeA = checkSuccList(n->ante->n->succ);
			//partB = n->ante->next->n->e;
			partB = R_SECOND(n)->e;
			freeB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeB = checkSuccList(n->ante->next->n->succ);
			
			if(n->ante->next->next->next !=NULL)    // ah ?
			{
				// partAiB = n->ante->next->next->n->e;
				partAiB = R_THIRD(n)->e;
				freeAiB = checkGenealogie(n->ante->next->next->n); //reprise de l'ancienne version dessous
				// freeAiB = checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeAuB = checkGenealogie(n->ante->next->next->next->n); // ancienne version dessous
				// freeAuB = checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				//oldPart = n->ante->next->next->n->e;
				freeAuB = checkGenealogie(n->ante->next->next->n); // ancienne version dessous
				// freeAuB = checkSuccList(n->ante->next->next->n->succ);
			}
			
			// sets
			partAe = SetFrom(partA);
			partBe = SetFrom(partB);
			if(n->ante->next->next->next !=NULL)
			{
				partAiBe = SetFrom(partAiB);
			}
			else
			{
				partAiBe = 0x0;
			}
			partAuBe = SetFrom(partAuB);
			
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
			fprintf(file,"(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)\n");
			fprintf(file,"(* marque des antécédents A B AiB : %d %d et %d*)\n",
							R_FIRST(n)->mark,
							R_SECOND(n)->mark,
							R_THIRD(n)->mark
							);
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAuBe);
			fprintf(file,"M%d : rk(",rankMaxAuB);
			printSetFile(file,partAuBe);
			fprintf(file,"nil) <= %d).\n",rankMaxAuB);
			fprintf(file,"{\n");
			
			// if(previousConstruct)
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			//else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
				printHypSetFile(file,partAe); 
				fprintf(file,"eq H");
				printHypSetFile(file,partAe);
				fprintf(file,"M%d).\n",rankMaxA);
			//}
			
			if(R_SECOND(n)->mark == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partBe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partBe);
				fprintf(file,"M%d).\n",rankMaxB);
			//}

			if(partAiB != 0x0)
			{
				//if(previousConstruct)
				if(R_THIRD(n)->mark == PROOF_ALREADY_DONE)
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
				// else {
					fprintf(file,"\tassert(H");
					printHypSetFile(file,partAiBe); 
					fprintf(file,"mtmp : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"m%d).\n",rankMinAiB);
				// }
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
		/*_______________________________________________________________

				règle 2 == règle 7 ou 8 de la thèse (ce sont 2 instances 
							de la même règle gérant sa symétrie)
		__________________________________________________________________*/
		else if (n->rule == 2)
		{	bool inter = false ; // intersection non vide
			//sets + ranks
			partA = n->e;
			partAuB = n->ante->n->e;
			freeAuB = checkGenealogie(n->ante->n); // reprise de l'ancienne version dessous
			// freeAuB = checkSuccList(n->ante->n->succ);
			if(n->ante->next->next->next !=NULL)
			{
				inter = true;
				partAiB = n->ante->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
				// freeAiB = checkSuccList(n->ante->next->n->succ);
				partB = n->ante->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->n); // reprise de l'ancienne version dessous
				// freeB = checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeA = checkGenealogie(n->ante->next->next->next->n); // reprise de l'ancienne version dessous
				//freeA = checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				partB = n->ante->next->n->e;
				freeB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
				// freeB = checkSuccList(n->ante->next->n->succ);
				//oldPart = n->ante->next->next->n->e;
				freeA = checkGenealogie(n->ante->next->next->n); // reprise de l'ancienne version dessous
				// freeA = checkSuccList(n->ante->next->next->n->succ);
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
			fprintf(file,"(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)\n");
			fprintf(file,"(* marque des antécédents AUB AiB B: %d %d et %d*)\n",
							R_FIRST(n)->mark,
							(inter) ? R_SECOND(n)->mark : -1,
							(inter) ? R_THIRD(n)->mark : R_SECOND(n)->mark
							);

			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"m%d : rk(",rankMinA);
			printSetFile(file,partAe);
			fprintf(file,"nil) >= %d).\n",rankMinA);
			fprintf(file,"{\n");

			// if(previousConstruct) // THIRD if AiB != 0 else SECOND
			if(((inter) ? R_THIRD(n)->mark : R_SECOND(n)->mark)  == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partBe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partBe);
				fprintf(file,"M%d).\n",rankMaxB);
			//}
			
			// if(previousConstruct)
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAuBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"m%d).\n",rankMinAuB);
			//}
			if(partAiB != 0x0)
			{
				//if(previousConstruct)
				if(R_SECOND(n)->mark == PROOF_ALREADY_DONE)
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
				//else {
					fprintf(file,"\tassert(H");
					printHypSetFile(file,partAiBe); 
					fprintf(file,"mtmp : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"m%d).\n",rankMinAiB);
				//}
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
		/*_______________________________________________________________

				règle 3 == règle 6  de la thèse
		__________________________________________________________________*/
		else if (n->rule == 3)
		{	
			//sets + ranks 
			partAiB = n->e;
			partA = R_FIRST(n)->e;
			freeA = checkGenealogie(n->ante->n); // reprise de l'ancienne version dessous
			// freeA = checkSuccList(n->ante->n->succ);
			partB = R_SECOND(n)->e;
			freeB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeB = checkSuccList(n->ante->next->n->succ);
			partAuB = R_THIRD(n)->e;
			freeAuB = checkGenealogie(n->ante->next->next->n); // reprise de l'ancienne version dessous
			// freeAuB = checkSuccList(n->ante->next->next->n->succ);
			if(n->ante->next->next->next !=NULL)
			{
				//oldPart = n->ante->next->next->next->n->e;
				freeAiB = checkGenealogie(n->ante->next->next->next->n); // reprise de l'ancienne version dessous
				// freeAiB = checkSuccList(n->ante->next->next->next->n->succ);
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
			fprintf(file,"(* Application de la règle 3 code (6 dans la thèse) *)\n");
			fprintf(file,"(* marque des antécédents A B AUB: %d %d et %d*)\n",
							R_FIRST(n)->mark,
							R_SECOND(n)->mark,
							R_THIRD(n)->mark
							);

			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAiBe);
			fprintf(file,"M%d : rk(",rankMaxAiB);
			printSetFile(file,partAiBe);
			fprintf(file,"nil) <= %d).\n",rankMaxAiB);
			fprintf(file,"{\n");
		
			//if(previousConstruct)
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAe);
				fprintf(file,"M%d).\n",rankMaxA);
			//}
			
			// if(previousConstruct)
			if(R_SECOND(n)->mark == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partBe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partBe);
				fprintf(file,"M%d).\n",rankMaxB);
			//}
			
			//if(previousConstruct)
			if(R_THIRD(n)->mark == PROOF_ALREADY_DONE)
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
			//else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAuBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"m%d).\n",rankMinAuB);
			//}

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
		/*_______________________________________________________________

				règle 4 == règle 7 ou 8 de la thèse (voir règle 2)
		__________________________________________________________________*/
		else if (n->rule == 4)
		{
			bool inter = false ;	// booléen vrai si l'intersection est non vide
			//sets + ranks 
			partB = n->e;
			partAuB = R_FIRST(n)->e;
			freeAuB = checkGenealogie(n->ante->n); // reprise de l'ancienne version dessous
			// freeAuB = checkSuccList(n->ante->n->succ);
			
			if(n->ante->next->next->next !=NULL)
			{
				inter = true ;
				partAiB = R_SECOND(n)->e;
				freeAiB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
				// freeAiB = checkSuccList(n->ante->next->n->succ);
				partA = R_THIRD(n)->e;
				freeA = checkGenealogie(n->ante->next->next->n); // reprise de l'ancienne version dessous
				// freeA = checkSuccList(n->ante->next->next->n->succ);
				//oldPart = n->ante->next->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->next->n); // reprise de l'ancienne version dessous
				// freeB = checkSuccList(n->ante->next->next->next->n->succ);
			}
			else
			{
				partAiB = 0x0;
				freeAiB = 0;
				partA = R_SECOND(n)->e;
				freeA = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
				// freeA = checkSuccList(n->ante->next->n->succ);
				//oldPart = n->ante->next->next->n->e;
				freeB = checkGenealogie(n->ante->next->next->n); // reprise de l'ancienne version  dessous
				// freeB = checkSuccList(n->ante->next->next->n->succ);
			}
			
			// sets
			partAe = SetFrom(partA);
			partBe = SetFrom(partB);
			if(inter)			// si AiB est non vide
			{
				partAiBe = SetFrom(partAiB);
			}
			else
			{
				partAiBe = 0x0;
			}
			partAuBe = SetFrom(partAuB);
			
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			if(inter)		// si AiB est non vide
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
			fprintf(file,"(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang %d et %d) *)\n", rankMinB,rankMaxB);
			fprintf(file,"(* marque des antécédents AUB AiB A: %d %d et %d*)\n",
							R_FIRST(n)->mark,
							(inter) ? R_SECOND(n)->mark : -1,
							(inter) ? R_THIRD(n)->mark : R_SECOND(n)->mark
							);
			fprintf(file,"(* ensembles concernés AUB : "), 
			printSetFile(file,SetFrom(R_FIRST(n)->e));
			fprintf(file," de rang : % d et %d \t", rankMinAuB, rankMaxAuB);
			fprintf(file," AiB : "); printSetFile(file,SetFrom((inter) ? R_SECOND(n)->e : 0));
			fprintf(file," de rang : % d et %d \t",rankMinAiB,rankMaxAiB );
			fprintf(file," A : "); printSetFile(file,SetFrom((inter) ? R_THIRD(n) -> e : R_SECOND(n)->e));
			fprintf(file,"  de rang : %d et %d *)\n", rankMinA,rankMaxA);

			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"m%d : rk(",rankMinB);
			printSetFile(file,partBe);
			fprintf(file,"nil) >= %d).\n",rankMinB);
			fprintf(file,"{\n");
			
			// if(previousConstruct)
			if(((inter) ? R_THIRD(n)->mark : R_SECOND(n)->mark) == PROOF_ALREADY_DONE)
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAe);
				fprintf(file,"M%d).\n",rankMaxA);
			// }
			
			// if(previousConstruct)
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			//else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAuBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAuBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAuB);
				printHypSetFile(file,partAuBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAuBe);
				fprintf(file,"m%d).\n",rankMinAuB);
			//}
			
			if(partAiB != 0x0)
			{
				//if(previousConstruct)
				if(R_SECOND(n)->mark == PROOF_ALREADY_DONE)
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
				// else {
					fprintf(file,"\tassert(H");
					printHypSetFile(file,partAiBe); 
					fprintf(file,"mtmp : rk(");
					printSetFile(file,partAiBe);
					fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinAiB);
					printHypSetFile(file,partAiBe);
					fprintf(file,"eq H");
					printHypSetFile(file,partAiBe);
					fprintf(file,"m%d).\n",rankMinAiB);
				// }
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
		/*_______________________________________________________________

				règle 5 == règle  1  de la thèse
				ou peut etre  2 ou 3 ou 4, plutôt 1 minB >= minA
		__________________________________________________________________*/
		else if (n->rule == 5)
		{
			//sets + ranks 
			
			partB = n->e;
			partA = n->ante->n->e;
			freeA = checkGenealogie(n->ante->n); // reprise de l'ancienne version  dessous
			// freeA = checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeB = checkSuccList(n->ante->next->n->succ);
			
			// sets
			partAe = SetFrom(partA);
			partBe = SetFrom(partB);
			// ranks			
			rankMinA = rankMin(partA);
			rankMaxA = rankMax(partA);
			rankMinB = rankMin(partB);
			rankMaxB = rankMax(partB);
			//oldRankMin = rankMin(oldPart);
			
			// export
			fprintf(file,"\n");
			fprintf(file,"(* Application de la règle 5 code (1 ou 2 dans la thèse) *)\n");
			fprintf(file,"(* marque de l'antécédent : %d *)\n",n->ante->n->mark);
			if(print_trace){DEB_PS("(* Application de la règle 5 code (1 ou 2 dans la thèse) *)\n");}
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"m%d : rk(",rankMinA);
			printSetFile(file,partBe);
			fprintf(file,"nil) >= %d).\n",rankMinA);
			fprintf(file,"{\n");
			
			//
			// cette partie n'a de sens que si le lemme a déjà été construit
			// c'était je pense de previousConstruct, mais dans cette version
			// on dirait que la valeur de cette variable est toujours true
			// if(previousConstruct) // ancienne version
			if(n->ante->n->mark==PROOF_ALREADY_DONE) // tentative de simplification .... 
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
			// else	{
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinA);
				printHypSetFile(file,partAe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAe);
				fprintf(file,"m%d).\n",rankMinA);
			// }
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
		/*_______________________________________________________________

				règle 6 == règle  3 ou 4  de la thèse
					maxA <= maxB
		__________________________________________________________________*/		
		else if (n->rule == 6)
		{
			//sets + ranks 
			partA = n->e;
			partB = n->ante->n->e;
			freeB = checkGenealogie(n->ante->n); // reprise de l'ancienne version  dessous
			// freeB = checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeA = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeA = checkSuccList(n->ante->next->n->succ);
			
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
			fprintf(file,"(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)\n");
			fprintf(file,"(* marque de l'antécédent : %d *)\n",n->ante->n->mark);
			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"M%d : rk(",rankMaxB);
			printSetFile(file,partAe);
			fprintf(file,"nil) <= %d).\n",rankMaxB);
			fprintf(file,"{\n");
			
			// if(previousConstruct)	// ancienne version
			if(n->ante->n->mark==PROOF_ALREADY_DONE) // tentative de simplification de la preuve
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
			// else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partBe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxB);
				printHypSetFile(file,partBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partBe);
				fprintf(file,"M%d).\n",rankMaxB);
			// }
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
			partB = R_FIRST(n)->e;
			freeB = checkGenealogie(n->ante->n); // reprise de l'ancienne version  dessous
			// freeB = checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeA = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeA = checkSuccList(n->ante->next->n->succ);
			
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
			fprintf(file,"(* Application de la règle 7 (code, 1 ou 2 dans la thèse) *)\n");
			fprintf(file,"(* marque de l'antécédent B : %d *)\n",R_FIRST(n)->mark);
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partAe);
			fprintf(file,"m%d : rk(",rankMinB);
			printSetFile(file,partAe);
			fprintf(file,"nil) >= %d).\n",rankMinB);
			fprintf(file,"{\n");
			
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			// else {		
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partBe); 
				fprintf(file,"mtmp : rk(");
				printSetFile(file,partBe);
				fprintf(file,"nil) >= %d) by (solve_hyps_min H",rankMinB);
				printHypSetFile(file,partBe);
				fprintf(file,"eq H");
				printHypSetFile(file,partBe);
				fprintf(file,"m%d).\n",rankMinB);
			//}

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
			partA = R_FIRST(n)->e;
			freeA = checkGenealogie(n->ante->n); // reprise de l'ancienne version dessous
			// freeA = checkSuccList(n->ante->n->succ);
			//oldPart = n->ante->next->n->e;
			freeB = checkGenealogie(n->ante->next->n); // reprise de l'ancienne version dessous
			// freeB = checkSuccList(n->ante->next->n->succ);
			
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
			fprintf(file,"(* Application de la règle 8 (code, 3 ou 4 dans la thèse) *)\n");
			fprintf(file,"(* marque de l'antécédent  A : %d *)\n",R_FIRST(n)->mark);
			
			fprintf(file,"assert(H");
			printHypSetFile(file,partBe);
			fprintf(file,"M%d : rk(",rankMaxA);
			printSetFile(file,partBe);
			fprintf(file,"nil) <= %d).\n",rankMaxA);
			fprintf(file,"{\n");
			
			//if(previousConstruct)
			if(R_FIRST(n)->mark == PROOF_ALREADY_DONE)
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
			//else {
				fprintf(file,"\tassert(H");
				printHypSetFile(file,partAe); 
				fprintf(file,"Mtmp : rk(");
				printSetFile(file,partAe);
				fprintf(file,"nil) <= %d) by (solve_hyps_max H",rankMaxA);
				printHypSetFile(file,partAe);
				fprintf(file,"eq H");
				printHypSetFile(file,partAe);
				fprintf(file,"M%d).\n",rankMaxA);
			//}
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
		
	}
n->mark = PROOF_WRITTEN_in_Lemma;
// n->mark = U_NOT_WRITTEN_IN_PROOF;
}
//*******************************************************************************
/*______________________________________________________________________________*


##  fin de la fonction constructProofaux()
	
________________________________________________________________________________*/
//*******************************************************************************




/********************************************************************************/
/*------------------------------------------------------------------------------*
*																				*
*    Fonction auxiliaires pour l'impression dans un fichier					*
*						des fonctions d'impression								*
*																				*
*_______________________________________________________________________________*/

void printSetFile_PS (FILE* file, myType e) {
	int i,j=0;
	for(i = 0; i < realSizemyType; i++)
	{

		if((e >> i) & 1) // changé
		{
				fprintf(file,"%s :: ",STATEMENT->p_names[j]);
		}
		j++;
	}
}

void printSetFile (FILE* file, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if((e >> i) & 1) // changé
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

		if((e >> i) & 1)
		{
				s += sprintf(s,"P%d :: ",j);
		}
		j++;
	}
	return s;
}

// remarque : c'est la même fonction que printSetFile() à un " ::" près ...
void printHypSetFile_PS(FILE* file, myType e) {
	int i,j=0;
	for(i = 0; i < realSizemyType; i++)
	{

		if((e >> i) & 1)
		{
				fprintf(file,"%s",STATEMENT->p_names[j]);
		}
		j++;
	}
}


void printHypSetFile (FILE* file, myType e) {
	int i,j=1;
	for(i = 0; i < realSizemyType; i++)
	{

		if((e >> i) & 1)
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

		if((e >> i) & 1)
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

