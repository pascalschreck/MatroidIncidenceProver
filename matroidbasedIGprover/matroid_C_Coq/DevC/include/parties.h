#ifndef __PARTIES_H_
#define __PARTIES_H_

#include "graph.h"
#include "globals.h"




#define R_ZERO(Node) ((Node))
#define R_FIRST(Node) ((Node)->ante->n)
#define R_SECOND(Node) ((Node)->ante->next->n)
#define R_THIRD(Node) ((Node)->ante->next->next->n)

extern FILE *debug_file;

typedef struct allocSize {
	int ** tab;
	int size;
} allocSize;

typedef struct graph {
	node * tab;
	int effectiveSize;
	int size;
	int effectiveAllocPow; // 
	int allocPow;
} graph;

allocSize allocSizeTab (int n, int m); 
		// Fonction qui alloue une table n*m permettant d'effectuer une reconstruction par couches : 
		// sauvegarde du nombre de points effectifs et de la taille effective pour chaque couche
		// n : nombre de couches
		// m ? dans les faits, c'est toujours 2
		// ça crée un tableau à n lignes et m (m = 2 en pratique) colonnes : 

graph allocGraph (int n); 
		// Fonction qui alloue le graphe de déductions à partir d'un nombre de points n

graph copyGraph(graph g1, graph g2, int res); 
		// Fonction qui copie un graphe g1 dans un graphe g2 sauf pour l'entier binaire res

graph convergenceParties (graph g, int res); 
		// Fonction qui sature le graphe de déductions g pour chercher les rangs de 
		// l'entier binaire res
	
graph applyPappus (graph g, int * convergence, int loopnumber); 
		// Fonction qui cherche une instance de Pappus dans le graphe de déductions g
	
graph applyPappusParties (graph g, int i, int j, int * convergence, int loopNumber); 
		// Fonction qui cherche une instance de Pappus dans 
		// le graphe de déductions g pour les entiers binaires i et j
		// i et j représentent les deux droites supportant chacune 3 points distincts

myType existPappusConfiguration(graph g, myType e1, myType e2, myType e3, myType e4, myType e5, myType e6); 
		// Fonction qui renvoie la droite construite par l'application de la propriété 
		// de Pappus sur les droites e1e2e3 et e4e5e6

myType existIntersectPoint(graph g, myType e1, myType e2); 
		// Fonction qui vérifie l'existence d'un point d'intersection entre deux 
		// entiers binaires e1 et e2 représentant des droites
		// prec : rang e1 = 2 et rnag e2 = 2

void preMark(node n); 
		// Fonction qui marque les noeuds du graphe de déductions à 1 à partir d'un noeud n

void unMark(node n); 
		// Fonction qui enlève le marquage du graphe de déductions

bool constructLemma(FILE* file, graph g, node n, allocSize alloctab ,int couche); 
		// Fonction qui reconstruit l'énoncé lemme dans le fichier file à partir 
		// d'un noeud n du graphe de déductions g

bool constructTheorem(FILE* file, graph g, node n,  allocSize   sizeTab, int couche);
		// Fonction qui reconstruit l'énoncé du théorème final dans le fichier file 
	
void constructIntro(FILE* file, graph g); 
		// Fonction qui reconstruit l'introduction de la preuve de l'énoncé 
		// dans le fichier file à partir du graphe de déductions g

void constructProofaux (FILE* file, node n, myType res, allocSize tab, int previousConstruct, bool print_trace); 
		// Fonction qui reconstruit le cheminement de la preuve dans le fichier file 
		// grâce au marquage à partir d'un n du graphe de déductions g

void constructProof (FILE* file, node n, allocSize tab, int previousConstruct); 
		// Fonction qui reconstruit la fin de la preuve de l'énoncé dans le fichier 
		// file à partir du noeud n

void printAllPoints(FILE *file, graph g);
		// écrit dans file la liste de tous les points de g séparés par un espace

void printSetFile (FILE* file, myType e); 
		// Fonction qui reconstruit dans un fichier file un entier binaire e sous forme 
		// d'ensemble (dans le langage Coq)

char *printSetString(char *s ,myType e);
		// même fonction que précédemment, mais qui écrit dans une chaîne (avec sprintf())
		// plutôt que dans un fichier
		// le pointeur returné pointe sur le premier caractère après l'écriture dans s

void printHypSetFile (FILE* file, myType e); 
		// Fonction qui reconstruit dans un fichier file un entier binaire e sous forme 
		// d'hypothèse (dans le langage Coq)

// ajout PS
char* printHypSetString (char *s, myType e);
		// même fonction que précédemment, mais qui écrit dans une chaîne (avec sprintf())
		// plutôt que dans un fichier
		// le pointeur returné pointe sur le premier caractère après l'écriture dans s 

void printLineGraph (graph g, int i); 
		// Fonction qui affiche une ligne i du graphe g avec le cheminement de la preuve

void printLineGraphWithoutProof (graph g, int i); 
		// Fonction qui affiche une ligne i du graphe g sans le cheminement de la preuve

void printGraph (graph g); 
		// Fonction qui affiche le graphe g avec le cheminement de la preuve

void printGraphWithoutProof(graph g); 
		// Fonction qui affiche le graphe g sans le cheminement de la preuve



#endif //__PARTIES_H_


