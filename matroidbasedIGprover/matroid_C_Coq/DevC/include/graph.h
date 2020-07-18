#ifndef __GRAPH_H_
#define __GRAPH_H_

#include "set.h"
#include "maths_addon.h"

typedef struct s_node s_node,*node;

typedef struct s_list {
	s_node * n;
	struct s_list * prev;
	struct s_list * next;
}s_list,*list;

struct s_node {
	myType e;
	int color;
	int mark;
	int rule;
	s_list * ante;
	s_list * succ;
};

node createNode (myType e); // Fonction qui crée un noeud sans informations
node addNode (list l, myType e, int rule); // Fonction qui crée un noeud avec la liste l des parents, l'entier binaire et la règle appliquée
list createList (node n); // Fonction qui une liste à partir d'un noeud n
list addList (list l, node n); // Fonction qui ajoute un noeud n à une liste l
int checkSuccList (list l); // Fonction qui renvoie un booléen selon le marquage des noeuds dans une liste l (permet la suppression des hypothèses lors de la reconstruction)
int checkGenealogie (node n); // Fonction qui vérifie la généalogie d'un noeud (permet la suppresion des hypothèses lors de la reconstruction)
int checkGenealogieUp (node n); // Fonction qui vérifie la généalogie supérieur d'un noeud (permet la suppresion des hypothèses lors de la reconstruction)
int checkGenealogieDown (node n); // Fonction qui vérifie la généalogie inférieur d'un noeud (permet la suppresion des hypothèses lors de la reconstruction)

void printList (list l); // Fonction qui affiche une liste
void printListWithMark (list l); // Fonction qui affiche une liste sauf marque
void printNode(node n); // Fonction qui affiche un noeud
void printNodes(node n, int space); // Fonction qui affiche une arborescence de noeuds

#endif //__GRAPH_H_


