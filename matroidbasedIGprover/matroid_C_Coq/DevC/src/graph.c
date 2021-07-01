#include "graph.h"
#include "parties.h"
#include "globals.h"

node createNode (myType e) {
	
	//create new node
	node new = (s_node *)malloc(sizeof(s_node));
		if(new==0){ fprintf(stderr,"dans createNode() pb. d'allocation"), exit(2);}
	new->e = e;
	new->color = 0;
	new->mark = (cardinal(e) > 1) ? UNUSED : SINGLE ;	// valeur 0 ou -2
	new->rule = 0;		// numéro de la règle de mise à jour
	new->ante = NULL;	//  pas de prédécesseur
	new->succ = NULL;	// pas de successeurs
	
	return new;
}
 
node addNode (list l, myType e, int rule) {
	
	//create new node
	node new = (s_node *)malloc(sizeof(s_node));
		if(new==0){ fprintf(stderr,"dans addNode() pb. d'allocation"), exit(2);}
	new->e = e;
	new->color = 0;
	new->mark = 0;
	new->rule = rule;
	new->ante = l;
	new->succ = NULL;

	list tmp = l;
	while(tmp != NULL)
	{
		if(tmp->n->succ == NULL)
		{
			tmp->n->succ = createList(new);
		}
		else
		{
			tmp->n->succ = addList(tmp->n->succ,new);
		}
		tmp = tmp->next;
	}
	return new;
}

list createList (node n) {
	
	//create new list
	list new = (s_list *)malloc(sizeof(s_list));
		if(new==0){ fprintf(stderr,"dans createList() pb. d'allocation"), exit(2);}
	new->n = n;
	new->next = NULL;
	new->prev = NULL;
	
	return new;
}

list addList (list l, node n) {

	//add element
	list new = (s_list *)malloc(sizeof(s_list));
		if(new==0){ fprintf(stderr,"dans addList() pb. d'allocation"), exit(2);}
	new->n = n;
	
	list tmp = l;
	while(tmp->next != NULL)
	{
		tmp = tmp->next;
	}
	
	tmp->next = new;
	new->prev = tmp;
	new->next = NULL;
	
	return l;
}

int checkSuccList (list l) {
	int mark = 1;
	
	list tmp = l;
	while(tmp != NULL && mark == 1)
	{
		if(tmp->n->mark == 1 || tmp->n->mark == 2)
		{
			mark = 0;
		}
		tmp = tmp->next;
	}
	
	return mark;
}

int checkGenealogie (node n) {
	int checkGen = checkGenealogieUp(n) && checkGenealogieDown(n);
	
	return checkGen;
}

int checkGenealogieUp (node n) {
	int mark = 1;
	myType checkset = n->e & 0x3FFFFFFFFFFFFFF;
	int checkGenUp = checkSuccList(n->succ);
	
	list tmp = n->succ;
	
	while(tmp != NULL && mark == 1)
	{
		if((tmp->n->e & 0x3FFFFFFFFFFFFFF) == checkset) //..... ça veut dire qu'on rertouve l'ens. des succeseurs ?
		{
			mark = 0;
			checkGenUp = checkGenUp && checkGenealogieUp(tmp->n);
		}
		tmp = tmp->next;
	}
	
	return checkGenUp;
}

int checkGenealogieDown (node n) {
	int mark = 1;
	myType checkset = n->e & 0x3FFFFFFFFFFFFFF;
	int checkGenDown = checkSuccList(n->succ);
	
	list tmp = n->ante;
	
	while(tmp != NULL && mark == 1)
	{
		if((tmp->n->e & 0x3FFFFFFFFFFFFFF) == checkset)
		{
			mark = 0;
			checkGenDown = checkGenDown && checkGenealogieDown(tmp->n);
		}
		tmp = tmp->next;
	}
	
	return checkGenDown;
}

void printList (list l) {
	list tmp = l;
	while(tmp != NULL)
	{
		printf("---->");printNode(tmp->n);printf("\n");
		tmp = tmp->next;
	}
}


void printListWithMark (list l) {
	list tmp = l;
	while(tmp != NULL && tmp->n->mark >= 1)
	{
		printf("---->");printNode(tmp->n);printf("\n");
		tmp = tmp->next;
	}
}


void printNode(node n) {
	if(n != NULL)
	{
		printSet(n->e);
	}
}

void printNodes(node n, int space) {
	if(n != NULL)
	{
		printSet(n->e);

		list tmp = n->ante;
		
		while(tmp != NULL)
		{
			int i = space;
			while(i > 0)
			{
				printf("     ");
				i--;
			}
			printf("%d -----> ", n->rule);
			printNodes(tmp->n, space+1);
			tmp=tmp->next;
		}
	}
}

/*---------------------------ajout PS pour écriture dans un fichier -------------------*/
void printListFile (FILE *file, list l) {
	list tmp = l;
	while(tmp != NULL)
	{
		fprintf(file, "---->");printNodeFile(file, tmp->n); fprintf(file, "\n");
		tmp = tmp->next;
	}
}

void printListWithMarkFile (FILE *file, list l) {
	list tmp = l;
	while(tmp != NULL && tmp->n->mark >= 1)
	{
		fprintf(file, "---->");printNodeFile(file, tmp->n);fprintf(file, "\n");
		tmp = tmp->next;
	}
}


void printNodeFile(FILE *file, node n) {
	if(n != NULL)
	{
		printSetFile(file, n->e);
	}
}

