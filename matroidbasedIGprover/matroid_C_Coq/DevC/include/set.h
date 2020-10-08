#ifndef __SET_H_
#define __SET_H_

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

// 64 bytes for set & 6 or 4 bits for rank min|max
#define myType unsigned long long

#include "./globals.h"
/*
// dim entre 1 et 7
#define dim 2

#if dim >= 4
	#define sizemyType 64
	#define realSizemyType 58
#elif dim <= 3
	#define sizemyType 64
	#define realSizemyType 60
#endif
*/

myType setIByte(myType e, int i); // Fonction qui met à jour un bit i à 1 dans un entier binaire e
myType unsetIByte(myType e, int i); // Fonction qui met à jour un bit i à 0 dans un entier binaire e
int getBytes(myType e, int i); // Fonction qui récupère dans un entier le ième bit dans un entier binaire e
myType getIBytes(myType e, int i); // Fonction qui récupère le ième bit à 1 dans un entier binaire e
int countBytes(myType e); // Fonction qui compte le nombre de bits à 1 dans un entier binaire e
myType initSet(); // Fonction qui initialise à 0x0 un entier binaire ... ah ?
myType DecToBin(int i); // Fonction qui renvoie un entier binaire à partir d'un entier i (qui était déjà en binaire)
myType initRanks(myType e); // Fonction qui initialise les rangs d'un entier binaire e ... ah ?

int rankMax(myType e); // Fonction qui renvoie le rang maximum d'un entier binaire e
myType setMax(myType e, int i); // Fonction qui met à jour le rang maximum par un entier i dans un entier binaire e
int rankMin(myType e); // Fonction qui renvoie le rang minimum d'un entier binaire e
myType setMin(myType e, int i); // Fonction qui met à jour le rang minimum par un entier i dans un entier binaire e
myType setMinMax(myType e, int i, int j); // Fonction qui met à jour le rang minimum/maximum par un entier j/i dans un entier binaire e
int rankMinMaxEqual(myType e, int value); // Fonction qui renvoie un booléen si le rang minimum et maximum sont égaux à value dans un entier binaire e
int incl(myType e1, myType e2); // Fonction qui renvoie un booléen si le e1 est inclus dans e2

void printSet(myType e); // Fonction qui affiche dans le détail un entier binaire e 
void printBytes(myType e); // Fonction qui affiche les bits d'un entier binaire e
void printBytesAsNumber(myType e); // Fonction qui affiche un entier représentant l'entier binaire e
void printBytesAsRank(myType e); // Fonction qui affiche le rang d'un entier binaire e

int cardinal(myType e);  // cardinal d'un ensemble ... arbitrairement limité à 25

#endif //__SET_H_
