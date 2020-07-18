#ifndef __MATHS_ADDON_H_
#define __MATHS_ADDON_H_

#include <stdio.h>
#include <stdlib.h>
#include <math.h>

int factRec(int n); // Fonction factorielle récursive
int fact(int n); // Fonction factorielle itérative
int spow (int n); // Fonction : 2^n -1
int binomial_slow(int n, int p); // Fonction binomiale naïve
int binomial_moderate(int n, int p); // Fonction binomiale légèrement optimisée
int binomial_fast(int n, int p); // Fonction binomiale optimisée

#endif //__MATHS_ADDON_H_
