// fichier fprintthings.h
#ifndef __FPRINTTHINGS_H__
#define __FPRINTTHINGS_H__

#include "parties.h"
#include "set.h"
#include "graph.h"
#include"maths_addon.h"

// Toutes les fonctions suivantes existent déjà dans une version
// où l'affichage se fait sur la sortie standard
// ici, j'ai juste ajouté systématiqument un fchier de sortie.

void fprintNode(FILE *out, node n);

void fprintLineGraphWithoutProof (FILE *out, graph g, int i);

void fprintGraphWithoutProof(FILE *out, graph g);

void fprintSet(FILE *out, myType e);

void fprintBytes(FILE *out, myType e);

void fprintBytesAsNumber(FILE *out, myType e);

void fprintBytesAsRank(FILE *out, myType e);

#endif