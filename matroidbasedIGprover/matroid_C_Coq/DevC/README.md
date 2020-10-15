# Configuration et compilation :

*Attention les indications données dans ce fichier sont en partie dépassées*

## Installation
Création de l'environnement (dossier obj/ bin/) : make init
Compilation du prouveur : make all
Exécution et redirection de l'affichage ./bin/main > ranks.txt

## Décomposition du projet :

maths_addon.c : fonctions mathématiques
set.c : encodage des ensembles sur des entiers binaires
graph.c : création et manipulation des noeuds dans un graphe
parties. c : création  et manipulation du graphe de déductions; algorithme de saturation, règle de Pappus; reconstruction de la preuve et export en Coq
main.c : fonction main et exemples d'énoncés géométriques à saturer

## Fonctionnement du prouveur :

Ouverture du fichier file
Allocation de la table sizeTab qui va stocker la décomposition de l'énoncé géométrique en plusieurs couches (si l'optimisation est utilisée) :
- nombre de points
- nombre de parties en fonction de ce nombre de points
Allocation du graphe en fonction du nombre de points
Chargement de l'énoncé géométrique (écriture dans une fonction à part de cet énoncé) :
- nombre de points
- nombre de parties
- hypothèses
- coloration des hypothèses (si l'optimisation est utilisée)
Mise à jour de la table sizeTab avec les informations de l'énoncé géométrique
Application de l'algorithme de saturation pour chercher le résultat à la ligne res
(Affichage du graphe)
Reconstruction de la preuve :
- prémarquage du graphe à partir du résultat
- construction de l'énoncé du lemme
- construction de l'introduction du lemme
- construction de la preuve dans son intégralité
Fermeture du fichier

## Algorithme de saturation :

Application de la boucle de saturation sur les 6 règles matroïdales (8-2 car fonctionnement croissant) jusqu'à saturation 
Puis application de la règle de Pappus
Si Pappus provoque un changement, on recommence la saturation
On s'arrête dès que le système a convergé

Mode affichage & mode debug permettant d'afficher pleins d'informations supplémentaires

## Notes supplémentaires :

L'algorithme utilise par défaut la coloration, cette optimisation peut être enlevé dans l'algorithme de saturation

## Structures de données

La structure de base pour la propagation des limites de rangs et l'historique d'application des règles est la structure de node :
  ```c
  struct s_node {
	myType e;
	int color;		// prévu pour des optimisations ... je ne sais pas si c'est utilisé
	int mark;			// marquage
	int rule;			// numéro de la règle appliquée (à l'origine de la création de ce noeud)
	s_list * ante;	// un noeud contient la liste des prédecesseur dans le raisonnement (?)
	s_list * succ;	// ?
};
  ```
  où 
  * le champs `e` est un entier (plus précisément dans la version actuelle un `unsigned long long` pour gèrer les grandes dimensions) où est stocké l'ensemble (comme un tableau de bit avec un bit par élément 1 si présent et 0 si absent) et les informations sur les rangs minimum et maximum connus (imposés ou déduits).
  * le champ `color` est prévu pour faire du marquage de noeud en vue d'optimisation, je ne suis pas sûr que cela soit utilisé dans la version actuelle.
  * le champ `mark` est utilisé pour marquer les noeuds pour gérer l'écriture de la preuve en Coq. Actuellement on a :

    -   0 pour non utilisé dans la preuve
    -   1 pour utile à la preuve, mais pas encore transcrit en Coq
    -   2 pour utile à la preuve, mais en attente de buts/noeuds en amont dont la preuve Coq est encore à produire
    -   3 preuve en cours d'écriture
    -   4 preuve écrite dans un lemme est réutilisable.
 * le champ `rule` est un entier correspondant au numéro de la règle qui a été appliquée pour produire le noeud. Cette règle est traduite en élément de preuve Coq.
 * le champs `ante` correspond à la liste des noeuds qui sonten prémisses dans la règle (par exemple dans la règle de Pappus, cette liste est très longue car il y a une dizaine de prémisses). C'est cette liste qu fait le lien avec les preuves antérieures au noeud.

 Un graphe est une table de noeuds avec des informations supplémentaires.