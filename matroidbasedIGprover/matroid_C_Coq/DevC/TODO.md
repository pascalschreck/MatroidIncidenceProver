# TODO et remarques

## FIXME
### To do
* corriger tous les bugs dans la production de la preuve :
    - DONE des Lemmes ne sont pas écrits (toujours pas !) alors qu'ils sont utilisés
    - (?) une utilsation de la actique matroid2 devrait être faite mais ne l'est pas. Pire, le terme matroid2 n'aparaît pas 
    dans le fichier parties.c où la preuve est censée être  écrite. 
* DONE Enlever les infos de déboggage quand ça fonctionnera ou mieux les mettres dans la compilation
* tester plus en profondeur les raisonnements par contradiction (c'est un cas où la propagation de contrainte (avant ou arrière) pourrait bien fonctionner)
* TODO regarder la perte de marquage et/ou de reconstruction de théorèmes qui seraient dus (?) à la gestion des couches de raisonnement.
* TODO regarder le cas multi couche avec  le nouveu parcours pour construire la preuve.
* TODO on peut facilement ajouter plusieurs conclusion : ça peut être utile pour prouver un théorème de Deasragues assez complet en dim 3 et 4

### In progress


### Done
* les commentaires vides font planter l'entrée

* ajouter le mot clé "none" ou None" pour signifier qu'il n'y a pas de conclusion (remarque, il faut toujours une conclusion finale dans l'énoncé)

* Filtrage des lemmes inutiles : 
    - conclusion avec un singleton
    - conclusion dans les hypothèses    
    mais c'est en commentaire pour le moment : il y avait de problème dans l'utilisation des lemmes. 

*  il y a un problème assez fondamental dans la manière dont la preuve est écrite avec l'algo. de David :
   *  si un noeud est marqué à 1 'U_NOT_WRITTEN_IN_PROOF' on écrit un lemme dans cet ordre
  
        1. énoncé du lemme 
   
            (écriture dans le fichier de "Lemma xxx : forall \<tous les points\> ) \<toutes les hypothèses\> -> \<l'ensemble résultat à pour rang le rang min= rang max\> 
        2. phase d'introduction des variables (tous les points et toutes les hypothèses de l'énoncé)
        3. phase d'écriture de la preuve : il s'agit de lancer une procédure axuiliaire des arguments 
        de la règle utilisée (ça va être l'objet de la phase 4), puis de compléter par des arguments 
        génériques fondés sur l'initialisation de la fonction rang
        4. examen des arguments pour preuves ... si les arguments sont encore au stade 1, on les marque à 2 ... mais ils ne sont pas sous fome de lemme sinon ils auraient le statut 1.

    Solution envisagée : différer l'écriture dans le fichier de la preuve jusqu'à ce que tous les pbs. des antécédents soient réglés. Cela peut se faire simplement en testant les antécédents avant d'écrire le lemme. 
## Couches (again)
Lorsqu'on déclare plusieurs couche, chaque couche donne lieu à un graphe distinct des autres couches. Cela implique des
opérations de recopie et de transfert d'information (notamment dans les marquages), mais cle n'est pas encore suffisant dans la version actuelle où des informtions sur les déducions sont oubliées.
Ne pourrait-on pas considérer un seul graphe et gérer les couches dans ce seul graphe ?

## Constriction et incidence
Après étude plus approfondie, la question des couches est moins pregnante qu'il n'apparaissait de prime abord. Elle peut cependant être utile si on veut structure (dans l'énoncé) le raisonnement et dans une certaine mesure, dans la production des lemmes utilisés. C'est aussi utile pour déboguer les énoncé : on a une indiation de l couche incriminée en cas de faute, 
on peut essayer de repérer des problèmes dans la propagation des rangs e arrêter le calcul plu rapidement au lieu d'attendre des heures ....

Comme cela est indiqué en commentaire dans le code de "parties.c" (fonction copyGrap()), pour le moment, le partage en couches se fait par recopie d'un graphe dans le graphe de la couche supérieure mais sans recopier le graphe de déduction (ce sont juste les initialisation des rangs + quelques info qui sont faites). Cela implique que les renseignements liés aux noeud qui seront marqués soient consignés dans un lemme qui sera utilisé dans la couche supérieure ... il vaudrait donc mieux que les lemmes en questions aient pour conclusion des égalités de rang et non des indégalités restantes (à moins que dans Coq on ait un procédé plus robuste de construction de la preuve).
Ainsi, il me semble préférabledu point de vue de la structure de l'énoncé et de la structure de la preuve que les points introduits dans une couch soient définis quand on passe à a couche supérieure.
E donc, on peut se poser la question de la bonne constriction d'un point en géométrie d'incidence dans un contexte donnée. Le cas le plus simple est celui-ci :
```  
points
    layer ABCD # import des points A, B, C et D qui ne contiennent pas des alignements et ont bien définis
    point M
hypothèses
    A B M : 2
    C D M : 2
conclusion
    M : construit   # ou construits s'il y a plusieurs points
```
Ca peut rester déclaratif, bien sûr, mais on peut aussi se poser la question de la bonne constriction des ces points.


## Décomposition et construction de la preuve
Dans les preuves (je ne les ai pas toutes regardées), on note la fabrication d'un grand nombre de lemmes inutiles : par exemple des lemmes où la conclusion est que le rang d'un ensemble avec un seul point est 1 (est-ce bug qui prend en compte des restes de l'initialisation ?) ou alors dont la conclusion est incluse dans les prémisses.
Il faudrait soit revoir la construction des lemmes et tâcher de fabriquer des choses intéressantes ou, si ça n'est pas possible, de nettoyer après-coup, la base de lemmes locale pour éliminer les lemmes triviaux.

Par ailleurs, la décomposition et la reconstruction de lemmes correspond à une certaine idée de la structure de la preuve correspondant à la construction de points intermédiaires. Dans le cas de la preuve de Desargues en dimension n, il y a une structuration et des lemmes de bases qui ne correspondent pas forcément à une preuve sympa : par exemple, on aimerait pouvoir réutiliser que 2 triagles en prespectives satisfont les hyptohèses de Desargues 2,5D et le réutiliser sur toutes les 2-facettes. 

--> voir plus bas la question des lemmes intermédiaires



## Manipulation des règles 

Prévoir un méta-cadre, au moins pour les règles sortant du cadre minimal de la géométrie d(incidence)

* Pappus
* Dandelin-Galucci
* autres ? (en rapport avec les réels comme m5 truc de Mc...)

Une remarque qui me semblait ne concerner que les règles : les spécifications géométriques en n'utilisant que les rangs sont assez difficiles à écrire, et encore plus à écrire de manière correcte.
C'est le cas de la règle de DG dont voici une formulation dans un langage mockup

```
# DG_rule
# tentative de définition de règle en utilisant l'exemple de DG
# qui est plutôt complexe.
# je remarque qu'il est plus facile d'exprimer cette règle avec de la 
# géométrie qu'avec des rang ... c'était sans doute aussi le cas 
# de certains énoncés de thm ... sauf qu'en on arrive en dim. > 3
rule
hypotheses
    lines
        d1 d2 d3 d4 D1 D2 D3 D4
    points
        O A B C Ap Bp D E F G H I J K   
        # on ajoute le 16ème points ? a priori, DG dit que le rang de certains points
        # (ceux portés par deux droites) forment un ensemble 
        # de rang 3 (coplanaires)
        # et donc les droites se coupent 
        # cependant, la preuve de Papps par DL vu dans ... impose la création 
        # d'un nouveau point 
    constraints
        linealldifferent : d1 d2 d3 d4 D1 D2 D3 D4
        pointalldifferent : O A B C Ap Bp D E F G H I J K
        incidence O D1
        incidence O d1
        ...
        nointersection d4 D4
conclusion
        add point X
        X on d4
        X on D4
endofrule
```
### Autre sujet de discussion : 
Essayer de prouver Desargues en utilisant Pappus (théorème de Hessenberg) : ce n'est as si facile car il y a plusieurs cas. Celui où l'un des triangles est inscrit dans l'autre (cas Cévien car les sommets se correspondent par une perspective) est en particulier beaucoup plus difficile à montrer que le cas générique où aucun sommet d'un trianle n'appartient à un coté de l'autre.

## Réflexions sur les manières possibles d'écrire un énoncé (lien avec la complexité) 
La remarque plus haut s'applique aussi à mes tentatives de définir 3 plans "indépendants" en 3D, c'est-à-dire 3 plans qui ne se coupent pas suivant la même droite.
Mes premiers essais m'ont conduit à des énoncés compliqués avec 17 points (ou plus) où on définissait les 3 droites d'intersection des plans et on spécifaient qu'elles étaient distinctes. Une version plus simple (mais dont on peut douter qu'elle soit complète) de la propriété que trois tels plans se coupent en un point se trouve être la suivant :

```
# inter2Plan.stat
# en 3D l'intersection de 3 plans "indépendants" est un point
context
      dimension 3
      layers 1
endofcontext
layer 0
  points
    A B C Ap Bp Cp As Bs Cs  M X Y
  hypotheses
# trois plans distincts
    A B C : 3
    Ap Bp Cp : 3
    As Bs Cs : 3
    A B C Ap Bp Cp : 4
    A B C As Bs Cs : 4
    Ap Bp Cp As Bs Cs : 4

# X et Y appartiennent aux trois plans
    Y A B C : 3
    X A B C : 3
    Y Ap Bp Cp : 3
    X Ap Bp Cp : 3
    Y As Bs Cs : 3
    X As Bs Cs : 3

# M dans l''intersection de ABC et ApBpCp
    M A B C : 3
    M Ap Bp Cp : 3

# M n'est pas dans AsBsCs
    M As Bs Cs : 4

# donc les droits plans ne partagent pas de droite commune
  conclusion
     X Y : 1
endoflayer
  conclusion
    X Y : 1
end
```
où on voit qu'il suffit de définir 1 point dans intersection de deux plans et de dire que ce point n'appartient pas au 3ème plan.

On a ainsi un énoncé avec 12 points au lieu de 17 ... ce qui est énorme puisque la complexité est exponentielle, et une définition plus simple de 3 plans indépendants : il existe un point qui appartient à 2 plans, mais pas au troisième.

Parmi diverses réflexions que cela m'inspire : peut-être serait-il bien d'enrichir le langage de description avec les notions de droites et de plans et avec des contraintes de plus haut niveau. Un préprocesseur pourrait alors traduire ces énoncé en rang.

### Décomposition en couche
suggestion : les points de base
puis les points construits avec les points de base
puis les points de deuxième génération
puis ...
On peut même essayer de placer les points de générations utltérieurs un à un :
pour le calcul des rangs, ça ne change pas, en revanche le dernier lemme (le théorème) a une preuve moins long car les lemmes intermedaires sont produits à l'intersection des couches.

## Lemmes intermédiaires

Actuellement, la décomposition de la preuve suit une approche hiérarchique suggérée par le treillis matroïdal. De cette manière :
* le comportement du prouveur n'est pas trop perturbé ... il n'est pas amélioré non plus
* les traces utiles dans les sous-treillis sont rangées dans des lemmes d'une manière peu réutilisable en fait (même s'il y a des forall devant les points, le lemme n'est pas forcément symétrique vis-à-vis de l'introduction des points).
* la "factorisation" ne se fait qu'au niveau de la preuve et au moment de la reconstruction et cela permet à Coq de gérer le preuves engendrées qui sont très volumineuses.

On peut généraliser sans doute cette approche. Cependant, sans faire de changements radicaux, il me paraît difficile d'utiliser la décomposition du treillis  pour accélérer le calcul des rangs et ensuite pour utiliser, en toute généralité, les lemmes produits  dans le reste de la démonstration.

## Utilité des couches
En fait, la grande utilité des couches est de fabriquer des lemmes intermédiaires de sorte que la preuve de la conclusion ne soit pas trop longue : l'idée est que dans les couches tous les noeuds utilisés dans la preuve (marqués 1) donnent lieu à des lemmes.
Du coup, l'idée est la suivante : est-ce qu'avec 2 couches, une contenant quasiment tout et la dernière juste un point ou deux pour que le maximum de lemmes soient fabriqués n'est-elle pas suffisante pour simplifier la preuve ?
Même mieuw, on peut modifier un peu l'algorithme pour ne pas avoir à mettre de couches du tout !

### Discussion 
Rien n'empêche d'avoir une implantation non-hiérarchique des couches : il y a quelques retouches à faire dans la fonction main() (par exemple, ne pas faire de recopie du graphe qui doit être complété par de nouveaux points) et dans le marquage des sommets du graphe et dans le parcours pour déterminer la preuve par rétro-propagation. Cependant, l'utilité des morceaux "indépendants" n'est pas claire : on ne peut pas les utiliser dans le calcul des rangs (car cela serait beaucoup trop coûteux d'isoler tous les sommets "hypothèses") et donc ils ne seront pas non plus utilisés pour simplifier une longue preuve. 

C'est une des limites de cette approche qui avait comme objectif initial de faire des petites preuves et dont David a essayé de pousser plus loin pour prouver le théorème de Dandelin-Gallucci.

Pour faire des lemmes intermédiaires, il faudrait donc rester dans le contexte de Coq sans pouvoir utiliser cette possibilité à l'intérieur du solveur, à moins de le donner explicitement le moyen d'utiliser ces lemmes (par exemple avec le langage de l'interface) ... on se retrouve donc avec une des extensions initiales : pouvoir ajouter facilement des règles dans le prouveur. Au départ, cette extension était prévue pour faire le sens DG ==> Pappus, mais cette règle n'est pas facile à énoncer de manière à rester général et à prendre en compte : par exemple doit-on ajouter des points ou non ? 