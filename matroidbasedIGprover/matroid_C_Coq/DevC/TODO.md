# TODO et remarques

## Décomposition et construction de la preuve
Dans les preuves (je ne les ai pas toutes regardées), on note la fabrication d'un grand nombre de lemmes inutiles : par exemple des lemmes où la conclusion est que le rang d'un ensemble avec un seul point est 1 (est-ce bug qui prend en compte des restes de l'initialisation ?) ou alors dont la conclusion est incluse dans les prémisses.
Il faudrait soit revoir la construction des lemmes et tâcher de fabriquer des choses intéressantes ou, si ça n'est pas possible, de nettoyer après-coup, la base de lemmes locale pour éliminer les lemmes triviaux.

Par ailleurs, la décomposition et la reconstruction de lemmes correspond à une certaine idée de la structure de la preuve correspondant à la construction de points intermédiaires. Dans le cas de la preuve de Desargues en dimension n, il y a une structuration et des lemmes de bases qui ne correspondent pas forcément à une preuve sympa : par exemple, on aimerait pouvoir réutiliser que 2 triagles en prespectives satisfont les hyptohèses de Desargues 2,5D et le réutiliser sur toutes les 2-facettes.


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
mais aussi lors de mes tentatives de définir 3 plans "indépendants" en 3D, c'est-à-dire 3 plans qui ne se coupaient pas suivant la même droite.
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
