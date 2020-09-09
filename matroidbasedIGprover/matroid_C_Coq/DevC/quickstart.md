# Prise en main rapide

## Installation
Après avoir décompressé le fichier fourni, on a une arborescence avec les sources (src), les fichiers d'en-têtes (include), les fichiers objets, ... Il y a des exemples dans le répertoire ... "exemples".

 Le fichier Makefile est à la racine de cette arborescence. On lance "make" et normalement un fichier exécutable de nom "main" est dans bin.

## Ligne de commandes
Le nom de l'exécutable, faute de mieux pour le moment est main. Il n'y a pas vraiment de mode interactif, les noms de fichiers dans lesquels sont rangées les données et dans lequels les résultats seront stockés sont donné sur la ligne de commande (sinon ils ont des noms par défaut).

Pour le moment, le contrôle n'est pas robuste et on s'expose facilement à un arrêt brutal avec un "core dump".

Syntaxe :
> main \<nom de l'énoncé>
> 
ou

> main -s <énoncé> -ro \<rangs> -co \<preuvecoq> -n <règlesadd>

ou

> main -h

Dans le cas de le première ou de la deuxième forme si les options -ro et -co ne sont pas utilisées, le nom de l'énoncé est utilisé pour nommer les fichiers de sortie.

## Format des énoncés

Les énoncés sont écrits dans des fichiers textes qui ont la forme suivante :

- une section contexte qui commence par la ligne `context` et qui finit par la ligne `endofcontext`
  - qui contient l'indication de dimension du théorème : `dimension xxx` où `xxx` vaut un entier de 2 à 7.
  - le nombre de couches : `layers xxx` où `xxx` est un entier compris entre 1 et 16 (pour le moment)
- plusieurs sections layer (autant qu'indiqué dans la section `context` après le mot clé `layers`). Chaque couche (layer) commence par une ligne avec le mot clé `layer` suivi d'un nom (au plus 15 caractères) en se termine avec la ligne `endoflayer`. Dans chaque section layers, on doit trouver dans l'ordre décrit ci-dessous :
    - la liste des points de la couche, 
      - cette liste peut inclure les points de couches déjà définies en indiquant le mot clé `layer` suivi du nom de la couche,
      - mais aussi des points ajoutés pour cette couche, chaque point est désigné par un nom d'au plus 15 caractères
        
        voici un exemple (les indentations sont libres)
        ```
        layer tetraedres
          points
            layer triangles
            D Dp ad bd cd
         ...
         endoflayer
         ```
    - on a ensuite la liste des hypothèses sous forme de rangs imposés imposés à des ensemble. Il y a une hypothèse par ligne. Par exemple `A B C : 3` pour indiquer que ABC est un triangle non dégénéré.
    - et finalement, sous la même forme une conclusion (une conclusion par couche, ça peut servir pour le débogage) et des propriétés en plus qu'on pourrait vouloir vérifier (le solveur ne traite actuellement qu'une conclusion et je ne sais pas 'il mène la saturation jusqu'au bout).
    Voici un exemple complet de couche (desargues3D). Comme on le voit les propriétés supplémentaires ne sont pas forcément requises.
    ```
    layer tetraedres
      points
        layer triangles
        D Dp ad bd cd
     hypotheses
        O D : 2
        A D : 2
        B D : 2
        C D : 2
        O Dp : 2
        Ap Dp : 2
        Bp Dp : 2
        Cp Dp : 2
        D Dp : 2
        O D Dp : 2
        ad A D : 2
        ad Ap Dp : 2
        bd B D : 2
        bd Bp Dp : 2
        cd C D : 2
        cd Cp Dp : 2
        A B D : 3
        A C D : 3
        B C D : 3
        Ap Bp Dp : 3
        Ap Cp Dp : 3
        Bp Cp Dp : 3
        A B C D : 4
        Ap Bp Cp Dp : 4
        O A B C : 4
        O A B D : 4
        O A C D : 4
        O B C D : 4
        O Ap Bp Dp : 4
        O Ap Cp Dp : 4
        O Bp Cp Dp : 4
     conclusion
        ab ac ad bc bd cd : 3
    ```
- enfin, après la dernière couche, on a une conclusion générale et des propriétés supplémentaires à vérifier. Pour le moment, ceci n'est pas exploité sauf pour un affiche de contrôle.
Les commentaires commencent par un dièse # suivi d'un espace et se terminent avec la fin de la ligne. 
L'exemple complet du théorème de Deargues 3D est donné en annexe.


## Exploration du matroïde produit

Pas vraiment fait pour le moment sauf de manière sommaire. c'est le fichier des rangs qui est exploité.

## Sortie Coq

On peut choisir le nom du fichier. Le mutli-couche est exploité de manière simple, un certain nombre de choses restent à faire (coloration par exemple).

## Annexe

```

# fichier desargues3D_couches.txt
# Attention avec les commentaires :
#    il faut absolument un espace après #
# premier essai avec des couches
# les couches font partie de la réflection de la preuve :
# c'est une première ébauche de décomposition par blocs
# qui se traduit facilement en décomposition de preuve
context
   dimension  3 
   layers   2
endofcontext
# ----------- première couche : 
#  c'est Desarges en 2,5 D 2 triangles en perspectives dans l'espace
layer triangles
  points
    O A B C Ap Bp Cp ab ac bc
  hypotheses
    O A : 2
    O B : 2
    O C : 2
    A B : 2
    A C : 2
    B C : 2
    O Ap : 2
    O Bp : 2
    O Cp : 2
    Ap Bp : 2
    Ap Cp : 2
    Bp Cp : 2
    A Ap : 2
    B Bp : 2
    C Cp : 2
    O A Ap : 2
    O B Bp : 2
    O C Cp : 2
    ab A B : 2
    ab Ap Bp : 2
    ac A C : 2
    ac Ap Cp : 2
    bc B C : 2
    bc Bp Cp : 2
    A B C : 3
    Ap Bp Cp : 3
    O A B C : 4
    O Ap Bp Cp : 4
  conclusion
     ab ac bc : 2
endoflayer # triangles
# ------- deuxième couche : 
#  on ajoute le point D
layer tetraedres
   points
     layer triangles
     D Dp ad bd cd
  hypotheses
    O D : 2
    A D : 2
    B D : 2
    C D : 2
    O Dp : 2
    Ap Dp : 2
    Bp Dp : 2
    Cp Dp : 2
    D Dp : 2
    O D Dp : 2
    ad A D : 2
    ad Ap Dp : 2
    bd B D : 2
    bd Bp Dp : 2
    cd C D : 2
    cd Cp Dp : 2
    A B D : 3
    A C D : 3
    B C D : 3
    Ap Bp Dp : 3
    Ap Cp Dp : 3
    Bp Cp Dp : 3
    A B C D : 4
    Ap Bp Cp Dp : 4
    O A B C : 4
    O A B D : 4
    O A C D : 4
    O B C D : 4
    O Ap Bp Dp : 4
    O Ap Cp Dp : 4
    O Bp Cp Dp : 4
  conclusion
    ab ac ad bc bd cd : 3
endoflayer # tetrahedres
conclusion
   ab ac ad bc bd cd : 3
supplements
bc bd cd : 2
ac ad cd : 2
ab ad bd : 2
ab ac bc : 2
end

```