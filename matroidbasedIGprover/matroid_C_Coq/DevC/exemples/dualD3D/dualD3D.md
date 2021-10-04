# Dual du théorème de Desargues en 3D

## Rappel
On rappelle le théorème de Desargues en 3D :
```
Théorème.
Dans un espace projective d'incidence de dimension 3, si deux tétraèdres ABCD et A'B'C'D' sont en perspective suivant un point O, alors les 6 points d'intersection des cotés correspondants, s'ils existent, sont coplanaires et forment un quadrilatère complet.
```

## Formulation duale
On a le théorème dual en échangeant les types point et plan :

```
Théorème.
Dans un espace projective d'incidence de dimension 3, on se donne 9 plans PA, PB, PC, PD, PA', PB', PC', PD' et PO tels que l'intersection des 4 plans PA, PB, PC, PD est vide et l'intersection des 4 plans PA', PB', PC', PD' aussi. Si les intersection des plans correspondants consistent chacune en une droite contenue dans le plan PO, alors les droites définies par PA, PB d'une part et PA' PB', d'aute part sont coplanaires, ainsi que les 5 autres couples de droites définies de manière similaire. De plus, les 6 plans ainsi définis se coupent en un point.
```

Si on essaie brutalement de définir l'énoncé obtenu en n'utilisant que des points, on a 9 x 3 27 points rien que pour définir les 9 plans initaux. Il faut ensuite ajouter les 4 conditions sur leur intersection et l'inclusion dans PO ce qui ajoute 8 points, plus encores les 12 droites coplanaires (12 * 2 = 24 points) ce qui nous donne 59 points ... c'est beaucoup.

## Simplification
En essayant de simplifier au maximum, les 4 plans PA, PB, PC et PD en position générale peuvent être définis par 4 points seulement qui sont les points définis par 3 d'entre eux. Autrement dit, les dux quadruplets de plans peuvent être définis par 2 tétradèdres ! Appelons-les ABCD et A'B'C'D'.

La condidions d'intersection des plans (qui doit être inclue dans le plan PO) indique finalement que les deux faces se coupent en une droite de PO. Les quatres droites de PO forment un quadrilatère parfait et en mettant les 4 conditions ensembles, les sommets de ce quadrilatères sont les intersections des cotes correspondants.

La conclusion dit que les tétraèdres sont en perspectives.

Et donc, au bout du compte, le dual du théorème de Desargues en 3D correspond, modulo quelques résultats intermédiaires, à la réciproque de ce même théorème.

Remarque : c'est aussi ce qui se passe en 2D O:-*



