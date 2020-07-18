# DG_rule
# tentative de définition de règle en utilisant l'exemple de DG
# qui est plutôt complexe.
# je remarqu'il est plus facile d'exprimer cette règle avec de la 
# géométrie qu'avec des rang ... c'était sans doute aussi le cas 
# de certains énoncés de thm ... sauf qu'en on arrive en dim. > 3
rule
hypotheses
    lines
        d1 d2 d3 d4 D1 D2 D3 D4
    points
        O A B C Ap Bp D E F G H I J K   
        # on ajoute le 16ème points ? a priori, DG dit que le rang de certains points
        # (ceux portés par deux droites) forment un ensemble de rang 3 (coplanaires)
        # et donc les droites se coupent 
        # cependant, la preuve de Papps par DL vu dans ... impose la création 
        # d'un nouveu point 
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