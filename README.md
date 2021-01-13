# Bip 

## Bip : Matroid based Incidence Prover
This project is a fork of David Braun's prover developped at the end of his PhD.

The main design is preserved while some things have radically changed.

IO have been extended a lot. Specifically, a specification language is designed in order to easily try the prover.
This specification language includes a syntax for describing layers and the rank solver main loop has been modified accordingly.
The statement is written in a '*.stat' file using the specifiaction language.

Moreover, the solver has now debugging options and can produce different outputs :
- a file ('*.out') containing the lattice subtended by the matroid with the rank of each subset. In addition some tools are able to explore the matroid.
- a file ('*.v') for the Coq proof of the Lemma.
- todo/in progress: a file with the whole graph corresponding to the demonstration with tools to discover new theorems implied by the configuration.

In fact, the decompostion of a theorem into hierarchic layers is useless when it comes to increase the speed of the solver. This method was designed to reduce the size of the theorem proof.
But it is possible to do this within one layer and the simplication of the last lemma is dratically reduced compartively with the original algorithm. The idea is to write as lemma as many pieces of proof as possible. To d this, the order of reconstruction has to be reconsidered : it is not the arithmetic order of the set, but the topologic order wrt the dependences (the dependences are computed using the David's back travelsal algorithm)

The reconstruction of the Coq proof is safer and the algorithm slighty different. The ABC vs P1P2 notations can be used (this needs a modification in parties.h, by adding or not #define ABC, and a re-compilation).

A lot of comments have been added (mostly in French, sorry)

