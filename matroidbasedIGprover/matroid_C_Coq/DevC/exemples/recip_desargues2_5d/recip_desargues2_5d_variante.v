Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LA : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HAM : rk(A ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HAeq HAM1).
assert(HAm : rk(A ::  nil) >= 1) by (solve_hyps_min HAeq HAm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LB : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HBM : rk(B ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HBeq HBM1).
assert(HBm : rk(B ::  nil) >= 1) by (solve_hyps_min HBeq HBm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LC : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HCM : rk(C ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HCeq HCM1).
assert(HCm : rk(C ::  nil) >= 1) by (solve_hyps_min HCeq HCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Ap ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HApM : rk(Ap ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HApeq HApM1).
assert(HApm : rk(Ap ::  nil) >= 1) by (solve_hyps_min HApeq HApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCAp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HABCApM : rk(A :: B :: C :: Ap ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApm : rk(A :: B :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HABCApeq HABCApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Bp ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HBpM : rk(Bp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HBpeq HBpM1).
assert(HBpm : rk(Bp ::  nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCBp *)
(* dans la couche 0 *)
Lemma LABCApBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBp requis par la preuve de (?)ABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpm4 : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpM : rk(A :: B :: C :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpm : rk(A :: B :: C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HABCApBpeq HABCApBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCBp *)
(* dans la couche 0 *)
Lemma LABApBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: Ap :: Bp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HABApBpM : rk(A :: B :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABApBpm : rk(A :: B :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HABApBpeq HABApBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Bp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CBp requis par la preuve de (?)CBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HCBpm2 : rk(C :: Bp :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApBpmtmp : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4) by (solve_hyps_min HABCApBpeq HABCApBpm4).
	try assert(HBpeq : rk(Bp :: nil) = 1) by (apply LBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (C :: Bp :: nil) (A :: B :: Ap :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: nil) (C :: Bp :: A :: B :: Ap :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Bp :: A :: B :: Ap :: Bp :: nil) ((C :: Bp :: nil) ++ (A :: B :: Ap :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpmtmp;try rewrite HT2 in HABCApBpmtmp.
	assert(HT := rule_2 (C :: Bp :: nil) (A :: B :: Ap :: Bp :: nil) (Bp :: nil) 4 1 3 HABCApBpmtmp HBpmtmp HABApBpMtmp Hincl);apply HT.
}


assert(HCBpM : rk(C :: Bp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCBpeq HCBpM2).
assert(HCBpm : rk(C :: Bp ::  nil) >= 1) by (solve_hyps_min HCBpeq HCBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HABCBpM : rk(A :: B :: C :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpm : rk(A :: B :: C :: Bp ::  nil) >= 1) by (solve_hyps_min HABCBpeq HABCBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCApBp *)
(* dans la couche 0 *)
Lemma LCApBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HCApBpCpM : rk(C :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HCApBpCpm : rk(C :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HCApBpCpeq HCApBpCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCApBp *)
(* dans la couche 0 *)
Lemma LCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Cp ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HCpM : rk(Cp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HCpeq HCpM1).
assert(HCpm : rk(Cp ::  nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCApBp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Ap :: Bp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CApBp requis par la preuve de (?)CApBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CApBp requis par la preuve de (?)CApBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp ::  de rang :  4 et 4 	 AiB : C :: Bp ::  de rang :  2 et 2 	 A : A :: B :: C :: Bp ::   de rang : 4 et 4 *)
assert(HCApBpm2 : rk(C :: Ap :: Bp :: nil) >= 2).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCBpMtmp : rk(A :: B :: C :: Bp :: nil) <= 4) by (solve_hyps_max HABCBpeq HABCBpM4).
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApBpmtmp : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4) by (solve_hyps_min HABCApBpeq HABCApBpm4).
	try assert(HCBpeq : rk(C :: Bp :: nil) = 2) by (apply LCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCBpmtmp : rk(C :: Bp :: nil) >= 2) by (solve_hyps_min HCBpeq HCBpm2).
	assert(Hincl : incl (C :: Bp :: nil) (list_inter (A :: B :: C :: Bp :: nil) (C :: Ap :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: nil) (A :: B :: C :: Bp :: C :: Ap :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Bp :: C :: Ap :: Bp :: nil) ((A :: B :: C :: Bp :: nil) ++ (C :: Ap :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpmtmp;try rewrite HT2 in HABCApBpmtmp.
	assert(HT := rule_4 (A :: B :: C :: Bp :: nil) (C :: Ap :: Bp :: nil) (C :: Bp :: nil) 4 2 4 HABCApBpmtmp HCBpmtmp HABCBpMtmp Hincl); apply HT.
}
try clear HCBpM1. try clear HCBpM2. try clear HCBpM3. try clear HCBpm4. try clear HCBpm3. try clear HCBpm2. try clear HCBpm1. try clear HABCApBpM1. try clear HABCApBpM2. try clear HABCApBpM3. try clear HABCApBpm4. try clear HABCApBpm3. try clear HABCApBpm2. try clear HABCApBpm1. 

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -1 et 4*)
assert(HCApBpm3 : rk(C :: Ap :: Bp :: nil) >= 3).
{
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpMtmp : rk(Cp :: nil) <= 1) by (solve_hyps_max HCpeq HCpM1).
	try assert(HCApBpCpeq : rk(C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LCApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpCpmtmp : rk(C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HCApBpCpeq HCApBpCpm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: Bp :: nil) (Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Bp :: Cp :: nil) (C :: Ap :: Bp :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: Cp :: nil) ((C :: Ap :: Bp :: nil) ++ (Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApBpCpmtmp;try rewrite HT2 in HCApBpCpmtmp.
	assert(HT := rule_2 (C :: Ap :: Bp :: nil) (Cp :: nil) (nil) 4 0 1 HCApBpCpmtmp Hmtmp HCpMtmp Hincl);apply HT.
}


assert(HCApBpM : rk(C :: Ap :: Bp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCApBpeq HCApBpM3).
assert(HCApBpm : rk(C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HCApBpeq HCApBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACp *)
(* dans la couche 0 *)
Lemma LABCCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HABCCpM : rk(A :: B :: C :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCCpm : rk(A :: B :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HABCCpeq HABCCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACp *)
(* dans la couche 0 *)
Lemma LACp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Cp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCCp requis par la preuve de (?)ACp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)BCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)ABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : B ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HBCCpm2 : rk(B :: C :: Cp :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm4).
	try assert(HBeq : rk(B :: nil) = 1) by (apply LB with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: Ap :: Bp :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: B :: C :: Cp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpmtmp;try rewrite HT2 in HABCApBpCpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (B :: C :: Cp :: nil) (B :: nil) 4 1 3 HABCApBpCpmtmp HBmtmp HABApBpMtmp Hincl); apply HT.
}
try clear HBM1. try clear HBM2. try clear HBM3. try clear HBm4. try clear HBm3. try clear HBm2. try clear HBm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ACp requis par la preuve de (?)ACp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HACpm2 : rk(A :: Cp :: nil) >= 2).
{
	assert(HBCCpMtmp : rk(B :: C :: Cp :: nil) <= 3) by (solve_hyps_max HBCCpeq HBCCpM3).
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: nil) (A :: Cp :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Cp :: nil) ((A :: Cp :: nil) ++ (B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpmtmp;try rewrite HT2 in HABCCpmtmp.
	assert(HT := rule_2 (A :: Cp :: nil) (B :: C :: Cp :: nil) (Cp :: nil) 4 1 3 HABCCpmtmp HCpmtmp HBCCpMtmp Hincl);apply HT.
}


assert(HACpM : rk(A :: Cp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HACpeq HACpM2).
assert(HACpm : rk(A :: Cp ::  nil) >= 1) by (solve_hyps_min HACpeq HACpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCp *)
(* dans la couche 0 *)
Lemma LBCCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)BCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)ABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : B ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HBCCpm2 : rk(B :: C :: Cp :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm4).
	try assert(HBeq : rk(B :: nil) = 1) by (apply LB with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: Ap :: Bp :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: B :: C :: Cp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpmtmp;try rewrite HT2 in HABCApBpCpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (B :: C :: Cp :: nil) (B :: nil) 4 1 3 HABCApBpCpmtmp HBmtmp HABApBpMtmp Hincl); apply HT.
}
try clear HBM1. try clear HBM2. try clear HBM3. try clear HBm4. try clear HBm3. try clear HBm2. try clear HBm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Cp ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : A :: Cp ::   de rang : 2 et 2 *)
assert(HBCCpm3 : rk(B :: C :: Cp :: nil) >= 3).
{
	try assert(HACpeq : rk(A :: Cp :: nil) = 2) by (apply LACp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACpMtmp : rk(A :: Cp :: nil) <= 2) by (solve_hyps_max HACpeq HACpM2).
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: nil) (A :: Cp :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Cp :: nil) ((A :: Cp :: nil) ++ (B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpmtmp;try rewrite HT2 in HABCCpmtmp.
	assert(HT := rule_4 (A :: Cp :: nil) (B :: C :: Cp :: nil) (Cp :: nil) 4 1 2 HABCCpmtmp HCpmtmp HACpMtmp Hincl); apply HT.
}


assert(HBCCpM : rk(B :: C :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBCCpeq HBCCpM3).
assert(HBCCpm : rk(B :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HBCCpeq HBCCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCp *)
(* dans la couche 0 *)
Lemma LCCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Cp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CCp requis par la preuve de (?)CCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : C :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HCCpm2 : rk(C :: Cp :: nil) >= 2).
{
	try assert(HCApBpeq : rk(C :: Ap :: Bp :: nil) = 3) by (apply LCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpMtmp : rk(C :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HCApBpeq HCApBpM3).
	try assert(HCApBpCpeq : rk(C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LCApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpCpmtmp : rk(C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HCApBpCpeq HCApBpCpm4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (C :: Ap :: Bp :: nil) (C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Bp :: Cp :: nil) (C :: Ap :: Bp :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: C :: Cp :: nil) ((C :: Ap :: Bp :: nil) ++ (C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApBpCpmtmp;try rewrite HT2 in HCApBpCpmtmp.
	assert(HT := rule_4 (C :: Ap :: Bp :: nil) (C :: Cp :: nil) (C :: nil) 4 1 3 HCApBpCpmtmp HCmtmp HCApBpMtmp Hincl); apply HT.
}
try clear HCM1. try clear HCM2. try clear HCM3. try clear HCm4. try clear HCm3. try clear HCm2. try clear HCm1. 

assert(HCCpM : rk(C :: Cp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCCpeq HCCpM2).
assert(HCCpm : rk(C :: Cp ::  nil) >= 1) by (solve_hyps_min HCCpeq HCCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Cp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BCp requis par la preuve de (?)BCp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HBCpm2 : rk(B :: Cp :: nil) >= 2).
{
	try assert(HCCpeq : rk(C :: Cp :: nil) = 2) by (apply LCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCCpMtmp : rk(C :: Cp :: nil) <= 2) by (solve_hyps_max HCCpeq HCCpM2).
	try assert(HBCCpeq : rk(B :: C :: Cp :: nil) = 3) by (apply LBCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCCpmtmp : rk(B :: C :: Cp :: nil) >= 3) by (solve_hyps_min HBCCpeq HBCCpm3).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (B :: Cp :: nil) (C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Cp :: nil) (B :: Cp :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Cp :: C :: Cp :: nil) ((B :: Cp :: nil) ++ (C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCCpmtmp;try rewrite HT2 in HBCCpmtmp.
	assert(HT := rule_2 (B :: Cp :: nil) (C :: Cp :: nil) (Cp :: nil) 3 1 2 HBCCpmtmp HCpmtmp HCCpMtmp Hincl);apply HT.
}


assert(HBCpM : rk(B :: Cp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBCpeq HBCpM2).
assert(HBCpm : rk(B :: Cp ::  nil) >= 1) by (solve_hyps_min HBCpeq HBCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACCp requis par la preuve de (?)ACCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)ACCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)ABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACCp requis par la preuve de (?)ACCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACCpm2 : rk(A :: C :: Cp :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm4).
	try assert(HAeq : rk(A :: nil) = 1) by (apply LA with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: Ap :: Bp :: A :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Cp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpmtmp;try rewrite HT2 in HABCApBpCpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Cp :: nil) (A :: nil) 4 1 3 HABCApBpCpmtmp HAmtmp HABApBpMtmp Hincl); apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Cp ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : B :: Cp ::   de rang : 2 et 2 *)
assert(HACCpm3 : rk(A :: C :: Cp :: nil) >= 3).
{
	try assert(HBCpeq : rk(B :: Cp :: nil) = 2) by (apply LBCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCpMtmp : rk(B :: Cp :: nil) <= 2) by (solve_hyps_max HBCpeq HBCpM2).
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (B :: Cp :: nil) (A :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: nil) (B :: Cp :: A :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Cp :: A :: C :: Cp :: nil) ((B :: Cp :: nil) ++ (A :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpmtmp;try rewrite HT2 in HABCCpmtmp.
	assert(HT := rule_4 (B :: Cp :: nil) (A :: C :: Cp :: nil) (Cp :: nil) 4 1 2 HABCCpmtmp HCpmtmp HBCpMtmp Hincl); apply HT.
}
try clear HABCCpM1. try clear HABCCpM2. try clear HABCCpM3. try clear HABCCpm4. try clear HABCCpm3. try clear HABCCpm2. try clear HABCCpm1. 

assert(HACCpM : rk(A :: C :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HACCpeq HACCpM3).
assert(HACCpm : rk(A :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HACCpeq HACCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Ap :: Cp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ApCp requis par la preuve de (?)ApCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HApCpm2 : rk(Ap :: Cp :: nil) >= 2).
{
	try assert(HCApBpeq : rk(C :: Ap :: Bp :: nil) = 3) by (apply LCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpMtmp : rk(C :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HCApBpeq HCApBpM3).
	try assert(HCApBpCpeq : rk(C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LCApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpCpmtmp : rk(C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HCApBpCpeq HCApBpCpm4).
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: Bp :: nil) (Ap :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Bp :: Cp :: nil) (C :: Ap :: Bp :: Ap :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: Ap :: Cp :: nil) ((C :: Ap :: Bp :: nil) ++ (Ap :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApBpCpmtmp;try rewrite HT2 in HCApBpCpmtmp.
	assert(HT := rule_4 (C :: Ap :: Bp :: nil) (Ap :: Cp :: nil) (Ap :: nil) 4 1 3 HCApBpCpmtmp HApmtmp HCApBpMtmp Hincl); apply HT.
}
try clear HApM1. try clear HApM2. try clear HApM3. try clear HApm4. try clear HApm3. try clear HApm2. try clear HApm1. 

assert(HApCpM : rk(Ap :: Cp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HApCpeq HApCpM2).
assert(HApCpm : rk(Ap :: Cp ::  nil) >= 1) by (solve_hyps_min HApCpeq HApCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAApCp *)
(* dans la couche 0 *)
Lemma LAApBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HAApBpCpM : rk(A :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HAApBpCpm : rk(A :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HAApBpCpeq HAApBpCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAApCp *)
(* dans la couche 0 *)
Lemma LBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Bp :: Cp ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BpCp requis par la preuve de (?)BpCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : Bp ::  de rang :  1 et 1 	 A : C :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HBpCpm2 : rk(Bp :: Cp :: nil) >= 2).
{
	try assert(HCApBpeq : rk(C :: Ap :: Bp :: nil) = 3) by (apply LCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpMtmp : rk(C :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HCApBpeq HCApBpM3).
	try assert(HCApBpCpeq : rk(C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LCApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCApBpCpmtmp : rk(C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HCApBpCpeq HCApBpCpm4).
	try assert(HBpeq : rk(Bp :: nil) = 1) by (apply LBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (C :: Ap :: Bp :: nil) (Bp :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Bp :: Cp :: nil) (C :: Ap :: Bp :: Bp :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: Bp :: Cp :: nil) ((C :: Ap :: Bp :: nil) ++ (Bp :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApBpCpmtmp;try rewrite HT2 in HCApBpCpmtmp.
	assert(HT := rule_4 (C :: Ap :: Bp :: nil) (Bp :: Cp :: nil) (Bp :: nil) 4 1 3 HCApBpCpmtmp HBpmtmp HCApBpMtmp Hincl); apply HT.
}
try clear HBpM1. try clear HBpM2. try clear HBpM3. try clear HBpm4. try clear HBpm3. try clear HBpm2. try clear HBpm1. try clear HCApBpCpM1. try clear HCApBpCpM2. try clear HCApBpCpM3. try clear HCApBpCpm4. try clear HCApBpCpm3. try clear HCApBpCpm2. try clear HCApBpCpm1. 

assert(HBpCpM : rk(Bp :: Cp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBpCpeq HBpCpM2).
assert(HBpCpm : rk(Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HBpCpeq HBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAApCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Ap :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AApCp requis par la preuve de (?)AApCp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour ACApCp requis par la preuve de (?)AApCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AApCp requis par la preuve de (?)AApCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: C :: Ap :: Cp ::  de rang :  3 et 3 	 AiB : Cp ::  de rang :  1 et 1 	 A : C :: Cp ::   de rang : 2 et 2 *)
assert(HAApCpm2 : rk(A :: Ap :: Cp :: nil) >= 2).
{
	try assert(HCCpeq : rk(C :: Cp :: nil) = 2) by (apply LCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCCpMtmp : rk(C :: Cp :: nil) <= 2) by (solve_hyps_max HCCpeq HCCpM2).
	assert(HACApCpmtmp : rk(A :: C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HACApCpeq HACApCpm3).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (C :: Cp :: nil) (A :: Ap :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Cp :: nil) (C :: Cp :: A :: Ap :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Cp :: A :: Ap :: Cp :: nil) ((C :: Cp :: nil) ++ (A :: Ap :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACApCpmtmp;try rewrite HT2 in HACApCpmtmp.
	assert(HT := rule_4 (C :: Cp :: nil) (A :: Ap :: Cp :: nil) (Cp :: nil) 3 1 2 HACApCpmtmp HCpmtmp HCCpMtmp Hincl); apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HAApCpm3 : rk(A :: Ap :: Cp :: nil) >= 3).
{
	try assert(HBpCpeq : rk(Bp :: Cp :: nil) = 2) by (apply LBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBpCpMtmp : rk(Bp :: Cp :: nil) <= 2) by (solve_hyps_max HBpCpeq HBpCpM2).
	try assert(HAApBpCpeq : rk(A :: Ap :: Bp :: Cp :: nil) = 4) by (apply LAApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAApBpCpmtmp : rk(A :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HAApBpCpeq HAApBpCpm4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Ap :: Cp :: nil) (Bp :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: Ap :: Bp :: Cp :: nil) (A :: Ap :: Cp :: Bp :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Ap :: Cp :: Bp :: Cp :: nil) ((A :: Ap :: Cp :: nil) ++ (Bp :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAApBpCpmtmp;try rewrite HT2 in HAApBpCpmtmp.
	assert(HT := rule_2 (A :: Ap :: Cp :: nil) (Bp :: Cp :: nil) (Cp :: nil) 4 1 2 HAApBpCpmtmp HCpmtmp HBpCpMtmp Hincl);apply HT.
}
try clear HBpCpM1. try clear HBpCpM2. try clear HBpCpM3. try clear HBpCpm4. try clear HBpCpm3. try clear HBpCpm2. try clear HBpCpm1. try clear HAApBpCpM1. try clear HAApBpCpM2. try clear HAApBpCpM3. try clear HAApBpCpm4. try clear HAApBpCpm3. try clear HAApBpCpm2. try clear HAApBpCpm1. 

assert(HAApCpM : rk(A :: Ap :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HAApCpeq HAApCpM3).
assert(HAApCpm : rk(A :: Ap :: Cp ::  nil) >= 1) by (solve_hyps_min HAApCpeq HAApCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Ap :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HACApCpM : rk(A :: C :: Ap :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApCpm : rk(A :: C :: Ap :: Cp ::  nil) >= 1) by (solve_hyps_min HACApCpeq HACApCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBBpCp *)
(* dans la couche 0 *)
Lemma LBApBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HBApBpCpM : rk(B :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBApBpCpm : rk(B :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HBApBpCpeq HBApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Bp :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BBpCp requis par la preuve de (?)BBpCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour BCBpCp requis par la preuve de (?)BBpCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BBpCp requis par la preuve de (?)BBpCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : B :: C :: Bp :: Cp ::  de rang :  3 et 3 	 AiB : Cp ::  de rang :  1 et 1 	 A : C :: Cp ::   de rang : 2 et 2 *)
assert(HBBpCpm2 : rk(B :: Bp :: Cp :: nil) >= 2).
{
	try assert(HCCpeq : rk(C :: Cp :: nil) = 2) by (apply LCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCCpMtmp : rk(C :: Cp :: nil) <= 2) by (solve_hyps_max HCCpeq HCCpM2).
	assert(HBCBpCpmtmp : rk(B :: C :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HBCBpCpeq HBCBpCpm3).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (C :: Cp :: nil) (B :: Bp :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: nil) (C :: Cp :: B :: Bp :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Cp :: B :: Bp :: Cp :: nil) ((C :: Cp :: nil) ++ (B :: Bp :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCBpCpmtmp;try rewrite HT2 in HBCBpCpmtmp.
	assert(HT := rule_4 (C :: Cp :: nil) (B :: Bp :: Cp :: nil) (Cp :: nil) 3 1 2 HBCBpCpmtmp HCpmtmp HCCpMtmp Hincl); apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : B :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : Ap :: Cp ::   de rang : 2 et 2 *)
assert(HBBpCpm3 : rk(B :: Bp :: Cp :: nil) >= 3).
{
	try assert(HApCpeq : rk(Ap :: Cp :: nil) = 2) by (apply LApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HApCpMtmp : rk(Ap :: Cp :: nil) <= 2) by (solve_hyps_max HApCpeq HApCpM2).
	try assert(HBApBpCpeq : rk(B :: Ap :: Bp :: Cp :: nil) = 4) by (apply LBApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBApBpCpmtmp : rk(B :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HBApBpCpeq HBApBpCpm4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (Ap :: Cp :: nil) (B :: Bp :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: Ap :: Bp :: Cp :: nil) (Ap :: Cp :: B :: Bp :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Cp :: B :: Bp :: Cp :: nil) ((Ap :: Cp :: nil) ++ (B :: Bp :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBApBpCpmtmp;try rewrite HT2 in HBApBpCpmtmp.
	assert(HT := rule_4 (Ap :: Cp :: nil) (B :: Bp :: Cp :: nil) (Cp :: nil) 4 1 2 HBApBpCpmtmp HCpmtmp HApCpMtmp Hincl); apply HT.
}
try clear HApCpM1. try clear HApCpM2. try clear HApCpM3. try clear HApCpm4. try clear HApCpm3. try clear HApCpm2. try clear HApCpm1. try clear HBApBpCpM1. try clear HBApBpCpM2. try clear HBApBpCpM3. try clear HBApBpCpm4. try clear HBApBpCpm3. try clear HBApBpCpm2. try clear HBApBpCpm1. 

assert(HBBpCpM : rk(B :: Bp :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBBpCpeq HBBpCpM3).
assert(HBBpCpm : rk(B :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HBBpCpeq HBBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Bp :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HBCBpCpM : rk(B :: C :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpCpm : rk(B :: C :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HBCBpCpeq HBCBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCp : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCp requis par la preuve de (?)ABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpCpM : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpm : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAApOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Ap :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HAApOoM : rk(A :: Ap :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HAApOoeq HAApOoM3).
assert(HAApOom : rk(A :: Ap :: Oo ::  nil) >= 1) by (solve_hyps_min HAApOoeq HAApOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBBpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

assert(HBBpOoM : rk(B :: Bp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBBpOoeq HBBpOoM3).
assert(HBBpOom : rk(B :: Bp :: Oo ::  nil) >= 1) by (solve_hyps_min HBBpOoeq HBBpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LACCpOo *)
(* dans constructLemma(), requis par LACApCpOo *)
(* dans la couche 0 *)
Lemma LAApCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Ap :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AApCpOo requis par la preuve de (?)AApCpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AApCpOo requis par la preuve de (?)AApCpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour AApCpOo requis par la preuve de (?)AApCpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HAApCpOoM3 : rk(A :: Ap :: Cp :: Oo :: nil) <= 3).
{
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpMtmp : rk(Cp :: nil) <= 1) by (solve_hyps_max HCpeq HCpM1).
	try assert(HAApOoeq : rk(A :: Ap :: Oo :: nil) = 2) by (apply LAApOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAApOoMtmp : rk(A :: Ap :: Oo :: nil) <= 2) by (solve_hyps_max HAApOoeq HAApOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Cp :: nil) (A :: Ap :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: Ap :: Cp :: Oo :: nil) (Cp :: A :: Ap :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Cp :: A :: Ap :: Oo :: nil) ((Cp :: nil) ++ (A :: Ap :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Cp :: nil) (A :: Ap :: Oo :: nil) (nil) 1 2 0 HCpMtmp HAApOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HAApOoM1. try clear HAApOoM2. try clear HAApOoM3. try clear HAApOom4. try clear HAApOom3. try clear HAApOom2. try clear HAApOom1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAApCpOom2 : rk(A :: Ap :: Cp :: Oo :: nil) >= 2).
{
	try assert(HACpeq : rk(A :: Cp :: nil) = 2) by (apply LACp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACpmtmp : rk(A :: Cp :: nil) >= 2) by (solve_hyps_min HACpeq HACpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil) 2 2 HACpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAApCpOom3 : rk(A :: Ap :: Cp :: Oo :: nil) >= 3).
{
	try assert(HAApCpeq : rk(A :: Ap :: Cp :: nil) = 3) by (apply LAApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAApCpmtmp : rk(A :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HAApCpeq HAApCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: Ap :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: Ap :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil) 3 3 HAApCpmtmp Hcomp Hincl);apply HT.
}


assert(HAApCpOoM : rk(A :: Ap :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HAApCpOom : rk(A :: Ap :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HAApCpOoeq HAApCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Ap :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApCpOo requis par la preuve de (?)ACApCpOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)ACApCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)ABCApCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpOom4 : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApCpOo requis par la preuve de (?)ACApCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ACApCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ABCApBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}
try clear HABCApM1. try clear HABCApM2. try clear HABCApM3. try clear HABCApm4. try clear HABCApm3. try clear HABCApm2. try clear HABCApm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AAp requis par la preuve de (?)ACApCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApCpOo requis par la preuve de (?)ACApCpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : A :: Ap ::  de rang :  1 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACApCpOom2 : rk(A :: C :: Ap :: Cp :: Oo :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpOomtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCApBpCpOoeq HABCApBpCpOom4).
	assert(HAApmtmp : rk(A :: Ap :: nil) >= 1) by (solve_hyps_min HAApeq HAApm1).
	assert(Hincl : incl (A :: Ap :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) (A :: B :: Ap :: Bp :: A :: C :: Ap :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Ap :: Cp :: Oo :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Ap :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpOomtmp;try rewrite HT2 in HABCApBpCpOomtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Cp :: Oo :: nil) (A :: Ap :: nil) 4 1 3 HABCApBpCpOomtmp HAApmtmp HABApBpMtmp Hincl); apply HT.
}
try clear HAApM1. try clear HAApM2. try clear HAApM3. try clear HAApm4. try clear HAApm3. try clear HAApm2. try clear HAApm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : B :: Cp ::   de rang : 2 et 2 *)
assert(HACApCpOom3 : rk(A :: C :: Ap :: Cp :: Oo :: nil) >= 3).
{
	try assert(HBCpeq : rk(B :: Cp :: nil) = 2) by (apply LBCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCpMtmp : rk(B :: Cp :: nil) <= 2) by (solve_hyps_max HBCpeq HBCpM2).
	assert(HABCApCpOomtmp : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCApCpOoeq HABCApCpOom4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (B :: Cp :: nil) (A :: C :: Ap :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: Oo :: nil) (B :: Cp :: A :: C :: Ap :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Cp :: A :: C :: Ap :: Cp :: Oo :: nil) ((B :: Cp :: nil) ++ (A :: C :: Ap :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpOomtmp;try rewrite HT2 in HABCApCpOomtmp.
	assert(HT := rule_4 (B :: Cp :: nil) (A :: C :: Ap :: Cp :: Oo :: nil) (Cp :: nil) 4 1 2 HABCApCpOomtmp HCpmtmp HBCpMtmp Hincl); apply HT.
}
try clear HABCApCpOoM1. try clear HABCApCpOoM2. try clear HABCApCpOoM3. try clear HABCApCpOom4. try clear HABCApCpOom3. try clear HABCApCpOom2. try clear HABCApCpOom1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HACApCpOoM3 : rk(A :: C :: Ap :: Cp :: Oo :: nil) <= 3).
{
	try assert(HACApCpeq : rk(A :: C :: Ap :: Cp :: nil) = 3) by (apply LACApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACApCpMtmp : rk(A :: C :: Ap :: Cp :: nil) <= 3) by (solve_hyps_max HACApCpeq HACApCpM3).
	try assert(HAApCpOoeq : rk(A :: Ap :: Cp :: Oo :: nil) = 3) by (apply LAApCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAApCpOoMtmp : rk(A :: Ap :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HAApCpOoeq HAApCpOoM3).
	try assert(HAApCpeq : rk(A :: Ap :: Cp :: nil) = 3) by (apply LAApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAApCpmtmp : rk(A :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HAApCpeq HAApCpm3).
	assert(Hincl : incl (A :: Ap :: Cp :: nil) (list_inter (A :: C :: Ap :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Cp :: Oo :: nil) (A :: C :: Ap :: Cp :: A :: Ap :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Ap :: Cp :: A :: Ap :: Cp :: Oo :: nil) ((A :: C :: Ap :: Cp :: nil) ++ (A :: Ap :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: C :: Ap :: Cp :: nil) (A :: Ap :: Cp :: Oo :: nil) (A :: Ap :: Cp :: nil) 3 3 3 HACApCpMtmp HAApCpOoMtmp HAApCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HACApCpOoM : rk(A :: C :: Ap :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApCpOom : rk(A :: C :: Ap :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HACApCpOoeq HACApCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACCpOo requis par la preuve de (?)ACCpOo pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACCpOo requis par la preuve de (?)ACCpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ACCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ABCApBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACCpOo requis par la preuve de (?)ACCpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACCpOom2 : rk(A :: C :: Cp :: Oo :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpOomtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCApBpCpOoeq HABCApBpCpOom4).
	try assert(HAeq : rk(A :: nil) = 1) by (apply LA with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) (A :: B :: Ap :: Bp :: A :: C :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Cp :: Oo :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpOomtmp;try rewrite HT2 in HABCApBpCpOomtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Cp :: Oo :: nil) (A :: nil) 4 1 3 HABCApBpCpOomtmp HAmtmp HABApBpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACCpOom3 : rk(A :: C :: Cp :: Oo :: nil) >= 3).
{
	try assert(HACCpeq : rk(A :: C :: Cp :: nil) = 3) by (apply LACCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACCpmtmp : rk(A :: C :: Cp :: nil) >= 3) by (solve_hyps_min HACCpeq HACCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Cp :: nil) (A :: C :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Cp :: nil) (A :: C :: Cp :: Oo :: nil) 3 3 HACCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACCpOoM3 : rk(A :: C :: Cp :: Oo :: nil) <= 3).
{
	try assert(HACApCpOoeq : rk(A :: C :: Ap :: Cp :: Oo :: nil) = 3) by (apply LACApCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACApCpOoMtmp : rk(A :: C :: Ap :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HACApCpOoeq HACApCpOoM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Cp :: Oo :: nil) (A :: C :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: C :: Cp :: Oo :: nil) (A :: C :: Ap :: Cp :: Oo :: nil) 3 3 HACApCpOoMtmp Hcomp Hincl);apply HT.
}


assert(HACCpOoM : rk(A :: C :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACCpOom : rk(A :: C :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HACCpOoeq HACCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)ABCApCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpOom4 : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApCpOoM : rk(A :: B :: C :: Ap :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApCpOom : rk(A :: B :: C :: Ap :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApCpOoeq HABCApCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBBpCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Bp :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BBpCpOo requis par la preuve de (?)BBpCpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BBpCpOo requis par la preuve de (?)BBpCpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BBpCpOo requis par la preuve de (?)BBpCpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HBBpCpOoM3 : rk(B :: Bp :: Cp :: Oo :: nil) <= 3).
{
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpMtmp : rk(Cp :: nil) <= 1) by (solve_hyps_max HCpeq HCpM1).
	try assert(HBBpOoeq : rk(B :: Bp :: Oo :: nil) = 2) by (apply LBBpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBBpOoMtmp : rk(B :: Bp :: Oo :: nil) <= 2) by (solve_hyps_max HBBpOoeq HBBpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Cp :: nil) (B :: Bp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: Bp :: Cp :: Oo :: nil) (Cp :: B :: Bp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Cp :: B :: Bp :: Oo :: nil) ((Cp :: nil) ++ (B :: Bp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Cp :: nil) (B :: Bp :: Oo :: nil) (nil) 1 2 0 HCpMtmp HBBpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBBpOoM1. try clear HBBpOoM2. try clear HBBpOoM3. try clear HBBpOom4. try clear HBBpOom3. try clear HBBpOom2. try clear HBBpOom1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBBpCpOom2 : rk(B :: Bp :: Cp :: Oo :: nil) >= 2).
{
	try assert(HBCpeq : rk(B :: Cp :: nil) = 2) by (apply LBCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCpmtmp : rk(B :: Cp :: nil) >= 2) by (solve_hyps_min HBCpeq HBCpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil) 2 2 HBCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBBpCpOom3 : rk(B :: Bp :: Cp :: Oo :: nil) >= 3).
{
	try assert(HBBpCpeq : rk(B :: Bp :: Cp :: nil) = 3) by (apply LBBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBBpCpmtmp : rk(B :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HBBpCpeq HBBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: Bp :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: Bp :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil) 3 3 HBBpCpmtmp Hcomp Hincl);apply HT.
}


assert(HBBpCpOoM : rk(B :: Bp :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBBpCpOom : rk(B :: Bp :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HBBpCpOoeq HBBpCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCBpCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Bp :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpCpOo requis par la preuve de (?)BCBpCpOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCBpCpOo requis par la preuve de (?)BCBpCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpCpOo requis par la preuve de (?)ABCBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpCpOom4 : rk(A :: B :: C :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpCpOo requis par la preuve de (?)BCBpCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)BCBpCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ABCApBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}
try clear HABCApM1. try clear HABCApM2. try clear HABCApM3. try clear HABCApm4. try clear HABCApm3. try clear HABCApm2. try clear HABCApm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)BCBpCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpCpOo requis par la preuve de (?)BCBpCpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : B :: Bp ::  de rang :  1 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HBCBpCpOom2 : rk(B :: C :: Bp :: Cp :: Oo :: nil) >= 2).
{
	try assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpCpOomtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCApBpCpOoeq HABCApBpCpOom4).
	assert(HBBpmtmp : rk(B :: Bp :: nil) >= 1) by (solve_hyps_min HBBpeq HBBpm1).
	assert(Hincl : incl (B :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) (A :: B :: Ap :: Bp :: B :: C :: Bp :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: B :: C :: Bp :: Cp :: Oo :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpOomtmp;try rewrite HT2 in HABCApBpCpOomtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: Oo :: nil) (B :: Bp :: nil) 4 1 3 HABCApBpCpOomtmp HBBpmtmp HABApBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : A :: Cp ::   de rang : 2 et 2 *)
assert(HBCBpCpOom3 : rk(B :: C :: Bp :: Cp :: Oo :: nil) >= 3).
{
	try assert(HACpeq : rk(A :: Cp :: nil) = 2) by (apply LACp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACpMtmp : rk(A :: Cp :: nil) <= 2) by (solve_hyps_max HACpeq HACpM2).
	assert(HABCBpCpOomtmp : rk(A :: B :: C :: Bp :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCBpCpOoeq HABCBpCpOom4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Bp :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: Cp :: Oo :: nil) (A :: Cp :: B :: C :: Bp :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Bp :: Cp :: Oo :: nil) ((A :: Cp :: nil) ++ (B :: C :: Bp :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpCpOomtmp;try rewrite HT2 in HABCBpCpOomtmp.
	assert(HT := rule_4 (A :: Cp :: nil) (B :: C :: Bp :: Cp :: Oo :: nil) (Cp :: nil) 4 1 2 HABCBpCpOomtmp HCpmtmp HACpMtmp Hincl); apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCBpCpOoM3 : rk(B :: C :: Bp :: Cp :: Oo :: nil) <= 3).
{
	try assert(HBCBpCpeq : rk(B :: C :: Bp :: Cp :: nil) = 3) by (apply LBCBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCBpCpMtmp : rk(B :: C :: Bp :: Cp :: nil) <= 3) by (solve_hyps_max HBCBpCpeq HBCBpCpM3).
	try assert(HBBpCpOoeq : rk(B :: Bp :: Cp :: Oo :: nil) = 3) by (apply LBBpCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBBpCpOoMtmp : rk(B :: Bp :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HBBpCpOoeq HBBpCpOoM3).
	try assert(HBBpCpeq : rk(B :: Bp :: Cp :: nil) = 3) by (apply LBBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBBpCpmtmp : rk(B :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HBBpCpeq HBBpCpm3).
	assert(Hincl : incl (B :: Bp :: Cp :: nil) (list_inter (B :: C :: Bp :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: Oo :: nil) (B :: C :: Bp :: Cp :: B :: Bp :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Bp :: Cp :: B :: Bp :: Cp :: Oo :: nil) ((B :: C :: Bp :: Cp :: nil) ++ (B :: Bp :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: Bp :: Cp :: nil) (B :: Bp :: Cp :: Oo :: nil) (B :: Bp :: Cp :: nil) 3 3 3 HBCBpCpMtmp HBBpCpOoMtmp HBBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HBCBpCpOoM : rk(B :: C :: Bp :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpCpOom : rk(B :: C :: Bp :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HBCBpCpOoeq HBCBpCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCBpCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp :: Cp :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpCpOo requis par la preuve de (?)ABCBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpCpOom4 : rk(A :: B :: C :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


assert(HABCBpCpOoM : rk(A :: B :: C :: Bp :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpCpOom : rk(A :: B :: C :: Bp :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HABCBpCpOoeq HABCBpCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpOo requis par la preuve de (?)ABCApBpCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}
try clear HABCApM1. try clear HABCApM2. try clear HABCApM3. try clear HABCApm4. try clear HABCApm3. try clear HABCApm2. try clear HABCApm1. 

assert(HABCApBpCpOoM : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpOom : rk(A :: B :: C :: Ap :: Bp :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApBpCpOoeq HABCApBpCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCCpOo : forall A B C Ap Bp Cp Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: Ap :: Bp ::  nil) = 3 ->
rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(A :: C :: Ap :: Cp ::  nil) = 3 -> rk(B :: C :: Bp :: Cp ::  nil) = 3 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Cp :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp Oo 
HABCApeq HABCBpeq HABApBpeq HABCCpeq HACApCpeq HBCBpCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HAApOoeq
HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CCpOo requis par la preuve de (?)CCpOo pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CCpOo requis par la preuve de (?)CCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCCpOom2 : rk(C :: Cp :: Oo :: nil) >= 2).
{
	try assert(HCCpeq : rk(C :: Cp :: nil) = 2) by (apply LCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HCCpmtmp : rk(C :: Cp :: nil) >= 2) by (solve_hyps_min HCCpeq HCCpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Cp :: nil) (C :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Cp :: nil) (C :: Cp :: Oo :: nil) 2 2 HCCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HCCpOoM2 : rk(C :: Cp :: Oo :: nil) <= 2).
{
	try assert(HACCpOoeq : rk(A :: C :: Cp :: Oo :: nil) = 3) by (apply LACCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HACCpOoMtmp : rk(A :: C :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HACCpOoeq HACCpOoM3).
	try assert(HBCBpCpOoeq : rk(B :: C :: Bp :: Cp :: Oo :: nil) = 3) by (apply LBCBpCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HBCBpCpOoMtmp : rk(B :: C :: Bp :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HBCBpCpOoeq HBCBpCpOoM3).
	try assert(HABCBpCpOoeq : rk(A :: B :: C :: Bp :: Cp :: Oo :: nil) = 4) by (apply LABCBpCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Oo := Oo) ;try assumption).
	assert(HABCBpCpOomtmp : rk(A :: B :: C :: Bp :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCBpCpOoeq HABCBpCpOom4).
	assert(Hincl : incl (C :: Cp :: Oo :: nil) (list_inter (A :: C :: Cp :: Oo :: nil) (B :: C :: Bp :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: Cp :: Oo :: nil) (A :: C :: Cp :: Oo :: B :: C :: Bp :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Cp :: Oo :: B :: C :: Bp :: Cp :: Oo :: nil) ((A :: C :: Cp :: Oo :: nil) ++ (B :: C :: Bp :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpCpOomtmp;try rewrite HT2 in HABCBpCpOomtmp.
	assert(HT := rule_3 (A :: C :: Cp :: Oo :: nil) (B :: C :: Bp :: Cp :: Oo :: nil) (C :: Cp :: Oo :: nil) 3 3 4 HACCpOoMtmp HBCBpCpOoMtmp HABCBpCpOomtmp Hincl);apply HT.
}


assert(HCCpOoM : rk(C :: Cp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCCpOoeq HCCpOoM3).
assert(HCCpOom : rk(C :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HCCpOoeq HCCpOom1).
intuition.
Qed.

