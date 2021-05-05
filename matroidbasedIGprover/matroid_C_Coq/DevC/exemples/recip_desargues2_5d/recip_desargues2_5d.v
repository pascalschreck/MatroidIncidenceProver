Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LA : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HAM : rk(A ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HAeq HAM1).
assert(HAm : rk(A ::  nil) >= 1) by (solve_hyps_min HAeq HAm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LB : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HBM : rk(B ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HBeq HBM1).
assert(HBm : rk(B ::  nil) >= 1) by (solve_hyps_min HBeq HBm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LC : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HCM : rk(C ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HCeq HCM1).
assert(HCm : rk(C ::  nil) >= 1) by (solve_hyps_min HCeq HCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Ap ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HApM : rk(Ap ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HApeq HApM1).
assert(HApm : rk(Ap ::  nil) >= 1) by (solve_hyps_min HApeq HApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCAp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HABCApM : rk(A :: B :: C :: Ap ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApm : rk(A :: B :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HABCApeq HABCApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Bp ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HBpM : rk(Bp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HBpeq HBpM1).
assert(HBpm : rk(Bp ::  nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCBp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HABCBpM : rk(A :: B :: C :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpm : rk(A :: B :: C :: Bp ::  nil) >= 1) by (solve_hyps_min HABCBpeq HABCBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBp requis par la preuve de (?)ABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpm4 : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpM : rk(A :: B :: C :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpm : rk(A :: B :: C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HABCApBpeq HABCApBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Cp ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HCpM : rk(Cp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HCpeq HCpM1).
assert(HCpm : rk(Cp ::  nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCCp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HABCCpM : rk(A :: B :: C :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCCpm : rk(A :: B :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HABCCpeq HABCCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCp : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCp requis par la preuve de (?)ABCApCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpm4 : rk(A :: B :: C :: Ap :: Cp :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApCpM : rk(A :: B :: C :: Ap :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApCpm : rk(A :: B :: C :: Ap :: Cp ::  nil) >= 1) by (solve_hyps_min HABCApCpeq HABCApCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(alpha ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HalphaM : rk(alpha ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max Halphaeq HalphaM1).
assert(Halpham : rk(alpha ::  nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LAalpha *)
(* dans la couche 0 *)
Lemma LABCApalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApalpha requis par la preuve de (?)ABCApalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApalpham4 : rk(A :: B :: C :: Ap :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApalphaM : rk(A :: B :: C :: Ap :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApalpham : rk(A :: B :: C :: Ap :: alpha ::  nil) >= 1) by (solve_hyps_min HABCApalphaeq HABCApalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LAalpha *)
(* dans la couche 0 *)
Lemma LAalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: alpha ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCApalpha requis par la preuve de (?)Aalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpalpha requis par la preuve de (?)BCApalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpalpha requis par la preuve de (?)ABCApBpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpalpham4 : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ABp requis par la preuve de (?)BCApalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCApalpha requis par la preuve de (?)BCApalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour BCalpha requis par la preuve de (?)BCApalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCApalpha requis par la preuve de (?)BCApalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HBCApalphaM3 : rk(B :: C :: Ap :: alpha :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (B :: C :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: alpha :: nil) (Ap :: B :: C :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: B :: C :: alpha :: nil) ((Ap :: nil) ++ (B :: C :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (B :: C :: alpha :: nil) (nil) 1 2 0 HApMtmp HBCalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: alpha ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : A :: Bp ::   de rang : 1 et 2 *)
assert(HBCApalpham2 : rk(B :: C :: Ap :: alpha :: nil) >= 2).
{
	assert(HABpMtmp : rk(A :: Bp :: nil) <= 2) by (solve_hyps_max HABpeq HABpM2).
	assert(HABCApBpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpalphaeq HABCApBpalpham4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: Bp :: nil) (B :: C :: Ap :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: alpha :: nil) (A :: Bp :: B :: C :: Ap :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Bp :: B :: C :: Ap :: alpha :: nil) ((A :: Bp :: nil) ++ (B :: C :: Ap :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpalphamtmp;try rewrite HT2 in HABCApBpalphamtmp.
	assert(HT := rule_4 (A :: Bp :: nil) (B :: C :: Ap :: alpha :: nil) (nil) 4 0 2 HABCApBpalphamtmp Hmtmp HABpMtmp Hincl); apply HT.
}
try clear HABpM1. try clear HABpM2. try clear HABpM3. try clear HABpm4. try clear HABpm3. try clear HABpm2. try clear HABpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Aalpha requis par la preuve de (?)Aalpha pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HAalpham2 : rk(A :: alpha :: nil) >= 2).
{
	assert(HBCApalphaMtmp : rk(B :: C :: Ap :: alpha :: nil) <= 3) by (solve_hyps_max HBCApalphaeq HBCApalphaM3).
	try assert(HABCApalphaeq : rk(A :: B :: C :: Ap :: alpha :: nil) = 4) by (apply LABCApalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApalphamtmp : rk(A :: B :: C :: Ap :: alpha :: nil) >= 4) by (solve_hyps_min HABCApalphaeq HABCApalpham4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (A :: alpha :: nil) (B :: C :: Ap :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: alpha :: nil) (A :: alpha :: B :: C :: Ap :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: alpha :: B :: C :: Ap :: alpha :: nil) ((A :: alpha :: nil) ++ (B :: C :: Ap :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApalphamtmp;try rewrite HT2 in HABCApalphamtmp.
	assert(HT := rule_2 (A :: alpha :: nil) (B :: C :: Ap :: alpha :: nil) (alpha :: nil) 4 1 3 HABCApalphamtmp Halphamtmp HBCApalphaMtmp Hincl);apply HT.
}
try clear HABCApalphaM1. try clear HABCApalphaM2. try clear HABCApalphaM3. try clear HABCApalpham4. try clear HABCApalpham3. try clear HABCApalpham2. try clear HABCApalpham1. 

assert(HAalphaM : rk(A :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HAalphaeq HAalphaM2).
assert(HAalpham : rk(A :: alpha ::  nil) >= 1) by (solve_hyps_min HAalphaeq HAalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: alpha ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HBCalphaM : rk(B :: C :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBCalphaeq HBCalphaM3).
assert(HBCalpham : rk(B :: C :: alpha ::  nil) >= 1) by (solve_hyps_min HBCalphaeq HBCalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LBpalpha *)
(* dans constructLemma(), requis par LBCBpalpha *)
(* dans la couche 0 *)
Lemma LABCBpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpalpha requis par la preuve de (?)ABCBpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpalpham4 : rk(A :: B :: C :: Bp :: alpha :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


assert(HABCBpalphaM : rk(A :: B :: C :: Bp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpalpham : rk(A :: B :: C :: Bp :: alpha ::  nil) >= 1) by (solve_hyps_min HABCBpalphaeq HABCBpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCBpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Bp :: alpha ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBpalpha requis par la preuve de (?)BCBpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpalpha requis par la preuve de (?)BCBpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpalpha requis par la preuve de (?)ABCApBpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpalpham4 : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AApBp requis par la preuve de (?)BCBpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AApBp requis par la preuve de (?)AApBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -1 et 4*)
assert(HAApBpm2 : rk(A :: Ap :: Bp :: nil) >= 2).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(HABCApBpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpalphaeq HABCApBpalpham4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: Ap :: Bp :: nil) (B :: C :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: alpha :: nil) (A :: Ap :: Bp :: B :: C :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Ap :: Bp :: B :: C :: alpha :: nil) ((A :: Ap :: Bp :: nil) ++ (B :: C :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpalphamtmp;try rewrite HT2 in HABCApBpalphamtmp.
	assert(HT := rule_2 (A :: Ap :: Bp :: nil) (B :: C :: alpha :: nil) (nil) 4 0 2 HABCApBpalphamtmp Hmtmp HBCalphaMtmp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBpalpha requis par la preuve de (?)BCBpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpalpha requis par la preuve de (?)BCBpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HBCBpalphaM3 : rk(B :: C :: Bp :: alpha :: nil) <= 3).
{
	try assert(HBpeq : rk(Bp :: nil) = 1) by (apply LBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpMtmp : rk(Bp :: nil) <= 1) by (solve_hyps_max HBpeq HBpM1).
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Bp :: nil) (B :: C :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: alpha :: nil) (Bp :: B :: C :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: B :: C :: alpha :: nil) ((Bp :: nil) ++ (B :: C :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: nil) (B :: C :: alpha :: nil) (nil) 1 2 0 HBpMtmp HBCalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: alpha ::  de rang :  4 et 4 	 AiB : Bp ::  de rang :  1 et 1 	 A : A :: Ap :: Bp ::   de rang : 2 et 3 *)
assert(HBCBpalpham2 : rk(B :: C :: Bp :: alpha :: nil) >= 2).
{
	assert(HAApBpMtmp : rk(A :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HAApBpeq HAApBpM3).
	assert(HABCApBpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpalphaeq HABCApBpalpham4).
	try assert(HBpeq : rk(Bp :: nil) = 1) by (apply LBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (A :: Ap :: Bp :: nil) (B :: C :: Bp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: alpha :: nil) (A :: Ap :: Bp :: B :: C :: Bp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Ap :: Bp :: B :: C :: Bp :: alpha :: nil) ((A :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpalphamtmp;try rewrite HT2 in HABCApBpalphamtmp.
	assert(HT := rule_4 (A :: Ap :: Bp :: nil) (B :: C :: Bp :: alpha :: nil) (Bp :: nil) 4 1 3 HABCApBpalphamtmp HBpmtmp HAApBpMtmp Hincl); apply HT.
}
try clear HAApBpM1. try clear HAApBpM2. try clear HAApBpM3. try clear HAApBpm4. try clear HAApBpm3. try clear HAApBpm2. try clear HAApBpm1. try clear HBpM1. try clear HBpM2. try clear HBpM3. try clear HBpm4. try clear HBpm3. try clear HBpm2. try clear HBpm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: alpha ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : A :: alpha ::   de rang : 2 et 2 *)
assert(HBCBpalpham3 : rk(B :: C :: Bp :: alpha :: nil) >= 3).
{
	try assert(HAalphaeq : rk(A :: alpha :: nil) = 2) by (apply LAalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HAalphaMtmp : rk(A :: alpha :: nil) <= 2) by (solve_hyps_max HAalphaeq HAalphaM2).
	try assert(HABCBpalphaeq : rk(A :: B :: C :: Bp :: alpha :: nil) = 4) by (apply LABCBpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpalphamtmp : rk(A :: B :: C :: Bp :: alpha :: nil) >= 4) by (solve_hyps_min HABCBpalphaeq HABCBpalpham4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (A :: alpha :: nil) (B :: C :: Bp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: alpha :: nil) (A :: alpha :: B :: C :: Bp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: alpha :: B :: C :: Bp :: alpha :: nil) ((A :: alpha :: nil) ++ (B :: C :: Bp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpalphamtmp;try rewrite HT2 in HABCBpalphamtmp.
	assert(HT := rule_4 (A :: alpha :: nil) (B :: C :: Bp :: alpha :: nil) (alpha :: nil) 4 1 2 HABCBpalphamtmp Halphamtmp HAalphaMtmp Hincl); apply HT.
}
try clear HABCBpalphaM1. try clear HABCBpalphaM2. try clear HABCBpalphaM3. try clear HABCBpalpham4. try clear HABCBpalpham3. try clear HABCBpalpham2. try clear HABCBpalpham1. 

assert(HBCBpalphaM : rk(B :: C :: Bp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpalpham : rk(B :: C :: Bp :: alpha ::  nil) >= 1) by (solve_hyps_min HBCBpalphaeq HBCBpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Bp :: alpha ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bpalpha requis par la preuve de (?)Bpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : B :: C :: Bp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : B :: C :: alpha ::   de rang : 2 et 2 *)
assert(HBpalpham2 : rk(Bp :: alpha :: nil) >= 2).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	try assert(HBCBpalphaeq : rk(B :: C :: Bp :: alpha :: nil) = 3) by (apply LBCBpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCBpalphamtmp : rk(B :: C :: Bp :: alpha :: nil) >= 3) by (solve_hyps_min HBCBpalphaeq HBCBpalpham3).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (B :: C :: alpha :: nil) (Bp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: alpha :: nil) (B :: C :: alpha :: Bp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: alpha :: Bp :: alpha :: nil) ((B :: C :: alpha :: nil) ++ (Bp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCBpalphamtmp;try rewrite HT2 in HBCBpalphamtmp.
	assert(HT := rule_4 (B :: C :: alpha :: nil) (Bp :: alpha :: nil) (alpha :: nil) 3 1 2 HBCBpalphamtmp Halphamtmp HBCalphaMtmp Hincl); apply HT.
}


assert(HBpalphaM : rk(Bp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBpalphaeq HBpalphaM2).
assert(HBpalpham : rk(Bp :: alpha ::  nil) >= 1) by (solve_hyps_min HBpalphaeq HBpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpalpha requis par la preuve de (?)ABCApBpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpalpham4 : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpalphaM : rk(A :: B :: C :: Ap :: Bp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpalpham : rk(A :: B :: C :: Ap :: Bp :: alpha ::  nil) >= 1) by (solve_hyps_min HABCApBpalphaeq HABCApBpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpalpha requis par la preuve de (?)ABCApCpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpalpham4 : rk(A :: B :: C :: Ap :: Cp :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApCpalphaM : rk(A :: B :: C :: Ap :: Cp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApCpalpham : rk(A :: B :: C :: Ap :: Cp :: alpha ::  nil) >= 1) by (solve_hyps_min HABCApCpalphaeq HABCApCpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HBpCpalphaM : rk(Bp :: Cp :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBpCpalphaeq HBpCpalphaM3).
assert(HBpCpalpham : rk(Bp :: Cp :: alpha ::  nil) >= 1) by (solve_hyps_min HBpCpalphaeq HBpCpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCBpCpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp :: Cp :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpCpalpha requis par la preuve de (?)ABCBpCpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpCpalpham4 : rk(A :: B :: C :: Bp :: Cp :: alpha :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


assert(HABCBpCpalphaM : rk(A :: B :: C :: Bp :: Cp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpCpalpham : rk(A :: B :: C :: Bp :: Cp :: alpha ::  nil) >= 1) by (solve_hyps_min HABCBpCpalphaeq HABCBpCpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCpalpha : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpalpha requis par la preuve de (?)ABCApBpCpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpalpham4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpCpalphaM : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpalpham : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha ::  nil) >= 1) by (solve_hyps_min HABCApBpCpalphaeq HABCApBpCpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(beta ::  nil) = 1.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HbetaM : rk(beta ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max Hbetaeq HbetaM1).
assert(Hbetam : rk(beta ::  nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HACbetaM : rk(A :: C :: beta ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HACbetaeq HACbetaM3).
assert(HACbetam : rk(A :: C :: beta ::  nil) >= 1) by (solve_hyps_min HACbetaeq HACbetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LApbeta *)
(* dans constructLemma(), requis par LACApbeta *)
(* dans la couche 0 *)
Lemma LABCApalphabeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: alpha :: beta ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApalphabeta requis par la preuve de (?)ABCApalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApalphabetam4 : rk(A :: B :: C :: Ap :: alpha :: beta :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApalphabetaM : rk(A :: B :: C :: Ap :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApalphabetam : rk(A :: B :: C :: Ap :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HABCApalphabetaeq HABCApalphabetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Ap :: beta ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpbeta requis par la preuve de (?)ABCApBpbeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpbetam4 : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: beta :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HACApbetaM3 : rk(A :: C :: Ap :: beta :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (Ap :: A :: C :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: beta :: nil) ((Ap :: nil) ++ (A :: C :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: beta :: nil) (nil) 1 2 0 HApMtmp HACbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: beta ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACApbetam2 : rk(A :: C :: Ap :: beta :: nil) >= 2).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (nil) 4 0 2 HABCApBpbetamtmp Hmtmp HBBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: alpha :: beta ::  de rang :  4 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : B :: C :: alpha ::   de rang : 2 et 2 *)
assert(HACApbetam3 : rk(A :: C :: Ap :: beta :: nil) >= 3).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	try assert(HABCApalphabetaeq : rk(A :: B :: C :: Ap :: alpha :: beta :: nil) = 4) by (apply LABCApalphabeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApalphabetamtmp : rk(A :: B :: C :: Ap :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HABCApalphabetaeq HABCApalphabetam4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: alpha :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: alpha :: beta :: nil) (B :: C :: alpha :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: alpha :: A :: C :: Ap :: beta :: nil) ((B :: C :: alpha :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApalphabetamtmp;try rewrite HT2 in HABCApalphabetamtmp.
	assert(HT := rule_4 (B :: C :: alpha :: nil) (A :: C :: Ap :: beta :: nil) (C :: nil) 4 1 2 HABCApalphabetamtmp HCmtmp HBCalphaMtmp Hincl); apply HT.
}
try clear HABCApalphabetaM1. try clear HABCApalphabetaM2. try clear HABCApalphabetaM3. try clear HABCApalphabetam4. try clear HABCApalphabetam3. try clear HABCApalphabetam2. try clear HABCApalphabetam1. 

assert(HACApbetaM : rk(A :: C :: Ap :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApbetam : rk(A :: C :: Ap :: beta ::  nil) >= 1) by (solve_hyps_min HACApbetaeq HACApbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Ap :: beta ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Apbeta requis par la preuve de (?)Apbeta pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: C :: Ap :: beta ::  de rang :  3 et 3 	 AiB : beta ::  de rang :  1 et 1 	 A : A :: C :: beta ::   de rang : 2 et 2 *)
assert(HApbetam2 : rk(Ap :: beta :: nil) >= 2).
{
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	try assert(HACApbetaeq : rk(A :: C :: Ap :: beta :: nil) = 3) by (apply LACApbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACApbetamtmp : rk(A :: C :: Ap :: beta :: nil) >= 3) by (solve_hyps_min HACApbetaeq HACApbetam3).
	try assert(Hbetaeq : rk(beta :: nil) = 1) by (apply Lbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (A :: C :: beta :: nil) (Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (A :: C :: beta :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: beta :: Ap :: beta :: nil) ((A :: C :: beta :: nil) ++ (Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACApbetamtmp;try rewrite HT2 in HACApbetamtmp.
	assert(HT := rule_4 (A :: C :: beta :: nil) (Ap :: beta :: nil) (beta :: nil) 3 1 2 HACApbetamtmp Hbetamtmp HACbetaMtmp Hincl); apply HT.
}
try clear HbetaM1. try clear HbetaM2. try clear HbetaM3. try clear Hbetam4. try clear Hbetam3. try clear Hbetam2. try clear Hbetam1. 

assert(HApbetaM : rk(Ap :: beta ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HApbetaeq HApbetaM2).
assert(HApbetam : rk(Ap :: beta ::  nil) >= 1) by (solve_hyps_min HApbetaeq HApbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: beta ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpbeta requis par la preuve de (?)ABCApBpbeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpbetam4 : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: beta :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpbetaM : rk(A :: B :: C :: Ap :: Bp :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpbetam : rk(A :: B :: C :: Ap :: Bp :: beta ::  nil) >= 1) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApCpbeta : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(Ap :: Cp :: beta ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HApCpbetaM : rk(Ap :: Cp :: beta ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HApCpbetaeq HApCpbetaM3).
assert(HApCpbetam : rk(Ap :: Cp :: beta ::  nil) >= 1) by (solve_hyps_min HApCpbetaeq HApCpbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAApOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: Ap :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HAApOoM : rk(A :: Ap :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HAApOoeq HAApOoM3).
assert(HAApOom : rk(A :: Ap :: Oo ::  nil) >= 1) by (solve_hyps_min HAApOoeq HAApOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBBpOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

assert(HBBpOoM : rk(B :: Bp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBBpOoeq HBBpOoM3).
assert(HBBpOom : rk(B :: Bp :: Oo ::  nil) >= 1) by (solve_hyps_min HBBpOoeq HBBpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCCpOo *)
(* dans constructLemma(), requis par LBCBpCpalphaOo *)
(* dans la couche 0 *)
Lemma LBCBpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Bp :: alpha :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpalphaOo requis par la preuve de (?)BCBpalphaOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCBpalphaOo requis par la preuve de (?)BCBpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpalphaOo requis par la preuve de (?)ABCBpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpalphaOom4 : rk(A :: B :: C :: Bp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpalphaOo requis par la preuve de (?)BCBpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpalphaOo requis par la preuve de (?)BCBpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpalphaOo requis par la preuve de (?)ABCApBpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpalphaOom4 : rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApbeta requis par la preuve de (?)BCBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HACApbetaM3 : rk(A :: C :: Ap :: beta :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (Ap :: A :: C :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: beta :: nil) ((Ap :: nil) ++ (A :: C :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: beta :: nil) (nil) 1 2 0 HApMtmp HACbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: beta ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACApbetam2 : rk(A :: C :: Ap :: beta :: nil) >= 2).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (nil) 4 0 2 HABCApBpbetamtmp Hmtmp HBBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HACApbetaMtmp : rk(A :: C :: Ap :: beta :: nil) <= 3) by (solve_hyps_max HACApbetaeq HACApbetaM3).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: C :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: C :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_2 (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (C :: nil) 4 1 3 HABCApBpbetamtmp HCmtmp HACApbetaMtmp Hincl);apply HT.
}
try clear HACApbetaM1. try clear HACApbetaM2. try clear HACApbetaM3. try clear HACApbetam4. try clear HACApbetam3. try clear HACApbetam2. try clear HACApbetam1. try clear HABCApBpbetaM1. try clear HABCApBpbetaM2. try clear HABCApBpbetaM3. try clear HABCApBpbetam4. try clear HABCApBpbetam3. try clear HABCApBpbetam2. try clear HABCApBpbetam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpalphaOo requis par la preuve de (?)BCBpalphaOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : B :: C :: Bp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Bp ::   de rang : 4 et 4 *)
assert(HBCBpalphaOom2 : rk(B :: C :: Bp :: alpha :: Oo :: nil) >= 2).
{
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpMtmp : rk(A :: B :: C :: Ap :: Bp :: nil) <= 4) by (solve_hyps_max HABCApBpeq HABCApBpM4).
	assert(HABCApBpalphaOomtmp : rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCApBpalphaOoeq HABCApBpalphaOom4).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 2) by (solve_hyps_min HBCBpeq HBCBpm2).
	assert(Hincl : incl (B :: C :: Bp :: nil) (list_inter (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: alpha :: Oo :: nil) ((A :: B :: C :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpalphaOomtmp;try rewrite HT2 in HABCApBpalphaOomtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: alpha :: Oo :: nil) (B :: C :: Bp :: nil) 4 2 4 HABCApBpalphaOomtmp HBCBpmtmp HABCApBpMtmp Hincl); apply HT.
}
try clear HABCApBpalphaOoM1. try clear HABCApBpalphaOoM2. try clear HABCApBpalphaOoM3. try clear HABCApBpalphaOom4. try clear HABCApBpalphaOom3. try clear HABCApBpalphaOom2. try clear HABCApBpalphaOom1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : A :: alpha ::   de rang : 2 et 2 *)
assert(HBCBpalphaOom3 : rk(B :: C :: Bp :: alpha :: Oo :: nil) >= 3).
{
	try assert(HAalphaeq : rk(A :: alpha :: nil) = 2) by (apply LAalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HAalphaMtmp : rk(A :: alpha :: nil) <= 2) by (solve_hyps_max HAalphaeq HAalphaM2).
	assert(HABCBpalphaOomtmp : rk(A :: B :: C :: Bp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCBpalphaOoeq HABCBpalphaOom4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (A :: alpha :: nil) (B :: C :: Bp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: alpha :: Oo :: nil) (A :: alpha :: B :: C :: Bp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: alpha :: B :: C :: Bp :: alpha :: Oo :: nil) ((A :: alpha :: nil) ++ (B :: C :: Bp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpalphaOomtmp;try rewrite HT2 in HABCBpalphaOomtmp.
	assert(HT := rule_4 (A :: alpha :: nil) (B :: C :: Bp :: alpha :: Oo :: nil) (alpha :: nil) 4 1 2 HABCBpalphaOomtmp Halphamtmp HAalphaMtmp Hincl); apply HT.
}
try clear HABCBpalphaOoM1. try clear HABCBpalphaOoM2. try clear HABCBpalphaOoM3. try clear HABCBpalphaOom4. try clear HABCBpalphaOom3. try clear HABCBpalphaOom2. try clear HABCBpalphaOom1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCBpalphaOoM3 : rk(B :: C :: Bp :: alpha :: Oo :: nil) <= 3).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	try assert(HBBpOoeq : rk(B :: Bp :: Oo :: nil) = 2) by (apply LBBpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBBpOoMtmp : rk(B :: Bp :: Oo :: nil) <= 2) by (solve_hyps_max HBBpOoeq HBBpOoM2).
	try assert(HBeq : rk(B :: nil) = 1) by (apply LB with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (B :: C :: alpha :: nil) (B :: Bp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: alpha :: Oo :: nil) (B :: C :: alpha :: B :: Bp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: alpha :: B :: Bp :: Oo :: nil) ((B :: C :: alpha :: nil) ++ (B :: Bp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: alpha :: nil) (B :: Bp :: Oo :: nil) (B :: nil) 2 2 1 HBCalphaMtmp HBBpOoMtmp HBmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBBpOoM1. try clear HBBpOoM2. try clear HBBpOoM3. try clear HBBpOom4. try clear HBBpOom3. try clear HBBpOom2. try clear HBBpOom1. try clear HBM1. try clear HBM2. try clear HBM3. try clear HBm4. try clear HBm3. try clear HBm2. try clear HBm1. 

assert(HBCBpalphaOoM : rk(B :: C :: Bp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpalphaOom : rk(B :: C :: Bp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HBCBpalphaOoeq HBCBpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCBpCpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpCpalphaOo requis par la preuve de (?)BCBpCpalphaOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCBpCpalphaOo requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpCpalphaOo requis par la preuve de (?)ABCBpCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpCpalphaOom4 : rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ACp requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpCpalphaOo requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpCpalphaOo requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpalphaOo requis par la preuve de (?)ABCApBpCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpalphaOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApbeta requis par la preuve de (?)BCBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HACApbetaM3 : rk(A :: C :: Ap :: beta :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (Ap :: A :: C :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: beta :: nil) ((Ap :: nil) ++ (A :: C :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: beta :: nil) (nil) 1 2 0 HApMtmp HACbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: beta ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACApbetam2 : rk(A :: C :: Ap :: beta :: nil) >= 2).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (nil) 4 0 2 HABCApBpbetamtmp Hmtmp HBBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HACApbetaMtmp : rk(A :: C :: Ap :: beta :: nil) <= 3) by (solve_hyps_max HACApbetaeq HACApbetaM3).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: C :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: C :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_2 (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (C :: nil) 4 1 3 HABCApBpbetamtmp HCmtmp HACApbetaMtmp Hincl);apply HT.
}
try clear HACApbetaM1. try clear HACApbetaM2. try clear HACApbetaM3. try clear HACApbetam4. try clear HACApbetam3. try clear HACApbetam2. try clear HACApbetam1. try clear HABCApBpbetaM1. try clear HABCApBpbetaM2. try clear HABCApBpbetaM3. try clear HABCApBpbetam4. try clear HABCApBpbetam3. try clear HABCApBpbetam2. try clear HABCApBpbetam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpCpalphaOo requis par la preuve de (?)BCBpCpalphaOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : B :: C :: Bp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Bp ::   de rang : 4 et 4 *)
assert(HBCBpCpalphaOom2 : rk(B :: C :: Bp :: Cp :: alpha :: Oo :: nil) >= 2).
{
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpMtmp : rk(A :: B :: C :: Ap :: Bp :: nil) <= 4) by (solve_hyps_max HABCApBpeq HABCApBpM4).
	assert(HABCApBpCpalphaOomtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCApBpCpalphaOoeq HABCApBpCpalphaOom4).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 2) by (solve_hyps_min HBCBpeq HBCBpm2).
	assert(Hincl : incl (B :: C :: Bp :: nil) (list_inter (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) ((A :: B :: C :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpalphaOomtmp;try rewrite HT2 in HABCApBpCpalphaOomtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil) (B :: C :: Bp :: nil) 4 2 4 HABCApBpCpalphaOomtmp HBCBpmtmp HABCApBpMtmp Hincl); apply HT.
}
try clear HABCApBpCpalphaOoM1. try clear HABCApBpCpalphaOoM2. try clear HABCApBpCpalphaOoM3. try clear HABCApBpCpalphaOom4. try clear HABCApBpCpalphaOom3. try clear HABCApBpCpalphaOom2. try clear HABCApBpCpalphaOom1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: Cp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : A :: Cp ::   de rang : 1 et 2 *)
assert(HBCBpCpalphaOom3 : rk(B :: C :: Bp :: Cp :: alpha :: Oo :: nil) >= 3).
{
	assert(HACpMtmp : rk(A :: Cp :: nil) <= 2) by (solve_hyps_max HACpeq HACpM2).
	assert(HABCBpCpalphaOomtmp : rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCBpCpalphaOoeq HABCBpCpalphaOom4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) ((A :: Cp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpCpalphaOomtmp;try rewrite HT2 in HABCBpCpalphaOomtmp.
	assert(HT := rule_4 (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil) (Cp :: nil) 4 1 2 HABCBpCpalphaOomtmp HCpmtmp HACpMtmp Hincl); apply HT.
}
try clear HABCBpCpalphaOoM1. try clear HABCBpCpalphaOoM2. try clear HABCBpCpalphaOoM3. try clear HABCBpCpalphaOom4. try clear HABCBpCpalphaOom3. try clear HABCBpCpalphaOom2. try clear HABCBpCpalphaOom1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCBpCpalphaOoM3 : rk(B :: C :: Bp :: Cp :: alpha :: Oo :: nil) <= 3).
{
	try assert(HBpCpalphaeq : rk(Bp :: Cp :: alpha :: nil) = 2) by (apply LBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpCpalphaMtmp : rk(Bp :: Cp :: alpha :: nil) <= 2) by (solve_hyps_max HBpCpalphaeq HBpCpalphaM2).
	try assert(HBCBpalphaOoeq : rk(B :: C :: Bp :: alpha :: Oo :: nil) = 3) by (apply LBCBpalphaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCBpalphaOoMtmp : rk(B :: C :: Bp :: alpha :: Oo :: nil) <= 3) by (solve_hyps_max HBCBpalphaOoeq HBCBpalphaOoM3).
	try assert(HBpalphaeq : rk(Bp :: alpha :: nil) = 2) by (apply LBpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpalphamtmp : rk(Bp :: alpha :: nil) >= 2) by (solve_hyps_min HBpalphaeq HBpalpham2).
	assert(Hincl : incl (Bp :: alpha :: nil) (list_inter (Bp :: Cp :: alpha :: nil) (B :: C :: Bp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: alpha :: Oo :: nil) (Bp :: Cp :: alpha :: B :: C :: Bp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: alpha :: B :: C :: Bp :: alpha :: Oo :: nil) ((Bp :: Cp :: alpha :: nil) ++ (B :: C :: Bp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: alpha :: nil) (B :: C :: Bp :: alpha :: Oo :: nil) (Bp :: alpha :: nil) 2 3 2 HBpCpalphaMtmp HBCBpalphaOoMtmp HBpalphamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpalphaM1. try clear HBpalphaM2. try clear HBpalphaM3. try clear HBpalpham4. try clear HBpalpham3. try clear HBpalpham2. try clear HBpalpham1. 

assert(HBCBpCpalphaOoM : rk(B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpCpalphaOom : rk(B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HBCBpCpalphaOoeq HBCBpCpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCCpOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(B :: C :: Cp :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCCpOo requis par la preuve de (?)BCCpOo pour la règle 6  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCCpbetaOo requis par la preuve de (?)BCCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCCpbetaOo requis par la preuve de (?)ABCCpbetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCCpbetaOom4 : rk(A :: B :: C :: Cp :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: beta :: Oo :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCCpOo requis par la preuve de (?)BCCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)BCCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)ABCApCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpOom4 : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCCp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ACp requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApbeta requis par la preuve de (?)BCBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HACApbetaM3 : rk(A :: C :: Ap :: beta :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (Ap :: A :: C :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: beta :: nil) ((Ap :: nil) ++ (A :: C :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: beta :: nil) (nil) 1 2 0 HApMtmp HACbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: beta ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACApbetam2 : rk(A :: C :: Ap :: beta :: nil) >= 2).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (nil) 4 0 2 HABCApBpbetamtmp Hmtmp HBBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HACApbetaMtmp : rk(A :: C :: Ap :: beta :: nil) <= 3) by (solve_hyps_max HACApbetaeq HACApbetaM3).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: C :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: C :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_2 (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (C :: nil) 4 1 3 HABCApBpbetamtmp HCmtmp HACApbetaMtmp Hincl);apply HT.
}
try clear HACApbetaM1. try clear HACApbetaM2. try clear HACApbetaM3. try clear HACApbetam4. try clear HACApbetam3. try clear HACApbetam2. try clear HACApbetam1. try clear HABCApBpbetaM1. try clear HABCApBpbetaM2. try clear HABCApBpbetaM3. try clear HABCApBpbetam4. try clear HABCApBpbetam3. try clear HABCApBpbetam2. try clear HABCApBpbetam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: alpha ::  de rang :  4 et 4 	 AiB : B :: C :: Bp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Bp ::   de rang : 4 et 4 *)
assert(HBCBpCpalpham2 : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 2).
{
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpMtmp : rk(A :: B :: C :: Ap :: Bp :: nil) <= 4) by (solve_hyps_max HABCApBpeq HABCApBpM4).
	try assert(HABCApBpCpalphaeq : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) = 4) by (apply LABCApBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpCpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpCpalphaeq HABCApBpCpalpham4).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 2) by (solve_hyps_min HBCBpeq HBCBpm2).
	assert(Hincl : incl (B :: C :: Bp :: nil) (list_inter (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: nil) ((A :: B :: C :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpalphamtmp;try rewrite HT2 in HABCApBpCpalphamtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil) (B :: C :: Bp :: nil) 4 2 4 HABCApBpCpalphamtmp HBCBpmtmp HABCApBpMtmp Hincl); apply HT.
}
try clear HABCApBpCpalphaM1. try clear HABCApBpCpalphaM2. try clear HABCApBpCpalphaM3. try clear HABCApBpCpalpham4. try clear HABCApBpCpalpham3. try clear HABCApBpCpalpham2. try clear HABCApBpCpalpham1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: Cp :: alpha ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : A :: Cp ::   de rang : 1 et 2 *)
assert(HBCBpCpalpham3 : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 3).
{
	assert(HACpMtmp : rk(A :: Cp :: nil) <= 2) by (solve_hyps_max HACpeq HACpM2).
	try assert(HABCBpCpalphaeq : rk(A :: B :: C :: Bp :: Cp :: alpha :: nil) = 4) by (apply LABCBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpCpalphamtmp : rk(A :: B :: C :: Bp :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCBpCpalphaeq HABCBpCpalpham4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: Cp :: alpha :: nil) (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: nil) ((A :: Cp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpCpalphamtmp;try rewrite HT2 in HABCBpCpalphamtmp.
	assert(HT := rule_4 (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil) (Cp :: nil) 4 1 2 HABCBpCpalphamtmp HCpmtmp HACpMtmp Hincl); apply HT.
}
try clear HABCBpCpalphaM1. try clear HABCBpCpalphaM2. try clear HABCBpCpalphaM3. try clear HABCBpCpalpham4. try clear HABCBpCpalpham3. try clear HABCBpCpalpham2. try clear HABCBpCpalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et 4*)
assert(HBCCpm2 : rk(B :: C :: Cp :: nil) >= 2).
{
	try assert(HBpCpalphaeq : rk(Bp :: Cp :: alpha :: nil) = 2) by (apply LBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpCpalphaMtmp : rk(Bp :: Cp :: alpha :: nil) <= 2) by (solve_hyps_max HBpCpalphaeq HBpCpalphaM2).
	assert(HBCBpCpalphamtmp : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 3) by (solve_hyps_min HBCBpCpalphaeq HBCBpCpalpham3).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (B :: C :: Cp :: nil) (Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: alpha :: nil) (B :: C :: Cp :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Cp :: Bp :: Cp :: alpha :: nil) ((B :: C :: Cp :: nil) ++ (Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCBpCpalphamtmp;try rewrite HT2 in HBCBpCpalphamtmp.
	assert(HT := rule_2 (B :: C :: Cp :: nil) (Bp :: Cp :: alpha :: nil) (Cp :: nil) 3 1 2 HBCBpCpalphamtmp HCpmtmp HBpCpalphaMtmp Hincl);apply HT.
}
try clear HBpCpalphaM1. try clear HBpCpalphaM2. try clear HBpCpalphaM3. try clear HBpCpalpham4. try clear HBpCpalpham3. try clear HBpCpalpham2. try clear HBpCpalpham1. try clear HBCBpCpalphaM1. try clear HBCBpCpalphaM2. try clear HBCBpCpalphaM3. try clear HBCBpCpalpham4. try clear HBCBpCpalpham3. try clear HBCBpCpalpham2. try clear HBCBpCpalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCCpOo requis par la preuve de (?)BCCpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Cp :: Oo ::  de rang :  4 et 4 	 AiB : B :: C :: Cp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Cp ::   de rang : 4 et 4 *)
assert(HBCCpOom2 : rk(B :: C :: Cp :: Oo :: nil) >= 2).
{
	try assert(HABCApCpeq : rk(A :: B :: C :: Ap :: Cp :: nil) = 4) by (apply LABCApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpMtmp : rk(A :: B :: C :: Ap :: Cp :: nil) <= 4) by (solve_hyps_max HABCApCpeq HABCApCpM4).
	assert(HABCApCpOomtmp : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4) by (solve_hyps_min HABCApCpOoeq HABCApCpOom4).
	assert(HBCCpmtmp : rk(B :: C :: Cp :: nil) >= 2) by (solve_hyps_min HBCCpeq HBCCpm2).
	assert(Hincl : incl (B :: C :: Cp :: nil) (list_inter (A :: B :: C :: Ap :: Cp :: nil) (B :: C :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: Oo :: nil) (A :: B :: C :: Ap :: Cp :: B :: C :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Cp :: B :: C :: Cp :: Oo :: nil) ((A :: B :: C :: Ap :: Cp :: nil) ++ (B :: C :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpOomtmp;try rewrite HT2 in HABCApCpOomtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Cp :: nil) (B :: C :: Cp :: Oo :: nil) (B :: C :: Cp :: nil) 4 2 4 HABCApCpOomtmp HBCCpmtmp HABCApCpMtmp Hincl); apply HT.
}
try clear HABCApCpOoM1. try clear HABCApCpOoM2. try clear HABCApCpOoM3. try clear HABCApCpOom4. try clear HABCApCpOom3. try clear HABCApCpOom2. try clear HABCApCpOom1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Cp :: beta :: Oo ::  de rang :  4 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : A :: C :: beta ::   de rang : 2 et 2 *)
assert(HBCCpOom3 : rk(B :: C :: Cp :: Oo :: nil) >= 3).
{
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(HABCCpbetaOomtmp : rk(A :: B :: C :: Cp :: beta :: Oo :: nil) >= 4) by (solve_hyps_min HABCCpbetaOoeq HABCCpbetaOom4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: C :: beta :: nil) (B :: C :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: beta :: Oo :: nil) (A :: C :: beta :: B :: C :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: beta :: B :: C :: Cp :: Oo :: nil) ((A :: C :: beta :: nil) ++ (B :: C :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpbetaOomtmp;try rewrite HT2 in HABCCpbetaOomtmp.
	assert(HT := rule_4 (A :: C :: beta :: nil) (B :: C :: Cp :: Oo :: nil) (C :: nil) 4 1 2 HABCCpbetaOomtmp HCmtmp HACbetaMtmp Hincl); apply HT.
}
try clear HABCCpbetaOoM1. try clear HABCCpbetaOoM2. try clear HABCCpbetaOoM3. try clear HABCCpbetaOom4. try clear HABCCpbetaOom3. try clear HABCCpbetaOom2. try clear HABCCpbetaOom1. 

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCCpOoM3 : rk(B :: C :: Cp :: Oo :: nil) <= 3).
{
	try assert(HBCBpCpalphaOoeq : rk(B :: C :: Bp :: Cp :: alpha :: Oo :: nil) = 3) by (apply LBCBpCpalphaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCBpCpalphaOoMtmp : rk(B :: C :: Bp :: Cp :: alpha :: Oo :: nil) <= 3) by (solve_hyps_max HBCBpCpalphaOoeq HBCBpCpalphaOoM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Cp :: Oo :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (B :: C :: Cp :: Oo :: nil) (B :: C :: Bp :: Cp :: alpha :: Oo :: nil) 3 3 HBCBpCpalphaOoMtmp Hcomp Hincl);apply HT.
}


assert(HBCCpOoM : rk(B :: C :: Cp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCCpOom : rk(B :: C :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HBCCpOoeq HBCCpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCpOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpOo requis par la preuve de (?)ABCApCpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpOom4 : rk(A :: B :: C :: Ap :: Cp :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
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
Lemma LABCBpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpalphaOo requis par la preuve de (?)ABCBpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpalphaOom4 : rk(A :: B :: C :: Bp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: alpha :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}


assert(HABCBpalphaOoM : rk(A :: B :: C :: Bp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpalphaOom : rk(A :: B :: C :: Bp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCBpalphaOoeq HABCBpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpalphaOo requis par la preuve de (?)ABCApBpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpalphaOom4 : rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: alpha :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpalphaOoM : rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpalphaOom : rk(A :: B :: C :: Ap :: Bp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApBpalphaOoeq HABCApBpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCCpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Cp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCCpalphaOo requis par la preuve de (?)ABCCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCCpalphaOom4 : rk(A :: B :: C :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: alpha :: Oo :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}


assert(HABCCpalphaOoM : rk(A :: B :: C :: Cp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCCpalphaOom : rk(A :: B :: C :: Cp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCCpalphaOoeq HABCCpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpalphaOo requis par la preuve de (?)ABCApCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpalphaOom4 : rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApCpalphaOoM : rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApCpalphaOom : rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApCpalphaOoeq HABCApCpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCBpCpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCBpCpalphaOo requis par la preuve de (?)ABCBpCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCBpCpalphaOom4 : rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCBpeq : rk(A :: B :: C :: Bp :: nil) = 4) by (apply LABCBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (A :: B :: C :: Bp :: Cp :: alpha :: Oo :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}
try clear HABCBpM1. try clear HABCBpM2. try clear HABCBpM3. try clear HABCBpm4. try clear HABCBpm3. try clear HABCBpm2. try clear HABCBpm1. 

assert(HABCBpCpalphaOoM : rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCBpCpalphaOom : rk(A :: B :: C :: Bp :: Cp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCBpCpalphaOoeq HABCBpCpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCpalphaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpalphaOo requis par la preuve de (?)ABCApBpCpalphaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpalphaOom4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApBpCpalphaOoM : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpalphaOom : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApBpCpalphaOoeq HABCApBpCpalphaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApbetaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Ap :: beta :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApbetaOo requis par la preuve de (?)ACApbetaOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApalphabetaOo requis par la preuve de (?)ACApbetaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApalphabetaOo requis par la preuve de (?)ABCApalphabetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApalphabetaOom4 : rk(A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbetaOo requis par la preuve de (?)ACApbetaOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: alpha :: beta :: Oo ::  de rang :  4 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : B :: C :: alpha ::   de rang : 2 et 2 *)
assert(HACApbetaOom3 : rk(A :: C :: Ap :: beta :: Oo :: nil) >= 3).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(HABCApalphabetaOomtmp : rk(A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) >= 4) by (solve_hyps_min HABCApalphabetaOoeq HABCApalphabetaOom4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: alpha :: nil) (A :: C :: Ap :: beta :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) (B :: C :: alpha :: A :: C :: Ap :: beta :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: alpha :: A :: C :: Ap :: beta :: Oo :: nil) ((B :: C :: alpha :: nil) ++ (A :: C :: Ap :: beta :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApalphabetaOomtmp;try rewrite HT2 in HABCApalphabetaOomtmp.
	assert(HT := rule_4 (B :: C :: alpha :: nil) (A :: C :: Ap :: beta :: Oo :: nil) (C :: nil) 4 1 2 HABCApalphabetaOomtmp HCmtmp HBCalphaMtmp Hincl); apply HT.
}
try clear HABCApalphabetaOoM1. try clear HABCApalphabetaOoM2. try clear HABCApalphabetaOoM3. try clear HABCApalphabetaOom4. try clear HABCApalphabetaOom3. try clear HABCApalphabetaOom2. try clear HABCApalphabetaOom1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HACApbetaOoM3 : rk(A :: C :: Ap :: beta :: Oo :: nil) <= 3).
{
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	try assert(HAApOoeq : rk(A :: Ap :: Oo :: nil) = 2) by (apply LAApOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HAApOoMtmp : rk(A :: Ap :: Oo :: nil) <= 2) by (solve_hyps_max HAApOoeq HAApOoM2).
	try assert(HAeq : rk(A :: nil) = 1) by (apply LA with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: beta :: nil) (A :: Ap :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: Oo :: nil) (A :: C :: beta :: A :: Ap :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: beta :: A :: Ap :: Oo :: nil) ((A :: C :: beta :: nil) ++ (A :: Ap :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: C :: beta :: nil) (A :: Ap :: Oo :: nil) (A :: nil) 2 2 1 HACbetaMtmp HAApOoMtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HAApOoM1. try clear HAApOoM2. try clear HAApOoM3. try clear HAApOom4. try clear HAApOom3. try clear HAApOom2. try clear HAApOom1. try clear HAM1. try clear HAM2. try clear HAM3. try clear HAm4. try clear HAm3. try clear HAm2. try clear HAm1. 

assert(HACApbetaOoM : rk(A :: C :: Ap :: beta :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApbetaOom : rk(A :: C :: Ap :: beta :: Oo ::  nil) >= 1) by (solve_hyps_min HACApbetaOoeq HACApbetaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCCpbetaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Cp :: beta :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCCpbetaOo requis par la preuve de (?)ABCCpbetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCCpbetaOom4 : rk(A :: B :: C :: Cp :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (A :: B :: C :: Cp :: beta :: Oo :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}


assert(HABCCpbetaOoM : rk(A :: B :: C :: Cp :: beta :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCCpbetaOom : rk(A :: B :: C :: Cp :: beta :: Oo ::  nil) >= 1) by (solve_hyps_min HABCCpbetaOoeq HABCCpbetaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApCpbetaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: C :: Ap :: Cp :: beta :: Oo ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApCpbetaOo requis par la preuve de (?)ACApCpbetaOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApCp requis par la preuve de (?)ACApCpbetaOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApCp requis par la preuve de (?)ACApCp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACCp requis par la preuve de (?)ACApCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCApalpha requis par la preuve de (?)ACCp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ABp requis par la preuve de (?)BCApalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCApalpha requis par la preuve de (?)BCApalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCApalpha requis par la preuve de (?)BCApalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HBCApalphaM3 : rk(B :: C :: Ap :: alpha :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (B :: C :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: alpha :: nil) (Ap :: B :: C :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: B :: C :: alpha :: nil) ((Ap :: nil) ++ (B :: C :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (B :: C :: alpha :: nil) (nil) 1 2 0 HApMtmp HBCalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: alpha ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : A :: Bp ::   de rang : 1 et 2 *)
assert(HBCApalpham2 : rk(B :: C :: Ap :: alpha :: nil) >= 2).
{
	assert(HABpMtmp : rk(A :: Bp :: nil) <= 2) by (solve_hyps_max HABpeq HABpM2).
	try assert(HABCApBpalphaeq : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) = 4) by (apply LABCApBpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpalphaeq HABCApBpalpham4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: Bp :: nil) (B :: C :: Ap :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: alpha :: nil) (A :: Bp :: B :: C :: Ap :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Bp :: B :: C :: Ap :: alpha :: nil) ((A :: Bp :: nil) ++ (B :: C :: Ap :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpalphamtmp;try rewrite HT2 in HABCApBpalphamtmp.
	assert(HT := rule_4 (A :: Bp :: nil) (B :: C :: Ap :: alpha :: nil) (nil) 4 0 2 HABCApBpalphamtmp Hmtmp HABpMtmp Hincl); apply HT.
}
try clear HABpM1. try clear HABpM2. try clear HABpM3. try clear HABpm4. try clear HABpm3. try clear HABpm2. try clear HABpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACCp requis par la preuve de (?)ACCp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HACCpm2 : rk(A :: C :: Cp :: nil) >= 2).
{
	assert(HBCApalphaMtmp : rk(B :: C :: Ap :: alpha :: nil) <= 3) by (solve_hyps_max HBCApalphaeq HBCApalphaM3).
	try assert(HABCApCpalphaeq : rk(A :: B :: C :: Ap :: Cp :: alpha :: nil) = 4) by (apply LABCApCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpalphamtmp : rk(A :: B :: C :: Ap :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApCpalphaeq HABCApCpalpham4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: C :: Cp :: nil) (B :: C :: Ap :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: alpha :: nil) (A :: C :: Cp :: B :: C :: Ap :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Cp :: B :: C :: Ap :: alpha :: nil) ((A :: C :: Cp :: nil) ++ (B :: C :: Ap :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpalphamtmp;try rewrite HT2 in HABCApCpalphamtmp.
	assert(HT := rule_2 (A :: C :: Cp :: nil) (B :: C :: Ap :: alpha :: nil) (C :: nil) 4 1 3 HABCApCpalphamtmp HCmtmp HBCApalphaMtmp Hincl);apply HT.
}
try clear HBCApalphaM1. try clear HBCApalphaM2. try clear HBCApalphaM3. try clear HBCApalpham4. try clear HBCApalpham3. try clear HBCApalpham2. try clear HBCApalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApCp requis par la preuve de (?)ACApCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Cp ::  de rang :  4 et 4 	 AiB : A :: C :: Cp ::  de rang :  2 et 3 	 A : A :: B :: C :: Cp ::   de rang : 4 et 4 *)
assert(HACApCpm2 : rk(A :: C :: Ap :: Cp :: nil) >= 2).
{
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpMtmp : rk(A :: B :: C :: Cp :: nil) <= 4) by (solve_hyps_max HABCCpeq HABCCpM4).
	try assert(HABCApCpeq : rk(A :: B :: C :: Ap :: Cp :: nil) = 4) by (apply LABCApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpmtmp : rk(A :: B :: C :: Ap :: Cp :: nil) >= 4) by (solve_hyps_min HABCApCpeq HABCApCpm4).
	assert(HACCpmtmp : rk(A :: C :: Cp :: nil) >= 2) by (solve_hyps_min HACCpeq HACCpm2).
	assert(Hincl : incl (A :: C :: Cp :: nil) (list_inter (A :: B :: C :: Cp :: nil) (A :: C :: Ap :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: nil) (A :: B :: C :: Cp :: A :: C :: Ap :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Cp :: A :: C :: Ap :: Cp :: nil) ((A :: B :: C :: Cp :: nil) ++ (A :: C :: Ap :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpmtmp;try rewrite HT2 in HABCApCpmtmp.
	assert(HT := rule_4 (A :: B :: C :: Cp :: nil) (A :: C :: Ap :: Cp :: nil) (A :: C :: Cp :: nil) 4 2 4 HABCApCpmtmp HACCpmtmp HABCCpMtmp Hincl); apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HACApCpm3 : rk(A :: C :: Ap :: Cp :: nil) >= 3).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	try assert(HABCApCpalphaeq : rk(A :: B :: C :: Ap :: Cp :: alpha :: nil) = 4) by (apply LABCApCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpalphamtmp : rk(A :: B :: C :: Ap :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApCpalphaeq HABCApCpalpham4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: C :: Ap :: Cp :: nil) (B :: C :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: alpha :: nil) (A :: C :: Ap :: Cp :: B :: C :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Ap :: Cp :: B :: C :: alpha :: nil) ((A :: C :: Ap :: Cp :: nil) ++ (B :: C :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpalphamtmp;try rewrite HT2 in HABCApCpalphamtmp.
	assert(HT := rule_2 (A :: C :: Ap :: Cp :: nil) (B :: C :: alpha :: nil) (C :: nil) 4 1 2 HABCApCpalphamtmp HCmtmp HBCalphaMtmp Hincl);apply HT.
}
try clear HABCApCpalphaM1. try clear HABCApCpalphaM2. try clear HABCApCpalphaM3. try clear HABCApCpalpham4. try clear HABCApCpalpham3. try clear HABCApCpalpham2. try clear HABCApCpalpham1. 

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApCpbetaOo requis par la preuve de (?)ACApCpbetaOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApCpbetaOo requis par la preuve de (?)ACApCpbetaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpbetaOo requis par la preuve de (?)ABCApCpbetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpbetaOom4 : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApCpbetaOo requis par la preuve de (?)ACApCpbetaOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Cp :: beta :: Oo ::  de rang :  4 et 4 	 AiB : A :: C :: Cp ::  de rang :  2 et 3 	 A : A :: B :: C :: Cp ::   de rang : 4 et 4 *)
assert(HACApCpbetaOom2 : rk(A :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 2).
{
	try assert(HABCCpeq : rk(A :: B :: C :: Cp :: nil) = 4) by (apply LABCCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpMtmp : rk(A :: B :: C :: Cp :: nil) <= 4) by (solve_hyps_max HABCCpeq HABCCpM4).
	assert(HABCApCpbetaOomtmp : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 4) by (solve_hyps_min HABCApCpbetaOoeq HABCApCpbetaOom4).
	assert(HACCpmtmp : rk(A :: C :: Cp :: nil) >= 2) by (solve_hyps_min HACCpeq HACCpm2).
	assert(Hincl : incl (A :: C :: Cp :: nil) (list_inter (A :: B :: C :: Cp :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) (A :: B :: C :: Cp :: A :: C :: Ap :: Cp :: beta :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Cp :: A :: C :: Ap :: Cp :: beta :: Oo :: nil) ((A :: B :: C :: Cp :: nil) ++ (A :: C :: Ap :: Cp :: beta :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpbetaOomtmp;try rewrite HT2 in HABCApCpbetaOomtmp.
	assert(HT := rule_4 (A :: B :: C :: Cp :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil) (A :: C :: Cp :: nil) 4 2 4 HABCApCpbetaOomtmp HACCpmtmp HABCCpMtmp Hincl); apply HT.
}
try clear HABCCpM1. try clear HABCCpM2. try clear HABCCpM3. try clear HABCCpm4. try clear HABCCpm3. try clear HABCCpm2. try clear HABCCpm1. try clear HACCpM1. try clear HACCpM2. try clear HACCpM3. try clear HACCpm4. try clear HACCpm3. try clear HACCpm2. try clear HACCpm1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HACApCpbetaOom3 : rk(A :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 3).
{
	assert(HACApCpmtmp : rk(A :: C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HACApCpeq HACApCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: Cp :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: Cp :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil) 3 3 HACApCpmtmp Hcomp Hincl);apply HT.
}
try clear HACApCpM1. try clear HACApCpM2. try clear HACApCpM3. try clear HACApCpm4. try clear HACApCpm3. try clear HACApCpm2. try clear HACApCpm1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HACApCpbetaOoM3 : rk(A :: C :: Ap :: Cp :: beta :: Oo :: nil) <= 3).
{
	try assert(HApCpbetaeq : rk(Ap :: Cp :: beta :: nil) = 2) by (apply LApCpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApCpbetaMtmp : rk(Ap :: Cp :: beta :: nil) <= 2) by (solve_hyps_max HApCpbetaeq HApCpbetaM2).
	try assert(HACApbetaOoeq : rk(A :: C :: Ap :: beta :: Oo :: nil) = 3) by (apply LACApbetaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACApbetaOoMtmp : rk(A :: C :: Ap :: beta :: Oo :: nil) <= 3) by (solve_hyps_max HACApbetaOoeq HACApbetaOoM3).
	try assert(HApbetaeq : rk(Ap :: beta :: nil) = 2) by (apply LApbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApbetamtmp : rk(Ap :: beta :: nil) >= 2) by (solve_hyps_min HApbetaeq HApbetam2).
	assert(Hincl : incl (Ap :: beta :: nil) (list_inter (Ap :: Cp :: beta :: nil) (A :: C :: Ap :: beta :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Cp :: beta :: Oo :: nil) (Ap :: Cp :: beta :: A :: C :: Ap :: beta :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Cp :: beta :: A :: C :: Ap :: beta :: Oo :: nil) ((Ap :: Cp :: beta :: nil) ++ (A :: C :: Ap :: beta :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Cp :: beta :: nil) (A :: C :: Ap :: beta :: Oo :: nil) (Ap :: beta :: nil) 2 3 2 HApCpbetaMtmp HACApbetaOoMtmp HApbetamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApCpbetaM1. try clear HApCpbetaM2. try clear HApCpbetaM3. try clear HApCpbetam4. try clear HApCpbetam3. try clear HApCpbetam2. try clear HApCpbetam1. try clear HApbetaM1. try clear HApbetaM2. try clear HApbetaM3. try clear HApbetam4. try clear HApbetam3. try clear HApbetam2. try clear HApbetam1. 

assert(HACApCpbetaOoM : rk(A :: C :: Ap :: Cp :: beta :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApCpbetaOom : rk(A :: C :: Ap :: Cp :: beta :: Oo ::  nil) >= 1) by (solve_hyps_min HACApCpbetaOoeq HACApCpbetaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApCpbetaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: Cp :: beta :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApCpbetaOo requis par la preuve de (?)ABCApCpbetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApCpbetaOom4 : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}


assert(HABCApCpbetaOoM : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApCpbetaOom : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApCpbetaOoeq HABCApCpbetaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApalphabetaOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(A :: B :: C :: Ap :: alpha :: beta :: Oo ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApalphabetaOo requis par la preuve de (?)ABCApalphabetaOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApalphabetaOom4 : rk(A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) >= 4).
{
	try assert(HABCApeq : rk(A :: B :: C :: Ap :: nil) = 4) by (apply LABCAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: alpha :: beta :: Oo :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}
try clear HABCApM1. try clear HABCApM2. try clear HABCApM3. try clear HABCApm4. try clear HABCApm3. try clear HABCApm2. try clear HABCApm1. 

assert(HABCApalphabetaOoM : rk(A :: B :: C :: Ap :: alpha :: beta :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApalphabetaOom : rk(A :: B :: C :: Ap :: alpha :: beta :: Oo ::  nil) >= 1) by (solve_hyps_min HABCApalphabetaOoeq HABCApalphabetaOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCCpOo : forall A B C Ap Bp Cp alpha beta gamma Oo ,
rk(A :: B :: C :: Ap ::  nil) = 4 -> rk(A :: B :: C :: Bp ::  nil) = 4 -> rk(A :: B :: C :: Cp ::  nil) = 4 ->
rk(A :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(B :: Ap :: Bp :: Cp ::  nil) = 4 -> rk(C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(B :: C :: alpha ::  nil) = 2 -> rk(Bp :: Cp :: alpha ::  nil) = 2 -> rk(A :: C :: beta ::  nil) = 2 ->
rk(Ap :: Cp :: beta ::  nil) = 2 -> rk(A :: B :: gamma ::  nil) = 2 -> rk(Ap :: Bp :: gamma ::  nil) = 2 ->
rk(A :: Ap :: Oo ::  nil) = 2 -> rk(B :: Bp :: Oo ::  nil) = 2 -> rk(C :: Cp :: Oo ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp alpha beta gamma Oo 
HABCApeq HABCBpeq HABCCpeq HAApBpCpeq HBApBpCpeq HCApBpCpeq HBCalphaeq HBpCpalphaeq HACbetaeq HApCpbetaeq
HABgammaeq HApBpgammaeq HAApOoeq HBBpOoeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CCpOo requis par la preuve de (?)CCpOo pour la règle 3  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCCpalphaOo requis par la preuve de (?)CCpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCCpalphaOo requis par la preuve de (?)BCCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCpalphaOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCCp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ACp requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApbeta requis par la preuve de (?)BCBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApbeta requis par la preuve de (?)ACApbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HACApbetaM3 : rk(A :: C :: Ap :: beta :: nil) <= 3).
{
	try assert(HApeq : rk(Ap :: nil) = 1) by (apply LAp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	try assert(HACbetaeq : rk(A :: C :: beta :: nil) = 2) by (apply LACbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACbetaMtmp : rk(A :: C :: beta :: nil) <= 2) by (solve_hyps_max HACbetaeq HACbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: beta :: nil) (Ap :: A :: C :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: beta :: nil) ((Ap :: nil) ++ (A :: C :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: beta :: nil) (nil) 1 2 0 HApMtmp HACbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: beta ::  de rang :  4 et 4 	 AiB :  de rang :  0 et 0 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACApbetam2 : rk(A :: C :: Ap :: beta :: nil) >= 2).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (nil) 4 0 2 HABCApBpbetamtmp Hmtmp HBBpMtmp Hincl); apply HT.
}
try clear HBBpM1. try clear HBBpM2. try clear HBBpM3. try clear HBBpm4. try clear HBBpm3. try clear HBBpm2. try clear HBBpm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HACApbetaMtmp : rk(A :: C :: Ap :: beta :: nil) <= 3) by (solve_hyps_max HACApbetaeq HACApbetaM3).
	try assert(HABCApBpbetaeq : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) = 4) by (apply LABCApBpbeta with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpbetamtmp : rk(A :: B :: C :: Ap :: Bp :: beta :: nil) >= 4) by (solve_hyps_min HABCApBpbetaeq HABCApBpbetam4).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: beta :: nil) (B :: C :: Bp :: A :: C :: Ap :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Bp :: A :: C :: Ap :: beta :: nil) ((B :: C :: Bp :: nil) ++ (A :: C :: Ap :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpbetamtmp;try rewrite HT2 in HABCApBpbetamtmp.
	assert(HT := rule_2 (B :: C :: Bp :: nil) (A :: C :: Ap :: beta :: nil) (C :: nil) 4 1 3 HABCApBpbetamtmp HCmtmp HACApbetaMtmp Hincl);apply HT.
}
try clear HACApbetaM1. try clear HACApbetaM2. try clear HACApbetaM3. try clear HACApbetam4. try clear HACApbetam3. try clear HACApbetam2. try clear HACApbetam1. try clear HABCApBpbetaM1. try clear HABCApBpbetaM2. try clear HABCApBpbetaM3. try clear HABCApBpbetam4. try clear HABCApBpbetam3. try clear HABCApBpbetam2. try clear HABCApBpbetam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpCpalpha requis par la preuve de (?)BCBpCpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: Cp :: alpha ::  de rang :  4 et 4 	 AiB : B :: C :: Bp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Bp ::   de rang : 4 et 4 *)
assert(HBCBpCpalpham2 : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 2).
{
	try assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpMtmp : rk(A :: B :: C :: Ap :: Bp :: nil) <= 4) by (solve_hyps_max HABCApBpeq HABCApBpM4).
	try assert(HABCApBpCpalphaeq : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) = 4) by (apply LABCApBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApBpCpalphamtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCApBpCpalphaeq HABCApBpCpalpham4).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 2) by (solve_hyps_min HBCBpeq HBCBpm2).
	assert(Hincl : incl (B :: C :: Bp :: nil) (list_inter (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: alpha :: nil) (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Bp :: B :: C :: Bp :: Cp :: alpha :: nil) ((A :: B :: C :: Ap :: Bp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpalphamtmp;try rewrite HT2 in HABCApBpCpalphamtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Bp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil) (B :: C :: Bp :: nil) 4 2 4 HABCApBpCpalphamtmp HBCBpmtmp HABCApBpMtmp Hincl); apply HT.
}
try clear HABCApBpCpalphaM1. try clear HABCApBpCpalphaM2. try clear HABCApBpCpalphaM3. try clear HABCApBpCpalpham4. try clear HABCApBpCpalpham3. try clear HABCApBpCpalpham2. try clear HABCApBpCpalpham1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: Bp :: Cp :: alpha ::  de rang :  4 et 4 	 AiB : Cp ::  de rang :  1 et 1 	 A : A :: Cp ::   de rang : 1 et 2 *)
assert(HBCBpCpalpham3 : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 3).
{
	assert(HACpMtmp : rk(A :: Cp :: nil) <= 2) by (solve_hyps_max HACpeq HACpM2).
	try assert(HABCBpCpalphaeq : rk(A :: B :: C :: Bp :: Cp :: alpha :: nil) = 4) by (apply LABCBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCBpCpalphamtmp : rk(A :: B :: C :: Bp :: Cp :: alpha :: nil) >= 4) by (solve_hyps_min HABCBpCpalphaeq HABCBpCpalpham4).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: Cp :: alpha :: nil) (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Cp :: B :: C :: Bp :: Cp :: alpha :: nil) ((A :: Cp :: nil) ++ (B :: C :: Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpCpalphamtmp;try rewrite HT2 in HABCBpCpalphamtmp.
	assert(HT := rule_4 (A :: Cp :: nil) (B :: C :: Bp :: Cp :: alpha :: nil) (Cp :: nil) 4 1 2 HABCBpCpalphamtmp HCpmtmp HACpMtmp Hincl); apply HT.
}
try clear HABCBpCpalphaM1. try clear HABCBpCpalphaM2. try clear HABCBpCpalphaM3. try clear HABCBpCpalpham4. try clear HABCBpCpalpham3. try clear HABCBpCpalpham2. try clear HABCBpCpalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCCp requis par la preuve de (?)BCCp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et 4*)
assert(HBCCpm2 : rk(B :: C :: Cp :: nil) >= 2).
{
	try assert(HBpCpalphaeq : rk(Bp :: Cp :: alpha :: nil) = 2) by (apply LBpCpalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBpCpalphaMtmp : rk(Bp :: Cp :: alpha :: nil) <= 2) by (solve_hyps_max HBpCpalphaeq HBpCpalphaM2).
	assert(HBCBpCpalphamtmp : rk(B :: C :: Bp :: Cp :: alpha :: nil) >= 3) by (solve_hyps_min HBCBpCpalphaeq HBCBpCpalpham3).
	try assert(HCpeq : rk(Cp :: nil) = 1) by (apply LCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCpmtmp : rk(Cp :: nil) >= 1) by (solve_hyps_min HCpeq HCpm1).
	assert(Hincl : incl (Cp :: nil) (list_inter (B :: C :: Cp :: nil) (Bp :: Cp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: alpha :: nil) (B :: C :: Cp :: Bp :: Cp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Cp :: Bp :: Cp :: alpha :: nil) ((B :: C :: Cp :: nil) ++ (Bp :: Cp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCBpCpalphamtmp;try rewrite HT2 in HBCBpCpalphamtmp.
	assert(HT := rule_2 (B :: C :: Cp :: nil) (Bp :: Cp :: alpha :: nil) (Cp :: nil) 3 1 2 HBCBpCpalphamtmp HCpmtmp HBpCpalphaMtmp Hincl);apply HT.
}
try clear HBpCpalphaM1. try clear HBpCpalphaM2. try clear HBpCpalphaM3. try clear HBpCpalpham4. try clear HBpCpalpham3. try clear HBpCpalpham2. try clear HBpCpalpham1. try clear HBCBpCpalphaM1. try clear HBCBpCpalphaM2. try clear HBCBpCpalphaM3. try clear HBCBpCpalpham4. try clear HBCBpCpalpham3. try clear HBCBpCpalpham2. try clear HBCBpCpalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCCpalphaOo requis par la preuve de (?)BCCpalphaOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Cp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : B :: C :: Cp ::  de rang :  2 et 3 	 A : A :: B :: C :: Ap :: Cp ::   de rang : 4 et 4 *)
assert(HBCCpalphaOom2 : rk(B :: C :: Cp :: alpha :: Oo :: nil) >= 2).
{
	try assert(HABCApCpeq : rk(A :: B :: C :: Ap :: Cp :: nil) = 4) by (apply LABCApCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpMtmp : rk(A :: B :: C :: Ap :: Cp :: nil) <= 4) by (solve_hyps_max HABCApCpeq HABCApCpM4).
	try assert(HABCApCpalphaOoeq : rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil) = 4) by (apply LABCApCpalphaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpalphaOomtmp : rk(A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCApCpalphaOoeq HABCApCpalphaOom4).
	assert(HBCCpmtmp : rk(B :: C :: Cp :: nil) >= 2) by (solve_hyps_min HBCCpeq HBCCpm2).
	assert(Hincl : incl (B :: C :: Cp :: nil) (list_inter (A :: B :: C :: Ap :: Cp :: nil) (B :: C :: Cp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: alpha :: Oo :: nil) (A :: B :: C :: Ap :: Cp :: B :: C :: Cp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: Cp :: B :: C :: Cp :: alpha :: Oo :: nil) ((A :: B :: C :: Ap :: Cp :: nil) ++ (B :: C :: Cp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpalphaOomtmp;try rewrite HT2 in HABCApCpalphaOomtmp.
	assert(HT := rule_4 (A :: B :: C :: Ap :: Cp :: nil) (B :: C :: Cp :: alpha :: Oo :: nil) (B :: C :: Cp :: nil) 4 2 4 HABCApCpalphaOomtmp HBCCpmtmp HABCApCpMtmp Hincl); apply HT.
}
try clear HABCApCpalphaOoM1. try clear HABCApCpalphaOoM2. try clear HABCApCpalphaOoM3. try clear HABCApCpalphaOom4. try clear HABCApCpalphaOom3. try clear HABCApCpalphaOom2. try clear HABCApCpalphaOom1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Cp :: alpha :: Oo ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : A :: alpha ::   de rang : 2 et 2 *)
assert(HBCCpalphaOom3 : rk(B :: C :: Cp :: alpha :: Oo :: nil) >= 3).
{
	try assert(HAalphaeq : rk(A :: alpha :: nil) = 2) by (apply LAalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HAalphaMtmp : rk(A :: alpha :: nil) <= 2) by (solve_hyps_max HAalphaeq HAalphaM2).
	try assert(HABCCpalphaOoeq : rk(A :: B :: C :: Cp :: alpha :: Oo :: nil) = 4) by (apply LABCCpalphaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCCpalphaOomtmp : rk(A :: B :: C :: Cp :: alpha :: Oo :: nil) >= 4) by (solve_hyps_min HABCCpalphaOoeq HABCCpalphaOom4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (A :: alpha :: nil) (B :: C :: Cp :: alpha :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: alpha :: Oo :: nil) (A :: alpha :: B :: C :: Cp :: alpha :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: alpha :: B :: C :: Cp :: alpha :: Oo :: nil) ((A :: alpha :: nil) ++ (B :: C :: Cp :: alpha :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpalphaOomtmp;try rewrite HT2 in HABCCpalphaOomtmp.
	assert(HT := rule_4 (A :: alpha :: nil) (B :: C :: Cp :: alpha :: Oo :: nil) (alpha :: nil) 4 1 2 HABCCpalphaOomtmp Halphamtmp HAalphaMtmp Hincl); apply HT.
}
try clear HABCCpalphaOoM1. try clear HABCCpalphaOoM2. try clear HABCCpalphaOoM3. try clear HABCCpalphaOom4. try clear HABCCpalphaOom3. try clear HABCCpalphaOom2. try clear HABCCpalphaOom1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CCpOo requis par la preuve de (?)CCpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : B :: C :: Cp :: alpha :: Oo ::  de rang :  3 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : B :: C :: alpha ::   de rang : 2 et 2 *)
assert(HCCpOom2 : rk(C :: Cp :: Oo :: nil) >= 2).
{
	try assert(HBCalphaeq : rk(B :: C :: alpha :: nil) = 2) by (apply LBCalpha with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCalphaMtmp : rk(B :: C :: alpha :: nil) <= 2) by (solve_hyps_max HBCalphaeq HBCalphaM2).
	assert(HBCCpalphaOomtmp : rk(B :: C :: Cp :: alpha :: Oo :: nil) >= 3) by (solve_hyps_min HBCCpalphaOoeq HBCCpalphaOom3).
	try assert(HCeq : rk(C :: nil) = 1) by (apply LC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (B :: C :: alpha :: nil) (C :: Cp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Cp :: alpha :: Oo :: nil) (B :: C :: alpha :: C :: Cp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: alpha :: C :: Cp :: Oo :: nil) ((B :: C :: alpha :: nil) ++ (C :: Cp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCCpalphaOomtmp;try rewrite HT2 in HBCCpalphaOomtmp.
	assert(HT := rule_4 (B :: C :: alpha :: nil) (C :: Cp :: Oo :: nil) (C :: nil) 3 1 2 HBCCpalphaOomtmp HCmtmp HBCalphaMtmp Hincl); apply HT.
}
try clear HBCCpalphaOoM1. try clear HBCCpalphaOoM2. try clear HBCCpalphaOoM3. try clear HBCCpalphaOom4. try clear HBCCpalphaOom3. try clear HBCCpalphaOom2. try clear HBCCpalphaOom1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HCCpOoM2 : rk(C :: Cp :: Oo :: nil) <= 2).
{
	try assert(HBCCpOoeq : rk(B :: C :: Cp :: Oo :: nil) = 3) by (apply LBCCpOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HBCCpOoMtmp : rk(B :: C :: Cp :: Oo :: nil) <= 3) by (solve_hyps_max HBCCpOoeq HBCCpOoM3).
	try assert(HACApCpbetaOoeq : rk(A :: C :: Ap :: Cp :: beta :: Oo :: nil) = 3) by (apply LACApCpbetaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HACApCpbetaOoMtmp : rk(A :: C :: Ap :: Cp :: beta :: Oo :: nil) <= 3) by (solve_hyps_max HACApCpbetaOoeq HACApCpbetaOoM3).
	try assert(HABCApCpbetaOoeq : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) = 4) by (apply LABCApCpbetaOo with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (alpha := alpha) (beta := beta) (gamma := gamma) (Oo := Oo) ;try assumption).
	assert(HABCApCpbetaOomtmp : rk(A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) >= 4) by (solve_hyps_min HABCApCpbetaOoeq HABCApCpbetaOom4).
	assert(Hincl : incl (C :: Cp :: Oo :: nil) (list_inter (B :: C :: Cp :: Oo :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Cp :: beta :: Oo :: nil) (B :: C :: Cp :: Oo :: A :: C :: Ap :: Cp :: beta :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Cp :: Oo :: A :: C :: Ap :: Cp :: beta :: Oo :: nil) ((B :: C :: Cp :: Oo :: nil) ++ (A :: C :: Ap :: Cp :: beta :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApCpbetaOomtmp;try rewrite HT2 in HABCApCpbetaOomtmp.
	assert(HT := rule_3 (B :: C :: Cp :: Oo :: nil) (A :: C :: Ap :: Cp :: beta :: Oo :: nil) (C :: Cp :: Oo :: nil) 3 3 4 HBCCpOoMtmp HACApCpbetaOoMtmp HABCApCpbetaOomtmp Hincl);apply HT.
}


assert(HCCpOoM : rk(C :: Cp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCCpOoeq HCCpOoM3).
assert(HCCpOom : rk(C :: Cp :: Oo ::  nil) >= 1) by (solve_hyps_min HCCpOoeq HCCpOom1).
intuition.
Qed.

