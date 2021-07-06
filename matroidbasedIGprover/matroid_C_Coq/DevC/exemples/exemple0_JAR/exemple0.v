Load "preamble2D.v".


(* dans la couche 0 *)
Lemma LABCD : forall A B C D ,
rk(A :: C ::  nil) = 2 -> rk(A :: B :: D ::  nil) = 3 -> rk(C :: D ::  nil) = 2 ->
rk(A :: C :: D ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 3.
Proof.

intros A B C D 
HACeq HABDeq HCDeq HACDeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCD requis par la preuve de (?)ABCD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCD requis par la preuve de (?)ABCD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDm2 : rk(A :: B :: C :: D :: nil) >= 2).
{
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (A :: B :: C :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (A :: B :: C :: D :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDm3 : rk(A :: B :: C :: D :: nil) >= 3).
{
	assert(HABDmtmp : rk(A :: B :: D :: nil) >= 3) by (solve_hyps_min HABDeq HABDm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: nil) (A :: B :: C :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: nil) (A :: B :: C :: D :: nil) 3 3 HABDmtmp Hcomp Hincl);apply HT.
}

assert(HABCDM : rk(A :: B :: C :: D ::  nil) <= 3) by (solve_hyps_max HABCDeq HABCDM3).
assert(HABCDm : rk(A :: B :: C :: D ::  nil) >= 1) by (solve_hyps_min HABCDeq HABCDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABC : forall A B C D ,
rk(A :: C ::  nil) = 2 -> rk(A :: B :: D ::  nil) = 3 -> rk(C :: D ::  nil) = 2 ->
rk(A :: C :: D ::  nil) = 2 -> rk(A :: B :: C ::  nil) = 3.
Proof.

intros A B C D 
HACeq HABDeq HCDeq HACDeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABC requis par la preuve de (?)ABC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABC requis par la preuve de (?)ABC pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCm2 : rk(A :: B :: C :: nil) >= 2).
{
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (A :: B :: C :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (A :: B :: C :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et -4*)
assert(HABCm3 : rk(A :: B :: C :: nil) >= 3).
{
	assert(HACDMtmp : rk(A :: C :: D :: nil) <= 2) by (solve_hyps_max HACDeq HACDM2).
	assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 3) by (apply LABCD with (A := A) (B := B) (C := C) (D := D) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 3) by (solve_hyps_min HABCDeq HABCDm3).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (A :: B :: C :: nil) (A :: C :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: nil) (A :: B :: C :: A :: C :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A :: C :: D :: nil) ((A :: B :: C :: nil) ++ (A :: C :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDmtmp;try rewrite HT2 in HABCDmtmp.
	assert(HT := rule_2 (A :: B :: C :: nil) (A :: C :: D :: nil) (A :: C :: nil) 3 2 2 HABCDmtmp HACmtmp HACDMtmp Hincl);apply HT.
}

assert(HABCM : rk(A :: B :: C ::  nil) <= 3) by (solve_hyps_max HABCeq HABCM3).
assert(HABCm : rk(A :: B :: C ::  nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
intuition.
Qed.

