Load "preamble5D.v".


(* dans constructLemma(), requis par LCp1 *)
(* dans constructLemma(), requis par LCDEp1 *)
(* dans la couche 0 *)
Lemma LABCDEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: p1 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDEp1 requis par la preuve de (?)ABCDEp1 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDp1 requis par la preuve de (?)ABCDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCp1 requis par la preuve de (?)ABCDp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp1 requis par la preuve de (?)ABCp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCp1M3 : rk(A :: B :: C :: p1 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: nil) (C :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: B :: p1 :: nil) ((C :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HCMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDp1 requis par la preuve de (?)ABCDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDp1M4 : rk(A :: B :: C :: D :: p1 :: nil) <= 4).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABCp1Mtmp : rk(A :: B :: C :: p1 :: nil) <= 3) by (solve_hyps_max HABCp1eq HABCp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: C :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p1 :: nil) (D :: A :: B :: C :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: C :: p1 :: nil) ((D :: nil) ++ (A :: B :: C :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: C :: p1 :: nil) (nil) 1 3 0 HDMtmp HABCp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1 requis par la preuve de (?)ABCDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDEp1M5 : rk(A :: B :: C :: D :: E :: p1 :: nil) <= 5).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCDp1Mtmp : rk(A :: B :: C :: D :: p1 :: nil) <= 4) by (solve_hyps_max HABCDp1eq HABCDp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: nil) (E :: A :: B :: C :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: C :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: D :: p1 :: nil) (nil) 1 4 0 HEMtmp HABCDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1m5 : rk(A :: B :: C :: D :: E :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEp1M : rk(A :: B :: C :: D :: E :: p1 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEp1m : rk(A :: B :: C :: D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HABCDEp1eq HABCDEp1m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCDEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(C :: D :: E :: p1 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEp1 requis par la preuve de (?)CDEp1 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HCDEp1m4 : rk(C :: D :: E :: p1 :: nil) >= 4).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1eq : rk(A :: B :: C :: D :: E :: p1 :: nil) = 5) by (apply LABCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1mtmp : rk(A :: B :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEp1eq HABCDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: B :: p1 :: nil) (C :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: nil) (A :: B :: p1 :: C :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: C :: D :: E :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (C :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1mtmp;try rewrite HT2 in HABCDEp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (C :: D :: E :: p1 :: nil) (p1 :: nil) 5 1 2 HABCDEp1mtmp Hp1mtmp HABp1Mtmp Hincl); apply HT.
}

assert(HCDEp1M : rk(C :: D :: E :: p1 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HCDEp1eq HCDEp1M4).
assert(HCDEp1m : rk(C :: D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HCDEp1eq HCDEp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LCp1 *)
(* dans la couche 0 *)
Lemma LCp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(C :: p1 ::  nil) = 2.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour DEp1 requis par la preuve de (?)Cp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)DEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour DEp1 requis par la preuve de (?)DEp1 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: D :: E :: p1 ::  de rang :  3 et 4 	 AiB : p1 ::  de rang :  1 et 1 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HDEp1m2 : rk(D :: E :: p1 :: nil) >= 2).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABDEp1mtmp : rk(A :: B :: D :: E :: p1 :: nil) >= 3) by (solve_hyps_min HABDEp1eq HABDEp1m3).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: B :: p1 :: nil) (D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (A :: B :: p1 :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: D :: E :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEp1mtmp;try rewrite HT2 in HABDEp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (D :: E :: p1 :: nil) (p1 :: nil) 3 1 2 HABDEp1mtmp Hp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Cp1 requis par la preuve de (?)Cp1 pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 5*)
assert(HCp1m2 : rk(C :: p1 :: nil) >= 2).
{
	assert(HDEp1Mtmp : rk(D :: E :: p1 :: nil) <= 3) by (solve_hyps_max HDEp1eq HDEp1M3).
	assert(HCDEp1eq : rk(C :: D :: E :: p1 :: nil) = 4) by (apply LCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCDEp1mtmp : rk(C :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HCDEp1eq HCDEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: p1 :: nil) (C :: p1 :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: D :: E :: p1 :: nil) ((C :: p1 :: nil) ++ (D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEp1mtmp;try rewrite HT2 in HCDEp1mtmp.
	assert(HT := rule_2 (C :: p1 :: nil) (D :: E :: p1 :: nil) (p1 :: nil) 4 1 3 HCDEp1mtmp Hp1mtmp HDEp1Mtmp Hincl);apply HT.
}

assert(HCp1M : rk(C :: p1 ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HCp1eq HCp1M2).
assert(HCp1m : rk(C :: p1 ::  nil) >= 1) by (solve_hyps_min HCp1eq HCp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LACp1 *)
(* dans la couche 0 *)
Lemma LACDEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: D :: E :: p1 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEp1 requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bp1 requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACDEp1 requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1 requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1 requis par la preuve de (?)ABCDEApEpp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABApEp requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApEp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HABApEpm2 : rk(A :: B :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: B :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp1 requis par la preuve de (?)ACDEp1 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HACDEp1m2 : rk(A :: C :: D :: E :: p1 :: nil) >= 2).
{
	assert(HABApEpMtmp : rk(A :: B :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HABApEpeq HABApEpM4).
	assert(HABCDEApEpp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1eq HABCDEApEpp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: nil) (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: nil) ((A :: B :: Ap :: Ep :: nil) ++ (A :: C :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1mtmp;try rewrite HT2 in HABCDEApEpp1mtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1mtmp HAmtmp HABApEpMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : B :: p1 ::   de rang : 1 et 2 *)
assert(HACDEp1m4 : rk(A :: C :: D :: E :: p1 :: nil) >= 4).
{
	assert(HBp1Mtmp : rk(B :: p1 :: nil) <= 2) by (solve_hyps_max HBp1eq HBp1M2).
	assert(HABCDEp1eq : rk(A :: B :: C :: D :: E :: p1 :: nil) = 5) by (apply LABCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1mtmp : rk(A :: B :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEp1eq HABCDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: nil) (B :: p1 :: A :: C :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: p1 :: A :: C :: D :: E :: p1 :: nil) ((B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1mtmp;try rewrite HT2 in HABCDEp1mtmp.
	assert(HT := rule_4 (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: nil) (p1 :: nil) 5 1 2 HABCDEp1mtmp Hp1mtmp HBp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 ::  de rang :  5 et 5 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp1m5 : rk(A :: C :: D :: E :: p1 :: nil) >= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1eq : rk(A :: B :: C :: D :: E :: p1 :: nil) = 5) by (apply LABCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1mtmp : rk(A :: B :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEp1eq HABCDEp1m5).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1mtmp;try rewrite HT2 in HABCDEp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: nil) (A :: p1 :: nil) 5 2 2 HABCDEp1mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

assert(HACDEp1M : rk(A :: C :: D :: E :: p1 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HACDEp1eq HACDEp1M5).
assert(HACDEp1m : rk(A :: C :: D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HACDEp1eq HACDEp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LACp1 *)
(* dans la couche 0 *)
Lemma LDEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(D :: E :: p1 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour DEp1 requis par la preuve de (?)DEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)DEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour DEp1 requis par la preuve de (?)DEp1 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: D :: E :: p1 ::  de rang :  3 et 4 	 AiB : p1 ::  de rang :  1 et 1 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HDEp1m2 : rk(D :: E :: p1 :: nil) >= 2).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABDEp1mtmp : rk(A :: B :: D :: E :: p1 :: nil) >= 3) by (solve_hyps_min HABDEp1eq HABDEp1m3).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: B :: p1 :: nil) (D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (A :: B :: p1 :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: D :: E :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEp1mtmp;try rewrite HT2 in HABDEp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (D :: E :: p1 :: nil) (p1 :: nil) 3 1 2 HABDEp1mtmp Hp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : C :: D :: E :: p1 ::  de rang :  4 et 4 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HDEp1m3 : rk(D :: E :: p1 :: nil) >= 3).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HCDEp1eq : rk(C :: D :: E :: p1 :: nil) = 4) by (apply LCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCDEp1mtmp : rk(C :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HCDEp1eq HCDEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: p1 :: nil) (C :: p1 :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: D :: E :: p1 :: nil) ((C :: p1 :: nil) ++ (D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEp1mtmp;try rewrite HT2 in HCDEp1mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (D :: E :: p1 :: nil) (p1 :: nil) 4 1 2 HCDEp1mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

assert(HDEp1M : rk(D :: E :: p1 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HDEp1eq HDEp1M3).
assert(HDEp1m : rk(D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HDEp1eq HDEp1m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: p1 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACp1 requis par la preuve de (?)ACp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACp1 requis par la preuve de (?)ACp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACp1m2 : rk(A :: C :: p1 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: p1 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HACp1m3 : rk(A :: C :: p1 :: nil) >= 3).
{
	assert(HDEp1eq : rk(D :: E :: p1 :: nil) = 3) by (apply LDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDEp1Mtmp : rk(D :: E :: p1 :: nil) <= 3) by (solve_hyps_max HDEp1eq HDEp1M3).
	assert(HACDEp1eq : rk(A :: C :: D :: E :: p1 :: nil) = 5) by (apply LACDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEp1mtmp : rk(A :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HACDEp1eq HACDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: C :: p1 :: nil) (D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: nil) (A :: C :: p1 :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p1 :: D :: E :: p1 :: nil) ((A :: C :: p1 :: nil) ++ (D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1mtmp;try rewrite HT2 in HACDEp1mtmp.
	assert(HT := rule_2 (A :: C :: p1 :: nil) (D :: E :: p1 :: nil) (p1 :: nil) 5 1 3 HACDEp1mtmp Hp1mtmp HDEp1Mtmp Hincl);apply HT.
}

assert(HACp1M : rk(A :: C :: p1 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HACp1eq HACp1M3).
assert(HACp1m : rk(A :: C :: p1 ::  nil) >= 1) by (solve_hyps_min HACp1eq HACp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LDp1 *)
(* dans la couche 0 *)
Lemma LADEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: D :: E :: p1 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ADEp1 requis par la preuve de (?)ADEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ADEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADEp1 requis par la preuve de (?)ADEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEp1 requis par la preuve de (?)ADEp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADEp1m2 : rk(A :: D :: E :: p1 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: E :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: E :: p1 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: D :: E :: p1 ::  de rang :  3 et 4 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HADEp1m3 : rk(A :: D :: E :: p1 :: nil) >= 3).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABDEp1mtmp : rk(A :: B :: D :: E :: p1 :: nil) >= 3) by (solve_hyps_min HABDEp1eq HABDEp1m3).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (A :: B :: p1 :: A :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: D :: E :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (A :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEp1mtmp;try rewrite HT2 in HABDEp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: D :: E :: p1 :: nil) (A :: p1 :: nil) 3 2 2 HABDEp1mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HADEp1m4 : rk(A :: D :: E :: p1 :: nil) >= 4).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HACDEp1eq : rk(A :: C :: D :: E :: p1 :: nil) = 5) by (apply LACDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEp1mtmp : rk(A :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HACDEp1eq HACDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (A :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: nil) (C :: p1 :: A :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: D :: E :: p1 :: nil) ((C :: p1 :: nil) ++ (A :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1mtmp;try rewrite HT2 in HACDEp1mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: D :: E :: p1 :: nil) (p1 :: nil) 5 1 2 HACDEp1mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

assert(HADEp1M : rk(A :: D :: E :: p1 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HADEp1eq HADEp1M4).
assert(HADEp1m : rk(A :: D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HADEp1eq HADEp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LDp1 *)
(* dans la couche 0 *)
Lemma LDp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(D :: p1 ::  nil) = 2.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AEp1 requis par la preuve de (?)Dp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AEp1 requis par la preuve de (?)AEp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAEp1m2 : rk(A :: E :: p1 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: E :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: E :: p1 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Dp1 requis par la preuve de (?)Dp1 pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 5*)
assert(HDp1m2 : rk(D :: p1 :: nil) >= 2).
{
	assert(HAEp1Mtmp : rk(A :: E :: p1 :: nil) <= 3) by (solve_hyps_max HAEp1eq HAEp1M3).
	assert(HADEp1eq : rk(A :: D :: E :: p1 :: nil) = 4) by (apply LADEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEp1mtmp : rk(A :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HADEp1eq HADEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: nil) (D :: p1 :: A :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: E :: p1 :: nil) ((D :: p1 :: nil) ++ (A :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1mtmp;try rewrite HT2 in HADEp1mtmp.
	assert(HT := rule_2 (D :: p1 :: nil) (A :: E :: p1 :: nil) (p1 :: nil) 4 1 3 HADEp1mtmp Hp1mtmp HAEp1Mtmp Hincl);apply HT.
}

assert(HDp1M : rk(D :: p1 ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HDp1eq HDp1M2).
assert(HDp1m : rk(D :: p1 ::  nil) >= 1) by (solve_hyps_min HDp1eq HDp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LADp1 *)
(* dans la couche 0 *)
Lemma LADp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: D :: p1 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Ep1 requis par la preuve de (?)ADp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADp1 requis par la preuve de (?)ADp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADp1 requis par la preuve de (?)ADp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADp1m2 : rk(A :: D :: p1 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: p1 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 5*)
assert(HADp1m3 : rk(A :: D :: p1 :: nil) >= 3).
{
	assert(HEp1Mtmp : rk(E :: p1 :: nil) <= 2) by (solve_hyps_max HEp1eq HEp1M2).
	assert(HADEp1eq : rk(A :: D :: E :: p1 :: nil) = 4) by (apply LADEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEp1mtmp : rk(A :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HADEp1eq HADEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: D :: p1 :: nil) (E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: nil) (A :: D :: p1 :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p1 :: E :: p1 :: nil) ((A :: D :: p1 :: nil) ++ (E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1mtmp;try rewrite HT2 in HADEp1mtmp.
	assert(HT := rule_2 (A :: D :: p1 :: nil) (E :: p1 :: nil) (p1 :: nil) 4 1 2 HADEp1mtmp Hp1mtmp HEp1Mtmp Hincl);apply HT.
}

assert(HADp1M : rk(A :: D :: p1 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HADp1eq HADp1M3).
assert(HADp1m : rk(A :: D :: p1 ::  nil) >= 1) by (solve_hyps_min HADp1eq HADp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LACDp1 *)
(* dans la couche 0 *)
Lemma LEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(E :: p1 ::  nil) = 2.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Ep1 requis par la preuve de (?)Ep1 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: D :: E :: p1 ::  de rang :  4 et 4 	 AiB : p1 ::  de rang :  1 et 1 	 A : A :: D :: p1 ::   de rang : 3 et 3 *)
assert(HEp1m2 : rk(E :: p1 :: nil) >= 2).
{
	assert(HADp1eq : rk(A :: D :: p1 :: nil) = 3) by (apply LADp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADp1Mtmp : rk(A :: D :: p1 :: nil) <= 3) by (solve_hyps_max HADp1eq HADp1M3).
	assert(HADEp1eq : rk(A :: D :: E :: p1 :: nil) = 4) by (apply LADEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEp1mtmp : rk(A :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HADEp1eq HADEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: D :: p1 :: nil) (E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: nil) (A :: D :: p1 :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p1 :: E :: p1 :: nil) ((A :: D :: p1 :: nil) ++ (E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1mtmp;try rewrite HT2 in HADEp1mtmp.
	assert(HT := rule_4 (A :: D :: p1 :: nil) (E :: p1 :: nil) (p1 :: nil) 4 1 3 HADEp1mtmp Hp1mtmp HADp1Mtmp Hincl); apply HT.
}

assert(HEp1M : rk(E :: p1 ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HEp1eq HEp1M2).
assert(HEp1m : rk(E :: p1 ::  nil) >= 1) by (solve_hyps_min HEp1eq HEp1m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACDp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: D :: p1 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDp1 requis par la preuve de (?)ACDp1 pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCDp1 requis par la preuve de (?)ACDp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCDp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDp1 requis par la preuve de (?)ABCDp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCp1 requis par la preuve de (?)ABCDp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp1 requis par la preuve de (?)ABCp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCp1M3 : rk(A :: B :: C :: p1 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: nil) (C :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: B :: p1 :: nil) ((C :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HCMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDp1 requis par la preuve de (?)ABCDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDp1M4 : rk(A :: B :: C :: D :: p1 :: nil) <= 4).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABCp1Mtmp : rk(A :: B :: C :: p1 :: nil) <= 3) by (solve_hyps_max HABCp1eq HABCp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: C :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p1 :: nil) (D :: A :: B :: C :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: C :: p1 :: nil) ((D :: nil) ++ (A :: B :: C :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: C :: p1 :: nil) (nil) 1 3 0 HDMtmp HABCp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCDp1m3 : rk(A :: B :: C :: D :: p1 :: nil) >= 3).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (E :: Ap :: A :: B :: C :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: D :: p1 :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: D :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACDp1 requis par la preuve de (?)ACDp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp1 requis par la preuve de (?)ACDp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACDp1m2 : rk(A :: C :: D :: p1 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: D :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: D :: p1 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: p1 ::  de rang :  3 et 4 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDp1m3 : rk(A :: C :: D :: p1 :: nil) >= 3).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDp1mtmp : rk(A :: B :: C :: D :: p1 :: nil) >= 3) by (solve_hyps_min HABCDp1eq HABCDp1m3).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p1 :: nil) (A :: B :: p1 :: A :: C :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: p1 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDp1mtmp;try rewrite HT2 in HABCDp1mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: p1 :: nil) (A :: p1 :: nil) 3 2 2 HABCDp1mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HACDp1m4 : rk(A :: C :: D :: p1 :: nil) >= 4).
{
	assert(HEp1eq : rk(E :: p1 :: nil) = 2) by (apply LEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HEp1Mtmp : rk(E :: p1 :: nil) <= 2) by (solve_hyps_max HEp1eq HEp1M2).
	assert(HACDEp1eq : rk(A :: C :: D :: E :: p1 :: nil) = 5) by (apply LACDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEp1mtmp : rk(A :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HACDEp1eq HACDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (A :: C :: D :: p1 :: nil) (E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: nil) (A :: C :: D :: p1 :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: p1 :: E :: p1 :: nil) ((A :: C :: D :: p1 :: nil) ++ (E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1mtmp;try rewrite HT2 in HACDEp1mtmp.
	assert(HT := rule_2 (A :: C :: D :: p1 :: nil) (E :: p1 :: nil) (p1 :: nil) 5 1 2 HACDEp1mtmp Hp1mtmp HEp1Mtmp Hincl);apply HT.
}

assert(HACDp1M : rk(A :: C :: D :: p1 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HACDp1eq HACDp1M4).
assert(HACDp1m : rk(A :: C :: D :: p1 ::  nil) >= 1) by (solve_hyps_min HACDp1eq HACDp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LABEp1 *)
(* dans la couche 0 *)
Lemma LABDEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: D :: E :: p1 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HABDEp1m4 : rk(A :: B :: D :: E :: p1 :: nil) >= 4).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HABCDEp1eq : rk(A :: B :: C :: D :: E :: p1 :: nil) = 5) by (apply LABCDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1mtmp : rk(A :: B :: C :: D :: E :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEp1eq HABCDEp1m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: nil) (C :: p1 :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: B :: D :: E :: p1 :: nil) ((C :: p1 :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1mtmp;try rewrite HT2 in HABCDEp1mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: B :: D :: E :: p1 :: nil) (p1 :: nil) 5 1 2 HABCDEp1mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

assert(HABDEp1M : rk(A :: B :: D :: E :: p1 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABDEp1eq HABDEp1M5).
assert(HABDEp1m : rk(A :: B :: D :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HABDEp1eq HABDEp1m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABEp1 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: E :: p1 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: D :: E :: p1 ::  de rang :  4 et 4 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABEp1m3 : rk(A :: B :: E :: p1 :: nil) >= 3).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABDEp1eq : rk(A :: B :: D :: E :: p1 :: nil) = 4) by (apply LABDEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABDEp1mtmp : rk(A :: B :: D :: E :: p1 :: nil) >= 4) by (solve_hyps_min HABDEp1eq HABDEp1m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (D :: p1 :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: E :: p1 :: nil) ((D :: p1 :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEp1mtmp;try rewrite HT2 in HABDEp1mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: E :: p1 :: nil) (p1 :: nil) 4 1 2 HABDEp1mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

assert(HABEp1M : rk(A :: B :: E :: p1 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HABEp1eq HABEp1M4).
assert(HABEp1m : rk(A :: B :: E :: p1 ::  nil) >= 1) by (solve_hyps_min HABEp1eq HABEp1m1).
intuition.
Qed.

(* dans constructLemma(), requis par LABp2 *)
(* dans la couche 0 *)
Lemma LABCDEp2 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: p2 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDEp2 requis par la preuve de (?)ABCDEp2 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDp2 requis par la preuve de (?)ABCDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCp2 requis par la preuve de (?)ABCDp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp2 requis par la preuve de (?)ABCp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCp2M3 : rk(A :: B :: C :: p2 :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p2 :: nil) (B :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: C :: p2 :: nil) ((B :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HBMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDp2 requis par la preuve de (?)ABCDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDp2M4 : rk(A :: B :: C :: D :: p2 :: nil) <= 4).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABCp2Mtmp : rk(A :: B :: C :: p2 :: nil) <= 3) by (solve_hyps_max HABCp2eq HABCp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p2 :: nil) (D :: A :: B :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: C :: p2 :: nil) ((D :: nil) ++ (A :: B :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: C :: p2 :: nil) (nil) 1 3 0 HDMtmp HABCp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp2 requis par la preuve de (?)ABCDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDEp2M5 : rk(A :: B :: C :: D :: E :: p2 :: nil) <= 5).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCDp2Mtmp : rk(A :: B :: C :: D :: p2 :: nil) <= 4) by (solve_hyps_max HABCDp2eq HABCDp2M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p2 :: nil) (E :: A :: B :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: B :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: D :: p2 :: nil) (nil) 1 4 0 HEMtmp HABCDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp2m5 : rk(A :: B :: C :: D :: E :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEp2M : rk(A :: B :: C :: D :: E :: p2 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEp2m : rk(A :: B :: C :: D :: E :: p2 ::  nil) >= 1) by (solve_hyps_min HABCDEp2eq HABCDEp2m1).
intuition.
Qed.

(* dans constructLemma(), requis par LABp2 *)
(* dans constructLemma(), requis par LACDEp2 *)
(* dans constructLemma(), requis par LABCDEp1p2 *)
(* dans la couche 0 *)
Lemma LABCDEp1p2 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: p1 :: p2 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABCDEp1p2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p2 requis par la preuve de (?)ABCDEp1p2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p2 requis par la preuve de (?)ABCDEp1p2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p2m5 : rk(A :: B :: C :: D :: E :: p1 :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HABCDEp1p2M5 : rk(A :: B :: C :: D :: E :: p1 :: p2 :: nil) <= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 2 4 1 HABp1Mtmp HACDEp2Mtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEp1p2M : rk(A :: B :: C :: D :: E :: p1 :: p2 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEp1p2m : rk(A :: B :: C :: D :: E :: p1 :: p2 ::  nil) >= 1) by (solve_hyps_min HABCDEp1p2eq HABCDEp1p2m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACDEp2 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: D :: E :: p2 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 ::  de rang :  5 et 5 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp2m4 : rk(A :: C :: D :: E :: p2 :: nil) >= 4).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1p2eq : rk(A :: B :: C :: D :: E :: p1 :: p2 :: nil) = 5) by (apply LABCDEp1p2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1p2mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2eq HABCDEp1p2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2mtmp;try rewrite HT2 in HABCDEp1p2mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 2 HABCDEp1p2mtmp HAmtmp HABp1Mtmp Hincl); apply HT.
}

assert(HACDEp2M : rk(A :: C :: D :: E :: p2 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HACDEp2eq HACDEp2M5).
assert(HACDEp2m : rk(A :: C :: D :: E :: p2 ::  nil) >= 1) by (solve_hyps_min HACDEp2eq HACDEp2m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABp2 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: p2 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABp2 requis par la preuve de (?)ABp2 pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABp2 requis par la preuve de (?)ABp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABp2m2 : rk(A :: B :: p2 :: nil) >= 2).
{
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p2 :: nil) (A :: B :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p2 :: nil) (A :: B :: p2 :: nil) 2 2 HAp2mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HABp2m3 : rk(A :: B :: p2 :: nil) >= 3).
{
	assert(HACDEp2eq : rk(A :: C :: D :: E :: p2 :: nil) = 4) by (apply LACDEp2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEp2eq : rk(A :: B :: C :: D :: E :: p2 :: nil) = 5) by (apply LABCDEp2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp2mtmp : rk(A :: B :: C :: D :: E :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEp2eq HABCDEp2m5).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: B :: p2 :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p2 :: nil) (A :: B :: p2 :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p2 :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: p2 :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp2mtmp;try rewrite HT2 in HABCDEp2mtmp.
	assert(HT := rule_2 (A :: B :: p2 :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: p2 :: nil) 5 2 4 HABCDEp2mtmp HAp2mtmp HACDEp2Mtmp Hincl);apply HT.
}

assert(HABp2M : rk(A :: B :: p2 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HABp2eq HABp2M3).
assert(HABp2m : rk(A :: B :: p2 ::  nil) >= 1) by (solve_hyps_min HABp2eq HABp2m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABp1p2 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: p1 :: p2 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABp1p2 requis par la preuve de (?)ABp1p2 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABp1p2 requis par la preuve de (?)ABp1p2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABp1p2 requis par la preuve de (?)ABp1p2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABp1p2m2 : rk(A :: B :: p1 :: p2 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: B :: p1 :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: B :: p1 :: p2 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HABp1p2M3 : rk(A :: B :: p1 :: p2 :: nil) <= 3).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hp2Mtmp : rk(p2 :: nil) <= 1) by (solve_hyps_max Hp2eq Hp2M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: p1 :: nil) (p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: p1 :: p2 :: nil) (A :: B :: p1 :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: p2 :: nil) ((A :: B :: p1 :: nil) ++ (p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (p2 :: nil) (nil) 2 1 0 HABp1Mtmp Hp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABp1p2m3 : rk(A :: B :: p1 :: p2 :: nil) >= 3).
{
	assert(HABp2eq : rk(A :: B :: p2 :: nil) = 3) by (apply LABp2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABp2mtmp : rk(A :: B :: p2 :: nil) >= 3) by (solve_hyps_min HABp2eq HABp2m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: p2 :: nil) (A :: B :: p1 :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: p2 :: nil) (A :: B :: p1 :: p2 :: nil) 3 3 HABp2mtmp Hcomp Hincl);apply HT.
}

assert(HABp1p2M : rk(A :: B :: p1 :: p2 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HABp1p2eq HABp1p2M4).
assert(HABp1p2m : rk(A :: B :: p1 :: p2 ::  nil) >= 1) by (solve_hyps_min HABp1p2eq HABp1p2m1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCp3 *)
(* dans la couche 0 *)
Lemma LABCDEp3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: p3 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDEp3 requis par la preuve de (?)ABCDEp3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDp3 requis par la preuve de (?)ABCDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp3 requis par la preuve de (?)ABCDp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp3 requis par la preuve de (?)ABDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp3M3 : rk(A :: B :: D :: p3 :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p3 :: nil) (B :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: D :: p3 :: nil) ((B :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HBMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDp3 requis par la preuve de (?)ABCDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDp3M4 : rk(A :: B :: C :: D :: p3 :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABDp3Mtmp : rk(A :: B :: D :: p3 :: nil) <= 3) by (solve_hyps_max HABDp3eq HABDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: B :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p3 :: nil) (C :: A :: B :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: B :: D :: p3 :: nil) ((C :: nil) ++ (A :: B :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: B :: D :: p3 :: nil) (nil) 1 3 0 HCMtmp HABDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp3 requis par la preuve de (?)ABCDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDEp3M5 : rk(A :: B :: C :: D :: E :: p3 :: nil) <= 5).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCDp3Mtmp : rk(A :: B :: C :: D :: p3 :: nil) <= 4) by (solve_hyps_max HABCDp3eq HABCDp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p3 :: nil) (E :: A :: B :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: B :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: D :: p3 :: nil) (nil) 1 4 0 HEMtmp HABCDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp3m5 : rk(A :: B :: C :: D :: E :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEp3M : rk(A :: B :: C :: D :: E :: p3 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEp3m : rk(A :: B :: C :: D :: E :: p3 ::  nil) >= 1) by (solve_hyps_min HABCDEp3eq HABCDEp3m1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCp3 *)
(* dans constructLemma(), requis par LADEp3 *)
(* dans constructLemma(), requis par LACDEp1p3 *)
(* dans constructLemma(), requis par LABCDEp1p3 *)
(* dans la couche 0 *)
Lemma LABCDEp1p3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: p1 :: p3 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ABCDEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp3m3 : rk(A :: C :: D :: E :: p3 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 5 0 2 HABCDEApp3mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3 requis par la preuve de (?)ABCDEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3 requis par la preuve de (?)ABCDEp1p3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HABCDEp1p3M5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) <= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p3 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p3 :: nil) (A :: nil) 2 4 1 HABp1Mtmp HACDEp3Mtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEp1p3M : rk(A :: B :: C :: D :: E :: p1 :: p3 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEp1p3m : rk(A :: B :: C :: D :: E :: p1 :: p3 ::  nil) >= 1) by (solve_hyps_min HABCDEp1p3eq HABCDEp1p3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACDEp1p3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: D :: E :: p1 :: p3 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3 requis par la preuve de (?)ABCDEp1p3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bp1 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACDEp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp3m3 : rk(A :: C :: D :: E :: p3 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 5 0 2 HABCDEApp3mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDEp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ABCDEApEpp1p3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABApEp requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApEp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HABApEpm2 : rk(A :: B :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: B :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEp1p3 requis par la preuve de (?)ACDEp1p3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HACDEp1p3m2 : rk(A :: C :: D :: E :: p1 :: p3 :: nil) >= 2).
{
	assert(HABApEpMtmp : rk(A :: B :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HABApEpeq HABApEpM4).
	assert(HABCDEApEpp1p3mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3eq HABCDEApEpp1p3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p3 :: nil) ((A :: B :: Ap :: Ep :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3mtmp;try rewrite HT2 in HABCDEApEpp1p3mtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3mtmp HAmtmp HABApEpMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp1p3M5 : rk(A :: C :: D :: E :: p1 :: p3 :: nil) <= 5).
{
	assert(Hp1Mtmp : rk(p1 :: nil) <= 1) by (solve_hyps_max Hp1eq Hp1M1).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p1 :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p3 :: nil) (p1 :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p1 :: A :: C :: D :: E :: p3 :: nil) ((p1 :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p1 :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 1 4 0 Hp1Mtmp HACDEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : B :: p1 ::   de rang : 1 et 2 *)
assert(HACDEp1p3m4 : rk(A :: C :: D :: E :: p1 :: p3 :: nil) >= 4).
{
	assert(HBp1Mtmp : rk(B :: p1 :: nil) <= 2) by (solve_hyps_max HBp1eq HBp1M2).
	assert(HABCDEp1p3mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3eq HABCDEp1p3m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: nil) (B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: nil) ((B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3mtmp;try rewrite HT2 in HABCDEp1p3mtmp.
	assert(HT := rule_4 (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3mtmp Hp1mtmp HBp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 ::  de rang :  5 et 5 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp1p3m5 : rk(A :: C :: D :: E :: p1 :: p3 :: nil) >= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1p3eq : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) = 5) by (apply LABCDEp1p3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1p3mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3eq HABCDEp1p3m5).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3mtmp;try rewrite HT2 in HABCDEp1p3mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: nil) (A :: p1 :: nil) 5 2 2 HABCDEp1p3mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

assert(HACDEp1p3M : rk(A :: C :: D :: E :: p1 :: p3 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HACDEp1p3m : rk(A :: C :: D :: E :: p1 :: p3 ::  nil) >= 1) by (solve_hyps_min HACDEp1p3eq HACDEp1p3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LADEp3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: D :: E :: p3 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEApp3M5 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: D :: E :: p3 :: nil) ((Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 1 4 0 HApMtmp HACDEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEApp3m4 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: nil) 5 1 2 HABCDEApp3mtmp HApmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEp3M3 : rk(A :: D :: E :: p3 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: nil) (E :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: D :: p3 :: nil) ((E :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HEMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: p3 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HADEp3m2 : rk(A :: D :: E :: p3 :: nil) >= 2).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HACDEApp3mtmp : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4) by (solve_hyps_min HACDEApp3eq HACDEApp3m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: D :: E :: p3 :: nil) ((C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApp3mtmp;try rewrite HT2 in HACDEApp3mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (nil) 4 0 2 HACDEApp3mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -1 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p3 ::  de rang :  5 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HADEp3m3 : rk(A :: D :: E :: p3 :: nil) >= 3).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HACDEp1p3eq : rk(A :: C :: D :: E :: p1 :: p3 :: nil) = 5) by (apply LACDEp1p3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEp1p3mtmp : rk(A :: C :: D :: E :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HACDEp1p3eq HACDEp1p3m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: p1 :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p3 :: nil) (C :: p1 :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: D :: E :: p3 :: nil) ((C :: p1 :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p3mtmp;try rewrite HT2 in HACDEp1p3mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: D :: E :: p3 :: nil) (nil) 5 0 2 HACDEp1p3mtmp Hmtmp HCp1Mtmp Hincl); apply HT.
}

assert(HADEp3M : rk(A :: D :: E :: p3 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HADEp3eq HADEp3M4).
assert(HADEp3m : rk(A :: D :: E :: p3 ::  nil) >= 1) by (solve_hyps_min HADEp3eq HADEp3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCp3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(B :: C :: p3 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCp3 requis par la preuve de (?)BCp3 pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)BCp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CEp3 requis par la preuve de (?)ABCEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ABCDEApEpp1p3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp1p3m2 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp1p3mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3eq HABCDEApEpp1p3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3mtmp;try rewrite HT2 in HABCDEApEpp1p3mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HABCEp1p3M5 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) <= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HCEp3Mtmp : rk(C :: E :: p3 :: nil) <= 3) by (solve_hyps_max HCEp3eq HCEp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: p1 :: nil) (C :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: nil) (A :: B :: p1 :: C :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: C :: E :: p3 :: nil) ((A :: B :: p1 :: nil) ++ (C :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (C :: E :: p3 :: nil) (nil) 2 3 0 HABp1Mtmp HCEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp1p3m3 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp1p3m4 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p3eq : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) = 5) by (apply LABCDEp1p3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1p3mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3eq HABCDEp1p3m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: nil) (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3mtmp;try rewrite HT2 in HABCDEp1p3mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCp3 requis par la preuve de (?)BCp3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p1 :: p3 ::  de rang :  4 et 5 	 AiB : B ::  de rang :  1 et 1 	 A : A :: B :: E :: p1 ::   de rang : 3 et 3 *)
assert(HBCp3m2 : rk(B :: C :: p3 :: nil) >= 2).
{
	assert(HABEp1eq : rk(A :: B :: E :: p1 :: nil) = 3) by (apply LABEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABCEp1p3mtmp : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 4) by (solve_hyps_min HABCEp1p3eq HABCEp1p3m4).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: nil) (A :: B :: E :: p1 :: B :: C :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: E :: p1 :: B :: C :: p3 :: nil) ((A :: B :: E :: p1 :: nil) ++ (B :: C :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp1p3mtmp;try rewrite HT2 in HABCEp1p3mtmp.
	assert(HT := rule_4 (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: nil) (B :: nil) 4 1 3 HABCEp1p3mtmp HBmtmp HABEp1Mtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HBCp3m3 : rk(B :: C :: p3 :: nil) >= 3).
{
	assert(HADEp3eq : rk(A :: D :: E :: p3 :: nil) = 3) by (apply LADEp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEp3Mtmp : rk(A :: D :: E :: p3 :: nil) <= 3) by (solve_hyps_max HADEp3eq HADEp3M3).
	assert(HABCDEp3eq : rk(A :: B :: C :: D :: E :: p3 :: nil) = 5) by (apply LABCDEp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp3mtmp : rk(A :: B :: C :: D :: E :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp3eq HABCDEp3m5).
	assert(Hp3mtmp : rk(p3 :: nil) >= 1) by (solve_hyps_min Hp3eq Hp3m1).
	assert(Hincl : incl (p3 :: nil) (list_inter (B :: C :: p3 :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p3 :: nil) (B :: C :: p3 :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: p3 :: A :: D :: E :: p3 :: nil) ((B :: C :: p3 :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp3mtmp;try rewrite HT2 in HABCDEp3mtmp.
	assert(HT := rule_2 (B :: C :: p3 :: nil) (A :: D :: E :: p3 :: nil) (p3 :: nil) 5 1 3 HABCDEp3mtmp Hp3mtmp HADEp3Mtmp Hincl);apply HT.
}

assert(HBCp3M : rk(B :: C :: p3 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HBCp3eq HBCp3M3).
assert(HBCp3m : rk(B :: C :: p3 ::  nil) >= 1) by (solve_hyps_min HBCp3eq HBCp3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCp3 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: p3 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCp3 requis par la preuve de (?)ABCp3 pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCDp3 requis par la preuve de (?)ABCp3 pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCDp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCDp3 requis par la preuve de (?)ABCDp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCDApp3 requis par la preuve de (?)ABCDp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCDApp3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEApp3M5 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: D :: E :: p3 :: nil) ((Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 1 4 0 HApMtmp HACDEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEApp3m4 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: nil) 5 1 2 HABCDEApp3mtmp HApmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEp3M3 : rk(A :: D :: E :: p3 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: nil) (E :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: D :: p3 :: nil) ((E :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HEMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: p3 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HADEp3m2 : rk(A :: D :: E :: p3 :: nil) >= 2).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HACDEApp3mtmp : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4) by (solve_hyps_min HACDEApp3eq HACDEApp3m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: D :: E :: p3 :: nil) ((C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApp3mtmp;try rewrite HT2 in HACDEApp3mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (nil) 4 0 2 HACDEApp3mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDE requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: D :: E ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABDEApBpCpDpEpm2 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABDEmtmp : rk(A :: B :: D :: E :: nil) >= 1) by (solve_hyps_min HABDEeq HABDEm1).
	assert(Hincl : incl (A :: B :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: D :: E :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABDEmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApBpCpDpEpm5 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HABCApm2 : rk(A :: B :: C :: Ap :: nil) >= 2).
{
	assert(HABDEApBpCpDpEpMtmp : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABDEApBpCpDpEpeq HABDEApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABDEApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABCApm3 : rk(A :: B :: C :: Ap :: nil) >= 3).
{
	assert(HADEp3Mtmp : rk(A :: D :: E :: p3 :: nil) <= 3) by (solve_hyps_max HADEp3eq HADEp3M3).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (A :: nil) 5 1 3 HABCDEApp3mtmp HAmtmp HADEp3Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCDApp3 requis par la preuve de (?)ABCDApp3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDApp3 requis par la preuve de (?)ABCDApp3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDp3 requis par la preuve de (?)ABCDApp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp3 requis par la preuve de (?)ABCDp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp3 requis par la preuve de (?)ABDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp3M3 : rk(A :: B :: D :: p3 :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p3 :: nil) (B :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: D :: p3 :: nil) ((B :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HBMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDp3 requis par la preuve de (?)ABCDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDp3M4 : rk(A :: B :: C :: D :: p3 :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABDp3Mtmp : rk(A :: B :: D :: p3 :: nil) <= 3) by (solve_hyps_max HABDp3eq HABDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: B :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p3 :: nil) (C :: A :: B :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: B :: D :: p3 :: nil) ((C :: nil) ++ (A :: B :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: B :: D :: p3 :: nil) (nil) 1 3 0 HCMtmp HABDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDApp3 requis par la preuve de (?)ABCDApp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDApp3M5 : rk(A :: B :: C :: D :: Ap :: p3 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABCDp3Mtmp : rk(A :: B :: C :: D :: p3 :: nil) <= 4) by (solve_hyps_max HABCDp3eq HABCDp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: Ap :: p3 :: nil) (Ap :: A :: B :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: C :: D :: p3 :: nil) ((Ap :: nil) ++ (A :: B :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: C :: D :: p3 :: nil) (nil) 1 4 0 HApMtmp HABCDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCDApp3m2 : rk(A :: B :: C :: D :: Ap :: p3 :: nil) >= 2).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: D :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: D :: Ap :: p3 :: nil) 2 2 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCDApp3m3 : rk(A :: B :: C :: D :: Ap :: p3 :: nil) >= 3).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HABCApeq HABCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: D :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: D :: Ap :: p3 :: nil) 3 3 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABCDp3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: Ap :: p3 ::  de rang :  3 et 5 	 AiB : D ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABCDp3m2 : rk(A :: B :: C :: D :: p3 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABCDApp3mtmp : rk(A :: B :: C :: D :: Ap :: p3 :: nil) >= 3) by (solve_hyps_min HABCDApp3eq HABCDApp3m3).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (D :: Ap :: nil) (A :: B :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: Ap :: p3 :: nil) (D :: Ap :: A :: B :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: C :: D :: p3 :: nil) ((D :: Ap :: nil) ++ (A :: B :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDApp3mtmp;try rewrite HT2 in HABCDApp3mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: C :: D :: p3 :: nil) (D :: nil) 3 1 2 HABCDApp3mtmp HDmtmp HDApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCDp3m3 : rk(A :: B :: C :: D :: p3 :: nil) >= 3).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (E :: Ap :: A :: B :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: D :: p3 :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: D :: p3 :: nil) (nil) 5 0 2 HABCDEApp3mtmp Hmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCp3 requis par la preuve de (?)ABCp3 pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)ABCp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CEp3 requis par la preuve de (?)ABCEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3 requis par la preuve de (?)ABCDEApEpp1p3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp1p3 requis par la preuve de (?)ABCEp1p3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp1p3m2 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp1p3mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3eq HABCDEApEpp1p3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3mtmp;try rewrite HT2 in HABCDEApEpp1p3mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HABCEp1p3M5 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) <= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HCEp3Mtmp : rk(C :: E :: p3 :: nil) <= 3) by (solve_hyps_max HCEp3eq HCEp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: p1 :: nil) (C :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: nil) (A :: B :: p1 :: C :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: C :: E :: p3 :: nil) ((A :: B :: p1 :: nil) ++ (C :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (C :: E :: p3 :: nil) (nil) 2 3 0 HABp1Mtmp HCEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp1p3m3 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 ::  de rang :  5 et 5 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp1p3m4 : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p3eq : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) = 5) by (apply LABCDEp1p3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp1p3mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3eq HABCDEp1p3m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: nil) (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3mtmp;try rewrite HT2 in HABCDEp1p3mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp3 requis par la preuve de (?)ABCp3 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p1 :: p3 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: p1 ::   de rang : 2 et 2 *)
assert(HABCp3m2 : rk(A :: B :: C :: p3 :: nil) >= 2).
{
	assert(HEp1eq : rk(E :: p1 :: nil) = 2) by (apply LEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HEp1Mtmp : rk(E :: p1 :: nil) <= 2) by (solve_hyps_max HEp1eq HEp1M2).
	assert(HABCEp1p3mtmp : rk(A :: B :: C :: E :: p1 :: p3 :: nil) >= 4) by (solve_hyps_min HABCEp1p3eq HABCEp1p3m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: p1 :: nil) (A :: B :: C :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: nil) (E :: p1 :: A :: B :: C :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: p1 :: A :: B :: C :: p3 :: nil) ((E :: p1 :: nil) ++ (A :: B :: C :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp1p3mtmp;try rewrite HT2 in HABCEp1p3mtmp.
	assert(HT := rule_4 (E :: p1 :: nil) (A :: B :: C :: p3 :: nil) (nil) 4 0 2 HABCEp1p3mtmp Hmtmp HEp1Mtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et -4*)
assert(HABCp3m3 : rk(A :: B :: C :: p3 :: nil) >= 3).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HABCDp3mtmp : rk(A :: B :: C :: D :: p3 :: nil) >= 3) by (solve_hyps_min HABCDp3eq HABCDp3m3).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: B :: C :: p3 :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: p3 :: nil) (A :: B :: C :: p3 :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: p3 :: A :: D :: p3 :: nil) ((A :: B :: C :: p3 :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDp3mtmp;try rewrite HT2 in HABCDp3mtmp.
	assert(HT := rule_2 (A :: B :: C :: p3 :: nil) (A :: D :: p3 :: nil) (A :: p3 :: nil) 3 2 2 HABCDp3mtmp HAp3mtmp HADp3Mtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HABCp3m4 : rk(A :: B :: C :: p3 :: nil) >= 4).
{
	assert(HADEp3eq : rk(A :: D :: E :: p3 :: nil) = 3) by (apply LADEp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEp3Mtmp : rk(A :: D :: E :: p3 :: nil) <= 3) by (solve_hyps_max HADEp3eq HADEp3M3).
	assert(HABCDEp3eq : rk(A :: B :: C :: D :: E :: p3 :: nil) = 5) by (apply LABCDEp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEp3mtmp : rk(A :: B :: C :: D :: E :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEp3eq HABCDEp3m5).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: B :: C :: p3 :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p3 :: nil) (A :: B :: C :: p3 :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: p3 :: A :: D :: E :: p3 :: nil) ((A :: B :: C :: p3 :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp3mtmp;try rewrite HT2 in HABCDEp3mtmp.
	assert(HT := rule_2 (A :: B :: C :: p3 :: nil) (A :: D :: E :: p3 :: nil) (A :: p3 :: nil) 5 2 3 HABCDEp3mtmp HAp3mtmp HADEp3Mtmp Hincl);apply HT.
}

assert(HABCp3M : rk(A :: B :: C :: p3 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HABCp3eq HABCp3M4).
assert(HABCp3m : rk(A :: B :: C :: p3 ::  nil) >= 1) by (solve_hyps_min HABCp3eq HABCp3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCp1p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: p1 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCp1p5 requis par la preuve de (?)ABCp1p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCp1p5 requis par la preuve de (?)ABCp1p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp1p5 requis par la preuve de (?)ABCp1p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCp5 requis par la preuve de (?)ABCp1p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp5 requis par la preuve de (?)ABCDEApp5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp5m5 : rk(A :: B :: C :: D :: E :: Ap :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEApp3M5 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: D :: E :: p3 :: nil) ((Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 1 4 0 HApMtmp HACDEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEApp3m4 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: nil) 5 1 2 HABCDEApp3mtmp HApmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEp3M3 : rk(A :: D :: E :: p3 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: nil) (E :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: D :: p3 :: nil) ((E :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HEMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: p3 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HADEp3m2 : rk(A :: D :: E :: p3 :: nil) >= 2).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HACDEApp3mtmp : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4) by (solve_hyps_min HACDEApp3eq HACDEApp3m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: D :: E :: p3 :: nil) ((C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApp3mtmp;try rewrite HT2 in HACDEApp3mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (nil) 4 0 2 HACDEApp3mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDE requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: D :: E ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABDEApBpCpDpEpm2 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABDEmtmp : rk(A :: B :: D :: E :: nil) >= 1) by (solve_hyps_min HABDEeq HABDEm1).
	assert(Hincl : incl (A :: B :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: D :: E :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABDEmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApBpCpDpEpm5 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HABCApm2 : rk(A :: B :: C :: Ap :: nil) >= 2).
{
	assert(HABDEApBpCpDpEpMtmp : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABDEApBpCpDpEpeq HABDEApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABDEApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABCApm3 : rk(A :: B :: C :: Ap :: nil) >= 3).
{
	assert(HADEp3Mtmp : rk(A :: D :: E :: p3 :: nil) <= 3) by (solve_hyps_max HADEp3eq HADEp3M3).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (A :: nil) 5 1 3 HABCDEApp3mtmp HAmtmp HADEp3Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCEp5 requis par la preuve de (?)ABCEApp5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCp5 requis par la preuve de (?)ABCEp5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp5 requis par la preuve de (?)ABCp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCp5M3 : rk(A :: B :: C :: p5 :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p5 :: nil) (A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: p5 :: nil) ((A :: nil) ++ (B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (B :: C :: p5 :: nil) (nil) 1 2 0 HAMtmp HBCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCEp5 requis par la preuve de (?)ABCEp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCEp5M4 : rk(A :: B :: C :: E :: p5 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCp5Mtmp : rk(A :: B :: C :: p5 :: nil) <= 3) by (solve_hyps_max HABCp5eq HABCp5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p5 :: nil) (E :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: p5 :: nil) ((E :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: p5 :: nil) (nil) 1 3 0 HEMtmp HABCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCEApp5M5 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABCEp5Mtmp : rk(A :: B :: C :: E :: p5 :: nil) <= 4) by (solve_hyps_max HABCEp5eq HABCEp5M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: C :: E :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: p5 :: nil) (Ap :: A :: B :: C :: E :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: C :: E :: p5 :: nil) ((Ap :: nil) ++ (A :: B :: C :: E :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: C :: E :: p5 :: nil) (nil) 1 4 0 HApMtmp HABCEp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCEApp5m2 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 2).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) 2 2 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCEApp5m3 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 3).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HABCApeq HABCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) 3 3 HABCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p5 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABCEApp5m4 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 4).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABCDEApp5mtmp : rk(A :: B :: C :: D :: E :: Ap :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApp5eq HABCDEApp5m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p5 :: nil) (D :: Ap :: A :: B :: C :: E :: Ap :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: C :: E :: Ap :: p5 :: nil) ((D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp5mtmp;try rewrite HT2 in HABCDEApp5mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) (Ap :: nil) 5 1 2 HABCDEApp5mtmp HApmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCp5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: E :: Ap :: p5 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCp5m2 : rk(A :: B :: C :: p5 :: nil) >= 2).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCEApp5mtmp : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 4) by (solve_hyps_min HABCEApp5eq HABCEApp5m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: p5 :: nil) (E :: Ap :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: p5 :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEApp5mtmp;try rewrite HT2 in HABCEApp5mtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: p5 :: nil) (nil) 4 0 2 HABCEApp5mtmp Hmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCp1p5 requis par la preuve de (?)ABCp1p5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCp1p5M4 : rk(A :: B :: C :: p1 :: p5 :: nil) <= 4).
{
	assert(Hp1Mtmp : rk(p1 :: nil) <= 1) by (solve_hyps_max Hp1eq Hp1M1).
	assert(HABCp5Mtmp : rk(A :: B :: C :: p5 :: nil) <= 3) by (solve_hyps_max HABCp5eq HABCp5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p1 :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: p5 :: nil) (p1 :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p1 :: A :: B :: C :: p5 :: nil) ((p1 :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p1 :: nil) (A :: B :: C :: p5 :: nil) (nil) 1 3 0 Hp1Mtmp HABCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCp1p5m2 : rk(A :: B :: C :: p1 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: B :: C :: p1 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: B :: C :: p1 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HABCp1p5M3 : rk(A :: B :: C :: p1 :: p5 :: nil) <= 3).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: p1 :: nil) (B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: p5 :: nil) (A :: B :: p1 :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: B :: C :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (B :: C :: p5 :: nil) (B :: nil) 2 2 1 HABp1Mtmp HBCp5Mtmp HBmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCp1p5m3 : rk(A :: B :: C :: p1 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: p1 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: p1 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

assert(HABCp1p5M : rk(A :: B :: C :: p1 :: p5 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABCp1p5eq HABCp1p5M5).
assert(HABCp1p5m : rk(A :: B :: C :: p1 :: p5 ::  nil) >= 1) by (solve_hyps_min HABCp1p5eq HABCp1p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpp1p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpp1p5 requis par la preuve de (?)ApBpCpDpEpp1p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpp1p5 requis par la preuve de (?)ApBpCpDpEpp1p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpp1p5m5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HApBpCpDpEpp1p5M5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) <= 5).
{
	assert(HApBpCpDpEpp1Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp1eq HApBpCpDpEpp1M5).
	assert(HApBpCpDpEpp5Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp5eq HApBpCpDpEpp5M5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpp1Mtmp HApBpCpDpEpp5Mtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpp1p5M : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpp1p5m : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpp1p5eq HApBpCpDpEpp1p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCp2p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: p2 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCp2p5 requis par la preuve de (?)ABCp2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCp2p5 requis par la preuve de (?)ABCp2p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCp5 requis par la preuve de (?)ABCp2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp5 requis par la preuve de (?)ABCDEApp5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp5m5 : rk(A :: B :: C :: D :: E :: Ap :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp3 requis par la preuve de (?)ABCDEApp3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp3m5 : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p3 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp3 requis par la preuve de (?)ACDp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp3M3 : rk(A :: C :: D :: p3 :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p3 :: nil) (C :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: p3 :: nil) ((C :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HCMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp3 requis par la preuve de (?)ACDEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp3M4 : rk(A :: C :: D :: E :: p3 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp3Mtmp : rk(A :: C :: D :: p3 :: nil) <= 3) by (solve_hyps_max HACDp3eq HACDp3M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p3 :: nil) (E :: A :: C :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p3 :: nil) ((E :: nil) ++ (A :: C :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p3 :: nil) (nil) 1 3 0 HEMtmp HACDp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApp3 requis par la preuve de (?)ACDEApp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEApp3M5 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HACDEp3Mtmp : rk(A :: C :: D :: E :: p3 :: nil) <= 4) by (solve_hyps_max HACDEp3eq HACDEp3M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: A :: C :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: D :: E :: p3 :: nil) ((Ap :: nil) ++ (A :: C :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: D :: E :: p3 :: nil) (nil) 1 4 0 HApMtmp HACDEp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p3 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEApp3m4 : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: Ap :: p3 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: Ap :: p3 :: nil) (Ap :: nil) 5 1 2 HABCDEApp3mtmp HApmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEp3 requis par la preuve de (?)ADEp3 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEp3M3 : rk(A :: D :: E :: p3 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: D :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: nil) (E :: A :: D :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: D :: p3 :: nil) ((E :: nil) ++ (A :: D :: p3 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: D :: p3 :: nil) (nil) 1 2 0 HEMtmp HADp3Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: p3 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HADEp3m2 : rk(A :: D :: E :: p3 :: nil) >= 2).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HACDEApp3mtmp : rk(A :: C :: D :: E :: Ap :: p3 :: nil) >= 4) by (solve_hyps_min HACDEApp3eq HACDEApp3m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: p3 :: nil) (C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: D :: E :: p3 :: nil) ((C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApp3mtmp;try rewrite HT2 in HACDEApp3mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (nil) 4 0 2 HACDEApp3mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDE requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApBpCpDpEp requis par la preuve de (?)ABDEApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: D :: E ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABDEApBpCpDpEpm2 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABDEmtmp : rk(A :: B :: D :: E :: nil) >= 1) by (solve_hyps_min HABDEeq HABDEm1).
	assert(Hincl : incl (A :: B :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: D :: E :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABDEmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApBpCpDpEpm5 : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCAp requis par la preuve de (?)ABCAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HABCApm2 : rk(A :: B :: C :: Ap :: nil) >= 2).
{
	assert(HABDEApBpCpDpEpMtmp : rk(A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABDEApBpCpDpEpeq HABDEApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: B :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABDEApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABCApm3 : rk(A :: B :: C :: Ap :: nil) >= 3).
{
	assert(HADEp3Mtmp : rk(A :: D :: E :: p3 :: nil) <= 3) by (solve_hyps_max HADEp3eq HADEp3M3).
	assert(HABCDEApp3mtmp : rk(A :: B :: C :: D :: E :: Ap :: p3 :: nil) >= 5) by (solve_hyps_min HABCDEApp3eq HABCDEApp3m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p3 :: nil) (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: Ap :: A :: D :: E :: p3 :: nil) ((A :: B :: C :: Ap :: nil) ++ (A :: D :: E :: p3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp3mtmp;try rewrite HT2 in HABCDEApp3mtmp.
	assert(HT := rule_2 (A :: B :: C :: Ap :: nil) (A :: D :: E :: p3 :: nil) (A :: nil) 5 1 3 HABCDEApp3mtmp HAmtmp HADEp3Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCEp5 requis par la preuve de (?)ABCEApp5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCp5 requis par la preuve de (?)ABCEp5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCp5 requis par la preuve de (?)ABCp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCp5M3 : rk(A :: B :: C :: p5 :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p5 :: nil) (A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: p5 :: nil) ((A :: nil) ++ (B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (B :: C :: p5 :: nil) (nil) 1 2 0 HAMtmp HBCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCEp5 requis par la preuve de (?)ABCEp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCEp5M4 : rk(A :: B :: C :: E :: p5 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCp5Mtmp : rk(A :: B :: C :: p5 :: nil) <= 3) by (solve_hyps_max HABCp5eq HABCp5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p5 :: nil) (E :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: p5 :: nil) ((E :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: p5 :: nil) (nil) 1 3 0 HEMtmp HABCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEApp5 requis par la preuve de (?)ABCEApp5 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCEApp5M5 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABCEp5Mtmp : rk(A :: B :: C :: E :: p5 :: nil) <= 4) by (solve_hyps_max HABCEp5eq HABCEp5M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: C :: E :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: p5 :: nil) (Ap :: A :: B :: C :: E :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: C :: E :: p5 :: nil) ((Ap :: nil) ++ (A :: B :: C :: E :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: C :: E :: p5 :: nil) (nil) 1 4 0 HApMtmp HABCEp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCEApp5m2 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 2).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) 2 2 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCEApp5m3 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 3).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HABCApeq HABCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) 3 3 HABCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p5 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABCEApp5m4 : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 4).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABCDEApp5mtmp : rk(A :: B :: C :: D :: E :: Ap :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApp5eq HABCDEApp5m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p5 :: nil) (D :: Ap :: A :: B :: C :: E :: Ap :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: C :: E :: Ap :: p5 :: nil) ((D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp5mtmp;try rewrite HT2 in HABCDEApp5mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: p5 :: nil) (Ap :: nil) 5 1 2 HABCDEApp5mtmp HApmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCp5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: E :: Ap :: p5 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCp5m2 : rk(A :: B :: C :: p5 :: nil) >= 2).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCEApp5mtmp : rk(A :: B :: C :: E :: Ap :: p5 :: nil) >= 4) by (solve_hyps_min HABCEApp5eq HABCEApp5m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: p5 :: nil) (E :: Ap :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: p5 :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEApp5mtmp;try rewrite HT2 in HABCEApp5mtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: p5 :: nil) (nil) 4 0 2 HABCEApp5mtmp Hmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCp2p5 requis par la preuve de (?)ABCp2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCEp1p2p5 requis par la preuve de (?)ABCp2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p2p5 requis par la preuve de (?)ABCEp1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p2p5 requis par la preuve de (?)ABCDEp1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p2p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCEp1p2p5 requis par la preuve de (?)ABCEp1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp1p2p5 requis par la preuve de (?)ABCEp1p2p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p2p5 requis par la preuve de (?)ABCEp1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p2p5 requis par la preuve de (?)ABCDEApEpp1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p2p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp1p2p5 requis par la preuve de (?)ABCEp1p2p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp1p2p5m2 : rk(A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp1p2p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p2p5eq HABCDEApEpp1p2p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p5 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p2p5mtmp;try rewrite HT2 in HABCDEApEpp1p2p5mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p2p5mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp1p2p5m3 : rk(A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp1p2p5m4 : rk(A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p2p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2p5eq HABCDEp1p2p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: p5 :: nil) (D :: p1 :: A :: B :: C :: E :: p1 :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2p5mtmp;try rewrite HT2 in HABCDEp1p2p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p2p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCp2p5 requis par la preuve de (?)ABCp2p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p1 :: p2 :: p5 ::  de rang :  4 et 6 	 AiB :  de rang :  0 et 0 	 A : E :: p1 ::   de rang : 2 et 2 *)
assert(HABCp2p5m2 : rk(A :: B :: C :: p2 :: p5 :: nil) >= 2).
{
	assert(HEp1eq : rk(E :: p1 :: nil) = 2) by (apply LEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HEp1Mtmp : rk(E :: p1 :: nil) <= 2) by (solve_hyps_max HEp1eq HEp1M2).
	assert(HABCEp1p2p5mtmp : rk(A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) >= 4) by (solve_hyps_min HABCEp1p2p5eq HABCEp1p2p5m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: p1 :: nil) (A :: B :: C :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p2 :: p5 :: nil) (E :: p1 :: A :: B :: C :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: p1 :: A :: B :: C :: p2 :: p5 :: nil) ((E :: p1 :: nil) ++ (A :: B :: C :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp1p2p5mtmp;try rewrite HT2 in HABCEp1p2p5mtmp.
	assert(HT := rule_4 (E :: p1 :: nil) (A :: B :: C :: p2 :: p5 :: nil) (nil) 4 0 2 HABCEp1p2p5mtmp Hmtmp HEp1Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCp2p5M4 : rk(A :: B :: C :: p2 :: p5 :: nil) <= 4).
{
	assert(Hp2Mtmp : rk(p2 :: nil) <= 1) by (solve_hyps_max Hp2eq Hp2M1).
	assert(HABCp5Mtmp : rk(A :: B :: C :: p5 :: nil) <= 3) by (solve_hyps_max HABCp5eq HABCp5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p2 :: nil) (A :: B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p2 :: p5 :: nil) (p2 :: A :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p2 :: A :: B :: C :: p5 :: nil) ((p2 :: nil) ++ (A :: B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p2 :: nil) (A :: B :: C :: p5 :: nil) (nil) 1 3 0 Hp2Mtmp HABCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCp2p5m3 : rk(A :: B :: C :: p2 :: p5 :: nil) >= 3).
{
	assert(HABp2eq : rk(A :: B :: p2 :: nil) = 3) by (apply LABp2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABp2mtmp : rk(A :: B :: p2 :: nil) >= 3) by (solve_hyps_min HABp2eq HABp2m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: p2 :: nil) (A :: B :: C :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: p2 :: nil) (A :: B :: C :: p2 :: p5 :: nil) 3 3 HABp2mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HABCp2p5M3 : rk(A :: B :: C :: p2 :: p5 :: nil) <= 3).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: C :: p2 :: nil) (B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p2 :: p5 :: nil) (A :: C :: p2 :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: B :: C :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: C :: p2 :: nil) (B :: C :: p5 :: nil) (C :: nil) 2 2 1 HACp2Mtmp HBCp5Mtmp HCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCp2p5M : rk(A :: B :: C :: p2 :: p5 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABCp2p5eq HABCp2p5M5).
assert(HABCp2p5m : rk(A :: B :: C :: p2 :: p5 ::  nil) >= 1) by (solve_hyps_min HABCp2p5eq HABCp2p5m1).
intuition.
Qed.

(* dans constructLemma(), requis par LAp1p2p5 *)
(* dans la couche 0 *)
Lemma LABCp1p2p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: p1 :: p2 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCp1p2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCp1p2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABCp1p2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour Cp2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCp1p2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCp1p2p5 requis par la preuve de (?)ABCp1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCp1p2p5m2 : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HABCp1p2p5M5 : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) <= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HCp2p5Mtmp : rk(C :: p2 :: p5 :: nil) <= 3) by (solve_hyps_max HCp2p5eq HCp2p5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: p1 :: nil) (C :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: p2 :: p5 :: nil) (A :: B :: p1 :: C :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: C :: p2 :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (C :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: nil) (C :: p2 :: p5 :: nil) (nil) 2 3 0 HABp1Mtmp HCp2p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCp1p2p5m3 : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HABCp1p2p5M4 : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) <= 4).
{
	assert(Hp2Mtmp : rk(p2 :: nil) <= 1) by (solve_hyps_max Hp2eq Hp2M1).
	assert(HABCp1p5eq : rk(A :: B :: C :: p1 :: p5 :: nil) = 3) by (apply LABCp1p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCp1p5Mtmp : rk(A :: B :: C :: p1 :: p5 :: nil) <= 3) by (solve_hyps_max HABCp1p5eq HABCp1p5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p2 :: nil) (A :: B :: C :: p1 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: p2 :: p5 :: nil) (p2 :: A :: B :: C :: p1 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p2 :: A :: B :: C :: p1 :: p5 :: nil) ((p2 :: nil) ++ (A :: B :: C :: p1 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p2 :: nil) (A :: B :: C :: p1 :: p5 :: nil) (nil) 1 3 0 Hp2Mtmp HABCp1p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCp1p2p5M3 : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) <= 3).
{
	assert(HABp1p2eq : rk(A :: B :: p1 :: p2 :: nil) = 3) by (apply LABp1p2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABp1p2Mtmp : rk(A :: B :: p1 :: p2 :: nil) <= 3) by (solve_hyps_max HABp1p2eq HABp1p2M3).
	assert(HABCp2p5eq : rk(A :: B :: C :: p2 :: p5 :: nil) = 3) by (apply LABCp2p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCp2p5Mtmp : rk(A :: B :: C :: p2 :: p5 :: nil) <= 3) by (solve_hyps_max HABCp2p5eq HABCp2p5M3).
	assert(HABp2eq : rk(A :: B :: p2 :: nil) = 3) by (apply LABp2 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABp2mtmp : rk(A :: B :: p2 :: nil) >= 3) by (solve_hyps_min HABp2eq HABp2m3).
	assert(Hincl : incl (A :: B :: p2 :: nil) (list_inter (A :: B :: p1 :: p2 :: nil) (A :: B :: C :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: p1 :: p2 :: p5 :: nil) (A :: B :: p1 :: p2 :: A :: B :: C :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: p2 :: A :: B :: C :: p2 :: p5 :: nil) ((A :: B :: p1 :: p2 :: nil) ++ (A :: B :: C :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: p1 :: p2 :: nil) (A :: B :: C :: p2 :: p5 :: nil) (A :: B :: p2 :: nil) 3 3 3 HABp1p2Mtmp HABCp2p5Mtmp HABp2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCp1p2p5M : rk(A :: B :: C :: p1 :: p2 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCp1p2p5m : rk(A :: B :: C :: p1 :: p2 :: p5 ::  nil) >= 1) by (solve_hyps_min HABCp1p2p5eq HABCp1p2p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAp1p2p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: p1 :: p2 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour Ap1p2p5 requis par la preuve de (?)Ap1p2p5 pour la règle 6  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACp1p2p5 requis par la preuve de (?)Ap1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour p1p5 requis par la preuve de (?)ACp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ACp1p2p5 requis par la preuve de (?)ACp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACp1p2p5 requis par la preuve de (?)ACp1p2p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACp1p2p5 requis par la preuve de (?)ACp1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACp1p2p5m2 : rk(A :: C :: p1 :: p2 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACp1p2p5m3 : rk(A :: C :: p1 :: p2 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HACp1p2p5M4 : rk(A :: C :: p1 :: p2 :: p5 :: nil) <= 4).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hp1p5Mtmp : rk(p1 :: p5 :: nil) <= 2) by (solve_hyps_max Hp1p5eq Hp1p5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: C :: p2 :: nil) (p1 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: p1 :: p2 :: p5 :: nil) (A :: C :: p2 :: p1 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: p1 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (p1 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: C :: p2 :: nil) (p1 :: p5 :: nil) (nil) 2 2 0 HACp2Mtmp Hp1p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour Ap1p2p5 requis par la preuve de (?)Ap1p2p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour Ap1p2p5 requis par la preuve de (?)Ap1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAp1p2p5m2 : rk(A :: p1 :: p2 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: p1 :: p2 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: p1 :: p2 :: p5 ::  de rang :  3 et 4 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HAp1p2p5m3 : rk(A :: p1 :: p2 :: p5 :: nil) >= 3).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACp1p2p5mtmp : rk(A :: C :: p1 :: p2 :: p5 :: nil) >= 3) by (solve_hyps_min HACp1p2p5eq HACp1p2p5m3).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: p1 :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: p1 :: p2 :: p5 :: nil) (A :: C :: p2 :: A :: p1 :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: p1 :: p2 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: p1 :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACp1p2p5mtmp;try rewrite HT2 in HACp1p2p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: p1 :: p2 :: p5 :: nil) (A :: p2 :: nil) 3 2 2 HACp1p2p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAp1p2p5M3 : rk(A :: p1 :: p2 :: p5 :: nil) <= 3).
{
	assert(HABCp1p2p5eq : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) = 3) by (apply LABCp1p2p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCp1p2p5Mtmp : rk(A :: B :: C :: p1 :: p2 :: p5 :: nil) <= 3) by (solve_hyps_max HABCp1p2p5eq HABCp1p2p5M3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: p2 :: p5 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: p1 :: p2 :: p5 :: nil) (A :: B :: C :: p1 :: p2 :: p5 :: nil) 3 3 HABCp1p2p5Mtmp Hcomp Hincl);apply HT.
}

assert(HAp1p2p5M : rk(A :: p1 :: p2 :: p5 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HAp1p2p5eq HAp1p2p5M4).
assert(HAp1p2p5m : rk(A :: p1 :: p2 :: p5 ::  nil) >= 1) by (solve_hyps_min HAp1p2p5eq HAp1p2p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpp1p2p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpp1p2p5 requis par la preuve de (?)ApBpCpDpEpp1p2p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpp1p2p5 requis par la preuve de (?)ApBpCpDpEpp1p2p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpp1p2p5m5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpDpEpp1p2p5M5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) <= 5).
{
	assert(HApBpCpDpEpp2Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp2eq HApBpCpDpEpp2M5).
	assert(HApBpCpDpEpp1p5eq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) = 5) by (apply LApBpCpDpEpp1p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HApBpCpDpEpp1p5Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp1p5eq HApBpCpDpEpp1p5M5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: p2 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpp2Mtmp HApBpCpDpEpp1p5Mtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpp1p2p5M : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpp1p2p5m : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpp1p2p5eq HApBpCpDpEpp1p2p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCp3p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(B :: C :: p3 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCp3p5 requis par la preuve de (?)BCp3p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCp3p5 requis par la preuve de (?)BCp3p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCEp1p3p5 requis par la preuve de (?)BCp3p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3p5 requis par la preuve de (?)ABCEp1p3p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3p5 requis par la preuve de (?)ABCDEp1p3p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCEp1p3p5 requis par la preuve de (?)ABCEp1p3p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp1p3p5 requis par la preuve de (?)ABCEp1p3p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3p5 requis par la preuve de (?)ABCEp1p3p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3p5 requis par la preuve de (?)ABCDEApEpp1p3p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp1p3p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp1p3p5 requis par la preuve de (?)ABCEp1p3p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp1p3p5m2 : rk(A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp1p3p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3p5eq HABCDEApEpp1p3p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p5 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3p5mtmp;try rewrite HT2 in HABCDEApEpp1p3p5mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3p5mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp1p3p5m3 : rk(A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp1p3p5m4 : rk(A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p3p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3p5eq HABCDEp1p3p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: p5 :: nil) (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3p5mtmp;try rewrite HT2 in HABCDEp1p3p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCp3p5 requis par la preuve de (?)BCp3p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p1 :: p3 :: p5 ::  de rang :  4 et 6 	 AiB : B ::  de rang :  1 et 1 	 A : A :: B :: E :: p1 ::   de rang : 3 et 3 *)
assert(HBCp3p5m2 : rk(B :: C :: p3 :: p5 :: nil) >= 2).
{
	assert(HABEp1eq : rk(A :: B :: E :: p1 :: nil) = 3) by (apply LABEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABCEp1p3p5mtmp : rk(A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) >= 4) by (solve_hyps_min HABCEp1p3p5eq HABCEp1p3p5m4).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: p5 :: nil) (A :: B :: E :: p1 :: B :: C :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: E :: p1 :: B :: C :: p3 :: p5 :: nil) ((A :: B :: E :: p1 :: nil) ++ (B :: C :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp1p3p5mtmp;try rewrite HT2 in HABCEp1p3p5mtmp.
	assert(HT := rule_4 (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: p5 :: nil) (B :: nil) 4 1 3 HABCEp1p3p5mtmp HBmtmp HABEp1Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCp3p5M3 : rk(B :: C :: p3 :: p5 :: nil) <= 3).
{
	assert(Hp3Mtmp : rk(p3 :: nil) <= 1) by (solve_hyps_max Hp3eq Hp3M1).
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p3 :: nil) (B :: C :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: p3 :: p5 :: nil) (p3 :: B :: C :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p3 :: B :: C :: p5 :: nil) ((p3 :: nil) ++ (B :: C :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p3 :: nil) (B :: C :: p5 :: nil) (nil) 1 2 0 Hp3Mtmp HBCp5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCp3p5m3 : rk(B :: C :: p3 :: p5 :: nil) >= 3).
{
	assert(HBCp3eq : rk(B :: C :: p3 :: nil) = 3) by (apply LBCp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HBCp3mtmp : rk(B :: C :: p3 :: nil) >= 3) by (solve_hyps_min HBCp3eq HBCp3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: p3 :: nil) (B :: C :: p3 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: p3 :: nil) (B :: C :: p3 :: p5 :: nil) 3 3 HBCp3mtmp Hcomp Hincl);apply HT.
}

assert(HBCp3p5M : rk(B :: C :: p3 :: p5 ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HBCp3p5eq HBCp3p5M4).
assert(HBCp3p5m : rk(B :: C :: p3 :: p5 ::  nil) >= 1) by (solve_hyps_min HBCp3p5eq HBCp3p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpp1p2p3p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpp1p2p3p5 requis par la preuve de (?)ApBpCpDpEpp1p2p3p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpp1p2p3p5 requis par la preuve de (?)ApBpCpDpEpp1p2p3p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpp1p2p3p5m5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpDpEpp1p2p3p5M5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) <= 5).
{
	assert(HApBpCpDpEpp3Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp3eq HApBpCpDpEpp3M5).
	assert(HApBpCpDpEpp1p2p5eq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) = 5) by (apply LApBpCpDpEpp1p2p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HApBpCpDpEpp1p2p5Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp1p2p5eq HApBpCpDpEpp1p2p5M5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: p3 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpp3Mtmp HApBpCpDpEpp1p2p5Mtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpp1p2p3p5M : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpp1p2p3p5m : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpp1p2p3p5eq HApBpCpDpEpp1p2p3p5m1).
intuition.
Qed.

(* dans constructLemma(), requis par Lp3p4p5 *)
(* dans constructLemma(), requis par LBCp3p4p5 *)
(* dans la couche 0 *)
Lemma LABCEp3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: E :: p3 :: p4 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp3p4p5 requis par la preuve de (?)ABCDEp3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp3p4p5m5 : rk(A :: B :: C :: D :: E :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ABCDEp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3p4p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp3p4p5 requis par la preuve de (?)ABCDEApEpp3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp3p4p5 requis par la preuve de (?)ABCEp3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp3p4p5m2 : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp3p4p5eq HABCDEApEpp3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p3 :: p4 :: p5 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp3p4p5mtmp;try rewrite HT2 in HABCDEApEpp3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp3p4p5mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp3p4p5m3 : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3p4p5eq HABCDEp1p3p4p5m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3p4p5mtmp;try rewrite HT2 in HABCDEp1p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) (nil) 5 0 2 HABCDEp1p3p4p5mtmp Hmtmp HDp1Mtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp3p4p5m4 : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HABCp3eq : rk(A :: B :: C :: p3 :: nil) = 4) by (apply LABCp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCp3mtmp : rk(A :: B :: C :: p3 :: nil) >= 4) by (solve_hyps_min HABCp3eq HABCp3m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: p3 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: p3 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) 4 4 HABCp3mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HABCEp3p4p5m5 : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HABCDEp3p4p5mtmp : rk(A :: B :: C :: D :: E :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp3p4p5eq HABCDEp3p4p5m5).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp3p4p5mtmp;try rewrite HT2 in HABCDEp3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 5 2 2 HABCDEp3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et 5*)
assert(HABCEp3p4p5M5 : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) <= 5).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HBCp3p5eq : rk(B :: C :: p3 :: p5 :: nil) = 3) by (apply LBCp3p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HBCp3p5Mtmp : rk(B :: C :: p3 :: p5 :: nil) <= 3) by (solve_hyps_max HBCp3p5eq HBCp3p5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: E :: p4 :: nil) (B :: C :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: B :: C :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: B :: C :: p3 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (B :: C :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: E :: p4 :: nil) (B :: C :: p3 :: p5 :: nil) (nil) 2 3 0 HAEp4Mtmp HBCp3p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCEp3p4p5M : rk(A :: B :: C :: E :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCEp3p4p5m : rk(A :: B :: C :: E :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HABCEp3p4p5eq HABCEp3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCp3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(B :: C :: p3 :: p4 :: p5 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCp3p4p5 requis par la preuve de (?)BCp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour BCp3p4p5 requis par la preuve de (?)BCp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour BCp3p4p5 requis par la preuve de (?)BCp3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCEp1p3p4p5 requis par la preuve de (?)BCp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ABCDEp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3p4p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCEp1p3p4p5 requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEp1p3p4p5 requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3p4p5 requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3p4p5 requis par la preuve de (?)ABCDEApEpp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADApEp requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ADAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADApEp requis par la preuve de (?)ADApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: D :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HADApEpm2 : rk(A :: D :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: D :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: D :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: D :: Ap :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEp1p3p4p5 requis par la preuve de (?)ABCEp1p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HABCEp1p3p4p5m2 : rk(A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HADApEpMtmp : rk(A :: D :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HADApEpeq HADApEpM4).
	assert(HABCDEApEpp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3p4p5eq HABCDEApEpp1p3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: Ep :: A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((A :: D :: Ap :: Ep :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3p4p5mtmp;try rewrite HT2 in HABCDEApEpp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: Ap :: Ep :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3p4p5mtmp HAmtmp HADApEpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEp1p3p4p5m3 : rk(A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HABCEp1p3p4p5m4 : rk(A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HABCDEp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3p4p5eq HABCDEp1p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3p4p5mtmp;try rewrite HT2 in HABCDEp1p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3p4p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCp3p4p5 requis par la preuve de (?)BCp3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : B ::  de rang :  1 et 1 	 A : A :: B :: E :: p1 ::   de rang : 3 et 3 *)
assert(HBCp3p4p5m2 : rk(B :: C :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HABEp1eq : rk(A :: B :: E :: p1 :: nil) = 3) by (apply LABEp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABCEp1p3p4p5mtmp : rk(A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HABCEp1p3p4p5eq HABCEp1p3p4p5m4).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: B :: E :: p1 :: B :: C :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: E :: p1 :: B :: C :: p3 :: p4 :: p5 :: nil) ((A :: B :: E :: p1 :: nil) ++ (B :: C :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp1p3p4p5mtmp;try rewrite HT2 in HABCEp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: E :: p1 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil) (B :: nil) 4 1 3 HABCEp1p3p4p5mtmp HBmtmp HABEp1Mtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCp3p4p5m3 : rk(B :: C :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HBCp3eq : rk(B :: C :: p3 :: nil) = 3) by (apply LBCp3 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HBCp3mtmp : rk(B :: C :: p3 :: nil) >= 3) by (solve_hyps_min HBCp3eq HBCp3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: p3 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: p3 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil) 3 3 HBCp3mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HBCp3p4p5M4 : rk(B :: C :: p3 :: p4 :: p5 :: nil) <= 4).
{
	assert(Hp4Mtmp : rk(p4 :: nil) <= 1) by (solve_hyps_max Hp4eq Hp4M1).
	assert(HBCp3p5eq : rk(B :: C :: p3 :: p5 :: nil) = 3) by (apply LBCp3p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HBCp3p5Mtmp : rk(B :: C :: p3 :: p5 :: nil) <= 3) by (solve_hyps_max HBCp3p5eq HBCp3p5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (p4 :: nil) (B :: C :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: p3 :: p4 :: p5 :: nil) (p4 :: B :: C :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (p4 :: B :: C :: p3 :: p5 :: nil) ((p4 :: nil) ++ (B :: C :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (p4 :: nil) (B :: C :: p3 :: p5 :: nil) (nil) 1 3 0 Hp4Mtmp HBCp3p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: E :: p3 :: p4 :: p5 ::  de rang :  5 et 5 	 AiB : p4 ::  de rang :  1 et 1 	 A : A :: E :: p4 ::   de rang : 2 et 2 *)
assert(HBCp3p4p5m4 : rk(B :: C :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HABCEp3p4p5eq : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) = 5) by (apply LABCEp3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCEp3p4p5mtmp : rk(A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCEp3p4p5eq HABCEp3p4p5m5).
	assert(Hp4mtmp : rk(p4 :: nil) >= 1) by (solve_hyps_min Hp4eq Hp4m1).
	assert(Hincl : incl (p4 :: nil) (list_inter (A :: E :: p4 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: B :: C :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: B :: C :: p3 :: p4 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (B :: C :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEp3p4p5mtmp;try rewrite HT2 in HABCEp3p4p5mtmp.
	assert(HT := rule_4 (A :: E :: p4 :: nil) (B :: C :: p3 :: p4 :: p5 :: nil) (p4 :: nil) 5 1 2 HABCEp3p4p5mtmp Hp4mtmp HAEp4Mtmp Hincl); apply HT.
}

assert(HBCp3p4p5M : rk(B :: C :: p3 :: p4 :: p5 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HBCp3p4p5eq HBCp3p4p5M5).
assert(HBCp3p4p5m : rk(B :: C :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HBCp3p4p5eq HBCp3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lp3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(p3 :: p4 :: p5 ::  nil) = 3.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour p3p4p5 requis par la preuve de (?)p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour AEp3p4p5 requis par la preuve de (?)p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour p3p5 requis par la preuve de (?)AEp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AEp3p4p5 requis par la preuve de (?)AEp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ADEp3p4p5 requis par la preuve de (?)AEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour Ep4p5 requis par la preuve de (?)ADEp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ADEp3p4p5 requis par la preuve de (?)ADEp3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ACDEp1p3p4p5 requis par la preuve de (?)ADEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p3p4p5 requis par la preuve de (?)ABCDEp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p3p4p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDEp1p3p4p5 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bp1 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDEp1p3p4p5 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p3p4p5 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p3p4p5 requis par la preuve de (?)ABCDEApEpp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABApEp requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApEp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HABApEpm2 : rk(A :: B :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: B :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEp1p3p4p5 requis par la preuve de (?)ACDEp1p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HACDEp1p3p4p5m2 : rk(A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HABApEpMtmp : rk(A :: B :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HABApEpeq HABApEpM4).
	assert(HABCDEApEpp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p3p4p5eq HABCDEApEpp1p3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p3 :: p4 :: p5 :: nil) (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((A :: B :: Ap :: Ep :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p3p4p5mtmp;try rewrite HT2 in HABCDEApEpp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p3p4p5mtmp HAmtmp HABApEpMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : B :: p1 ::   de rang : 1 et 2 *)
assert(HACDEp1p3p4p5m4 : rk(A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HBp1Mtmp : rk(B :: p1 :: nil) <= 2) by (solve_hyps_max HBp1eq HBp1M2).
	assert(HABCDEp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3p4p5eq HABCDEp1p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3p4p5mtmp;try rewrite HT2 in HABCDEp1p3p4p5mtmp.
	assert(HT := rule_4 (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p3p4p5mtmp Hp1mtmp HBp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp1p3p4p5m5 : rk(A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p3p4p5eq HABCDEp1p3p4p5m5).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p3p4p5mtmp;try rewrite HT2 in HABCDEp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: nil) 5 2 2 HABCDEp1p3p4p5mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADEp3p4p5 requis par la preuve de (?)ADEp3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: C :: p1 ::   de rang : 3 et 3 *)
assert(HADEp3p4p5m3 : rk(A :: D :: E :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1Mtmp : rk(A :: C :: p1 :: nil) <= 3) by (solve_hyps_max HACp1eq HACp1M3).
	assert(HACDEp1p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p3p4p5eq HACDEp1p3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: p1 :: nil) (A :: D :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: C :: p1 :: A :: D :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p1 :: A :: D :: E :: p3 :: p4 :: p5 :: nil) ((A :: C :: p1 :: nil) ++ (A :: D :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p3p4p5mtmp;try rewrite HT2 in HACDEp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p1 :: nil) (A :: D :: E :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 3 HACDEp1p3p4p5mtmp HAmtmp HACp1Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HADEp3p4p5M5 : rk(A :: D :: E :: p3 :: p4 :: p5 :: nil) <= 5).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HEp4p5Mtmp : rk(E :: p4 :: p5 :: nil) <= 3) by (solve_hyps_max HEp4p5eq HEp4p5M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: D :: p3 :: nil) (E :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: E :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: E :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (E :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: D :: p3 :: nil) (E :: p4 :: p5 :: nil) (nil) 2 3 0 HADp3Mtmp HEp4p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AEp3p4p5 requis par la preuve de (?)AEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ADEp1p3p4p5 requis par la preuve de (?)AEp3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADEp1p3p4p5 requis par la preuve de (?)ADEp1p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADEp1p3p4p5 requis par la preuve de (?)ADEp1p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADEp1p3p4p5m2 : rk(A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HADEp1p3p4p5m4 : rk(A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HACDEp1p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p3p4p5eq HACDEp1p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (C :: p1 :: A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) ((C :: p1 :: nil) ++ (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p3p4p5mtmp;try rewrite HT2 in HACDEp1p3p4p5mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HACDEp1p3p4p5mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AEp3p4p5 requis par la preuve de (?)AEp3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: D :: E :: p1 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: D :: p1 ::   de rang : 3 et 3 *)
assert(HAEp3p4p5m2 : rk(A :: E :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HADp1eq : rk(A :: D :: p1 :: nil) = 3) by (apply LADp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADp1Mtmp : rk(A :: D :: p1 :: nil) <= 3) by (solve_hyps_max HADp1eq HADp1M3).
	assert(HADEp1p3p4p5mtmp : rk(A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HADEp1p3p4p5eq HADEp1p3p4p5m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: p1 :: nil) (A :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: p3 :: p4 :: p5 :: nil) (A :: D :: p1 :: A :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p1 :: A :: E :: p3 :: p4 :: p5 :: nil) ((A :: D :: p1 :: nil) ++ (A :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1p3p4p5mtmp;try rewrite HT2 in HADEp1p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p1 :: nil) (A :: E :: p3 :: p4 :: p5 :: nil) (A :: nil) 4 1 3 HADEp1p3p4p5mtmp HAmtmp HADp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: D :: E :: p3 :: p4 :: p5 ::  de rang :  3 et 5 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HAEp3p4p5m3 : rk(A :: E :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADEp3p4p5mtmp : rk(A :: D :: E :: p3 :: p4 :: p5 :: nil) >= 3) by (solve_hyps_min HADEp3p4p5eq HADEp3p4p5m3).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: E :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: E :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: E :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: E :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp3p4p5mtmp;try rewrite HT2 in HADEp3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: E :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 3 2 2 HADEp3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HAEp3p4p5M4 : rk(A :: E :: p3 :: p4 :: p5 :: nil) <= 4).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(Hp3p5Mtmp : rk(p3 :: p5 :: nil) <= 2) by (solve_hyps_max Hp3p5eq Hp3p5M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: E :: p4 :: nil) (p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: E :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: p3 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: E :: p4 :: nil) (p3 :: p5 :: nil) (nil) 2 2 0 HAEp4Mtmp Hp3p5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour p3p4p5 requis par la preuve de (?)p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: E :: p3 :: p4 :: p5 ::  de rang :  3 et 4 	 AiB : p4 ::  de rang :  1 et 1 	 A : A :: E :: p4 ::   de rang : 2 et 2 *)
assert(Hp3p4p5m2 : rk(p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HAEp3p4p5mtmp : rk(A :: E :: p3 :: p4 :: p5 :: nil) >= 3) by (solve_hyps_min HAEp3p4p5eq HAEp3p4p5m3).
	assert(Hp4mtmp : rk(p4 :: nil) >= 1) by (solve_hyps_min Hp4eq Hp4m1).
	assert(Hincl : incl (p4 :: nil) (list_inter (A :: E :: p4 :: nil) (p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: E :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: p3 :: p4 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAEp3p4p5mtmp;try rewrite HT2 in HAEp3p4p5mtmp.
	assert(HT := rule_4 (A :: E :: p4 :: nil) (p3 :: p4 :: p5 :: nil) (p4 :: nil) 3 1 2 HAEp3p4p5mtmp Hp4mtmp HAEp4Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : B :: C :: p3 :: p4 :: p5 ::  de rang :  4 et 4 	 AiB : p5 ::  de rang :  1 et 1 	 A : B :: C :: p5 ::   de rang : 2 et 2 *)
assert(Hp3p4p5m3 : rk(p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HBCp5Mtmp : rk(B :: C :: p5 :: nil) <= 2) by (solve_hyps_max HBCp5eq HBCp5M2).
	assert(HBCp3p4p5eq : rk(B :: C :: p3 :: p4 :: p5 :: nil) = 4) by (apply LBCp3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HBCp3p4p5mtmp : rk(B :: C :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HBCp3p4p5eq HBCp3p4p5m4).
	assert(Hp5mtmp : rk(p5 :: nil) >= 1) by (solve_hyps_min Hp5eq Hp5m1).
	assert(Hincl : incl (p5 :: nil) (list_inter (B :: C :: p5 :: nil) (p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: p3 :: p4 :: p5 :: nil) (B :: C :: p5 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: p5 :: p3 :: p4 :: p5 :: nil) ((B :: C :: p5 :: nil) ++ (p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCp3p4p5mtmp;try rewrite HT2 in HBCp3p4p5mtmp.
	assert(HT := rule_4 (B :: C :: p5 :: nil) (p3 :: p4 :: p5 :: nil) (p5 :: nil) 4 1 2 HBCp3p4p5mtmp Hp5mtmp HBCp5Mtmp Hincl); apply HT.
}

assert(Hp3p4p5M : rk(p3 :: p4 :: p5 ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max Hp3p4p5eq Hp3p4p5M3).
assert(Hp3p4p5m : rk(p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min Hp3p4p5eq Hp3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour Ap1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p2p3p4p5 requis par la preuve de (?)ABCDEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bp1 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABApEp requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApEp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HABApEpm2 : rk(A :: B :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: B :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HACDEp1p2p3p4p5m2 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HABApEpMtmp : rk(A :: B :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HABApEpeq HABApEpM4).
	assert(HABCDEApEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p2p3p4p5eq HABCDEApEpp1p2p3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: Ap :: Ep :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p2p3p4p5mtmp HAmtmp HABApEpMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : B :: p1 ::   de rang : 1 et 2 *)
assert(HACDEp1p2p3p4p5m4 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HBp1Mtmp : rk(B :: p1 :: nil) <= 2) by (solve_hyps_max HBp1eq HBp1M2).
	assert(HABCDEp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2p3p4p5eq HABCDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p2p3p4p5mtmp Hp1mtmp HBp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp1p2p3p4p5m5 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2p3p4p5eq HABCDEp1p2p3p4p5m5).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: nil) 5 2 2 HABCDEp1p2p3p4p5mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADEp1p2p3p4p5m2 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HADEp1p2p3p4p5m4 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (C :: p1 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((C :: p1 :: nil) ++ (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HACDEp1p2p3p4p5mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HADEp1p2p3p4p5m5 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 5 2 2 HACDEp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACEp1p2p3p4p5m2 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACEp1p2p3p4p5m3 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HACEp1p2p3p4p5m4 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HACDEp1p2p3p4p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAEp1p2p3p4p5m2 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m3 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HADEp1p2p3p4p5mtmp : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HADEp1p2p3p4p5eq HADEp1p2p3p4p5m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1p2p3p4p5mtmp;try rewrite HT2 in HADEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 4 1 2 HADEp1p2p3p4p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m4 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACEp1p2p3p4p5mtmp : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HACEp1p2p3p4p5eq HACEp1p2p3p4p5m4).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACEp1p2p3p4p5mtmp;try rewrite HT2 in HACEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 4 2 2 HACEp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m5 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADEp1p2p3p4p5mtmp : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HADEp1p2p3p4p5eq HADEp1p2p3p4p5m5).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1p2p3p4p5mtmp;try rewrite HT2 in HADEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 5 2 2 HADEp1p2p3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour Ap1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACDp1p2p3p4p5m2 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACDp1p2p3p4p5m3 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACDp1p2p3p4p5m4 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACDp1eq : rk(A :: C :: D :: p1 :: nil) = 4) by (apply LACDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDp1mtmp : rk(A :: C :: D :: p1 :: nil) >= 4) by (solve_hyps_min HACDp1eq HACDp1m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: C :: D :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: D :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 4 4 HACDp1mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADp1p2p3p4p5m2 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HADp1p2p3p4p5m3 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HADp1eq : rk(A :: D :: p1 :: nil) = 3) by (apply LADp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADp1mtmp : rk(A :: D :: p1 :: nil) >= 3) by (solve_hyps_min HADp1eq HADp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HADp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HADp1p2p3p4p5m4 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACDp1p2p3p4p5mtmp : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HACDp1p2p3p4p5eq HACDp1p2p3p4p5m4).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDp1p2p3p4p5mtmp;try rewrite HT2 in HACDp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 4 2 2 HACDp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour Ap1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)ACp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)ACp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACp1p2p3p4p5m2 : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACp1p2p3p4p5m3 : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour Ap1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour Ap1p2p3p4p5 requis par la preuve de (?)Ap1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAp1p2p3p4p5m2 : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  3 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HAp1p2p3p4p5m3 : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACp1p2p3p4p5mtmp : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3) by (solve_hyps_min HACp1p2p3p4p5eq HACp1p2p3p4p5m3).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACp1p2p3p4p5mtmp;try rewrite HT2 in HACp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 3 2 2 HACp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: D :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HAp1p2p3p4p5m4 : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADp1p2p3p4p5mtmp : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HADp1p2p3p4p5eq HADp1p2p3p4p5m4).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADp1p2p3p4p5mtmp;try rewrite HT2 in HADp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 4 2 2 HADp1p2p3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p4 ::  de rang :  2 et 2 	 A : A :: E :: p4 ::   de rang : 2 et 2 *)
assert(HAp1p2p3p4p5m5 : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HAEp1p2p3p4p5mtmp : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HAEp1p2p3p4p5eq HAEp1p2p3p4p5m5).
	assert(HAp4mtmp : rk(A :: p4 :: nil) >= 2) by (solve_hyps_min HAp4eq HAp4m2).
	assert(Hincl : incl (A :: p4 :: nil) (list_inter (A :: E :: p4 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAEp1p2p3p4p5mtmp;try rewrite HT2 in HAEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: E :: p4 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p4 :: nil) 5 2 2 HAEp1p2p3p4p5mtmp HAp4mtmp HAEp4Mtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et -2*)
assert(HAp1p2p3p4p5M5 : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) <= 5).
{
	assert(HAp1p2p5eq : rk(A :: p1 :: p2 :: p5 :: nil) = 3) by (apply LAp1p2p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HAp1p2p5Mtmp : rk(A :: p1 :: p2 :: p5 :: nil) <= 3) by (solve_hyps_max HAp1p2p5eq HAp1p2p5M3).
	assert(Hp3p4p5eq : rk(p3 :: p4 :: p5 :: nil) = 3) by (apply Lp3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(Hp3p4p5Mtmp : rk(p3 :: p4 :: p5 :: nil) <= 3) by (solve_hyps_max Hp3p4p5eq Hp3p4p5M3).
	assert(Hp5mtmp : rk(p5 :: nil) >= 1) by (solve_hyps_min Hp5eq Hp5m1).
	assert(Hincl : incl (p5 :: nil) (list_inter (A :: p1 :: p2 :: p5 :: nil) (p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: p2 :: p5 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: p1 :: p2 :: p5 :: p3 :: p4 :: p5 :: nil) ((A :: p1 :: p2 :: p5 :: nil) ++ (p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: p1 :: p2 :: p5 :: nil) (p3 :: p4 :: p5 :: nil) (p5 :: nil) 3 3 1 HAp1p2p5Mtmp Hp3p4p5Mtmp Hp5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HAp1p2p3p4p5M : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HAp1p2p3p4p5m : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HAp1p2p3p4p5eq HAp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ApBpCpDpEpp1p2p3p4p5 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpp1p2p3p4p5m5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpDpEpp1p2p3p4p5M5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) <= 5).
{
	assert(HApBpCpDpEpp4Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp4eq HApBpCpDpEpp4M5).
	assert(HApBpCpDpEpp1p2p3p5eq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) = 5) by (apply LApBpCpDpEpp1p2p3p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HApBpCpDpEpp1p2p3p5Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp1p2p3p5eq HApBpCpDpEpp1p2p3p5M5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: p4 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpp4Mtmp HApBpCpDpEpp1p2p3p5Mtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpp1p2p3p4p5M : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpp1p2p3p4p5m : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpp1p2p3p4p5eq HApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans constructLemma(), requis par LAApBpCpDpEpp1p2p3p4p5 *)
(* dans constructLemma(), requis par LAEApBpCpDpEpp1p2p3p4p5 *)
(* dans constructLemma(), requis par LADEApBpCpDpEpp1p2p3p4p5 *)
(* dans constructLemma(), requis par LACDEApBpCpDpEpp1p2p3p4p5 *)
(* dans la couche 0 *)
Lemma LABCDEApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpEpp1p2p3p4p5m6 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6).
{
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 6 6 HABCDEApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEApBpCpDpEpp1p2p3p4p5M : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEApBpCpDpEpp1p2p3p4p5m : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACDEApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ACAp pour la règle 2  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACAp requis par la preuve de (?)ACAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HACApm2 : rk(A :: C :: Ap :: nil) >= 2).
{
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((A :: C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (A :: nil) 5 1 4 HABCDEApp1mtmp HAmtmp HABDEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCE requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C :: E ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCEApBpCpDpEpm2 : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCEmtmp : rk(A :: B :: C :: E :: nil) >= 1) by (solve_hyps_min HABCEeq HABCEm1).
	assert(Hincl : incl (A :: B :: C :: E :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: E :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCEmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABCEApBpCpDpEpm5 : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDApm2 : rk(A :: C :: D :: Ap :: nil) >= 2).
{
	assert(HABCEApBpCpDpEpMtmp : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCEApBpCpDpEpeq HABCEApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 2) by (solve_hyps_min HACApeq HACApm2).
	assert(Hincl : incl (A :: C :: Ap :: nil) (list_inter (A :: C :: D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HACApmtmp HABCEApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HACDApm3 : rk(A :: C :: D :: Ap :: nil) >= 3).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: C :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 5 1 3 HABCDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCD requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C :: D ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCDApBpCpDpEpm2 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 1) by (solve_hyps_min HABCDeq HABCDm1).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCDmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCDApBpCpDpEpm5 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABC requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C ::  de rang :  1 et 3 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCApBpCpDpEpm2 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCApBpCpDpEpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 4).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCEApBpCpDpEpmtmp : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HABCEApBpCpDpEpeq HABCEApBpCpDpEpm5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEApBpCpDpEpmtmp;try rewrite HT2 in HABCEApBpCpDpEpmtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 5 1 2 HABCEApBpCpDpEpmtmp HApmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDEApm2 : rk(A :: C :: D :: E :: Ap :: nil) >= 2).
{
	assert(HABCApBpCpDpEpMtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCApBpCpDpEpeq HABCApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 2) by (solve_hyps_min HACApeq HACApm2).
	assert(Hincl : incl (A :: C :: Ap :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HACApmtmp HABCApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDEApm3 : rk(A :: C :: D :: E :: Ap :: nil) >= 3).
{
	assert(HABCDApBpCpDpEpMtmp : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCDApBpCpDpEpeq HABCDApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACDApmtmp : rk(A :: C :: D :: Ap :: nil) >= 3) by (solve_hyps_min HACDApeq HACDApm3).
	assert(Hincl : incl (A :: C :: D :: Ap :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: Ap :: nil) 6 3 6 HABCDEApBpCpDpEpmtmp HACDApmtmp HABCDApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HACDEApm4 : rk(A :: C :: D :: E :: Ap :: nil) >= 4).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: D :: E :: Ap :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: p1 :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil) (A :: nil) 5 1 2 HABCDEApp1mtmp HAmtmp HABp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEAp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEAp requis par la preuve de (?)ABCDEAp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApm5 : rk(A :: B :: C :: D :: E :: Ap :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: C :: D :: E :: Ap ::  de rang :  4 et 5 	 A : A :: B :: C :: D :: E :: Ap ::   de rang : 5 et 6 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m3 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HABCDEApMtmp : rk(A :: B :: C :: D :: E :: Ap :: nil) <= 6) by (solve_hyps_max HABCDEApeq HABCDEApM6).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m5).
	assert(HACDEApmtmp : rk(A :: C :: D :: E :: Ap :: nil) >= 4) by (solve_hyps_min HACDEApeq HACDEApm4).
	assert(Hincl : incl (A :: C :: D :: E :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: C :: D :: E :: Ap :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: C :: D :: E :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: D :: E :: Ap :: nil) 5 4 6 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HACDEApmtmp HABCDEApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : Bp ::  de rang :  1 et 1 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m4 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m5).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (B :: Bp :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (B :: Bp :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((B :: Bp :: nil) ++ (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Bp :: nil) 5 1 2 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HBpmtmp HBBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 6 et 6) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  6 et 6 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m6 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5eq : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 6) by (apply LABCDEApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m6).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: nil) 6 2 2 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

assert(HACDEApBpCpDpEpp1p2p3p4p5M : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HACDEApBpCpDpEpp1p2p3p4p5m : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HACDEApBpCpDpEpp1p2p3p4p5eq HACDEApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LADEApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ADEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ADEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEp1m2 : rk(A :: B :: E :: p1 :: nil) >= 2).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 4 0 2 HABDEApp1mtmp Hmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ACAp pour la règle 2  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEp1m3 : rk(A :: B :: D :: E :: p1 :: nil) >= 3).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 5 0 2 HABCDEApp1mtmp Hmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACAp requis par la preuve de (?)ACAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HACApm2 : rk(A :: C :: Ap :: nil) >= 2).
{
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Ap :: A :: B :: D :: E :: p1 :: nil) ((A :: C :: Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (A :: nil) 5 1 4 HABCDEApp1mtmp HAmtmp HABDEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCE requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEApBpCpDpEp requis par la preuve de (?)ABCEApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C :: E ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCEApBpCpDpEpm2 : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCEmtmp : rk(A :: B :: C :: E :: nil) >= 1) by (solve_hyps_min HABCEeq HABCEm1).
	assert(Hincl : incl (A :: B :: C :: E :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: E :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCEmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABCEApBpCpDpEpm5 : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDAp requis par la preuve de (?)ACDAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDApm2 : rk(A :: C :: D :: Ap :: nil) >= 2).
{
	assert(HABCEApBpCpDpEpMtmp : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCEApBpCpDpEpeq HABCEApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 2) by (solve_hyps_min HACApeq HACApm2).
	assert(Hincl : incl (A :: C :: Ap :: nil) (list_inter (A :: C :: D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: Ap :: A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: Ap :: nil) ++ (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: Ap :: nil) (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HACApmtmp HABCEApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HACDApm3 : rk(A :: C :: D :: Ap :: nil) >= 3).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: C :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 5 1 3 HABCDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EAp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCD requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDApBpCpDpEp requis par la preuve de (?)ABCDApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C :: D ::  de rang :  1 et 4 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCDApBpCpDpEpm2 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 1) by (solve_hyps_min HABCDeq HABCDm1).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCDmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: -4 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCDApBpCpDpEpm5 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 6 1 2 HABCDEApBpCpDpEpmtmp HApmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABC requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCApBpCpDpEp requis par la preuve de (?)ABCApBpCpDpEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: C ::  de rang :  1 et 3 	 A : A :: B :: C :: D :: E ::   de rang : 5 et 5 *)
assert(HABCApBpCpDpEpm2 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 2).
{
	assert(HABCDEMtmp : rk(A :: B :: C :: D :: E :: nil) <= 5) by (solve_hyps_max HABCDEeq HABCDEM5).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: D :: E :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: B :: C :: D :: E :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: nil) 6 1 5 HABCDEApBpCpDpEpmtmp HABCmtmp HABCDEMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : E :: Ap ::   de rang : 1 et 2 *)
assert(HABCApBpCpDpEpm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 4).
{
	assert(HEApMtmp : rk(E :: Ap :: nil) <= 2) by (solve_hyps_max HEApeq HEApM2).
	assert(HABCEApBpCpDpEpmtmp : rk(A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HABCEApBpCpDpEpeq HABCEApBpCpDpEpm5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((E :: Ap :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEApBpCpDpEpmtmp;try rewrite HT2 in HABCEApBpCpDpEpmtmp.
	assert(HT := rule_4 (E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: nil) 5 1 2 HABCEApBpCpDpEpmtmp HApmtmp HEApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEAp requis par la preuve de (?)ACDEAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDEApm2 : rk(A :: C :: D :: E :: Ap :: nil) >= 2).
{
	assert(HABCApBpCpDpEpMtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCApBpCpDpEpeq HABCApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 2) by (solve_hyps_min HACApeq HACApm2).
	assert(Hincl : incl (A :: C :: Ap :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HACApmtmp HABCApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HACDEApm3 : rk(A :: C :: D :: E :: Ap :: nil) >= 3).
{
	assert(HABCDApBpCpDpEpMtmp : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCDApBpCpDpEpeq HABCDApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HACDApmtmp : rk(A :: C :: D :: Ap :: nil) >= 3) by (solve_hyps_min HACDApeq HACDApm3).
	assert(Hincl : incl (A :: C :: D :: Ap :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: C :: D :: Ap :: nil) 6 3 6 HABCDEApBpCpDpEpmtmp HACDApmtmp HABCDApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HACDEApm4 : rk(A :: C :: D :: E :: Ap :: nil) >= 4).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (A :: C :: D :: E :: Ap :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: E :: Ap :: A :: B :: p1 :: nil) ((A :: C :: D :: E :: Ap :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_2 (A :: C :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil) (A :: nil) 5 1 2 HABCDEApp1mtmp HAmtmp HABp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEAp requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEAp requis par la preuve de (?)ABCDEAp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApm5 : rk(A :: B :: C :: D :: E :: Ap :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ACDEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: C :: D :: E :: Ap ::  de rang :  4 et 5 	 A : A :: B :: C :: D :: E :: Ap ::   de rang : 5 et 6 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m3 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HABCDEApMtmp : rk(A :: B :: C :: D :: E :: Ap :: nil) <= 6) by (solve_hyps_max HABCDEApeq HABCDEApM6).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m5).
	assert(HACDEApmtmp : rk(A :: C :: D :: E :: Ap :: nil) >= 4) by (solve_hyps_min HACDEApeq HACDEApm4).
	assert(Hincl : incl (A :: C :: D :: E :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: C :: D :: E :: Ap :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: C :: D :: E :: Ap :: nil) ++ (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: D :: E :: Ap :: nil) 5 4 6 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HACDEApmtmp HABCDEApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : Bp ::  de rang :  1 et 1 	 A : B :: Bp ::   de rang : 1 et 2 *)
assert(HACDEApBpCpDpEpp1p2p3p4p5m4 : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m5).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (B :: Bp :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (B :: Bp :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((B :: Bp :: nil) ++ (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Bp :: nil) 5 1 2 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HBpmtmp HBBpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CBp requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ADEAp requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ADEAp requis par la preuve de (?)ADEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADAp requis par la preuve de (?)ADEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADAp requis par la preuve de (?)ADAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HADApm2 : rk(A :: D :: Ap :: nil) >= 2).
{
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: Ap :: A :: B :: E :: p1 :: nil) ((A :: D :: Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: Ap :: nil) (A :: B :: E :: p1 :: nil) (A :: nil) 4 1 3 HABDEApp1mtmp HAmtmp HABEp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEAp requis par la preuve de (?)ADEAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 5 et 5*)
assert(HADEApm2 : rk(A :: D :: E :: Ap :: nil) >= 2).
{
	assert(HABCDApBpCpDpEpMtmp : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) <= 6) by (solve_hyps_max HABCDApBpCpDpEpeq HABCDApBpCpDpEpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HADApmtmp : rk(A :: D :: Ap :: nil) >= 2) by (solve_hyps_min HADApeq HADApm2).
	assert(Hincl : incl (A :: D :: Ap :: nil) (list_inter (A :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: Ap :: A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) ((A :: D :: E :: Ap :: nil) ++ (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_2 (A :: D :: E :: Ap :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: D :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HADApmtmp HABCDApBpCpDpEpMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HADEApm3 : rk(A :: D :: E :: Ap :: nil) >= 3).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (A :: D :: E :: Ap :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: Ap :: A :: B :: p1 :: nil) ((A :: D :: E :: Ap :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_2 (A :: D :: E :: Ap :: nil) (A :: B :: p1 :: nil) (A :: nil) 4 1 2 HABDEApp1mtmp HAmtmp HABp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)ADEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: D :: E :: Ap ::  de rang :  3 et 4 	 A : A :: B :: C :: D :: E :: Ap ::   de rang : 5 et 6 *)
assert(HADEApBpCpDpEpp1p2p3p4p5m2 : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HABCDEApMtmp : rk(A :: B :: C :: D :: E :: Ap :: nil) <= 6) by (solve_hyps_max HABCDEApeq HABCDEApM6).
	assert(HABCDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApBpCpDpEpp1p2p3p4p5eq HABCDEApBpCpDpEpp1p2p3p4p5m5).
	assert(HADEApmtmp : rk(A :: D :: E :: Ap :: nil) >= 3) by (solve_hyps_min HADEApeq HADEApm3).
	assert(Hincl : incl (A :: D :: E :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: C :: D :: E :: Ap :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: C :: D :: E :: Ap :: nil) ++ (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: E :: Ap :: nil) 5 3 6 HABCDEApBpCpDpEpp1p2p3p4p5mtmp HADEApmtmp HABCDEApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : Bp ::  de rang :  1 et 1 	 A : C :: Bp ::   de rang : 1 et 2 *)
assert(HADEApBpCpDpEpp1p2p3p4p5m3 : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HCBpMtmp : rk(C :: Bp :: nil) <= 2) by (solve_hyps_max HCBpeq HCBpM2).
	assert(HACDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HACDEApBpCpDpEpp1p2p3p4p5eq HACDEApBpCpDpEpp1p2p3p4p5m4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (C :: Bp :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (C :: Bp :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Bp :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((C :: Bp :: nil) ++ (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HACDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (C :: Bp :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Bp :: nil) 4 1 2 HACDEApBpCpDpEpp1p2p3p4p5mtmp HBpmtmp HCBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 6 et 6) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  6 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HADEApBpCpDpEpp1p2p3p4p5m6 : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACDEApBpCpDpEpp1p2p3p4p5eq : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 6) by (apply LACDEApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6) by (solve_hyps_min HACDEApBpCpDpEpp1p2p3p4p5eq HACDEApBpCpDpEpp1p2p3p4p5m6).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HACDEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 6 2 2 HACDEApBpCpDpEpp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

assert(HADEApBpCpDpEpp1p2p3p4p5M : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HADEApBpCpDpEpp1p2p3p4p5m : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HADEApBpCpDpEpp1p2p3p4p5eq HADEApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAEApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour AEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)AEApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour AEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)AEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour AEApEp requis par la preuve de (?)AEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AEAp requis par la preuve de (?)AEApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABEApp1 requis par la preuve de (?)AEAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp1 requis par la preuve de (?)ABCDEApp1 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp1m5 : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p1 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABDp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDp1 requis par la preuve de (?)ABDp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABDp1M3 : rk(A :: B :: D :: p1 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: p1 :: nil) (D :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: B :: p1 :: nil) ((D :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HDMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEp1 requis par la preuve de (?)ABDEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEp1M4 : rk(A :: B :: D :: E :: p1 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABDp1Mtmp : rk(A :: B :: D :: p1 :: nil) <= 3) by (solve_hyps_max HABDp1eq HABDp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: D :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: p1 :: nil) (E :: A :: B :: D :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: D :: p1 :: nil) ((E :: nil) ++ (A :: B :: D :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: D :: p1 :: nil) (nil) 1 3 0 HEMtmp HABDp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABDEApp1 requis par la preuve de (?)ABDEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEApp1M5 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) <= 5).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABDEp1Mtmp : rk(A :: B :: D :: E :: p1 :: nil) <= 4) by (solve_hyps_max HABDEp1eq HABDEp1M4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: D :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: D :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: D :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: D :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: D :: E :: p1 :: nil) (nil) 1 4 0 HApMtmp HABDEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p1 ::  de rang :  5 et 6 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap ::   de rang : 1 et 2 *)
assert(HABDEApp1m4 : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4).
{
	assert(HCApMtmp : rk(C :: Ap :: nil) <= 2) by (solve_hyps_max HCApeq HCApM2).
	assert(HABCDEApp1mtmp : rk(A :: B :: C :: D :: E :: Ap :: p1 :: nil) >= 5) by (solve_hyps_min HABCDEApp1eq HABCDEApp1m5).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p1 :: nil) (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: A :: B :: D :: E :: Ap :: p1 :: nil) ((C :: Ap :: nil) ++ (A :: B :: D :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp1mtmp;try rewrite HT2 in HABCDEApp1mtmp.
	assert(HT := rule_4 (C :: Ap :: nil) (A :: B :: D :: E :: Ap :: p1 :: nil) (Ap :: nil) 5 1 2 HABCDEApp1mtmp HApmtmp HCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DAp requis par la preuve de (?)ABEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEApp1 requis par la preuve de (?)ABEApp1 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABEp1 requis par la preuve de (?)ABEApp1 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABEp1 requis par la preuve de (?)ABEp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABEp1M3 : rk(A :: B :: E :: p1 :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: p1 :: nil) (E :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: p1 :: nil) ((E :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: p1 :: nil) (nil) 1 2 0 HEMtmp HABp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABEApp1 requis par la preuve de (?)ABEApp1 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABEApp1M4 : rk(A :: B :: E :: Ap :: p1 :: nil) <= 4).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HABEp1Mtmp : rk(A :: B :: E :: p1 :: nil) <= 3) by (solve_hyps_max HABEp1eq HABEp1M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: B :: E :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: Ap :: p1 :: nil) (Ap :: A :: B :: E :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: B :: E :: p1 :: nil) ((Ap :: nil) ++ (A :: B :: E :: p1 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: B :: E :: p1 :: nil) (nil) 1 3 0 HApMtmp HABEp1Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: D :: E :: Ap :: p1 ::  de rang :  4 et 5 	 AiB : Ap ::  de rang :  1 et 1 	 A : D :: Ap ::   de rang : 1 et 2 *)
assert(HABEApp1m3 : rk(A :: B :: E :: Ap :: p1 :: nil) >= 3).
{
	assert(HDApMtmp : rk(D :: Ap :: nil) <= 2) by (solve_hyps_max HDApeq HDApM2).
	assert(HABDEApp1mtmp : rk(A :: B :: D :: E :: Ap :: p1 :: nil) >= 4) by (solve_hyps_min HABDEApp1eq HABDEApp1m4).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (D :: Ap :: nil) (A :: B :: E :: Ap :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: Ap :: p1 :: nil) (D :: Ap :: A :: B :: E :: Ap :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: Ap :: A :: B :: E :: Ap :: p1 :: nil) ((D :: Ap :: nil) ++ (A :: B :: E :: Ap :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDEApp1mtmp;try rewrite HT2 in HABDEApp1mtmp.
	assert(HT := rule_4 (D :: Ap :: nil) (A :: B :: E :: Ap :: p1 :: nil) (Ap :: nil) 4 1 2 HABDEApp1mtmp HApmtmp HDApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AEAp requis par la preuve de (?)AEAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HAEApm2 : rk(A :: E :: Ap :: nil) >= 2).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABEApp1mtmp : rk(A :: B :: E :: Ap :: p1 :: nil) >= 3) by (solve_hyps_min HABEApp1eq HABEApp1m3).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: E :: Ap :: nil) (A :: B :: p1 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: Ap :: p1 :: nil) (A :: E :: Ap :: A :: B :: p1 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: Ap :: A :: B :: p1 :: nil) ((A :: E :: Ap :: nil) ++ (A :: B :: p1 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABEApp1mtmp;try rewrite HT2 in HABEApp1mtmp.
	assert(HT := rule_2 (A :: E :: Ap :: nil) (A :: B :: p1 :: nil) (A :: nil) 3 1 2 HABEApp1mtmp HAmtmp HABp1Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)AEApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour AEApEp requis par la preuve de (?)AEApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: E :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HAEApEpm2 : rk(A :: E :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HAEApmtmp : rk(A :: E :: Ap :: nil) >= 2) by (solve_hyps_min HAEApeq HAEApm2).
	assert(Hincl : incl (A :: E :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: E :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: E :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: E :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: E :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: E :: Ap :: Ep :: nil) (A :: E :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HAEApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour AEApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)AEApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HAEApBpCpDpEpp1p2p3p4p5m2 : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAEApEpmtmp : rk(A :: E :: Ap :: Ep :: nil) >= 2) by (solve_hyps_min HAEApEpeq HAEApEpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: E :: Ap :: Ep :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: E :: Ap :: Ep :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAEApEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAEApBpCpDpEpp1p2p3p4p5m5 : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 6 et 6) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  6 et 6 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HAEApBpCpDpEpp1p2p3p4p5m6 : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADEApBpCpDpEpp1p2p3p4p5eq : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 6) by (apply LADEApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6) by (solve_hyps_min HADEApBpCpDpEpp1p2p3p4p5eq HADEApBpCpDpEpp1p2p3p4p5m6).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HADEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 6 2 2 HADEApBpCpDpEpp1p2p3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

assert(HAEApBpCpDpEpp1p2p3p4p5M : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HAEApBpCpDpEpp1p2p3p4p5m : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HAEApBpCpDpEpp1p2p3p4p5eq HAEApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAApBpCpDpEpp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour AApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)AApBpCpDpEpp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour AApBpCpDpEpp1p2p3p4p5 requis par la preuve de (?)AApBpCpDpEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAApBpCpDpEpp1p2p3p4p5m5 : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 6 et 6) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  6 et 6 	 AiB : A :: p4 ::  de rang :  2 et 2 	 A : A :: E :: p4 ::   de rang : 2 et 2 *)
assert(HAApBpCpDpEpp1p2p3p4p5m6 : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HAEApBpCpDpEpp1p2p3p4p5eq : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 6) by (apply LAEApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HAEApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6) by (solve_hyps_min HAEApBpCpDpEpp1p2p3p4p5eq HAEApBpCpDpEpp1p2p3p4p5m6).
	assert(HAp4mtmp : rk(A :: p4 :: nil) >= 2) by (solve_hyps_min HAp4eq HAp4m2).
	assert(Hincl : incl (A :: p4 :: nil) (list_inter (A :: E :: p4 :: nil) (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAEApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HAEApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: E :: p4 :: nil) (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p4 :: nil) 6 2 2 HAEApBpCpDpEpp1p2p3p4p5mtmp HAp4mtmp HAEp4Mtmp Hincl); apply HT.
}

assert(HAApBpCpDpEpp1p2p3p4p5M : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 6) by (apply rk_upper_dim).
assert(HAApBpCpDpEpp1p2p3p4p5m : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min HAApBpCpDpEpp1p2p3p4p5eq HAApBpCpDpEpp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lp1p2p3p4p5 : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> rk(p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour p1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 3  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEp1p2p3p4p5 requis par la preuve de (?)ABCDEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Bp1 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApEpp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApEpp1p2p3p4p5 requis par la preuve de (?)ABCDEApEpp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApEpp1p2p3p4p5m5 : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABApEp requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABAp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApp2 requis par la preuve de (?)ABCDEApp2 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApp2m5 : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: p2 :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ABAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDp2 requis par la preuve de (?)ACDp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDp2M3 : rk(A :: C :: D :: p2 :: nil) <= 3).
{
	assert(HDMtmp : rk(D :: nil) <= 1) by (solve_hyps_max HDeq HDM1).
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (D :: nil) (A :: C :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p2 :: nil) (D :: A :: C :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: A :: C :: p2 :: nil) ((D :: nil) ++ (A :: C :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (D :: nil) (A :: C :: p2 :: nil) (nil) 1 2 0 HDMtmp HACp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEp2 requis par la preuve de (?)ACDEp2 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEp2M4 : rk(A :: C :: D :: E :: p2 :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDp2Mtmp : rk(A :: C :: D :: p2 :: nil) <= 3) by (solve_hyps_max HACDp2eq HACDp2M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p2 :: nil) (E :: A :: C :: D :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: p2 :: nil) ((E :: nil) ++ (A :: C :: D :: p2 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: p2 :: nil) (nil) 1 3 0 HEMtmp HACDp2Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: p2 ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: Ap ::   de rang : 1 et 2 *)
assert(HACDEp2m3 : rk(A :: C :: D :: E :: p2 :: nil) >= 3).
{
	assert(HBApMtmp : rk(B :: Ap :: nil) <= 2) by (solve_hyps_max HBApeq HBApM2).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_4 (B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (nil) 5 0 2 HABCDEApp2mtmp Hmtmp HBApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABAp requis par la preuve de (?)ABAp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABApm2 : rk(A :: B :: Ap :: nil) >= 2).
{
	assert(HACDEp2Mtmp : rk(A :: C :: D :: E :: p2 :: nil) <= 4) by (solve_hyps_max HACDEp2eq HACDEp2M4).
	assert(HABCDEApp2mtmp : rk(A :: B :: C :: D :: E :: Ap :: p2 :: nil) >= 5) by (solve_hyps_min HABCDEApp2eq HABCDEApp2m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: p2 :: nil) (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: D :: E :: p2 :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: D :: E :: p2 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApp2mtmp;try rewrite HT2 in HABCDEApp2mtmp.
	assert(HT := rule_2 (A :: B :: Ap :: nil) (A :: C :: D :: E :: p2 :: nil) (A :: nil) 5 1 4 HABCDEApp2mtmp HAmtmp HACDEp2Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDp requis par la preuve de (?)ABCDEApBpCpDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEApBpCpDpm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApEp requis par la preuve de (?)ABApEp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  de rang :  6 et 6 	 AiB : A :: B :: Ap ::  de rang :  2 et 3 	 A : A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp ::   de rang : 5 et 6 *)
assert(HABApEpm2 : rk(A :: B :: Ap :: Ep :: nil) >= 2).
{
	assert(HABCDEApBpCpDpMtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) <= 6) by (solve_hyps_max HABCDEApBpCpDpeq HABCDEApBpCpDpM6).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 2) by (solve_hyps_min HABApeq HABApm2).
	assert(Hincl : incl (A :: B :: Ap :: nil) (list_inter (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: A :: B :: Ap :: Ep :: nil) ((A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) ++ (A :: B :: Ap :: Ep :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpmtmp;try rewrite HT2 in HABCDEApBpCpDpEpmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: Ap :: Ep :: nil) (A :: B :: Ap :: nil) 6 2 6 HABCDEApBpCpDpEpmtmp HABApmtmp HABCDEApBpCpDpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEp1p2p3p4p5 requis par la preuve de (?)ACDEp1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B :: Ap :: Ep ::   de rang : 2 et 4 *)
assert(HACDEp1p2p3p4p5m2 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HABApEpMtmp : rk(A :: B :: Ap :: Ep :: nil) <= 4) by (solve_hyps_max HABApEpeq HABApEpM4).
	assert(HABCDEApEpp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEApEpp1p2p3p4p5eq HABCDEApEpp1p2p3p4p5m5).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Ep :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: Ap :: Ep :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApEpp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEApEpp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Ep :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: nil) 5 1 4 HABCDEApEpp1p2p3p4p5mtmp HAmtmp HABApEpMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : B :: p1 ::   de rang : 1 et 2 *)
assert(HACDEp1p2p3p4p5m4 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HBp1Mtmp : rk(B :: p1 :: nil) <= 2) by (solve_hyps_max HBp1eq HBp1M2).
	assert(HABCDEp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2p3p4p5eq HABCDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HABCDEp1p2p3p4p5mtmp Hp1mtmp HBp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p1 ::  de rang :  2 et 2 	 A : A :: B :: p1 ::   de rang : 2 et 2 *)
assert(HACDEp1p2p3p4p5m5 : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HABp1Mtmp : rk(A :: B :: p1 :: nil) <= 2) by (solve_hyps_max HABp1eq HABp1M2).
	assert(HABCDEp1p2p3p4p5mtmp : rk(A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HABCDEp1p2p3p4p5eq HABCDEp1p2p3p4p5m5).
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hincl : incl (A :: p1 :: nil) (list_inter (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: p1 :: A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: B :: p1 :: nil) ++ (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEp1p2p3p4p5mtmp;try rewrite HT2 in HABCDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: B :: p1 :: nil) (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: nil) 5 2 2 HABCDEp1p2p3p4p5mtmp HAp1mtmp HABp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADEp1p2p3p4p5 requis par la preuve de (?)ADEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADEp1p2p3p4p5m2 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : C :: p1 ::   de rang : 2 et 2 *)
assert(HADEp1p2p3p4p5m4 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HCp1eq : rk(C :: p1 :: nil) = 2) by (apply LCp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HCp1Mtmp : rk(C :: p1 :: nil) <= 2) by (solve_hyps_max HCp1eq HCp1M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (C :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (C :: p1 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: p1 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((C :: p1 :: nil) ++ (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (C :: p1 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HACDEp1p2p3p4p5mtmp Hp1mtmp HCp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HADEp1p2p3p4p5m5 : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 5 2 2 HACDEp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACEp1p2p3p4p5 requis par la preuve de (?)ACEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACEp1p2p3p4p5m2 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACEp1p2p3p4p5m3 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HACEp1p2p3p4p5m4 : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HACDEp1p2p3p4p5mtmp : rk(A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HACDEp1p2p3p4p5eq HACDEp1p2p3p4p5m5).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEp1p2p3p4p5mtmp;try rewrite HT2 in HACDEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 5 1 2 HACDEp1p2p3p4p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour AEp1p2p3p4p5 requis par la preuve de (?)AEp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAEp1p2p3p4p5m2 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : p1 ::  de rang :  1 et 1 	 A : D :: p1 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m3 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HDp1eq : rk(D :: p1 :: nil) = 2) by (apply LDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HDp1Mtmp : rk(D :: p1 :: nil) <= 2) by (solve_hyps_max HDp1eq HDp1M2).
	assert(HADEp1p2p3p4p5mtmp : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HADEp1p2p3p4p5eq HADEp1p2p3p4p5m4).
	assert(Hp1mtmp : rk(p1 :: nil) >= 1) by (solve_hyps_min Hp1eq Hp1m1).
	assert(Hincl : incl (p1 :: nil) (list_inter (D :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (D :: p1 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (D :: p1 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((D :: p1 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1p2p3p4p5mtmp;try rewrite HT2 in HADEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (D :: p1 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: nil) 4 1 2 HADEp1p2p3p4p5mtmp Hp1mtmp HDp1Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m4 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACEp1p2p3p4p5mtmp : rk(A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HACEp1p2p3p4p5eq HACEp1p2p3p4p5m4).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACEp1p2p3p4p5mtmp;try rewrite HT2 in HACEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 4 2 2 HACEp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : A :: p3 ::  de rang :  2 et 2 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(HAEp1p2p3p4p5m5 : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADEp1p2p3p4p5mtmp : rk(A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HADEp1p2p3p4p5eq HADEp1p2p3p4p5m5).
	assert(HAp3mtmp : rk(A :: p3 :: nil) >= 2) by (solve_hyps_min HAp3eq HAp3m2).
	assert(Hincl : incl (A :: p3 :: nil) (list_inter (A :: D :: p3 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEp1p2p3p4p5mtmp;try rewrite HT2 in HADEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p3 :: nil) 5 2 2 HADEp1p2p3p4p5mtmp HAp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour p1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDp1p2p3p4p5 requis par la preuve de (?)ACDp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACDp1p2p3p4p5m2 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACDp1p2p3p4p5m3 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACDp1p2p3p4p5m4 : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACDp1eq : rk(A :: C :: D :: p1 :: nil) = 4) by (apply LACDp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACDp1mtmp : rk(A :: C :: D :: p1 :: nil) >= 4) by (solve_hyps_min HACDp1eq HACDp1m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: C :: D :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: D :: p1 :: nil) (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 4 4 HACDp1mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ADp1p2p3p4p5 requis par la preuve de (?)ADp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HADp1p2p3p4p5m2 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HADp1p2p3p4p5m3 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HADp1eq : rk(A :: D :: p1 :: nil) = 3) by (apply LADp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HADp1mtmp : rk(A :: D :: p1 :: nil) >= 3) by (solve_hyps_min HADp1eq HADp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: p1 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HADp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -4 et -4*)
(* ensembles concernés AUB : A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : A :: p2 ::  de rang :  2 et 2 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(HADp1p2p3p4p5m4 : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACDp1p2p3p4p5mtmp : rk(A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HACDp1p2p3p4p5eq HACDp1p2p3p4p5m4).
	assert(HAp2mtmp : rk(A :: p2 :: nil) >= 2) by (solve_hyps_min HAp2eq HAp2m2).
	assert(Hincl : incl (A :: p2 :: nil) (list_inter (A :: C :: p2 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDp1p2p3p4p5mtmp;try rewrite HT2 in HACDp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p2 :: nil) 4 2 2 HACDp1p2p3p4p5mtmp HAp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour p1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)ACp1p2p3p4p5 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACp1p2p3p4p5 requis par la preuve de (?)ACp1p2p3p4p5 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACp1p2p3p4p5m2 : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HAp1mtmp : rk(A :: p1 :: nil) >= 2) by (solve_hyps_min HAp1eq HAp1m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 2 2 HAp1mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACp1p2p3p4p5m3 : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HACp1eq : rk(A :: C :: p1 :: nil) = 3) by (apply LACp1 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HACp1mtmp : rk(A :: C :: p1 :: nil) >= 3) by (solve_hyps_min HACp1eq HACp1m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: p1 :: nil) (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) 3 3 HACp1mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour p1p2p3p4p5 requis par la preuve de (?)p1p2p3p4p5 pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: C :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  3 et 6 	 AiB : p2 ::  de rang :  1 et 1 	 A : A :: C :: p2 ::   de rang : 2 et 2 *)
assert(Hp1p2p3p4p5m2 : rk(p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 2).
{
	assert(HACp2Mtmp : rk(A :: C :: p2 :: nil) <= 2) by (solve_hyps_max HACp2eq HACp2M2).
	assert(HACp1p2p3p4p5mtmp : rk(A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3) by (solve_hyps_min HACp1p2p3p4p5eq HACp1p2p3p4p5m3).
	assert(Hp2mtmp : rk(p2 :: nil) >= 1) by (solve_hyps_min Hp2eq Hp2m1).
	assert(Hincl : incl (p2 :: nil) (list_inter (A :: C :: p2 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: C :: p2 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: p2 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: C :: p2 :: nil) ++ (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACp1p2p3p4p5mtmp;try rewrite HT2 in HACp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: C :: p2 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p2 :: nil) 3 1 2 HACp1p2p3p4p5mtmp Hp2mtmp HACp2Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: D :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  4 et 6 	 AiB : p3 ::  de rang :  1 et 1 	 A : A :: D :: p3 ::   de rang : 2 et 2 *)
assert(Hp1p2p3p4p5m3 : rk(p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 3).
{
	assert(HADp3Mtmp : rk(A :: D :: p3 :: nil) <= 2) by (solve_hyps_max HADp3eq HADp3M2).
	assert(HADp1p2p3p4p5mtmp : rk(A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4) by (solve_hyps_min HADp1p2p3p4p5eq HADp1p2p3p4p5m4).
	assert(Hp3mtmp : rk(p3 :: nil) >= 1) by (solve_hyps_min Hp3eq Hp3m1).
	assert(Hincl : incl (p3 :: nil) (list_inter (A :: D :: p3 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: D :: p3 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: p3 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: D :: p3 :: nil) ++ (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADp1p2p3p4p5mtmp;try rewrite HT2 in HADp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: D :: p3 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p3 :: nil) 4 1 2 HADp1p2p3p4p5mtmp Hp3mtmp HADp3Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: E :: p1 :: p2 :: p3 :: p4 :: p5 ::  de rang :  5 et 6 	 AiB : p4 ::  de rang :  1 et 1 	 A : A :: E :: p4 ::   de rang : 2 et 2 *)
assert(Hp1p2p3p4p5m4 : rk(p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 4).
{
	assert(HAEp4Mtmp : rk(A :: E :: p4 :: nil) <= 2) by (solve_hyps_max HAEp4eq HAEp4M2).
	assert(HAEp1p2p3p4p5mtmp : rk(A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 5) by (solve_hyps_min HAEp1p2p3p4p5eq HAEp1p2p3p4p5m5).
	assert(Hp4mtmp : rk(p4 :: nil) >= 1) by (solve_hyps_min Hp4eq Hp4m1).
	assert(Hincl : incl (p4 :: nil) (list_inter (A :: E :: p4 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: E :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: E :: p4 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: E :: p4 :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: E :: p4 :: nil) ++ (p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAEp1p2p3p4p5mtmp;try rewrite HT2 in HAEp1p2p3p4p5mtmp.
	assert(HT := rule_4 (A :: E :: p4 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p4 :: nil) 5 1 2 HAEp1p2p3p4p5mtmp Hp4mtmp HAEp4Mtmp Hincl); apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(Hp1p2p3p4p5M4 : rk(p1 :: p2 :: p3 :: p4 :: p5 :: nil) <= 4).
{
	assert(HAp1p2p3p4p5eq : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 5) by (apply LAp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HAp1p2p3p4p5Mtmp : rk(A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) <= 5) by (solve_hyps_max HAp1p2p3p4p5eq HAp1p2p3p4p5M5).
	assert(HApBpCpDpEpp1p2p3p4p5eq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 5) by (apply LApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HApBpCpDpEpp1p2p3p4p5Mtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpp1p2p3p4p5eq HApBpCpDpEpp1p2p3p4p5M5).
	assert(HAApBpCpDpEpp1p2p3p4p5eq : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) = 6) by (apply LAApBpCpDpEpp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption).
	assert(HAApBpCpDpEpp1p2p3p4p5mtmp : rk(A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) >= 6) by (solve_hyps_min HAApBpCpDpEpp1p2p3p4p5eq HAApBpCpDpEpp1p2p3p4p5m6).
	assert(Hincl : incl (p1 :: p2 :: p3 :: p4 :: p5 :: nil) (list_inter (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (A :: p1 :: p2 :: p3 :: p4 :: p5 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: p1 :: p2 :: p3 :: p4 :: p5 :: Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ((A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAApBpCpDpEpp1p2p3p4p5mtmp;try rewrite HT2 in HAApBpCpDpEpp1p2p3p4p5mtmp.
	assert(HT := rule_3 (A :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: p1 :: p2 :: p3 :: p4 :: p5 :: nil) (p1 :: p2 :: p3 :: p4 :: p5 :: nil) 5 5 6 HAp1p2p3p4p5Mtmp HApBpCpDpEpp1p2p3p4p5Mtmp HAApBpCpDpEpp1p2p3p4p5mtmp Hincl);apply HT.
}


assert(Hp1p2p3p4p5M : rk(p1 :: p2 :: p3 :: p4 :: p5 ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max Hp1p2p3p4p5eq Hp1p2p3p4p5M5).
assert(Hp1p2p3p4p5m : rk(p1 :: p2 :: p3 :: p4 :: p5 ::  nil) >= 1) by (solve_hyps_min Hp1p2p3p4p5eq Hp1p2p3p4p5m1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: p1 ::  nil) = 2 -> rk(A :: B :: p1 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p1 ::  nil) = 5 ->
rk(A :: p2 ::  nil) = 2 -> rk(A :: C :: p2 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p2 ::  nil) = 5 ->
rk(A :: p3 ::  nil) = 2 -> rk(A :: D :: p3 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p3 ::  nil) = 5 ->
rk(A :: p4 ::  nil) = 2 -> rk(A :: E :: p4 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p4 ::  nil) = 5 ->
rk(B :: C :: p5 ::  nil) = 2 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: p5 ::  nil) = 5 -> 
	 rk(p1 :: p2 :: p3 :: p4 :: p5 ::  nil) = 4  .
Proof.

intros A B C D E Ap Bp Cp Dp Ep p1 p2 p3 p4 p5 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HAp1eq HABp1eq HApBpCpDpEpp1eq HAp2eq HACp2eq HApBpCpDpEpp2eq HAp3eq
HADp3eq HApBpCpDpEpp3eq HAp4eq HAEp4eq HApBpCpDpEpp4eq HBCp5eq HApBpCpDpEpp5eq .
repeat split.

	apply Lp1p2p3p4p5 with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (p1 := p1) (p2 := p2) (p3 := p3) (p4 := p4) (p5 := p5) ; assumption.
Qed .
