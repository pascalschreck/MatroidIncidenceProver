Load "preamble2D.v".


(* dans la couche 0 *)
Lemma LAB : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 2 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(A :: B ::  nil) = 2.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AB requis par la preuve de (?)AB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HABm2 : rk(A :: B :: nil) >= 2).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: nil) (C :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: nil) (A :: B :: C :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: nil) ((A :: B :: nil) ++ (C :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCmtmp;try rewrite HT2 in HABCmtmp.
	assert(HT := rule_2 (A :: B :: nil) (C :: nil) (nil) 3 0 1 HABCmtmp Hmtmp HCMtmp Hincl);apply HT.
}

assert(HABM : rk(A :: B ::  nil) <= 2) by (solve_hyps_max HABeq HABM2).
assert(HABm : rk(A :: B ::  nil) >= 1) by (solve_hyps_min HABeq HABm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAC : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 2 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(A :: C ::  nil) = 2.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AC requis par la preuve de (?)AC pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : A :: B :: C ::  de rang :  3 et 3 	 AiB :  de rang :  0 et 0 	 A : B ::   de rang : 1 et 1 *)
assert(HACm2 : rk(A :: C :: nil) >= 2).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: C :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: nil) (B :: A :: C :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: C :: nil) ((B :: nil) ++ (A :: C :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCmtmp;try rewrite HT2 in HABCmtmp.
	assert(HT := rule_4 (B :: nil) (A :: C :: nil) (nil) 3 0 1 HABCmtmp Hmtmp HBMtmp Hincl); apply HT.
}

assert(HACM : rk(A :: C ::  nil) <= 2) by (solve_hyps_max HACeq HACM2).
assert(HACm : rk(A :: C ::  nil) >= 1) by (solve_hyps_min HACeq HACm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACMNP *)
(* dans la couche 0 *)
Lemma LABCMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 2 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCMNPm2 : rk(A :: B :: C :: M :: N :: P :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (A :: B :: C :: M :: N :: P :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 2 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(A :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACMNP requis par la preuve de (?)ACMNP pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACMNP requis par la preuve de (?)ACMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACMNPm2 : rk(A :: C :: M :: N :: P :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (A :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (A :: C :: M :: N :: P :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P ::  de rang :  3 et 3 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: M ::   de rang : 2 et 2 *)
assert(HACMNPm3 : rk(A :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABMMtmp : rk(A :: B :: M :: nil) <= 2) by (solve_hyps_max HABMeq HABMM2).
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNPmtmp : rk(A :: B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HABCMNPeq HABCMNPm3).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: M :: nil) (A :: C :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: M :: A :: C :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: A :: C :: M :: N :: P :: nil) ((A :: B :: M :: nil) ++ (A :: C :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPmtmp;try rewrite HT2 in HABCMNPmtmp.
	assert(HT := rule_4 (A :: B :: M :: nil) (A :: C :: M :: N :: P :: nil) (A :: M :: nil) 3 2 2 HABCMNPmtmp HAMmtmp HABMMtmp Hincl); apply HT.
}

assert(HACMNPM : rk(A :: C :: M :: N :: P ::  nil) <= 3) by (solve_hyps_max HACMNPeq HACMNPM3).
assert(HACMNPm : rk(A :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HACMNPeq HACMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 2 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(M :: N :: P ::  nil) >= 2/\rk(M :: N :: P ::  nil) <= 3.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: C :: M :: N :: P ::  de rang :  3 et 3 	 AiB : N ::  de rang :  1 et 1 	 A : A :: C :: N ::   de rang : 2 et 2 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	assert(HACNMtmp : rk(A :: C :: N :: nil) <= 2) by (solve_hyps_max HACNeq HACNM2).
	assert(HACMNPeq : rk(A :: C :: M :: N :: P :: nil) = 3) by (apply LACMNP with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HACMNPmtmp : rk(A :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HACMNPeq HACMNPm3).
	assert(HNmtmp : rk(N :: nil) >= 1) by (solve_hyps_min HNeq HNm1).
	assert(Hincl : incl (N :: nil) (list_inter (A :: C :: N :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: M :: N :: P :: nil) (A :: C :: N :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: N :: M :: N :: P :: nil) ((A :: C :: N :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACMNPmtmp;try rewrite HT2 in HACMNPmtmp.
	assert(HT := rule_4 (A :: C :: N :: nil) (M :: N :: P :: nil) (N :: nil) 3 1 2 HACMNPmtmp HNmtmp HACNMtmp Hincl); apply HT.
}

assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
split. intuition. intuition. 
Qed.

