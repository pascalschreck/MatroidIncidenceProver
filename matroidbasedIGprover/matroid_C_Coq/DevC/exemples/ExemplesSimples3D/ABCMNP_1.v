Load "preamble2D.v".


(* dans la couche 0 *)
Lemma LAB : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 ->
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
Lemma LBC : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(B :: C ::  nil) = 2.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BC requis par la preuve de (?)BC pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -1 et -2*)
(* ensembles concernés AUB : A :: B :: C ::  de rang :  3 et 3 	 AiB :  de rang :  0 et 0 	 A : A ::   de rang : 1 et 1 *)
assert(HBCm2 : rk(B :: C :: nil) >= 2).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (B :: C :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: nil) (A :: B :: C :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: nil) ((A :: nil) ++ (B :: C :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCmtmp;try rewrite HT2 in HABCmtmp.
	assert(HT := rule_4 (A :: nil) (B :: C :: nil) (nil) 3 0 1 HABCmtmp Hmtmp HAMtmp Hincl); apply HT.
}

assert(HBCM : rk(B :: C ::  nil) <= 2) by (solve_hyps_max HBCeq HBCM2).
assert(HBCm : rk(B :: C ::  nil) >= 1) by (solve_hyps_min HBCeq HBCm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCMNP *)
(* dans la couche 0 *)
Lemma LABCMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 ->
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
Lemma LBCMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCMNP requis par la preuve de (?)BCMNP pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCMNP requis par la preuve de (?)BCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCMNPm2 : rk(B :: C :: M :: N :: P :: nil) >= 2).
{
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (B :: C :: M :: N :: P :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P ::  de rang :  3 et 3 	 AiB : M ::  de rang :  1 et 1 	 A : A :: M ::   de rang : 1 et 1 *)
assert(HBCMNPm3 : rk(B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNPmtmp : rk(A :: B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HABCMNPeq HABCMNPm3).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (B :: C :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: M :: B :: C :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: B :: C :: M :: N :: P :: nil) ((A :: M :: nil) ++ (B :: C :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPmtmp;try rewrite HT2 in HABCMNPmtmp.
	assert(HT := rule_4 (A :: M :: nil) (B :: C :: M :: N :: P :: nil) (M :: nil) 3 1 1 HABCMNPmtmp HMmtmp HAMMtmp Hincl); apply HT.
}

assert(HBCMNPM : rk(B :: C :: M :: N :: P ::  nil) <= 3) by (solve_hyps_max HBCMNPeq HBCMNPM3).
assert(HBCMNPm : rk(B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HBCMNPeq HBCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 ->
rk(A :: C :: N ::  nil) = 2 -> rk(B :: C :: P ::  nil) = 2 -> rk(M :: N :: P ::  nil) >= 2/\rk(M :: N :: P ::  nil) <= 3.
Proof.

intros A B C M N P 
HABCeq HAMeq HABMeq HACNeq HBCPeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : B :: C :: M :: N :: P ::  de rang :  3 et 3 	 AiB : P ::  de rang :  1 et 1 	 A : B :: C :: P ::   de rang : 2 et 2 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	assert(HBCPMtmp : rk(B :: C :: P :: nil) <= 2) by (solve_hyps_max HBCPeq HBCPM2).
	assert(HBCMNPeq : rk(B :: C :: M :: N :: P :: nil) = 3) by (apply LBCMNP with (A := A) (B := B) (C := C) (M := M) (N := N) (P := P) ; assumption).
	assert(HBCMNPmtmp : rk(B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HBCMNPeq HBCMNPm3).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (B :: C :: P :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: M :: N :: P :: nil) (B :: C :: P :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: P :: M :: N :: P :: nil) ((B :: C :: P :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCMNPmtmp;try rewrite HT2 in HBCMNPmtmp.
	assert(HT := rule_4 (B :: C :: P :: nil) (M :: N :: P :: nil) (P :: nil) 3 1 2 HBCMNPmtmp HPmtmp HBCPMtmp Hincl); apply HT.
}

assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
split. intuition. intuition. 
Qed.

