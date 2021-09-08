Load "preamble3D.v".


(* dans la couche 0 *)
Lemma LAB : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A :: B ::  nil) = 2.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AB requis par la preuve de (?)AB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HABm2 : rk(A :: B :: nil) >= 2).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABMmtmp : rk(A :: B :: M :: nil) >= 2) by (solve_hyps_min HABMeq HABMm2).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: nil) (A :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: M :: nil) (A :: B :: A :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: A :: M :: nil) ((A :: B :: nil) ++ (A :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABMmtmp;try rewrite HT2 in HABMmtmp.
	assert(HT := rule_2 (A :: B :: nil) (A :: M :: nil) (A :: nil) 2 1 1 HABMmtmp HAmtmp HAMMtmp Hincl);apply HT.
}

assert(HABM : rk(A :: B ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HABeq HABM2).
assert(HABm : rk(A :: B ::  nil) >= 1) by (solve_hyps_min HABeq HABm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBM : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(B :: M ::  nil) = 2.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BM requis par la preuve de (?)BM pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: M ::  de rang :  2 et 2 	 AiB : M ::  de rang :  1 et 1 	 A : A :: M ::   de rang : 1 et 1 *)
assert(HBMm2 : rk(B :: M :: nil) >= 2).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABMmtmp : rk(A :: B :: M :: nil) >= 2) by (solve_hyps_min HABMeq HABMm2).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (B :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: M :: nil) (A :: M :: B :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: B :: M :: nil) ((A :: M :: nil) ++ (B :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABMmtmp;try rewrite HT2 in HABMmtmp.
	assert(HT := rule_4 (A :: M :: nil) (B :: M :: nil) (M :: nil) 2 1 1 HABMmtmp HMmtmp HAMMtmp Hincl); apply HT.
}

assert(HBMM : rk(B :: M ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBMeq HBMM2).
assert(HBMm : rk(B :: M ::  nil) >= 1) by (solve_hyps_min HBMeq HBMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCN : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABCN requis par la preuve de (?)ABCN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABCN requis par la preuve de (?)ABCN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCN requis par la preuve de (?)ABCN pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCNM3 : rk(A :: B :: C :: N :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HACNMtmp : rk(A :: C :: N :: nil) <= 2) by (solve_hyps_max HACNeq HACNM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: N :: nil) (B :: A :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: C :: N :: nil) ((B :: nil) ++ (A :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: C :: N :: nil) (nil) 1 2 0 HBMtmp HACNMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCNm2 : rk(A :: B :: C :: N :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (A :: B :: C :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (A :: B :: C :: N :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCNm3 : rk(A :: B :: C :: N :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: N :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

assert(HABCNM : rk(A :: B :: C :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCNm : rk(A :: B :: C :: N ::  nil) >= 1) by (solve_hyps_min HABCNeq HABCNm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCMN *)
(* dans constructLemma(), requis par LACMN *)
(* dans la couche 0 *)
Lemma LABCMN : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNm3 : rk(A :: B :: C :: M :: N :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -2*)
assert(HABCMNM3 : rk(A :: B :: C :: M :: N :: nil) <= 3).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCNeq : rk(A :: B :: C :: N :: nil) = 3) by (apply LABCN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: A :: B :: C :: N :: nil) ((A :: M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: M :: nil) (A :: B :: C :: N :: nil) (A :: nil) 1 3 1 HAMMtmp HABCNMtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNM : rk(A :: B :: C :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNm : rk(A :: B :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HABCMNeq HABCMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACMN : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A :: C :: M :: N ::  nil) = 2.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ACMN requis par la preuve de (?)ACMN pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACMN requis par la preuve de (?)ACMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACMN requis par la preuve de (?)ACMN pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACMNM3 : rk(A :: C :: M :: N :: nil) <= 3).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HACNMtmp : rk(A :: C :: N :: nil) <= 2) by (solve_hyps_max HACNeq HACNM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: M :: N :: nil) (M :: A :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A :: C :: N :: nil) ((M :: nil) ++ (A :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A :: C :: N :: nil) (nil) 1 2 0 HMMtmp HACNMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HACMNM2 : rk(A :: C :: M :: N :: nil) <= 2).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HACNMtmp : rk(A :: C :: N :: nil) <= 2) by (solve_hyps_max HACNeq HACNM2).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: M :: nil) (A :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: M :: N :: nil) (A :: M :: A :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: A :: C :: N :: nil) ((A :: M :: nil) ++ (A :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: M :: nil) (A :: C :: N :: nil) (A :: nil) 1 2 1 HAMMtmp HACNMtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N ::  de rang :  3 et 3 	 AiB : M ::  de rang :  1 et 1 	 A : B :: M ::   de rang : 2 et 2 *)
assert(HACMNm2 : rk(A :: C :: M :: N :: nil) >= 2).
{
	assert(HBMeq : rk(B :: M :: nil) = 2) by (apply LBM with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HBMMtmp : rk(B :: M :: nil) <= 2) by (solve_hyps_max HBMeq HBMM2).
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNmtmp : rk(A :: B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HABCMNeq HABCMNm3).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (B :: M :: nil) (A :: C :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (B :: M :: A :: C :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: M :: A :: C :: M :: N :: nil) ((B :: M :: nil) ++ (A :: C :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNmtmp;try rewrite HT2 in HABCMNmtmp.
	assert(HT := rule_4 (B :: M :: nil) (A :: C :: M :: N :: nil) (M :: nil) 3 1 2 HABCMNmtmp HMmtmp HBMMtmp Hincl); apply HT.
}

assert(HACMNM : rk(A :: C :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACMNm : rk(A :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HACMNeq HACMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCMN : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(C :: M :: N ::  nil) = 2.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CMN requis par la preuve de (?)CMN pour la règle 6  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCMN requis par la preuve de (?)CMN pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCMN requis par la preuve de (?)BCMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N ::  de rang :  3 et 3 	 AiB : M ::  de rang :  1 et 1 	 A : A :: M ::   de rang : 1 et 1 *)
assert(HBCMNm3 : rk(B :: C :: M :: N :: nil) >= 3).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNmtmp : rk(A :: B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HABCMNeq HABCMNm3).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (B :: C :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: M :: B :: C :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: B :: C :: M :: N :: nil) ((A :: M :: nil) ++ (B :: C :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNmtmp;try rewrite HT2 in HABCMNmtmp.
	assert(HT := rule_4 (A :: M :: nil) (B :: C :: M :: N :: nil) (M :: nil) 3 1 1 HABCMNmtmp HMmtmp HAMMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CMN requis par la preuve de (?)CMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : B :: C :: M :: N ::  de rang :  3 et 4 	 AiB : M ::  de rang :  1 et 1 	 A : B :: M ::   de rang : 2 et 2 *)
assert(HCMNm2 : rk(C :: M :: N :: nil) >= 2).
{
	assert(HBMeq : rk(B :: M :: nil) = 2) by (apply LBM with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HBMMtmp : rk(B :: M :: nil) <= 2) by (solve_hyps_max HBMeq HBMM2).
	assert(HBCMNmtmp : rk(B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HBCMNeq HBCMNm3).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (B :: M :: nil) (C :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: M :: N :: nil) (B :: M :: C :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: M :: C :: M :: N :: nil) ((B :: M :: nil) ++ (C :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCMNmtmp;try rewrite HT2 in HBCMNmtmp.
	assert(HT := rule_4 (B :: M :: nil) (C :: M :: N :: nil) (M :: nil) 3 1 2 HBCMNmtmp HMmtmp HBMMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCMNM2 : rk(C :: M :: N :: nil) <= 2).
{
	assert(HACMNeq : rk(A :: C :: M :: N :: nil) = 2) by (apply LACMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HACMNMtmp : rk(A :: C :: M :: N :: nil) <= 2) by (solve_hyps_max HACMNeq HACMNM2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: M :: N :: nil) (A :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (C :: M :: N :: nil) (A :: C :: M :: N :: nil) 2 2 HACMNMtmp Hcomp Hincl);apply HT.
}

assert(HCMNM : rk(C :: M :: N ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCMNeq HCMNM3).
assert(HCMNm : rk(C :: M :: N ::  nil) >= 1) by (solve_hyps_min HCMNeq HCMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA'B'C'MP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A' :: B' :: C' :: M :: P ::  nil) = 3.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'MP requis par la preuve de (?)A'B'C'MP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour A'B'C'MP requis par la preuve de (?)A'B'C'MP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'MPm3 : rk(A' :: B' :: C' :: M :: P :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: P :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'MPM3 : rk(A' :: B' :: C' :: M :: P :: nil) <= 3).
{
	assert(HA'B'C'MMtmp : rk(A' :: B' :: C' :: M :: nil) <= 3) by (solve_hyps_max HA'B'C'Meq HA'B'C'MM3).
	assert(HA'B'C'PMtmp : rk(A' :: B' :: C' :: P :: nil) <= 3) by (solve_hyps_max HA'B'C'Peq HA'B'C'PM3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: P :: nil) (A' :: B' :: C' :: M :: A' :: B' :: C' :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M :: A' :: B' :: C' :: P :: nil) ((A' :: B' :: C' :: M :: nil) ++ (A' :: B' :: C' :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: P :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'MMtmp HA'B'C'PMtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA'B'C'MPM : rk(A' :: B' :: C' :: M :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HA'B'C'MPm : rk(A' :: B' :: C' :: M :: P ::  nil) >= 1) by (solve_hyps_min HA'B'C'MPeq HA'B'C'MPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCMNP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCMNP requis par la preuve de (?)BCMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNP requis par la preuve de (?)BCMNP pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCMNP requis par la preuve de (?)BCMNP pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P ::  de rang :  3 et 4 	 AiB : M ::  de rang :  1 et 1 	 A : A :: M ::   de rang : 1 et 1 *)
assert(HBCMNPm3 : rk(B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCMNPmtmp : rk(A :: B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HABCMNPeq HABCMNPm3).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (B :: C :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: M :: B :: C :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: B :: C :: M :: N :: P :: nil) ((A :: M :: nil) ++ (B :: C :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPmtmp;try rewrite HT2 in HABCMNPmtmp.
	assert(HT := rule_4 (A :: M :: nil) (B :: C :: M :: N :: P :: nil) (M :: nil) 3 1 1 HABCMNPmtmp HMmtmp HAMMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 -4 et -2*)
assert(HBCMNPM3 : rk(B :: C :: M :: N :: P :: nil) <= 3).
{
	assert(HCMNeq : rk(C :: M :: N :: nil) = 2) by (apply LCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HCMNMtmp : rk(C :: M :: N :: nil) <= 2) by (solve_hyps_max HCMNeq HCMNM2).
	assert(HBCPMtmp : rk(B :: C :: P :: nil) <= 2) by (solve_hyps_max HBCPeq HBCPM2).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (C :: M :: N :: nil) (B :: C :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: M :: N :: P :: nil) (C :: M :: N :: B :: C :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: M :: N :: B :: C :: P :: nil) ((C :: M :: N :: nil) ++ (B :: C :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: M :: N :: nil) (B :: C :: P :: nil) (C :: nil) 2 2 1 HCMNMtmp HBCPMtmp HCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HBCMNPM : rk(B :: C :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCMNPm : rk(B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HBCMNPeq HBCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA'B'C'MNP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A' :: B' :: C' :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'MNP requis par la preuve de (?)A'B'C'MNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour A'B'C'MNP requis par la preuve de (?)A'B'C'MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'MNPm3 : rk(A' :: B' :: C' :: M :: N :: P :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: P :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HA'B'C'MNPM3 : rk(A' :: B' :: C' :: M :: N :: P :: nil) <= 3).
{
	assert(HA'B'C'NMtmp : rk(A' :: B' :: C' :: N :: nil) <= 3) by (solve_hyps_max HA'B'C'Neq HA'B'C'NM3).
	assert(HA'B'C'MPeq : rk(A' :: B' :: C' :: M :: P :: nil) = 3) by (apply LA'B'C'MP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HA'B'C'MPMtmp : rk(A' :: B' :: C' :: M :: P :: nil) <= 3) by (solve_hyps_max HA'B'C'MPeq HA'B'C'MPM3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: N :: nil) (A' :: B' :: C' :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: N :: P :: nil) (A' :: B' :: C' :: N :: A' :: B' :: C' :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: N :: A' :: B' :: C' :: M :: P :: nil) ((A' :: B' :: C' :: N :: nil) ++ (A' :: B' :: C' :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: N :: nil) (A' :: B' :: C' :: M :: P :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'NMtmp HA'B'C'MPMtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA'B'C'MNPM : rk(A' :: B' :: C' :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HA'B'C'MNPm : rk(A' :: B' :: C' :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HA'B'C'MNPeq HA'B'C'MNPm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBCA'B'C'MNP *)
(* dans la couche 0 *)
Lemma LABCA'B'C'MNP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCA'B'C'MNP requis par la preuve de (?)ABCA'B'C'MNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCA'B'C'MNP requis par la preuve de (?)ABCA'B'C'MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNPm3 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNPm4 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 4).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 4) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) 4 4 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCA'B'C'MNPM : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCA'B'C'MNPm : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCA'B'C'MNPeq HABCA'B'C'MNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCA'B'C'MNP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCA'B'C'MNP requis par la preuve de (?)BCA'B'C'MNP pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCA'B'C'MNP requis par la preuve de (?)BCA'B'C'MNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCA'C' requis par la preuve de (?)BCA'B'C'MNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCA' requis par la preuve de (?)BCA'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCA'M requis par la preuve de (?)BCA' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCA'M requis par la preuve de (?)ABCA'M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'Mm3 : rk(A :: B :: C :: A' :: M :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: M :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCA' requis par la preuve de (?)BCA' pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -1 et -4*)
assert(HBCA'm2 : rk(B :: C :: A' :: nil) >= 2).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCA'Mmtmp : rk(A :: B :: C :: A' :: M :: nil) >= 3) by (solve_hyps_min HABCA'Meq HABCA'Mm3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: C :: A' :: nil) (A :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: M :: nil) (B :: C :: A' :: A :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: A' :: A :: M :: nil) ((B :: C :: A' :: nil) ++ (A :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'Mmtmp;try rewrite HT2 in HABCA'Mmtmp.
	assert(HT := rule_2 (B :: C :: A' :: nil) (A :: M :: nil) (nil) 3 0 1 HABCA'Mmtmp Hmtmp HAMMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCA'B' requis par la preuve de (?)BCA'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'm3 : rk(A :: B :: C :: A' :: B' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCA'C' requis par la preuve de (?)BCA'C' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: -4 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: A' :: B' :: C' ::  de rang :  4 et 4 	 AiB : B :: C :: A' ::  de rang :  2 et 3 	 A : A :: B :: C :: A' :: B' ::   de rang : 3 et 4 *)
assert(HBCA'C'm2 : rk(B :: C :: A' :: C' :: nil) >= 2).
{
	assert(HABCA'B'Mtmp : rk(A :: B :: C :: A' :: B' :: nil) <= 4) by (solve_hyps_max HABCA'B'eq HABCA'B'M4).
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 4) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm4).
	assert(HBCA'mtmp : rk(B :: C :: A' :: nil) >= 2) by (solve_hyps_min HBCA'eq HBCA'm2).
	assert(Hincl : incl (B :: C :: A' :: nil) (list_inter (A :: B :: C :: A' :: B' :: nil) (B :: C :: A' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: B :: C :: A' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A' :: B' :: B :: C :: A' :: C' :: nil) ((A :: B :: C :: A' :: B' :: nil) ++ (B :: C :: A' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'mtmp;try rewrite HT2 in HABCA'B'C'mtmp.
	assert(HT := rule_4 (A :: B :: C :: A' :: B' :: nil) (B :: C :: A' :: C' :: nil) (B :: C :: A' :: nil) 4 2 4 HABCA'B'C'mtmp HBCA'mtmp HABCA'B'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCA'B'C'MNP requis par la preuve de (?)BCA'B'C'MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HBCA'B'C'MNPm2 : rk(B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 2).
{
	assert(HBCA'C'mtmp : rk(B :: C :: A' :: C' :: nil) >= 2) by (solve_hyps_min HBCA'C'eq HBCA'C'm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: A' :: C' :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: A' :: C' :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) 2 2 HBCA'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HBCA'B'C'MNPm3 : rk(B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: A' :: B' :: C' :: M :: N :: P ::  de rang :  4 et 4 	 AiB : M ::  de rang :  1 et 1 	 A : A :: M ::   de rang : 1 et 1 *)
assert(HBCA'B'C'MNPm4 : rk(B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 4).
{
	assert(HAMMtmp : rk(A :: M :: nil) <= 1) by (solve_hyps_max HAMeq HAMM1).
	assert(HABCA'B'C'MNPeq : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) = 4) by (apply LABCA'B'C'MNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HABCA'B'C'MNPmtmp : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 4) by (solve_hyps_min HABCA'B'C'MNPeq HABCA'B'C'MNPm4).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) (A :: M :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) ((A :: M :: nil) ++ (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'MNPmtmp;try rewrite HT2 in HABCA'B'C'MNPmtmp.
	assert(HT := rule_4 (A :: M :: nil) (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) (M :: nil) 4 1 1 HABCA'B'C'MNPmtmp HMmtmp HAMMtmp Hincl); apply HT.
}

assert(HBCA'B'C'MNPM : rk(B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCA'B'C'MNPm : rk(B :: C :: A' :: B' :: C' :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HBCA'B'C'MNPeq HBCA'B'C'MNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : B :: C :: M :: N :: P ::  de rang :  3 et 3 	 AiB : P ::  de rang :  1 et 1 	 A : B :: C :: P ::   de rang : 2 et 2 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	assert(HBCPMtmp : rk(B :: C :: P :: nil) <= 2) by (solve_hyps_max HBCPeq HBCPM2).
	assert(HBCMNPeq : rk(B :: C :: M :: N :: P :: nil) = 3) by (apply LBCMNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HBCMNPmtmp : rk(B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HBCMNPeq HBCMNPm3).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (B :: C :: P :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: M :: N :: P :: nil) (B :: C :: P :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: P :: M :: N :: P :: nil) ((B :: C :: P :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCMNPmtmp;try rewrite HT2 in HBCMNPmtmp.
	assert(HT := rule_4 (B :: C :: P :: nil) (M :: N :: P :: nil) (P :: nil) 3 1 2 HBCMNPmtmp HPmtmp HBCPMtmp Hincl); apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HMNPM2 : rk(M :: N :: P :: nil) <= 2).
{
	assert(HBCMNPeq : rk(B :: C :: M :: N :: P :: nil) = 3) by (apply LBCMNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HBCMNPMtmp : rk(B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HBCMNPeq HBCMNPM3).
	assert(HA'B'C'MNPeq : rk(A' :: B' :: C' :: M :: N :: P :: nil) = 3) by (apply LA'B'C'MNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HA'B'C'MNPMtmp : rk(A' :: B' :: C' :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HA'B'C'MNPeq HA'B'C'MNPM3).
	assert(HBCA'B'C'MNPeq : rk(B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) = 4) by (apply LBCA'B'C'MNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption).
	assert(HBCA'B'C'MNPmtmp : rk(B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) >= 4) by (solve_hyps_min HBCA'B'C'MNPeq HBCA'B'C'MNPm4).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (B :: C :: M :: N :: P :: nil) (A' :: B' :: C' :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: A' :: B' :: C' :: M :: N :: P :: nil) (B :: C :: M :: N :: P :: A' :: B' :: C' :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: M :: N :: P :: A' :: B' :: C' :: M :: N :: P :: nil) ((B :: C :: M :: N :: P :: nil) ++ (A' :: B' :: C' :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCA'B'C'MNPmtmp;try rewrite HT2 in HBCA'B'C'MNPmtmp.
	assert(HT := rule_3 (B :: C :: M :: N :: P :: nil) (A' :: B' :: C' :: M :: N :: P :: nil) (M :: N :: P :: nil) 3 3 4 HBCMNPMtmp HA'B'C'MNPMtmp HBCA'B'C'MNPmtmp Hincl);apply HT.
}


assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C A' B' C' M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 4 ->
rk(A :: M ::  nil) = 1 -> rk(A :: B :: M ::  nil) = 2 -> rk(A' :: B' :: C' :: M ::  nil) = 3 ->
rk(A :: C :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(B :: C :: P ::  nil) = 2 ->
rk(A' :: B' :: C' :: P ::  nil) = 3 -> 
	 rk(M :: N :: P ::  nil) = 2  .
Proof.

intros A B C A' B' C' M N P 
HABCeq HA'B'C'eq HABCA'B'C'eq HAMeq HABMeq HA'B'C'Meq HACNeq HA'B'C'Neq HBCPeq HA'B'C'Peq
.
repeat split.

	apply LMNP with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) (P := P) ; assumption.
Qed .
