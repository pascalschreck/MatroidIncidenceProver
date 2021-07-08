Load "preamble4D.v".


(* dans constructLemma(), requis par LAM *)
(* dans la couche 0 *)
Lemma LAH1H2H3H4M : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AH1H2H3H4M requis par la preuve de (?)AH1H2H3H4M pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AH1H2H3H4M requis par la preuve de (?)AH1H2H3H4M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4Mm4 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4Mm5 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HAH1H2H3H4MM : rk(A :: H1 :: H2 :: H3 :: H4 :: M ::  nil) <= 5) by (apply rk_upper_dim).
assert(HAH1H2H3H4Mm : rk(A :: H1 :: H2 :: H3 :: H4 :: M ::  nil) >= 1) by (solve_hyps_min HAH1H2H3H4Meq HAH1H2H3H4Mm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAM : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: M ::  nil) = 2.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AM requis par la preuve de (?)AM pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HAMm2 : rk(A :: M :: nil) >= 2).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HAH1H2H3H4Meq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: nil) = 5) by (apply LAH1H2H3H4M with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAH1H2H3H4Mmtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4Meq HAH1H2H3H4Mm5).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: H1 :: H2 :: H3 :: H4 :: M :: nil) (A :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil) ((A :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAH1H2H3H4Mmtmp;try rewrite HT2 in HAH1H2H3H4Mmtmp.
	assert(HT := rule_2 (A :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil) (M :: nil) 5 1 4 HAH1H2H3H4Mmtmp HMmtmp HH1H2H3H4MMtmp Hincl);apply HT.
}

assert(HAMM : rk(A :: M ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max HAMeq HAMM2).
assert(HAMm : rk(A :: M ::  nil) >= 1) by (solve_hyps_min HAMeq HAMm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMN *)
(* dans la couche 0 *)
Lemma LAH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AH1H2H3H4MN requis par la preuve de (?)AH1H2H3H4MN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AH1H2H3H4MN requis par la preuve de (?)AH1H2H3H4MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNm4 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNm5 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HAH1H2H3H4MNM : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HAH1H2H3H4MNm : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) >= 1) by (solve_hyps_min HAH1H2H3H4MNeq HAH1H2H3H4MNm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMN *)
(* dans la couche 0 *)
Lemma LH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MN requis par la preuve de (?)H1H2H3H4MN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MN requis par la preuve de (?)H1H2H3H4MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HH1H2H3H4MNM4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HH1H2H3H4NMtmp : rk(H1 :: H2 :: H3 :: H4 :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Neq HH1H2H3H4NM4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: N :: nil) ((H1 :: H2 :: H3 :: H4 :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4MMtmp HH1H2H3H4NMtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MNM : rk(H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNm : rk(H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNeq HH1H2H3H4MNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAMN : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour AMN requis par la preuve de (?)AMN pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour ABCMN requis par la preuve de (?)AMN pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 5  *)
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
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCMNM4 : rk(A :: B :: C :: M :: N :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A :: B :: C :: N :: nil) ((M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A :: B :: C :: N :: nil) (nil) 1 3 0 HMMtmp HABCNMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCMNM3 : rk(A :: B :: C :: M :: N :: nil) <= 3).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCNMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour AMN requis par la preuve de (?)AMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N ::  de rang :  3 et 3 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNm2 : rk(A :: M :: N :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNmtmp : rk(A :: B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HABCMNeq HABCMNm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNmtmp;try rewrite HT2 in HABCMNmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: nil) (A :: M :: nil) 3 2 3 HABCMNmtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HAMNm3 : rk(A :: M :: N :: nil) >= 3).
{
	assert(HH1H2H3H4MNeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 4) by (apply LH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HH1H2H3H4MNMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNeq HH1H2H3H4MNM4).
	assert(HAH1H2H3H4MNeq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LAH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAH1H2H3H4MNmtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4MNeq HAH1H2H3H4MNm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (A :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) ((A :: M :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAH1H2H3H4MNmtmp;try rewrite HT2 in HAH1H2H3H4MNmtmp.
	assert(HT := rule_2 (A :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (M :: N :: nil) 5 2 4 HAH1H2H3H4MNmtmp HMNmtmp HH1H2H3H4MNMtmp Hincl);apply HT.
}

assert(HAMNM : rk(A :: M :: N ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HAMNeq HAMNM3).
assert(HAMNm : rk(A :: M :: N ::  nil) >= 1) by (solve_hyps_min HAMNeq HAMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMN : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 5  *)
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
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCMNM4 : rk(A :: B :: C :: M :: N :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A :: B :: C :: N :: nil) ((M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A :: B :: C :: N :: nil) (nil) 1 3 0 HMMtmp HABCNMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCMNM3 : rk(A :: B :: C :: M :: N :: nil) <= 3).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCNMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNM : rk(A :: B :: C :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCMNm : rk(A :: B :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HABCMNeq HABCMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: B :: C :: M :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMPm3 : rk(A :: B :: C :: M :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCMPM4 : rk(A :: B :: C :: M :: P :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A :: B :: C :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: P :: nil) (M :: A :: B :: C :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A :: B :: C :: P :: nil) ((M :: nil) ++ (A :: B :: C :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A :: B :: C :: P :: nil) (nil) 1 3 0 HMMtmp HABCPMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCMPM3 : rk(A :: B :: C :: M :: P :: nil) <= 3).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: P :: nil) (A :: B :: C :: M :: A :: B :: C :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: P :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMPM : rk(A :: B :: C :: M :: P ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCMPm : rk(A :: B :: C :: M :: P ::  nil) >= 1) by (solve_hyps_min HABCMPeq HABCMPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(H1 :: H2 :: H3 :: H4 :: M :: P ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MP requis par la preuve de (?)H1H2H3H4MP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MP requis par la preuve de (?)H1H2H3H4MP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MPm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: P :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: P :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HH1H2H3H4MPM4 : rk(H1 :: H2 :: H3 :: H4 :: M :: P :: nil) <= 4).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HH1H2H3H4PMtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Peq HH1H2H3H4PM4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: P :: nil) ((H1 :: H2 :: H3 :: H4 :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4MMtmp HH1H2H3H4PMtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MPM : rk(H1 :: H2 :: H3 :: H4 :: M :: P ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MPm : rk(H1 :: H2 :: H3 :: H4 :: M :: P ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MPeq HH1H2H3H4MPm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMNP *)
(* dans la couche 0 *)
Lemma LABCMNP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HABCMNPM4 : rk(A :: B :: C :: M :: N :: P :: nil) <= 4).
{
	assert(HNMtmp : rk(N :: nil) <= 1) by (solve_hyps_max HNeq HNM1).
	assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMPMtmp : rk(A :: B :: C :: M :: P :: nil) <= 3) by (solve_hyps_max HABCMPeq HABCMPM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (N :: nil) (A :: B :: C :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (N :: A :: B :: C :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (N :: A :: B :: C :: M :: P :: nil) ((N :: nil) ++ (A :: B :: C :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (N :: nil) (A :: B :: C :: M :: P :: nil) (nil) 1 3 0 HNMtmp HABCMPMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABCMNPM3 : rk(A :: B :: C :: M :: N :: P :: nil) <= 3).
{
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMPMtmp : rk(A :: B :: C :: M :: P :: nil) <= 3) by (solve_hyps_max HABCMPeq HABCMPM3).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCNMtmp HABCMPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAMNP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour AMNP requis par la preuve de (?)AMNP pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour AMNP requis par la preuve de (?)AMNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNP requis par la preuve de (?)AMNP pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour AMNP requis par la preuve de (?)AMNP pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNPm2 : rk(A :: M :: N :: P :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPmtmp : rk(A :: B :: C :: M :: N :: P :: nil) >= 3) by (solve_hyps_min HABCMNPeq HABCMNPm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: M :: A :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: P :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPmtmp;try rewrite HT2 in HABCMNPmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: P :: nil) (A :: M :: nil) 3 2 3 HABCMNPmtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPm3 : rk(A :: M :: N :: P :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPM3 : rk(A :: M :: N :: P :: nil) <= 3).
{
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCMNPMtmp Hcomp Hincl);apply HT.
}

assert(HAMNPM : rk(A :: M :: N :: P ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HAMNPeq HAMNPM4).
assert(HAMNPm : rk(A :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HAMNPeq HAMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MNP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNP requis par la preuve de (?)H1H2H3H4MNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNP requis par la preuve de (?)H1H2H3H4MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNPm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HH1H2H3H4MNPM4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) <= 4).
{
	assert(HH1H2H3H4NMtmp : rk(H1 :: H2 :: H3 :: H4 :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Neq HH1H2H3H4NM4).
	assert(HH1H2H3H4MPeq : rk(H1 :: H2 :: H3 :: H4 :: M :: P :: nil) = 4) by (apply LH1H2H3H4MP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HH1H2H3H4MPMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: P :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MPeq HH1H2H3H4MPM4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: P :: nil) ((H1 :: H2 :: H3 :: H4 :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: P :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4NMtmp HH1H2H3H4MPMtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MNPM : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNPm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNPeq HH1H2H3H4MNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAH1H2H3H4MNP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AH1H2H3H4MNP requis par la preuve de (?)AH1H2H3H4MNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AH1H2H3H4MNP requis par la preuve de (?)AH1H2H3H4MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNPm4 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNPm5 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HAH1H2H3H4MNPM : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) <= 5) by (apply rk_upper_dim).
assert(HAH1H2H3H4MNPm : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HAH1H2H3H4MNPeq HAH1H2H3H4MNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HMNPM2 : rk(M :: N :: P :: nil) <= 2).
{
	assert(HAMNPeq : rk(A :: M :: N :: P :: nil) = 3) by (apply LAMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAMNPMtmp : rk(A :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HAMNPeq HAMNPM3).
	assert(HH1H2H3H4MNPeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) = 4) by (apply LH1H2H3H4MNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HH1H2H3H4MNPMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNPeq HH1H2H3H4MNPM4).
	assert(HAH1H2H3H4MNPeq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) = 5) by (apply LAH1H2H3H4MNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption).
	assert(HAH1H2H3H4MNPmtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4MNPeq HAH1H2H3H4MNPm5).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: M :: N :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) (A :: M :: N :: P :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: P :: H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) ((A :: M :: N :: P :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAH1H2H3H4MNPmtmp;try rewrite HT2 in HAH1H2H3H4MNPmtmp.
	assert(HT := rule_3 (A :: M :: N :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: nil) (M :: N :: P :: nil) 3 4 5 HAMNPMtmp HH1H2H3H4MNPMtmp HAH1H2H3H4MNPmtmp Hincl);apply HT.
}


assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C H1 H2 H3 H4 M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 4 -> 
	 rk(M :: N :: P ::  nil) = 2  .
Proof.

intros A B C H1 H2 H3 H4 M N P 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
.
repeat split.

	apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) ; assumption.
Qed .
