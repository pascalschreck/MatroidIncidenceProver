Load "preamble4D.v".


(* dans constructLemma(), requis par LAM *)
(* dans la couche 0 *)
Lemma LAH1H2H3H4M : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
Lemma LAM : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: M ::  nil) = 2.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AM requis par la preuve de (?)AM pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HAMm2 : rk(A :: M :: nil) >= 2).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HAH1H2H3H4Meq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: nil) = 5) by (apply LAH1H2H3H4M with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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

(* dans la couche 0 *)
Lemma LABH1H2H3H4M : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABH1H2H3H4M requis par la preuve de (?)ABH1H2H3H4M pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABH1H2H3H4M requis par la preuve de (?)ABH1H2H3H4M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4Mm4 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4Mm5 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HABH1H2H3H4MM : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABH1H2H3H4Mm : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M ::  nil) >= 1) by (solve_hyps_min HABH1H2H3H4Meq HABH1H2H3H4Mm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACH1H2H3H4M : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACH1H2H3H4M requis par la preuve de (?)ACH1H2H3H4M pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACH1H2H3H4M requis par la preuve de (?)ACH1H2H3H4M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACH1H2H3H4Mm4 : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACH1H2H3H4Mm5 : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HACH1H2H3H4MM : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M ::  nil) <= 5) by (apply rk_upper_dim).
assert(HACH1H2H3H4Mm : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M ::  nil) >= 1) by (solve_hyps_min HACH1H2H3H4Meq HACH1H2H3H4Mm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMN *)
(* dans la couche 0 *)
Lemma LAH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
Lemma LH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
Lemma LAMN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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
	assert(HH1H2H3H4MNeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 4) by (apply LH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNeq HH1H2H3H4MNM4).
	assert(HAH1H2H3H4MNeq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LAH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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

(* dans constructLemma(), requis par LABMN *)
(* dans la couche 0 *)
Lemma LABH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABH1H2H3H4MN requis par la preuve de (?)ABH1H2H3H4MN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABH1H2H3H4MN requis par la preuve de (?)ABH1H2H3H4MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4MNm4 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4MNm5 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HABH1H2H3H4MNM : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABH1H2H3H4MNm : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) >= 1) by (solve_hyps_min HABH1H2H3H4MNeq HABH1H2H3H4MNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABMN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABMN requis par la preuve de (?)ABMN pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour ABCMN requis par la preuve de (?)ABMN pour la règle 6  *)
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

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABMN requis par la preuve de (?)ABMN pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABM requis par la preuve de (?)ABMN pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABM requis par la preuve de (?)ABM pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HABMm2 : rk(A :: B :: M :: nil) >= 2).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HABH1H2H3H4Meq : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) = 5) by (apply LABH1H2H3H4M with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABH1H2H3H4Mmtmp : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5) by (solve_hyps_min HABH1H2H3H4Meq HABH1H2H3H4Mm5).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: B :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: nil) (A :: B :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil) ((A :: B :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABH1H2H3H4Mmtmp;try rewrite HT2 in HABH1H2H3H4Mmtmp.
	assert(HT := rule_2 (A :: B :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil) (M :: nil) 5 1 4 HABH1H2H3H4Mmtmp HMmtmp HH1H2H3H4MMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABMN requis par la preuve de (?)ABMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N ::  de rang :  3 et 3 	 AiB : A :: B :: M ::  de rang :  2 et 3 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HABMNm2 : rk(A :: B :: M :: N :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNmtmp : rk(A :: B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HABCMNeq HABCMNm3).
	assert(HABMmtmp : rk(A :: B :: M :: nil) >= 2) by (solve_hyps_min HABMeq HABMm2).
	assert(Hincl : incl (A :: B :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: B :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: M :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNmtmp;try rewrite HT2 in HABCMNmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: B :: M :: N :: nil) (A :: B :: M :: nil) 3 2 3 HABCMNmtmp HABMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABMNM3 : rk(A :: B :: M :: N :: nil) <= 3).
{
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: M :: N :: nil) (A :: B :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: M :: N :: nil) (A :: B :: C :: M :: N :: nil) 3 3 HABCMNMtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HABMNm3 : rk(A :: B :: M :: N :: nil) >= 3).
{
	assert(HH1H2H3H4MNeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 4) by (apply LH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNeq HH1H2H3H4MNM4).
	assert(HABH1H2H3H4MNeq : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LABH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABH1H2H3H4MNmtmp : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5) by (solve_hyps_min HABH1H2H3H4MNeq HABH1H2H3H4MNm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (A :: B :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) ((A :: B :: M :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABH1H2H3H4MNmtmp;try rewrite HT2 in HABH1H2H3H4MNmtmp.
	assert(HT := rule_2 (A :: B :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (M :: N :: nil) 5 2 4 HABH1H2H3H4MNmtmp HMNmtmp HH1H2H3H4MNMtmp Hincl);apply HT.
}

assert(HABMNM : rk(A :: B :: M :: N ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HABMNeq HABMNM4).
assert(HABMNm : rk(A :: B :: M :: N ::  nil) >= 1) by (solve_hyps_min HABMNeq HABMNm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACMN *)
(* dans la couche 0 *)
Lemma LACH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACH1H2H3H4MN requis par la preuve de (?)ACH1H2H3H4MN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACH1H2H3H4MN requis par la preuve de (?)ACH1H2H3H4MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACH1H2H3H4MNm4 : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HACH1H2H3H4MNm5 : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HACH1H2H3H4MNM : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HACH1H2H3H4MNm : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) >= 1) by (solve_hyps_min HACH1H2H3H4MNeq HACH1H2H3H4MNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACMN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACMN requis par la preuve de (?)ACMN pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour ABCMN requis par la preuve de (?)ACMN pour la règle 6  *)
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

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACMN requis par la preuve de (?)ACMN pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACM requis par la preuve de (?)ACMN pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACM requis par la preuve de (?)ACM pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HACMm2 : rk(A :: C :: M :: nil) >= 2).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HACH1H2H3H4Meq : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) = 5) by (apply LACH1H2H3H4M with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HACH1H2H3H4Mmtmp : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5) by (solve_hyps_min HACH1H2H3H4Meq HACH1H2H3H4Mm5).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: C :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) (A :: C :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil) ((A :: C :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACH1H2H3H4Mmtmp;try rewrite HT2 in HACH1H2H3H4Mmtmp.
	assert(HT := rule_2 (A :: C :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil) (M :: nil) 5 1 4 HACH1H2H3H4Mmtmp HMmtmp HH1H2H3H4MMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACMN requis par la preuve de (?)ACMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N ::  de rang :  3 et 3 	 AiB : A :: C :: M ::  de rang :  2 et 3 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HACMNm2 : rk(A :: C :: M :: N :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNmtmp : rk(A :: B :: C :: M :: N :: nil) >= 3) by (solve_hyps_min HABCMNeq HABCMNm3).
	assert(HACMmtmp : rk(A :: C :: M :: nil) >= 2) by (solve_hyps_min HACMeq HACMm2).
	assert(Hincl : incl (A :: C :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: C :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: C :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: C :: M :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: C :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNmtmp;try rewrite HT2 in HABCMNmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: C :: M :: N :: nil) (A :: C :: M :: nil) 3 2 3 HABCMNmtmp HACMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HACMNM3 : rk(A :: C :: M :: N :: nil) <= 3).
{
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: M :: N :: nil) (A :: B :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: C :: M :: N :: nil) (A :: B :: C :: M :: N :: nil) 3 3 HABCMNMtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HACMNm3 : rk(A :: C :: M :: N :: nil) >= 3).
{
	assert(HH1H2H3H4MNeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 4) by (apply LH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNeq HH1H2H3H4MNM4).
	assert(HACH1H2H3H4MNeq : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LACH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HACH1H2H3H4MNmtmp : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5) by (solve_hyps_min HACH1H2H3H4MNeq HACH1H2H3H4MNm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: C :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (A :: C :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: M :: N :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) ((A :: C :: M :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACH1H2H3H4MNmtmp;try rewrite HT2 in HACH1H2H3H4MNmtmp.
	assert(HT := rule_2 (A :: C :: M :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (M :: N :: nil) 5 2 4 HACH1H2H3H4MNmtmp HMNmtmp HH1H2H3H4MNMtmp Hincl);apply HT.
}

assert(HACMNM : rk(A :: C :: M :: N ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HACMNeq HACMNM4).
assert(HACMNm : rk(A :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HACMNeq HACMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMN : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
Lemma LABCMP : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: M :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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

(* dans constructLemma(), requis par LMNP *)
(* dans la couche 0 *)
Lemma LH1H2H3H4MNPM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNPM' requis par la preuve de (?)H1H2H3H4MNPM' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNPM' requis par la preuve de (?)H1H2H3H4MNPM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNPM'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNPM'm5 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) >= 5).
{
	assert(HH1H2H3H4Pmtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: nil) >= 5) by (solve_hyps_min HH1H2H3H4Peq HH1H2H3H4Pm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) 5 5 HH1H2H3H4Pmtmp Hcomp Hincl);apply HT.
}

assert(HH1H2H3H4MNPM'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNPM'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNPM'eq HH1H2H3H4MNPM'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LMNP *)
(* dans constructLemma(), requis par LH1H2H3H4MNM' *)
(* dans la couche 0 *)
Lemma LH1H2H3H4MM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: M' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MM' requis par la preuve de (?)H1H2H3H4MM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MM' requis par la preuve de (?)H1H2H3H4MM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MM'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HH1H2H3H4MM'M4 : rk(H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) <= 4).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HH1H2H3H4M'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'eq HH1H2H3H4M'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: M' :: nil) ((H1 :: H2 :: H3 :: H4 :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4MMtmp HH1H2H3H4M'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MM'M : rk(H1 :: H2 :: H3 :: H4 :: M :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MM'm : rk(H1 :: H2 :: H3 :: H4 :: M :: M' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MM'eq HH1H2H3H4MM'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MNM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNM' requis par la preuve de (?)H1H2H3H4MNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNM' requis par la preuve de (?)H1H2H3H4MNM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNM'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HH1H2H3H4MNM'M4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) <= 4).
{
	assert(HH1H2H3H4NMtmp : rk(H1 :: H2 :: H3 :: H4 :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Neq HH1H2H3H4NM4).
	assert(HH1H2H3H4MM'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) = 4) by (apply LH1H2H3H4MM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MM'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MM'eq HH1H2H3H4MM'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) ((H1 :: H2 :: H3 :: H4 :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4NMtmp HH1H2H3H4MM'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MNM'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNM'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNM'eq HH1H2H3H4MNM'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 2  *)
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

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HMNPm3 : rk(M :: N :: P :: nil) >= 3).
{
	assert(HH1H2H3H4MNM'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) = 4) by (apply LH1H2H3H4MNM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNM'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNM'eq HH1H2H3H4MNM'M4).
	assert(HH1H2H3H4MNPM'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) = 5) by (apply LH1H2H3H4MNPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNPM'mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4MNPM'eq HH1H2H3H4MNPM'm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (M :: N :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: P :: M' :: nil) (M :: N :: P :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: P :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) ((M :: N :: P :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HH1H2H3H4MNPM'mtmp;try rewrite HT2 in HH1H2H3H4MNPM'mtmp.
	assert(HT := rule_2 (M :: N :: P :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) (M :: N :: nil) 5 2 4 HH1H2H3H4MNPM'mtmp HMNmtmp HH1H2H3H4MNM'Mtmp Hincl);apply HT.
}

assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMNP *)
(* dans la couche 0 *)
Lemma LABCMNP : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
	assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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
	assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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
Lemma LAMNP : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

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
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPM3 : rk(A :: M :: N :: P :: nil) <= 3).
{
	assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCMNPMtmp Hcomp Hincl);apply HT.
}

assert(HAMNPM : rk(A :: M :: N :: P ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HAMNPeq HAMNPM4).
assert(HAMNPm : rk(A :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HAMNPeq HAMNPm1).
intuition.
Qed.

(* dans constructLemma(), requis par LMNA' *)
(* dans la couche 0 *)
Lemma LH1H2H3H4MNA'M' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNA'M' requis par la preuve de (?)H1H2H3H4MNA'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNA'M' requis par la preuve de (?)H1H2H3H4MNA'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNA'M'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNA'M'm5 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) >= 5).
{
	assert(HH1H2H3H4A'mtmp : rk(H1 :: H2 :: H3 :: H4 :: A' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4A'eq HH1H2H3H4A'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: A' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: A' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) 5 5 HH1H2H3H4A'mtmp Hcomp Hincl);apply HT.
}

assert(HH1H2H3H4MNA'M'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNA'M'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNA'M'eq HH1H2H3H4MNA'M'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNA' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(M :: N :: A' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNA' requis par la preuve de (?)MNA' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNA' requis par la preuve de (?)MNA' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'm2 : rk(M :: N :: A' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(HMNA'm3 : rk(M :: N :: A' :: nil) >= 3).
{
	assert(HH1H2H3H4MNM'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) = 4) by (apply LH1H2H3H4MNM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNM'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNM'eq HH1H2H3H4MNM'M4).
	assert(HH1H2H3H4MNA'M'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) = 5) by (apply LH1H2H3H4MNA'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNA'M'mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4MNA'M'eq HH1H2H3H4MNA'M'm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (M :: N :: A' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: A' :: M' :: nil) (M :: N :: A' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: A' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) ((M :: N :: A' :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HH1H2H3H4MNA'M'mtmp;try rewrite HT2 in HH1H2H3H4MNA'M'mtmp.
	assert(HT := rule_2 (M :: N :: A' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: nil) (M :: N :: nil) 5 2 4 HH1H2H3H4MNA'M'mtmp HMNmtmp HH1H2H3H4MNM'Mtmp Hincl);apply HT.
}

assert(HMNA'M : rk(M :: N :: A' ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HMNA'eq HMNA'M3).
assert(HMNA'm : rk(M :: N :: A' ::  nil) >= 1) by (solve_hyps_min HMNA'eq HMNA'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LPM' *)
(* dans la couche 0 *)
Lemma LH1H2H3H4PM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: P :: M' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4PM' requis par la preuve de (?)H1H2H3H4PM' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4PM' requis par la preuve de (?)H1H2H3H4PM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4PM'm4 : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4PM'm5 : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) >= 5).
{
	assert(HH1H2H3H4Pmtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: nil) >= 5) by (solve_hyps_min HH1H2H3H4Peq HH1H2H3H4Pm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) 5 5 HH1H2H3H4Pmtmp Hcomp Hincl);apply HT.
}

assert(HH1H2H3H4PM'M : rk(H1 :: H2 :: H3 :: H4 :: P :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4PM'm : rk(H1 :: H2 :: H3 :: H4 :: P :: M' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4PM'eq HH1H2H3H4PM'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(P :: M' ::  nil) = 2.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PM' requis par la preuve de (?)PM' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : H1 :: H2 :: H3 :: H4 :: P :: M' ::  de rang :  5 et 5 	 AiB : M' ::  de rang :  1 et 1 	 A : H1 :: H2 :: H3 :: H4 :: M' ::   de rang : 4 et 4 *)
assert(HPM'm2 : rk(P :: M' :: nil) >= 2).
{
	assert(HH1H2H3H4M'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'eq HH1H2H3H4M'M4).
	assert(HH1H2H3H4PM'eq : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) = 5) by (apply LH1H2H3H4PM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4PM'mtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4PM'eq HH1H2H3H4PM'm5).
	assert(HM'mtmp : rk(M' :: nil) >= 1) by (solve_hyps_min HM'eq HM'm1).
	assert(Hincl : incl (M' :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M' :: nil) (P :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: P :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: P :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: P :: M' :: nil) ((H1 :: H2 :: H3 :: H4 :: M' :: nil) ++ (P :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HH1H2H3H4PM'mtmp;try rewrite HT2 in HH1H2H3H4PM'mtmp.
	assert(HT := rule_4 (H1 :: H2 :: H3 :: H4 :: M' :: nil) (P :: M' :: nil) (M' :: nil) 5 1 4 HH1H2H3H4PM'mtmp HM'mtmp HH1H2H3H4M'Mtmp Hincl); apply HT.
}

assert(HPM'M : rk(P :: M' ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max HPM'eq HPM'M2).
assert(HPM'm : rk(P :: M' ::  nil) >= 1) by (solve_hyps_min HPM'eq HPM'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCPM' *)
(* dans la couche 0 *)
Lemma LABCPA'B'C'M' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: P :: A' :: B' :: C' :: M' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCPA'B'C'M' requis par la preuve de (?)ABCPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'm3 : rk(A :: B :: C :: A' :: B' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HABCA'B'm4 : rk(A :: B :: C :: A' :: B' :: nil) >= 4).
{
	assert(HC'Mtmp : rk(C' :: nil) <= 1) by (solve_hyps_max HC'eq HC'M1).
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: A' :: B' :: nil) (C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) ((A :: B :: C :: A' :: B' :: nil) ++ (C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'mtmp;try rewrite HT2 in HABCA'B'C'mtmp.
	assert(HT := rule_2 (A :: B :: C :: A' :: B' :: nil) (C' :: nil) (nil) 5 0 1 HABCA'B'C'mtmp Hmtmp HC'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCPA'B'C'M' requis par la preuve de (?)ABCPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCPA'B'C'M' requis par la preuve de (?)ABCPA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPA'B'C'M'm3 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCPA'B'C'M'm4 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HABCA'B'mtmp : rk(A :: B :: C :: A' :: B' :: nil) >= 4) by (solve_hyps_min HABCA'B'eq HABCA'B'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) 4 4 HABCA'B'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPA'B'C'M'm5 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) >= 5).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) 5 5 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCPA'B'C'M'M : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCPA'B'C'M'm : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' ::  nil) >= 1) by (solve_hyps_min HABCPA'B'C'M'eq HABCPA'B'C'M'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCPM' *)
(* dans la couche 0 *)
Lemma LPA'B'C'M' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(P :: A' :: B' :: C' :: M' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PA'B'C'M' requis par la preuve de (?)PA'B'C'M' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PA'B'C'M' requis par la preuve de (?)PA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour PA'B'C'M' requis par la preuve de (?)PA'B'C'M' pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPA'B'C'M'M4 : rk(P :: A' :: B' :: C' :: M' :: nil) <= 4).
{
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: A' :: B' :: C' :: M' :: nil) ((P :: nil) ++ (A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (A' :: B' :: C' :: M' :: nil) (nil) 1 3 0 HPMtmp HA'B'C'M'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPA'B'C'M'm3 : rk(P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: M' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HPA'B'C'M'M3 : rk(P :: A' :: B' :: C' :: M' :: nil) <= 3).
{
	assert(HPA'B'C'Mtmp : rk(P :: A' :: B' :: C' :: nil) <= 3) by (solve_hyps_max HPA'B'C'eq HPA'B'C'M3).
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (P :: A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: A' :: B' :: C' :: A' :: B' :: C' :: M' :: nil) ((P :: A' :: B' :: C' :: nil) ++ (A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HPA'B'C'Mtmp HA'B'C'M'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPA'B'C'M'M : rk(P :: A' :: B' :: C' :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HPA'B'C'M'm : rk(P :: A' :: B' :: C' :: M' ::  nil) >= 1) by (solve_hyps_min HPA'B'C'M'eq HPA'B'C'M'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCPM' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: P :: M' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCPM' requis par la preuve de (?)ABCPM' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCPM' requis par la preuve de (?)ABCPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCPM' requis par la preuve de (?)ABCPM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPM'm3 : rk(A :: B :: C :: P :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HABCPM'M4 : rk(A :: B :: C :: P :: M' :: nil) <= 4).
{
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: P :: nil) (M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: P :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: M' :: nil) ((A :: B :: C :: P :: nil) ++ (M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: P :: nil) (M' :: nil) (nil) 3 1 0 HABCPMtmp HM'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HABCPM'm4 : rk(A :: B :: C :: P :: M' :: nil) >= 4).
{
	assert(HPA'B'C'M'eq : rk(P :: A' :: B' :: C' :: M' :: nil) = 3) by (apply LPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'M'Mtmp : rk(P :: A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HPA'B'C'M'eq HPA'B'C'M'M3).
	assert(HABCPA'B'C'M'eq : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) = 5) by (apply LABCPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPA'B'C'M'mtmp : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) >= 5) by (solve_hyps_min HABCPA'B'C'M'eq HABCPA'B'C'M'm5).
	assert(HPM'eq : rk(P :: M' :: nil) = 2) by (apply LPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPM'mtmp : rk(P :: M' :: nil) >= 2) by (solve_hyps_min HPM'eq HPM'm2).
	assert(Hincl : incl (P :: M' :: nil) (list_inter (A :: B :: C :: P :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: P :: A' :: B' :: C' :: M' :: nil) (A :: B :: C :: P :: M' :: P :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: M' :: P :: A' :: B' :: C' :: M' :: nil) ((A :: B :: C :: P :: M' :: nil) ++ (P :: A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCPA'B'C'M'mtmp;try rewrite HT2 in HABCPA'B'C'M'mtmp.
	assert(HT := rule_2 (A :: B :: C :: P :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil) (P :: M' :: nil) 5 2 3 HABCPA'B'C'M'mtmp HPM'mtmp HPA'B'C'M'Mtmp Hincl);apply HT.
}

assert(HABCPM'M : rk(A :: B :: C :: P :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCPM'm : rk(A :: B :: C :: P :: M' ::  nil) >= 1) by (solve_hyps_min HABCPM'eq HABCPM'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNPA'B'C'M' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCMNPA'B'C'M' requis par la preuve de (?)ABCMNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCMNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'm3 : rk(A :: B :: C :: A' :: B' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HABCA'B'm4 : rk(A :: B :: C :: A' :: B' :: nil) >= 4).
{
	assert(HC'Mtmp : rk(C' :: nil) <= 1) by (solve_hyps_max HC'eq HC'M1).
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: A' :: B' :: nil) (C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) ((A :: B :: C :: A' :: B' :: nil) ++ (C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'mtmp;try rewrite HT2 in HABCA'B'C'mtmp.
	assert(HT := rule_2 (A :: B :: C :: A' :: B' :: nil) (C' :: nil) (nil) 5 0 1 HABCA'B'C'mtmp Hmtmp HC'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPA'B'C'M' requis par la preuve de (?)ABCMNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPA'B'C'M' requis par la preuve de (?)ABCMNPA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPA'B'C'M'm3 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCMNPA'B'C'M'm4 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HABCA'B'mtmp : rk(A :: B :: C :: A' :: B' :: nil) >= 4) by (solve_hyps_min HABCA'B'eq HABCA'B'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) 4 4 HABCA'B'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPA'B'C'M'm5 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 5).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) 5 5 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCMNPA'B'C'M'M : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCMNPA'B'C'M'm : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' ::  nil) >= 1) by (solve_hyps_min HABCMNPA'B'C'M'eq HABCMNPA'B'C'M'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MN' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MN' requis par la preuve de (?)H1H2H3H4MN' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MN' requis par la preuve de (?)H1H2H3H4MN' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MN'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HH1H2H3H4MN'M4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) <= 4).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HH1H2H3H4N'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4N'eq HH1H2H3H4N'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: H1 :: H2 :: H3 :: H4 :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M :: nil) (H1 :: H2 :: H3 :: H4 :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4MMtmp HH1H2H3H4N'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MN'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MN'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MN'eq HH1H2H3H4MN'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MNN' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNN' requis par la preuve de (?)H1H2H3H4MNN' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNN' requis par la preuve de (?)H1H2H3H4MNN' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNN'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HH1H2H3H4MNN'M4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) <= 4).
{
	assert(HH1H2H3H4NMtmp : rk(H1 :: H2 :: H3 :: H4 :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Neq HH1H2H3H4NM4).
	assert(HH1H2H3H4MN'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) = 4) by (apply LH1H2H3H4MN' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MN'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MN'eq HH1H2H3H4MN'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: N :: H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: N :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: N :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4NMtmp HH1H2H3H4MN'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MNN'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNN'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNN'eq HH1H2H3H4MNN'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPA'B'C'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(P :: A' :: B' :: C' :: N' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PA'B'C'N' requis par la preuve de (?)PA'B'C'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PA'B'C'N' requis par la preuve de (?)PA'B'C'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour PA'B'C'N' requis par la preuve de (?)PA'B'C'N' pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HPA'B'C'N'M4 : rk(P :: A' :: B' :: C' :: N' :: nil) <= 4).
{
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: N' :: nil) (P :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: A' :: B' :: C' :: N' :: nil) ((P :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (A' :: B' :: C' :: N' :: nil) (nil) 1 3 0 HPMtmp HA'B'C'N'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPA'B'C'N'm3 : rk(P :: A' :: B' :: C' :: N' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: N' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HPA'B'C'N'M3 : rk(P :: A' :: B' :: C' :: N' :: nil) <= 3).
{
	assert(HPA'B'C'Mtmp : rk(P :: A' :: B' :: C' :: nil) <= 3) by (solve_hyps_max HPA'B'C'eq HPA'B'C'M3).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (P :: A' :: B' :: C' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: N' :: nil) (P :: A' :: B' :: C' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: A' :: B' :: C' :: A' :: B' :: C' :: N' :: nil) ((P :: A' :: B' :: C' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: A' :: B' :: C' :: nil) (A' :: B' :: C' :: N' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HPA'B'C'Mtmp HA'B'C'N'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPA'B'C'N'M : rk(P :: A' :: B' :: C' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HPA'B'C'N'm : rk(P :: A' :: B' :: C' :: N' ::  nil) >= 1) by (solve_hyps_min HPA'B'C'N'eq HPA'B'C'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4M'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M' :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4M'N' requis par la preuve de (?)H1H2H3H4M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4M'N' requis par la preuve de (?)H1H2H3H4M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4M'N'm4 : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HH1H2H3H4M'N'M4 : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) <= 4).
{
	assert(HH1H2H3H4M'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'eq HH1H2H3H4M'M4).
	assert(HH1H2H3H4N'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4N'eq HH1H2H3H4N'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: H1 :: H2 :: H3 :: H4 :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: H1 :: H2 :: H3 :: H4 :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: M' :: nil) ++ (H1 :: H2 :: H3 :: H4 :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4M'Mtmp HH1H2H3H4N'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4M'N'M : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4M'N'm : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4M'N'eq HH1H2H3H4M'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LH1H2H3H4MNM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4MNM'N' requis par la preuve de (?)H1H2H3H4MNM'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4MNM'N' requis par la preuve de (?)H1H2H3H4MNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4MNM'N'm4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HH1H2H3H4MNM'N'M4 : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) <= 4).
{
	assert(HH1H2H3H4M'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'eq HH1H2H3H4M'M4).
	assert(HH1H2H3H4MNN'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) = 4) by (apply LH1H2H3H4MNN' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNN'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNN'eq HH1H2H3H4MNN'M4).
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: M' :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: H2 :: H3 :: H4 :: M' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: nil) 4 4 4 HH1H2H3H4M'Mtmp HH1H2H3H4MNN'Mtmp HH1H2H3H4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HH1H2H3H4MNM'N'M : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4MNM'N'm : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4MNM'N'eq HH1H2H3H4MNM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAH1H2H3H4MNM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AH1H2H3H4MNM'N' requis par la preuve de (?)AH1H2H3H4MNM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AH1H2H3H4MNM'N' requis par la preuve de (?)AH1H2H3H4MNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNM'N'm4 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAH1H2H3H4MNM'N'm5 : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HAH1H2H3H4MNM'N'M : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HAH1H2H3H4MNM'N'm : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HAH1H2H3H4MNM'N'eq HAH1H2H3H4MNM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LPM'N' *)
(* dans la couche 0 *)
Lemma LH1H2H3H4PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour H1H2H3H4PM'N' requis par la preuve de (?)H1H2H3H4PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour H1H2H3H4PM'N' requis par la preuve de (?)H1H2H3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4PM'N'm4 : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HH1H2H3H4PM'N'm5 : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HH1H2H3H4Pmtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: nil) >= 5) by (solve_hyps_min HH1H2H3H4Peq HH1H2H3H4Pm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: P :: nil) (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 5 5 HH1H2H3H4Pmtmp Hcomp Hincl);apply HT.
}

assert(HH1H2H3H4PM'N'M : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HH1H2H3H4PM'N'm : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HH1H2H3H4PM'N'eq HH1H2H3H4PM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(P :: M' :: N' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PM'N' requis par la preuve de (?)PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PM'N' requis par la preuve de (?)PM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : M' ::  de rang :  1 et 1 	 A : H1 :: H2 :: H3 :: H4 :: M' ::   de rang : 4 et 4 *)
assert(HPM'N'm2 : rk(P :: M' :: N' :: nil) >= 2).
{
	assert(HH1H2H3H4M'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'eq HH1H2H3H4M'M4).
	assert(HH1H2H3H4PM'N'eq : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LH1H2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4PM'N'mtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4PM'N'eq HH1H2H3H4PM'N'm5).
	assert(HM'mtmp : rk(M' :: nil) >= 1) by (solve_hyps_min HM'eq HM'm1).
	assert(Hincl : incl (M' :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M' :: nil) (P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: P :: M' :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: M' :: nil) ++ (P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HH1H2H3H4PM'N'mtmp;try rewrite HT2 in HH1H2H3H4PM'N'mtmp.
	assert(HT := rule_4 (H1 :: H2 :: H3 :: H4 :: M' :: nil) (P :: M' :: N' :: nil) (M' :: nil) 5 1 4 HH1H2H3H4PM'N'mtmp HM'mtmp HH1H2H3H4M'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : M' :: N' ::  de rang :  2 et 2 	 A : H1 :: H2 :: H3 :: H4 :: M' :: N' ::   de rang : 4 et 4 *)
assert(HPM'N'm3 : rk(P :: M' :: N' :: nil) >= 3).
{
	assert(HH1H2H3H4M'N'eq : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) = 4) by (apply LH1H2H3H4M'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4M'N'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4M'N'eq HH1H2H3H4M'N'M4).
	assert(HH1H2H3H4PM'N'eq : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LH1H2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4PM'N'mtmp : rk(H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HH1H2H3H4PM'N'eq HH1H2H3H4PM'N'm5).
	assert(HM'N'mtmp : rk(M' :: N' :: nil) >= 2) by (solve_hyps_min HM'N'eq HM'N'm2).
	assert(Hincl : incl (M' :: N' :: nil) (list_inter (H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) (P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M' :: N' :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: H2 :: H3 :: H4 :: M' :: N' :: P :: M' :: N' :: nil) ((H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) ++ (P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HH1H2H3H4PM'N'mtmp;try rewrite HT2 in HH1H2H3H4PM'N'mtmp.
	assert(HT := rule_4 (H1 :: H2 :: H3 :: H4 :: M' :: N' :: nil) (P :: M' :: N' :: nil) (M' :: N' :: nil) 5 2 4 HH1H2H3H4PM'N'mtmp HM'N'mtmp HH1H2H3H4M'N'Mtmp Hincl); apply HT.
}

assert(HPM'N'M : rk(P :: M' :: N' ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HPM'N'eq HPM'N'M3).
assert(HPM'N'm : rk(P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HPM'N'eq HPM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCPM'N' *)
(* dans la couche 0 *)
Lemma LABCPA'B'C'M'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCPA'B'C'M'N' requis par la preuve de (?)ABCPA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCPA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'm3 : rk(A :: B :: C :: A' :: B' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HABCA'B'm4 : rk(A :: B :: C :: A' :: B' :: nil) >= 4).
{
	assert(HC'Mtmp : rk(C' :: nil) <= 1) by (solve_hyps_max HC'eq HC'M1).
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: A' :: B' :: nil) (C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A' :: B' :: C' :: nil) ((A :: B :: C :: A' :: B' :: nil) ++ (C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'mtmp;try rewrite HT2 in HABCA'B'C'mtmp.
	assert(HT := rule_2 (A :: B :: C :: A' :: B' :: nil) (C' :: nil) (nil) 5 0 1 HABCA'B'C'mtmp Hmtmp HC'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCPA'B'C'M'N' requis par la preuve de (?)ABCPA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCPA'B'C'M'N' requis par la preuve de (?)ABCPA'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPA'B'C'M'N'm3 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCPA'B'C'M'N'm4 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) >= 4).
{
	assert(HABCA'B'mtmp : rk(A :: B :: C :: A' :: B' :: nil) >= 4) by (solve_hyps_min HABCA'B'eq HABCA'B'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) 4 4 HABCA'B'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPA'B'C'M'N'm5 : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) >= 5).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) 5 5 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCPA'B'C'M'N'M : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCPA'B'C'M'N'm : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCPA'B'C'M'N'eq HABCPA'B'C'M'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCPM'N' *)
(* dans la couche 0 *)
Lemma LPA'B'C'M'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(P :: A' :: B' :: C' :: M' :: N' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PA'B'C'M'N' requis par la preuve de (?)PA'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour PA'B'C'M'N' requis par la preuve de (?)PA'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour PA'B'C'M'N' requis par la preuve de (?)PA'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HPA'B'C'M'N'm3 : rk(P :: A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (P :: A' :: B' :: C' :: M' :: N' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HPA'B'C'M'N'M4 : rk(P :: A' :: B' :: C' :: M' :: N' :: nil) <= 4).
{
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(HPA'B'C'N'eq : rk(P :: A' :: B' :: C' :: N' :: nil) = 3) by (apply LPA'B'C'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'N'Mtmp : rk(P :: A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HPA'B'C'N'eq HPA'B'C'N'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M' :: nil) (P :: A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: M' :: N' :: nil) (M' :: P :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M' :: P :: A' :: B' :: C' :: N' :: nil) ((M' :: nil) ++ (P :: A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M' :: nil) (P :: A' :: B' :: C' :: N' :: nil) (nil) 1 3 0 HM'Mtmp HPA'B'C'N'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HPA'B'C'M'N'M3 : rk(P :: A' :: B' :: C' :: M' :: N' :: nil) <= 3).
{
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(HPA'B'C'N'eq : rk(P :: A' :: B' :: C' :: N' :: nil) = 3) by (apply LPA'B'C'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'N'Mtmp : rk(P :: A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HPA'B'C'N'eq HPA'B'C'N'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: A' :: B' :: C' :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: N' :: nil) ((A' :: B' :: C' :: M' :: nil) ++ (P :: A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: N' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'M'Mtmp HPA'B'C'N'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HPA'B'C'M'N'M : rk(P :: A' :: B' :: C' :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HPA'B'C'M'N'm : rk(P :: A' :: B' :: C' :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HPA'B'C'M'N'eq HPA'B'C'M'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCPM'N' requis par la preuve de (?)ABCPM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCPM'N' requis par la preuve de (?)ABCPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCPM'N' requis par la preuve de (?)ABCPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCPM'N'm3 : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCPM'N'm4 : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HABCPM'N'm5 : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5).
{
	assert(HPA'B'C'M'N'eq : rk(P :: A' :: B' :: C' :: M' :: N' :: nil) = 3) by (apply LPA'B'C'M'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'M'N'Mtmp : rk(P :: A' :: B' :: C' :: M' :: N' :: nil) <= 3) by (solve_hyps_max HPA'B'C'M'N'eq HPA'B'C'M'N'M3).
	assert(HABCPA'B'C'M'N'eq : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) = 5) by (apply LABCPA'B'C'M'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPA'B'C'M'N'mtmp : rk(A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPA'B'C'M'N'eq HABCPA'B'C'M'N'm5).
	assert(HPM'N'eq : rk(P :: M' :: N' :: nil) = 3) by (apply LPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPM'N'mtmp : rk(P :: M' :: N' :: nil) >= 3) by (solve_hyps_min HPM'N'eq HPM'N'm3).
	assert(Hincl : incl (P :: M' :: N' :: nil) (list_inter (A :: B :: C :: P :: M' :: N' :: nil) (P :: A' :: B' :: C' :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: P :: A' :: B' :: C' :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: P :: A' :: B' :: C' :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: M' :: N' :: P :: A' :: B' :: C' :: M' :: N' :: nil) ((A :: B :: C :: P :: M' :: N' :: nil) ++ (P :: A' :: B' :: C' :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCPA'B'C'M'N'mtmp;try rewrite HT2 in HABCPA'B'C'M'N'mtmp.
	assert(HT := rule_2 (A :: B :: C :: P :: M' :: N' :: nil) (P :: A' :: B' :: C' :: M' :: N' :: nil) (P :: M' :: N' :: nil) 5 3 3 HABCPA'B'C'M'N'mtmp HPM'N'mtmp HPA'B'C'M'N'Mtmp Hincl);apply HT.
}

assert(HABCPM'N'M : rk(A :: B :: C :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCPM'N'm : rk(A :: B :: C :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCH1PM'N' *)
(* dans la couche 0 *)
Lemma LABCH1H2H3H4PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2H3H4PM'N' requis par la preuve de (?)ABCH1H2H3H4PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2H3H4PM'N' requis par la preuve de (?)ABCH1H2H3H4PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2H3H4PM'N' requis par la preuve de (?)ABCH1H2H3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4PM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4PM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4PM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HABCH1H2H3H4PM'N'M : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH1H2H3H4PM'N'm : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH1H2H3H4PM'N'eq HABCH1H2H3H4PM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCH1PM'N' *)
(* dans la couche 0 *)
Lemma LABCH1PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H1 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH1PM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCH1M requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1M requis par la preuve de (?)ABCH1M pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1M requis par la preuve de (?)ABCH1M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1Mm3 : rk(A :: B :: C :: H1 :: M :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: M :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCH1MM4 : rk(A :: B :: C :: H1 :: M :: nil) <= 4).
{
	assert(HH1Mtmp : rk(H1 :: nil) <= 1) by (solve_hyps_max HH1eq HH1M1).
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (H1 :: nil) (A :: B :: C :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: M :: nil) (H1 :: A :: B :: C :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: A :: B :: C :: M :: nil) ((H1 :: nil) ++ (A :: B :: C :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: nil) (A :: B :: C :: M :: nil) (nil) 1 3 0 HH1Mtmp HABCMMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH2H3H4PM'N'm3 : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: B :: C ::  de rang :  3 et 3 	 A : A :: B :: C :: H1 :: M ::   de rang : 3 et 4 *)
assert(HABCH2H3H4PM'N'm4 : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCH1MMtmp : rk(A :: B :: C :: H1 :: M :: nil) <= 4) by (solve_hyps_max HABCH1Meq HABCH1MM4).
	assert(HABCH1H2H3H4MPM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2H3H4MPM'N'eq HABCH1H2H3H4MPM'N'm5).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: H1 :: M :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: M :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: M :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: M :: nil) ++ (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2H3H4MPM'N'mtmp;try rewrite HT2 in HABCH1H2H3H4MPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: H1 :: M :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: nil) 5 3 4 HABCH1H2H3H4MPM'N'mtmp HABCmtmp HABCH1MMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1PM'N' requis par la preuve de (?)ABCH1PM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1PM'N' requis par la preuve de (?)ABCH1PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1PM'N' requis par la preuve de (?)ABCH1PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1PM'N'm3 : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH1PM'N'm4 : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HABCH1PM'N'm5 : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH2H3H4PM'N'Mtmp : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH2H3H4PM'N'eq HABCH2H3H4PM'N'M5).
	assert(HABCH1H2H3H4PM'N'eq : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1H2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1H2H3H4PM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2H3H4PM'N'eq HABCH1H2H3H4PM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: P :: M' :: N' :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2H3H4PM'N'mtmp;try rewrite HT2 in HABCH1H2H3H4PM'N'mtmp.
	assert(HT := rule_2 (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH1H2H3H4PM'N'mtmp HABCPM'N'mtmp HABCH2H3H4PM'N'Mtmp Hincl);apply HT.
}

assert(HABCH1PM'N'M : rk(A :: B :: C :: H1 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH1PM'N'm : rk(A :: B :: C :: H1 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH1PM'N'eq HABCH1PM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCH2PM'N' *)
(* dans la couche 0 *)
Lemma LABCH2H3H4PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCH1M requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1M requis par la preuve de (?)ABCH1M pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1M requis par la preuve de (?)ABCH1M pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1Mm3 : rk(A :: B :: C :: H1 :: M :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: M :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HABCH1MM4 : rk(A :: B :: C :: H1 :: M :: nil) <= 4).
{
	assert(HH1Mtmp : rk(H1 :: nil) <= 1) by (solve_hyps_max HH1eq HH1M1).
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (H1 :: nil) (A :: B :: C :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: M :: nil) (H1 :: A :: B :: C :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (H1 :: A :: B :: C :: M :: nil) ((H1 :: nil) ++ (A :: B :: C :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (H1 :: nil) (A :: B :: C :: M :: nil) (nil) 1 3 0 HH1Mtmp HABCMMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH2H3H4PM'N' requis par la preuve de (?)ABCH2H3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH2H3H4PM'N'm3 : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et 5*)
(* ensembles concernés AUB : A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: B :: C ::  de rang :  3 et 3 	 A : A :: B :: C :: H1 :: M ::   de rang : 3 et 4 *)
assert(HABCH2H3H4PM'N'm4 : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCH1MMtmp : rk(A :: B :: C :: H1 :: M :: nil) <= 4) by (solve_hyps_max HABCH1Meq HABCH1MM4).
	assert(HABCH1H2H3H4MPM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2H3H4MPM'N'eq HABCH1H2H3H4MPM'N'm5).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: H1 :: M :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: M :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: M :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: M :: nil) ++ (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2H3H4MPM'N'mtmp;try rewrite HT2 in HABCH1H2H3H4MPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: H1 :: M :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: nil) 5 3 4 HABCH1H2H3H4MPM'N'mtmp HABCmtmp HABCH1MMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: B :: C :: P :: M' :: N' ::  de rang :  5 et 5 	 A : A :: B :: C :: H1 :: P :: M' :: N' ::   de rang : 5 et 5 *)
assert(HABCH2H3H4PM'N'm5 : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH1PM'N'eq : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1PM'N'Mtmp : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH1PM'N'eq HABCH1PM'N'M5).
	assert(HABCH1H2H3H4PM'N'eq : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1H2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1H2H3H4PM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2H3H4PM'N'eq HABCH1H2H3H4PM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: P :: M' :: N' :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: P :: M' :: N' :: A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2H3H4PM'N'mtmp;try rewrite HT2 in HABCH1H2H3H4PM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH1H2H3H4PM'N'mtmp HABCPM'N'mtmp HABCH1PM'N'Mtmp Hincl); apply HT.
}

assert(HABCH2H3H4PM'N'M : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH2H3H4PM'N'm : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH2H3H4PM'N'eq HABCH2H3H4PM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCH2PM'N' *)
(* dans la couche 0 *)
Lemma LABCH2PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H2 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH2PM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH3H4PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH3H4PM'N'm3 : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH3H4PM'N'm4 : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH2PM'N' requis par la preuve de (?)ABCH2PM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH2PM'N' requis par la preuve de (?)ABCH2PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH2PM'N' requis par la preuve de (?)ABCH2PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH2PM'N'm3 : rk(A :: B :: C :: H2 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH2PM'N'm4 : rk(A :: B :: C :: H2 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HABCH2PM'N'm5 : rk(A :: B :: C :: H2 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH3H4PM'N'Mtmp : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH3H4PM'N'eq HABCH3H4PM'N'M5).
	assert(HABCH2H3H4PM'N'eq : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH2H3H4PM'N'mtmp : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH2H3H4PM'N'eq HABCH2H3H4PM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H2 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH2H3H4PM'N'mtmp;try rewrite HT2 in HABCH2H3H4PM'N'mtmp.
	assert(HT := rule_2 (A :: B :: C :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH2H3H4PM'N'mtmp HABCPM'N'mtmp HABCH3H4PM'N'Mtmp Hincl);apply HT.
}

assert(HABCH2PM'N'M : rk(A :: B :: C :: H2 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH2PM'N'm : rk(A :: B :: C :: H2 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH2PM'N'eq HABCH2PM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCH1H2PM'N' *)
(* dans la couche 0 *)
Lemma LABCH3H4PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH3H4PM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH3H4PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH3H4PM'N' requis par la preuve de (?)ABCH3H4PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH3H4PM'N'm3 : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH3H4PM'N'm4 : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: B :: C :: P :: M' :: N' ::  de rang :  5 et 5 	 A : A :: B :: C :: H2 :: P :: M' :: N' ::   de rang : 5 et 5 *)
assert(HABCH3H4PM'N'm5 : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH2PM'N'eq : rk(A :: B :: C :: H2 :: P :: M' :: N' :: nil) = 5) by (apply LABCH2PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH2PM'N'Mtmp : rk(A :: B :: C :: H2 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH2PM'N'eq HABCH2PM'N'M5).
	assert(HABCH2H3H4PM'N'eq : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH2H3H4PM'N'mtmp : rk(A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH2H3H4PM'N'eq HABCH2H3H4PM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H2 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH2H3H4PM'N'mtmp;try rewrite HT2 in HABCH2H3H4PM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH2H3H4PM'N'mtmp HABCPM'N'mtmp HABCH2PM'N'Mtmp Hincl); apply HT.
}

assert(HABCH3H4PM'N'M : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH3H4PM'N'm : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH3H4PM'N'eq HABCH3H4PM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCH1H2PM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2PM'N' requis par la preuve de (?)ABCH1H2PM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2PM'N' requis par la preuve de (?)ABCH1H2PM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2PM'N' requis par la preuve de (?)ABCH1H2PM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2PM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH1H2PM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HABCH1H2PM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH3H4PM'N'eq : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH3H4PM'N'Mtmp : rk(A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH3H4PM'N'eq HABCH3H4PM'N'M5).
	assert(HABCH1H2H3H4PM'N'eq : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1H2H3H4PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1H2H3H4PM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2H3H4PM'N'eq HABCH1H2H3H4PM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2H3H4PM'N'mtmp;try rewrite HT2 in HABCH1H2H3H4PM'N'mtmp.
	assert(HT := rule_2 (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: H3 :: H4 :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH1H2H3H4PM'N'mtmp HABCPM'N'mtmp HABCH3H4PM'N'Mtmp Hincl);apply HT.
}

assert(HABCH1H2PM'N'M : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH1H2PM'N'm : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH1H2PM'N'eq HABCH1H2PM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCH1H2H3H4MPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2H3H4MPM'N' requis par la preuve de (?)ABCH1H2H3H4MPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2H3H4MPM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HABCH1H2H3H4MPM'N'M : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH1H2H3H4MPM'N'm : rk(A :: B :: C :: H1 :: H2 :: H3 :: H4 :: M :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH1H2H3H4MPM'N'eq HABCH1H2H3H4MPM'N'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAMNPM'N' *)
(* dans constructLemma(), requis par LACMNPM'N' *)
(* dans constructLemma(), requis par LABCMNPM'N' *)
(* dans la couche 0 *)
Lemma LABCH1H2MNPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCH1H2MNPM'N' requis par la preuve de (?)ABCH1H2MNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCH1H2MNPM'N' requis par la preuve de (?)ABCH1H2MNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCH1H2MNPM'N' requis par la preuve de (?)ABCH1H2MNPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCH1H2MNPM'N'm3 : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH1H2MNPM'N'm4 : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCH1H2MNPM'N'm5 : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH1PM'N'eq : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1PM'N'mtmp : rk(A :: B :: C :: H1 :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1PM'N'eq HABCH1PM'N'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: H1 :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) 5 5 HABCH1PM'N'mtmp Hcomp Hincl);apply HT.
}

assert(HABCH1H2MNPM'N'M : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCH1H2MNPM'N'm : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCH1H2MNPM'N'eq HABCH1H2MNPM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: B :: C :: M :: N :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ABCMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ABCMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ABCMNPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'N'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCMNPM'N'm4 : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 4).
{
	assert(HABCPM'eq : rk(A :: B :: C :: P :: M' :: nil) = 4) by (apply LABCPM' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'mtmp : rk(A :: B :: C :: P :: M' :: nil) >= 4) by (solve_hyps_min HABCPM'eq HABCPM'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: P :: M' :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) 4 4 HABCPM'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: B :: C :: P :: M' :: N' ::  de rang :  5 et 5 	 A : A :: B :: C :: H1 :: H2 :: P :: M' :: N' ::   de rang : 5 et 5 *)
assert(HABCMNPM'N'm5 : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABCH1H2PM'N'eq : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) = 5) by (apply LABCH1H2PM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1H2PM'N'Mtmp : rk(A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) <= 5) by (solve_hyps_max HABCH1H2PM'N'eq HABCH1H2PM'N'M5).
	assert(HABCH1H2MNPM'N'eq : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) = 5) by (apply LABCH1H2MNPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCH1H2MNPM'N'mtmp : rk(A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCH1H2MNPM'N'eq HABCH1H2MNPM'N'm5).
	assert(HABCPM'N'eq : rk(A :: B :: C :: P :: M' :: N' :: nil) = 5) by (apply LABCPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCPM'N'mtmp : rk(A :: B :: C :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCPM'N'eq HABCPM'N'm5).
	assert(Hincl : incl (A :: B :: C :: P :: M' :: N' :: nil) (list_inter (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: H1 :: H2 :: M :: N :: P :: M' :: N' :: nil) (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: A :: B :: C :: M :: N :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: A :: B :: C :: M :: N :: P :: M' :: N' :: nil) ((A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) ++ (A :: B :: C :: M :: N :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCH1H2MNPM'N'mtmp;try rewrite HT2 in HABCH1H2MNPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: H1 :: H2 :: P :: M' :: N' :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) (A :: B :: C :: P :: M' :: N' :: nil) 5 5 5 HABCH1H2MNPM'N'mtmp HABCPM'N'mtmp HABCH1H2PM'N'Mtmp Hincl); apply HT.
}

assert(HABCMNPM'N'M : rk(A :: B :: C :: M :: N :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCMNPM'N'm : rk(A :: B :: C :: M :: N :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HABCMNPM'N'eq HABCMNPM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACMNPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: C :: M :: N :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACMNPM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour MNM'N' requis par la preuve de (?)AMNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNPM' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMM'm3 : rk(A :: B :: C :: M :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HABCMM'M4 : rk(A :: B :: C :: M :: M' :: nil) <= 4).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: M :: nil) (M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: M :: nil) ++ (M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (M' :: nil) (nil) 3 1 0 HABCMMtmp HM'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNM'm3 : rk(A :: B :: C :: M :: N :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNM'M4 : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4).
{
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCMM'Mtmp : rk(A :: B :: C :: M :: M' :: nil) <= 4) by (solve_hyps_max HABCMM'eq HABCMM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCNMtmp HABCMM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNPM'M4 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4).
{
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HABCMNM'Mtmp : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4) by (solve_hyps_max HABCMNM'eq HABCMNM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: nil) (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil) ((A :: B :: C :: P :: nil) ++ (A :: B :: C :: M :: N :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCPMtmp HABCMNM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)ABCMNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPA'B'C'm3 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNPA'B'C'm2 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPA'B'C'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HABCMNPA'B'C'eq HABCMNPA'B'C'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'mtmp;try rewrite HT2 in HABCMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: nil) 3 2 3 HABCMNPA'B'C'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPA'B'C'm3 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'm2 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : M :: N :: P ::  de rang :  3 et 3 	 A : A :: M :: N :: P ::   de rang : 3 et 3 *)
assert(HMNPA'B'C'm3 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNPeq : rk(A :: M :: N :: P :: nil) = 3) by (apply LAMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNPMtmp : rk(A :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HAMNPeq HAMNPM3).
	assert(HAMNPA'B'C'mtmp : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HAMNPA'B'C'eq HAMNPA'B'C'm3).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: M :: N :: P :: nil) ++ (M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAMNPA'B'C'mtmp;try rewrite HT2 in HAMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: nil) 3 3 3 HAMNPA'B'C'mtmp HMNPmtmp HAMNPMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HMNPA'B'C'm4 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4).
{
	assert(HABCMNPM'Mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4) by (solve_hyps_max HABCMNPM'eq HABCMNPM'M4).
	assert(HABCMNPA'B'C'M'eq : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) = 5) by (apply LABCMNPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCMNPA'B'C'M'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 5) by (solve_hyps_min HABCMNPA'B'C'M'eq HABCMNPA'B'C'M'm5).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil) ((M :: N :: P :: A' :: B' :: C' :: nil) ++ (A :: B :: C :: M :: N :: P :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'M'mtmp;try rewrite HT2 in HABCMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) (M :: N :: P :: nil) 5 3 4 HABCMNPA'B'C'M'mtmp HMNPmtmp HABCMNPM'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'M'm2 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNPA'B'C'M'm3 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 3 3 HMNPmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNPA'B'C'M'm4 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HMNPA'B'C'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'eq HMNPA'B'C'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 4 4 HMNPA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 4*)
assert(HMNA'B'C'M'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HPA'B'C'M'eq : rk(P :: A' :: B' :: C' :: M' :: nil) = 3) by (apply LPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'M'Mtmp : rk(P :: A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HPA'B'C'M'eq HPA'B'C'M'M3).
	assert(HMNPA'B'C'M'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'M'eq HMNPA'B'C'M'm4).
	assert(HA'B'C'M'mtmp : rk(A' :: B' :: C' :: M' :: nil) >= 3) by (solve_hyps_min HA'B'C'M'eq HA'B'C'M'm3).
	assert(Hincl : incl (A' :: B' :: C' :: M' :: nil) (list_inter (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil) ((M :: N :: A' :: B' :: C' :: M' :: nil) ++ (P :: A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNPA'B'C'M'mtmp;try rewrite HT2 in HMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: M' :: nil) 4 3 3 HMNPA'B'C'M'mtmp HA'B'C'M'mtmp HPA'B'C'M'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'N'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'N'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNA'B'C'M'N'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4).
{
	assert(HMNA'B'C'M'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'eq HMNA'B'C'M'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 4 4 HMNA'B'C'M'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour A'B'C'M'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'M'N'm3 : rk(A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA'B'C'M'N'M4 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 4).
{
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M' :: A' :: B' :: C' :: N' :: nil) ((M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M' :: nil) (A' :: B' :: C' :: N' :: nil) (nil) 1 3 0 HM'Mtmp HA'B'C'N'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'M'N'M3 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3).
{
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil) ((A' :: B' :: C' :: M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'M'Mtmp HA'B'C'N'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNM'N'm2 : rk(M :: N :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 5*)
assert(HMNM'N'm3 : rk(M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'M'N'Mtmp : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'N'eq HA'B'C'M'N'M3).
	assert(HMNA'B'C'M'N'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'N'eq HMNA'B'C'M'N'm4).
	assert(HM'N'mtmp : rk(M' :: N' :: nil) >= 2) by (solve_hyps_min HM'N'eq HM'N'm2).
	assert(Hincl : incl (M' :: N' :: nil) (list_inter (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil) ((M :: N :: M' :: N' :: nil) ++ (A' :: B' :: C' :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNA'B'C'M'N'mtmp;try rewrite HT2 in HMNA'B'C'M'N'mtmp.
	assert(HT := rule_2 (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) (M' :: N' :: nil) 4 2 3 HMNA'B'C'M'N'mtmp HM'N'mtmp HA'B'C'M'N'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNM'N' requis par la preuve de (?)ABCMNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNM'N'm3 : rk(A :: B :: C :: M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: M' :: N' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNM'N'm2 : rk(A :: M :: N :: M' :: N' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNM'N'mtmp : rk(A :: B :: C :: M :: N :: M' :: N' :: nil) >= 3) by (solve_hyps_min HABCMNM'N'eq HABCMNM'N'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: M' :: N' :: nil) (A :: B :: C :: M :: A :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: M' :: N' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNM'N'mtmp;try rewrite HT2 in HABCMNM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: M' :: N' :: nil) (A :: M :: nil) 3 2 3 HABCMNM'N'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNM'N'm3 : rk(A :: M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: M' :: N' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 5 et 4*)
assert(HAMNM'N'm4 : rk(A :: M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4MNM'N'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) = 4) by (apply LH1H2H3H4MNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNM'N'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNM'N'eq HH1H2H3H4MNM'N'M4).
	assert(HAH1H2H3H4MNM'N'eq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) = 5) by (apply LAH1H2H3H4MNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAH1H2H3H4MNM'N'mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4MNM'N'eq HAH1H2H3H4MNM'N'm5).
	assert(HMNM'N'mtmp : rk(M :: N :: M' :: N' :: nil) >= 3) by (solve_hyps_min HMNM'N'eq HMNM'N'm3).
	assert(Hincl : incl (M :: N :: M' :: N' :: nil) (list_inter (A :: M :: N :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) (A :: M :: N :: M' :: N' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: M' :: N' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) ((A :: M :: N :: M' :: N' :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAH1H2H3H4MNM'N'mtmp;try rewrite HT2 in HAH1H2H3H4MNM'N'mtmp.
	assert(HT := rule_2 (A :: M :: N :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) (M :: N :: M' :: N' :: nil) 5 3 4 HAH1H2H3H4MNM'N'mtmp HMNM'N'mtmp HH1H2H3H4MNM'N'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ACMNPM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACMNPM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ABCMNPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'N'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACM requis par la preuve de (?)ACMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACM requis par la preuve de (?)ACM pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HACMm2 : rk(A :: C :: M :: nil) >= 2).
{
	assert(HH1H2H3H4MMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: nil) <= 4) by (solve_hyps_max HH1H2H3H4Meq HH1H2H3H4MM4).
	assert(HACH1H2H3H4Meq : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) = 5) by (apply LACH1H2H3H4M with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HACH1H2H3H4Mmtmp : rk(A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) >= 5) by (solve_hyps_min HACH1H2H3H4Meq HACH1H2H3H4Mm5).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: C :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: H1 :: H2 :: H3 :: H4 :: M :: nil) (A :: C :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: M :: H1 :: H2 :: H3 :: H4 :: M :: nil) ((A :: C :: M :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACH1H2H3H4Mmtmp;try rewrite HT2 in HACH1H2H3H4Mmtmp.
	assert(HT := rule_2 (A :: C :: M :: nil) (H1 :: H2 :: H3 :: H4 :: M :: nil) (M :: nil) 5 1 4 HACH1H2H3H4Mmtmp HMmtmp HH1H2H3H4MMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACMNPM'N' requis par la preuve de (?)ACMNPM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: M' :: N' ::  de rang :  3 et 5 	 AiB : A :: C :: M ::  de rang :  2 et 3 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HACMNPM'N'm2 : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPM'N'mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 3) by (solve_hyps_min HABCMNPM'N'eq HABCMNPM'N'm3).
	assert(HACMmtmp : rk(A :: C :: M :: nil) >= 2) by (solve_hyps_min HACMeq HACMm2).
	assert(Hincl : incl (A :: C :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) (A :: B :: C :: M :: A :: C :: M :: N :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: C :: M :: N :: P :: M' :: N' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: C :: M :: N :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPM'N'mtmp;try rewrite HT2 in HABCMNPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil) (A :: C :: M :: nil) 3 2 3 HABCMNPM'N'mtmp HACMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACMNPM'N'm3 : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HACMNPM'N'm4 : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) >= 4).
{
	assert(HAMNM'N'mtmp : rk(A :: M :: N :: M' :: N' :: nil) >= 4) by (solve_hyps_min HAMNM'N'eq HAMNM'N'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: M' :: N' :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: M' :: N' :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil) 4 4 HAMNM'N'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: M :: N ::  de rang :  3 et 3 	 A : A :: B :: M :: N ::   de rang : 3 et 3 *)
assert(HACMNPM'N'm5 : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) >= 5).
{
	assert(HABMNeq : rk(A :: B :: M :: N :: nil) = 3) by (apply LABMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABMNMtmp : rk(A :: B :: M :: N :: nil) <= 3) by (solve_hyps_max HABMNeq HABMNM3).
	assert(HABCMNPM'N'eq : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) = 5) by (apply LABCMNPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCMNPM'N'mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABCMNPM'N'eq HABCMNPM'N'm5).
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hincl : incl (A :: M :: N :: nil) (list_inter (A :: B :: M :: N :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) (A :: B :: M :: N :: A :: C :: M :: N :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: N :: A :: C :: M :: N :: P :: M' :: N' :: nil) ((A :: B :: M :: N :: nil) ++ (A :: C :: M :: N :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPM'N'mtmp;try rewrite HT2 in HABCMNPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: M :: N :: nil) (A :: C :: M :: N :: P :: M' :: N' :: nil) (A :: M :: N :: nil) 5 3 3 HABCMNPM'N'mtmp HAMNmtmp HABMNMtmp Hincl); apply HT.
}

assert(HACMNPM'N'M : rk(A :: C :: M :: N :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HACMNPM'N'm : rk(A :: C :: M :: N :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HACMNPM'N'eq HACMNPM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAMNPM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A :: M :: N :: P :: M' :: N' ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AMNPM'N' requis par la preuve de (?)AMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour MNM'N' requis par la preuve de (?)AMNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNPM' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMM'm3 : rk(A :: B :: C :: M :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HABCMM'M4 : rk(A :: B :: C :: M :: M' :: nil) <= 4).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: M :: nil) (M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: M :: nil) ++ (M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (M' :: nil) (nil) 3 1 0 HABCMMtmp HM'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNM'm3 : rk(A :: B :: C :: M :: N :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNM'M4 : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4).
{
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCMM'Mtmp : rk(A :: B :: C :: M :: M' :: nil) <= 4) by (solve_hyps_max HABCMM'eq HABCMM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCNMtmp HABCMM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNPM'M4 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4).
{
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HABCMNM'Mtmp : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4) by (solve_hyps_max HABCMNM'eq HABCMNM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: nil) (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil) ((A :: B :: C :: P :: nil) ++ (A :: B :: C :: M :: N :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCPMtmp HABCMNM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)ABCMNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPA'B'C'm3 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNPA'B'C'm2 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPA'B'C'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HABCMNPA'B'C'eq HABCMNPA'B'C'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'mtmp;try rewrite HT2 in HABCMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: nil) 3 2 3 HABCMNPA'B'C'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPA'B'C'm3 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'm2 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : M :: N :: P ::  de rang :  3 et 3 	 A : A :: M :: N :: P ::   de rang : 3 et 3 *)
assert(HMNPA'B'C'm3 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNPeq : rk(A :: M :: N :: P :: nil) = 3) by (apply LAMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNPMtmp : rk(A :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HAMNPeq HAMNPM3).
	assert(HAMNPA'B'C'mtmp : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HAMNPA'B'C'eq HAMNPA'B'C'm3).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: M :: N :: P :: nil) ++ (M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAMNPA'B'C'mtmp;try rewrite HT2 in HAMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: nil) 3 3 3 HAMNPA'B'C'mtmp HMNPmtmp HAMNPMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HMNPA'B'C'm4 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4).
{
	assert(HABCMNPM'Mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4) by (solve_hyps_max HABCMNPM'eq HABCMNPM'M4).
	assert(HABCMNPA'B'C'M'eq : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) = 5) by (apply LABCMNPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCMNPA'B'C'M'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 5) by (solve_hyps_min HABCMNPA'B'C'M'eq HABCMNPA'B'C'M'm5).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil) ((M :: N :: P :: A' :: B' :: C' :: nil) ++ (A :: B :: C :: M :: N :: P :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'M'mtmp;try rewrite HT2 in HABCMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) (M :: N :: P :: nil) 5 3 4 HABCMNPA'B'C'M'mtmp HMNPmtmp HABCMNPM'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'M'm2 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNPA'B'C'M'm3 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 3 3 HMNPmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNPA'B'C'M'm4 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HMNPA'B'C'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'eq HMNPA'B'C'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 4 4 HMNPA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 4*)
assert(HMNA'B'C'M'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HPA'B'C'M'eq : rk(P :: A' :: B' :: C' :: M' :: nil) = 3) by (apply LPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'M'Mtmp : rk(P :: A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HPA'B'C'M'eq HPA'B'C'M'M3).
	assert(HMNPA'B'C'M'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'M'eq HMNPA'B'C'M'm4).
	assert(HA'B'C'M'mtmp : rk(A' :: B' :: C' :: M' :: nil) >= 3) by (solve_hyps_min HA'B'C'M'eq HA'B'C'M'm3).
	assert(Hincl : incl (A' :: B' :: C' :: M' :: nil) (list_inter (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil) ((M :: N :: A' :: B' :: C' :: M' :: nil) ++ (P :: A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNPA'B'C'M'mtmp;try rewrite HT2 in HMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: M' :: nil) 4 3 3 HMNPA'B'C'M'mtmp HA'B'C'M'mtmp HPA'B'C'M'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'N'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'N'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNA'B'C'M'N'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4).
{
	assert(HMNA'B'C'M'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'eq HMNA'B'C'M'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 4 4 HMNA'B'C'M'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour A'B'C'M'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'M'N'm3 : rk(A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA'B'C'M'N'M4 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 4).
{
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M' :: A' :: B' :: C' :: N' :: nil) ((M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M' :: nil) (A' :: B' :: C' :: N' :: nil) (nil) 1 3 0 HM'Mtmp HA'B'C'N'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'M'N'M3 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3).
{
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil) ((A' :: B' :: C' :: M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'M'Mtmp HA'B'C'N'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNM'N'm2 : rk(M :: N :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 5*)
assert(HMNM'N'm3 : rk(M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'M'N'Mtmp : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'N'eq HA'B'C'M'N'M3).
	assert(HMNA'B'C'M'N'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'N'eq HMNA'B'C'M'N'm4).
	assert(HM'N'mtmp : rk(M' :: N' :: nil) >= 2) by (solve_hyps_min HM'N'eq HM'N'm2).
	assert(Hincl : incl (M' :: N' :: nil) (list_inter (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil) ((M :: N :: M' :: N' :: nil) ++ (A' :: B' :: C' :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNA'B'C'M'N'mtmp;try rewrite HT2 in HMNA'B'C'M'N'mtmp.
	assert(HT := rule_2 (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) (M' :: N' :: nil) 4 2 3 HMNA'B'C'M'N'mtmp HM'N'mtmp HA'B'C'M'N'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNM'N' requis par la preuve de (?)ABCMNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNM'N'm3 : rk(A :: B :: C :: M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNM'N' requis par la preuve de (?)AMNM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: M' :: N' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNM'N'm2 : rk(A :: M :: N :: M' :: N' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNM'N'mtmp : rk(A :: B :: C :: M :: N :: M' :: N' :: nil) >= 3) by (solve_hyps_min HABCMNM'N'eq HABCMNM'N'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: M' :: N' :: nil) (A :: B :: C :: M :: A :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: M' :: N' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNM'N'mtmp;try rewrite HT2 in HABCMNM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: M' :: N' :: nil) (A :: M :: nil) 3 2 3 HABCMNM'N'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNM'N'm3 : rk(A :: M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: M' :: N' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 5 et 4*)
assert(HAMNM'N'm4 : rk(A :: M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HH1H2H3H4MNM'N'eq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) = 4) by (apply LH1H2H3H4MNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNM'N'Mtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNM'N'eq HH1H2H3H4MNM'N'M4).
	assert(HAH1H2H3H4MNM'N'eq : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) = 5) by (apply LAH1H2H3H4MNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAH1H2H3H4MNM'N'mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4MNM'N'eq HAH1H2H3H4MNM'N'm5).
	assert(HMNM'N'mtmp : rk(M :: N :: M' :: N' :: nil) >= 3) by (solve_hyps_min HMNM'N'eq HMNM'N'm3).
	assert(Hincl : incl (M :: N :: M' :: N' :: nil) (list_inter (A :: M :: N :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) (A :: M :: N :: M' :: N' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: M' :: N' :: H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) ((A :: M :: N :: M' :: N' :: nil) ++ (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAH1H2H3H4MNM'N'mtmp;try rewrite HT2 in HAH1H2H3H4MNM'N'mtmp.
	assert(HT := rule_2 (A :: M :: N :: M' :: N' :: nil) (H1 :: H2 :: H3 :: H4 :: M :: N :: M' :: N' :: nil) (M :: N :: M' :: N' :: nil) 5 3 4 HAH1H2H3H4MNM'N'mtmp HMNM'N'mtmp HH1H2H3H4MNM'N'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNPM'N' requis par la preuve de (?)AMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNPM'N' requis par la preuve de (?)AMNPM'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)AMNPM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM'N' requis par la preuve de (?)ABCMNPM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'N'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNPM'N' requis par la preuve de (?)AMNPM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: M' :: N' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNPM'N'm2 : rk(A :: M :: N :: P :: M' :: N' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPM'N'mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: N' :: nil) >= 3) by (solve_hyps_min HABCMNPM'N'eq HABCMNPM'N'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: N' :: nil) (A :: B :: C :: M :: A :: M :: N :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: P :: M' :: N' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPM'N'mtmp;try rewrite HT2 in HABCMNPM'N'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: P :: M' :: N' :: nil) (A :: M :: nil) 3 2 3 HABCMNPM'N'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPM'N'm3 : rk(A :: M :: N :: P :: M' :: N' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: M' :: N' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HAMNPM'N'm4 : rk(A :: M :: N :: P :: M' :: N' :: nil) >= 4).
{
	assert(HAMNM'N'mtmp : rk(A :: M :: N :: M' :: N' :: nil) >= 4) by (solve_hyps_min HAMNM'N'eq HAMNM'N'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: M' :: N' :: nil) (A :: M :: N :: P :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: M' :: N' :: nil) (A :: M :: N :: P :: M' :: N' :: nil) 4 4 HAMNM'N'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 5) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: C :: M :: N :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : A :: M :: N ::  de rang :  3 et 3 	 A : A :: C :: M :: N ::   de rang : 3 et 3 *)
assert(HAMNPM'N'm5 : rk(A :: M :: N :: P :: M' :: N' :: nil) >= 5).
{
	assert(HACMNeq : rk(A :: C :: M :: N :: nil) = 3) by (apply LACMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HACMNMtmp : rk(A :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HACMNeq HACMNM3).
	assert(HACMNPM'N'eq : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) = 5) by (apply LACMNPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HACMNPM'N'mtmp : rk(A :: C :: M :: N :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HACMNPM'N'eq HACMNPM'N'm5).
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hincl : incl (A :: M :: N :: nil) (list_inter (A :: C :: M :: N :: nil) (A :: M :: N :: P :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: M :: N :: P :: M' :: N' :: nil) (A :: C :: M :: N :: A :: M :: N :: P :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: M :: N :: A :: M :: N :: P :: M' :: N' :: nil) ((A :: C :: M :: N :: nil) ++ (A :: M :: N :: P :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACMNPM'N'mtmp;try rewrite HT2 in HACMNPM'N'mtmp.
	assert(HT := rule_4 (A :: C :: M :: N :: nil) (A :: M :: N :: P :: M' :: N' :: nil) (A :: M :: N :: nil) 5 3 3 HACMNPM'N'mtmp HAMNmtmp HACMNMtmp Hincl); apply HT.
}

assert(HAMNPM'N'M : rk(A :: M :: N :: P :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HAMNPM'N'm : rk(A :: M :: N :: P :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HAMNPM'N'eq HAMNPM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA'B'C'M'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(A' :: B' :: C' :: M' :: N' ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'M'N' requis par la preuve de (?)A'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'M'N'm3 : rk(A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA'B'C'M'N'M4 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 4).
{
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M' :: A' :: B' :: C' :: N' :: nil) ((M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M' :: nil) (A' :: B' :: C' :: N' :: nil) (nil) 1 3 0 HM'Mtmp HA'B'C'N'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'M'N'M3 : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3).
{
	assert(HA'B'C'M'Mtmp : rk(A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'eq HA'B'C'M'M3).
	assert(HA'B'C'N'Mtmp : rk(A' :: B' :: C' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'N'eq HA'B'C'N'M3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M' :: A' :: B' :: C' :: N' :: nil) ((A' :: B' :: C' :: M' :: nil) ++ (A' :: B' :: C' :: N' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: N' :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'M'Mtmp HA'B'C'N'Mtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA'B'C'M'N'M : rk(A' :: B' :: C' :: M' :: N' ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA'B'C'M'N'm : rk(A' :: B' :: C' :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HA'B'C'M'N'eq HA'B'C'M'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNM'N' : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> rk(M :: N :: M' :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNPM' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMM' requis par la preuve de (?)ABCMM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMM'm3 : rk(A :: B :: C :: M :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HABCMM'M4 : rk(A :: B :: C :: M :: M' :: nil) <= 4).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HM'Mtmp : rk(M' :: nil) <= 1) by (solve_hyps_max HM'eq HM'M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: M :: nil) (M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: M :: nil) ++ (M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (M' :: nil) (nil) 3 1 0 HABCMMtmp HM'Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNM' requis par la preuve de (?)ABCMNM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNM'm3 : rk(A :: B :: C :: M :: N :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNM'M4 : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4).
{
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	assert(HABCMM'Mtmp : rk(A :: B :: C :: M :: M' :: nil) <= 4) by (solve_hyps_max HABCMM'eq HABCMM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: M' :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCNMtmp HABCMM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPM' requis par la preuve de (?)ABCMNPM' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPM'm3 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HABCMNPM'M4 : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4).
{
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	assert(HABCMNM'Mtmp : rk(A :: B :: C :: M :: N :: M' :: nil) <= 4) by (solve_hyps_max HABCMNM'eq HABCMNM'M4).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: M' :: nil) (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: P :: A :: B :: C :: M :: N :: M' :: nil) ((A :: B :: C :: P :: nil) ++ (A :: B :: C :: M :: N :: M' :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: M' :: nil) (A :: B :: C :: nil) 3 4 3 HABCPMtmp HABCMNM'Mtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCMNPA'B'C' requis par la preuve de (?)ABCMNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCMNPA'B'C'm3 : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour AMNPA'B'C' requis par la preuve de (?)AMNPA'B'C' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : A :: M ::  de rang :  2 et 2 	 A : A :: B :: C :: M ::   de rang : 3 et 3 *)
assert(HAMNPA'B'C'm2 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	assert(HABCMNPA'B'C'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HABCMNPA'B'C'eq HABCMNPA'B'C'm3).
	assert(HAMeq : rk(A :: M :: nil) = 2) by (apply LAM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMmtmp : rk(A :: M :: nil) >= 2) by (solve_hyps_min HAMeq HAMm2).
	assert(Hincl : incl (A :: M :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: B :: C :: M :: nil) ++ (A :: M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'mtmp;try rewrite HT2 in HABCMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: nil) 3 2 3 HABCMNPA'B'C'mtmp HAMmtmp HABCMMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HAMNPA'B'C'm3 : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNeq : rk(A :: M :: N :: nil) = 3) by (apply LAMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNmtmp : rk(A :: M :: N :: nil) >= 3) by (solve_hyps_min HAMNeq HAMNm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: M :: N :: nil) (A :: M :: N :: P :: A' :: B' :: C' :: nil) 3 3 HAMNmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C' requis par la preuve de (?)MNPA'B'C' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'm2 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: M :: N :: P :: A' :: B' :: C' ::  de rang :  3 et 5 	 AiB : M :: N :: P ::  de rang :  3 et 3 	 A : A :: M :: N :: P ::   de rang : 3 et 3 *)
assert(HMNPA'B'C'm3 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 3).
{
	assert(HAMNPeq : rk(A :: M :: N :: P :: nil) = 3) by (apply LAMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNPMtmp : rk(A :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HAMNPeq HAMNPM3).
	assert(HAMNPA'B'C'mtmp : rk(A :: M :: N :: P :: A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HAMNPA'B'C'eq HAMNPA'B'C'm3).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: M :: N :: P :: A' :: B' :: C' :: nil) (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: P :: M :: N :: P :: A' :: B' :: C' :: nil) ((A :: M :: N :: P :: nil) ++ (M :: N :: P :: A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAMNPA'B'C'mtmp;try rewrite HT2 in HAMNPA'B'C'mtmp.
	assert(HT := rule_4 (A :: M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: nil) 3 3 3 HAMNPA'B'C'mtmp HMNPmtmp HAMNPMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 5*)
assert(HMNPA'B'C'm4 : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4).
{
	assert(HABCMNPM'Mtmp : rk(A :: B :: C :: M :: N :: P :: M' :: nil) <= 4) by (solve_hyps_max HABCMNPM'eq HABCMNPM'M4).
	assert(HABCMNPA'B'C'M'eq : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) = 5) by (apply LABCMNPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABCMNPA'B'C'M'mtmp : rk(A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 5) by (solve_hyps_min HABCMNPA'B'C'M'eq HABCMNPA'B'C'M'm5).
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: P :: A' :: B' :: C' :: A :: B :: C :: M :: N :: P :: M' :: nil) ((M :: N :: P :: A' :: B' :: C' :: nil) ++ (A :: B :: C :: M :: N :: P :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCMNPA'B'C'M'mtmp;try rewrite HT2 in HABCMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: P :: A' :: B' :: C' :: nil) (A :: B :: C :: M :: N :: P :: M' :: nil) (M :: N :: P :: nil) 5 3 4 HABCMNPA'B'C'M'mtmp HMNPmtmp HABCMNPM'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNPA'B'C'M' requis par la preuve de (?)MNPA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNPA'B'C'M'm2 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNPA'B'C'M'm3 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNPeq : rk(M :: N :: P :: nil) = 3) by (apply LMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNPmtmp : rk(M :: N :: P :: nil) >= 3) by (solve_hyps_min HMNPeq HMNPm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 3 3 HMNPmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNPA'B'C'M'm4 : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HMNPA'B'C'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'eq HMNPA'B'C'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: P :: A' :: B' :: C' :: nil) (M :: N :: P :: A' :: B' :: C' :: M' :: nil) 4 4 HMNPA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M' requis par la preuve de (?)MNA'B'C'M' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 4*)
assert(HMNA'B'C'M'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4).
{
	assert(HPA'B'C'M'eq : rk(P :: A' :: B' :: C' :: M' :: nil) = 3) by (apply LPA'B'C'M' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HPA'B'C'M'Mtmp : rk(P :: A' :: B' :: C' :: M' :: nil) <= 3) by (solve_hyps_max HPA'B'C'M'eq HPA'B'C'M'M3).
	assert(HMNPA'B'C'M'mtmp : rk(M :: N :: P :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNPA'B'C'M'eq HMNPA'B'C'M'm4).
	assert(HA'B'C'M'mtmp : rk(A' :: B' :: C' :: M' :: nil) >= 3) by (solve_hyps_min HA'B'C'M'eq HA'B'C'M'm3).
	assert(Hincl : incl (A' :: B' :: C' :: M' :: nil) (list_inter (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: P :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: A' :: B' :: C' :: M' :: P :: A' :: B' :: C' :: M' :: nil) ((M :: N :: A' :: B' :: C' :: M' :: nil) ++ (P :: A' :: B' :: C' :: M' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNPA'B'C'M'mtmp;try rewrite HT2 in HMNPA'B'C'M'mtmp.
	assert(HT := rule_2 (M :: N :: A' :: B' :: C' :: M' :: nil) (P :: A' :: B' :: C' :: M' :: nil) (A' :: B' :: C' :: M' :: nil) 4 3 3 HMNPA'B'C'M'mtmp HA'B'C'M'mtmp HPA'B'C'M'Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour MNA'B'C'M'N' requis par la preuve de (?)MNA'B'C'M'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNA'B'C'M'N'm2 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNA'B'C'M'N'm3 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 3).
{
	assert(HMNA'eq : rk(M :: N :: A' :: nil) = 3) by (apply LMNA' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HMNA'mtmp : rk(M :: N :: A' :: nil) >= 3) by (solve_hyps_min HMNA'eq HMNA'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 3 3 HMNA'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HMNA'B'C'M'N'm4 : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4).
{
	assert(HMNA'B'C'M'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'eq HMNA'B'C'M'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: A' :: B' :: C' :: M' :: nil) (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) 4 4 HMNA'B'C'M'mtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNM'N'm2 : rk(M :: N :: M' :: N' :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: M' :: N' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: M' :: N' :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -4 et 4*)
assert(HMNM'N'm3 : rk(M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HA'B'C'M'N'eq : rk(A' :: B' :: C' :: M' :: N' :: nil) = 3) by (apply LA'B'C'M'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HA'B'C'M'N'Mtmp : rk(A' :: B' :: C' :: M' :: N' :: nil) <= 3) by (solve_hyps_max HA'B'C'M'N'eq HA'B'C'M'N'M3).
	assert(HMNA'B'C'M'N'mtmp : rk(M :: N :: A' :: B' :: C' :: M' :: N' :: nil) >= 4) by (solve_hyps_min HMNA'B'C'M'N'eq HMNA'B'C'M'N'm4).
	assert(HM'N'mtmp : rk(M' :: N' :: nil) >= 2) by (solve_hyps_min HM'N'eq HM'N'm2).
	assert(Hincl : incl (M' :: N' :: nil) (list_inter (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (M :: N :: A' :: B' :: C' :: M' :: N' :: nil) (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: N :: M' :: N' :: A' :: B' :: C' :: M' :: N' :: nil) ((M :: N :: M' :: N' :: nil) ++ (A' :: B' :: C' :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HMNA'B'C'M'N'mtmp;try rewrite HT2 in HMNA'B'C'M'N'mtmp.
	assert(HT := rule_2 (M :: N :: M' :: N' :: nil) (A' :: B' :: C' :: M' :: N' :: nil) (M' :: N' :: nil) 4 2 3 HMNA'B'C'M'N'mtmp HM'N'mtmp HA'B'C'M'N'Mtmp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : A :: M :: N :: P :: M' :: N' ::  de rang :  5 et 5 	 AiB : M :: N ::  de rang :  2 et 2 	 A : A :: M :: N :: P ::   de rang : 3 et 3 *)
assert(HMNM'N'm4 : rk(M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HAMNPeq : rk(A :: M :: N :: P :: nil) = 3) by (apply LAMNP with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNPMtmp : rk(A :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HAMNPeq HAMNPM3).
	assert(HAMNPM'N'eq : rk(A :: M :: N :: P :: M' :: N' :: nil) = 5) by (apply LAMNPM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HAMNPM'N'mtmp : rk(A :: M :: N :: P :: M' :: N' :: nil) >= 5) by (solve_hyps_min HAMNPM'N'eq HAMNPM'N'm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: M :: N :: P :: nil) (M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: M :: N :: P :: M' :: N' :: nil) (A :: M :: N :: P :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: M :: N :: P :: M :: N :: M' :: N' :: nil) ((A :: M :: N :: P :: nil) ++ (M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HAMNPM'N'mtmp;try rewrite HT2 in HAMNPM'N'mtmp.
	assert(HT := rule_4 (A :: M :: N :: P :: nil) (M :: N :: M' :: N' :: nil) (M :: N :: nil) 5 2 3 HAMNPM'N'mtmp HMNmtmp HAMNPMtmp Hincl); apply HT.
}

assert(HMNM'N'M : rk(M :: N :: M' :: N' ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HMNM'N'eq HMNM'N'M4).
assert(HMNM'N'm : rk(M :: N :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HMNM'N'eq HMNM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C H1 H2 H3 H4 M N P A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: P ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 -> rk(A' :: B' :: C' ::  nil) = 3 ->
rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(P :: A' :: B' :: C' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 ->
rk(A' :: B' :: C' :: M' ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 ->
rk(M' :: N' ::  nil) = 2 -> 
	 rk(M :: N :: M' :: N' ::  nil) = 4  .
Proof.

intros A B C H1 H2 H3 H4 M N P A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HABCPeq HH1H2H3H4Peq
HH1H2H3H4A'eq HA'B'C'eq HABCA'B'C'eq HPA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq HM'N'eq .
repeat split.

	apply LMNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (P := P) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption.
Qed .
