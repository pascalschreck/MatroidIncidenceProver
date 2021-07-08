Load "preamble4D.v".


(* dans la couche 0 *)
Lemma LAB : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(A :: B ::  nil) = 2.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AB requis par la preuve de (?)AB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -4*)
assert(HABm2 : rk(A :: B :: nil) >= 2).
{
	assert(HA'B'C'Mtmp : rk(A' :: B' :: C' :: nil) <= 3) by (solve_hyps_max HA'B'C'eq HA'B'C'M3).
	assert(HABA'B'C'mtmp : rk(A :: B :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABA'B'C'eq HABA'B'C'm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: nil) (A' :: B' :: C' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: A' :: B' :: C' :: nil) (A :: B :: A' :: B' :: C' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: A' :: B' :: C' :: nil) ((A :: B :: nil) ++ (A' :: B' :: C' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABA'B'C'mtmp;try rewrite HT2 in HABA'B'C'mtmp.
	assert(HT := rule_2 (A :: B :: nil) (A' :: B' :: C' :: nil) (nil) 5 0 3 HABA'B'C'mtmp Hmtmp HA'B'C'Mtmp Hincl);apply HT.
}

assert(HABM : rk(A :: B ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max HABeq HABM2).
assert(HABm : rk(A :: B ::  nil) >= 1) by (solve_hyps_min HABeq HABm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABH1H2H3H4 : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(A :: B :: H1 :: H2 :: H3 :: H4 ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABH1H2H3H4 requis par la preuve de (?)ABH1H2H3H4 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABH1H2H3H4 requis par la preuve de (?)ABH1H2H3H4 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4m4 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: nil) >= 4).
{
	assert(HH1H2H3H4mtmp : rk(H1 :: H2 :: H3 :: H4 :: nil) >= 4) by (solve_hyps_min HH1H2H3H4eq HH1H2H3H4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: nil) 4 4 HH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABH1H2H3H4m5 : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: nil) >= 5).
{
	assert(HAH1H2H3H4mtmp : rk(A :: H1 :: H2 :: H3 :: H4 :: nil) >= 5) by (solve_hyps_min HAH1H2H3H4eq HAH1H2H3H4m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: nil) 5 5 HAH1H2H3H4mtmp Hcomp Hincl);apply HT.
}

assert(HABH1H2H3H4M : rk(A :: B :: H1 :: H2 :: H3 :: H4 ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABH1H2H3H4m : rk(A :: B :: H1 :: H2 :: H3 :: H4 ::  nil) >= 1) by (solve_hyps_min HABH1H2H3H4eq HABH1H2H3H4m1).
intuition.
Qed.

(* dans constructLemma(), requis par LABMN *)
(* dans la couche 0 *)
Lemma LABH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 5.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

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

(* dans constructLemma(), requis par LABMN *)
(* dans la couche 0 *)
Lemma LH1H2H3H4MN : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M :: N ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

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
Lemma LABMN : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(A :: B :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

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
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABMN requis par la preuve de (?)ABMN pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N ::  de rang :  5 et 5 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: H1 :: H2 :: H3 :: H4 ::   de rang : 5 et 5 *)
assert(HABMNm2 : rk(A :: B :: M :: N :: nil) >= 2).
{
	assert(HABH1H2H3H4eq : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: nil) = 5) by (apply LABH1H2H3H4 with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABH1H2H3H4Mtmp : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: nil) <= 5) by (solve_hyps_max HABH1H2H3H4eq HABH1H2H3H4M5).
	assert(HABH1H2H3H4MNeq : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LABH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABH1H2H3H4MNmtmp : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) >= 5) by (solve_hyps_min HABH1H2H3H4MNeq HABH1H2H3H4MNm5).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) (A :: B :: H1 :: H2 :: H3 :: H4 :: A :: B :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: H1 :: H2 :: H3 :: H4 :: A :: B :: M :: N :: nil) ((A :: B :: H1 :: H2 :: H3 :: H4 :: nil) ++ (A :: B :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABH1H2H3H4MNmtmp;try rewrite HT2 in HABH1H2H3H4MNmtmp.
	assert(HT := rule_4 (A :: B :: H1 :: H2 :: H3 :: H4 :: nil) (A :: B :: M :: N :: nil) (A :: B :: nil) 5 2 5 HABH1H2H3H4MNmtmp HABmtmp HABH1H2H3H4Mtmp Hincl); apply HT.
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
	assert(HH1H2H3H4MNeq : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 4) by (apply LH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HH1H2H3H4MNMtmp : rk(H1 :: H2 :: H3 :: H4 :: M :: N :: nil) <= 4) by (solve_hyps_max HH1H2H3H4MNeq HH1H2H3H4MNM4).
	assert(HABH1H2H3H4MNeq : rk(A :: B :: H1 :: H2 :: H3 :: H4 :: M :: N :: nil) = 5) by (apply LABH1H2H3H4MN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
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

(* dans la couche 0 *)
Lemma LABCMN : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

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
Lemma LMNM'N' : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> rk(M :: N :: M' :: N' ::  nil) = 4.
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour MNM'N' requis par la preuve de (?)MNM'N' pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: M :: N :: M' :: N' ::  de rang :  5 et 5 	 AiB : M ::  de rang :  1 et 1 	 A : A :: B :: M ::   de rang : 2 et 3 *)
assert(HMNM'N'm3 : rk(M :: N :: M' :: N' :: nil) >= 3).
{
	assert(HABMeq : rk(A :: B :: M :: nil) = 3) by (apply LABM with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABMMtmp : rk(A :: B :: M :: nil) <= 3) by (solve_hyps_max HABMeq HABMM3).
	assert(HABMNM'N'mtmp : rk(A :: B :: M :: N :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABMNM'N'eq HABMNM'N'm5).
	assert(HMmtmp : rk(M :: nil) >= 1) by (solve_hyps_min HMeq HMm1).
	assert(Hincl : incl (M :: nil) (list_inter (A :: B :: M :: nil) (M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: M :: N :: M' :: N' :: nil) (A :: B :: M :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: M :: N :: M' :: N' :: nil) ((A :: B :: M :: nil) ++ (M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABMNM'N'mtmp;try rewrite HT2 in HABMNM'N'mtmp.
	assert(HT := rule_4 (A :: B :: M :: nil) (M :: N :: M' :: N' :: nil) (M :: nil) 5 1 3 HABMNM'N'mtmp HMmtmp HABMMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: -4 -4 et 4*)
(* ensembles concernés AUB : A :: B :: M :: N :: M' :: N' ::  de rang :  5 et 5 	 AiB : M :: N ::  de rang :  2 et 2 	 A : A :: B :: M :: N ::   de rang : 3 et 3 *)
assert(HMNM'N'm4 : rk(M :: N :: M' :: N' :: nil) >= 4).
{
	assert(HABMNeq : rk(A :: B :: M :: N :: nil) = 3) by (apply LABMN with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption).
	assert(HABMNMtmp : rk(A :: B :: M :: N :: nil) <= 3) by (solve_hyps_max HABMNeq HABMNM3).
	assert(HABMNM'N'mtmp : rk(A :: B :: M :: N :: M' :: N' :: nil) >= 5) by (solve_hyps_min HABMNM'N'eq HABMNM'N'm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: M :: N :: nil) (M :: N :: M' :: N' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: M :: N :: M' :: N' :: nil) (A :: B :: M :: N :: M :: N :: M' :: N' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: M :: N :: M :: N :: M' :: N' :: nil) ((A :: B :: M :: N :: nil) ++ (M :: N :: M' :: N' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABMNM'N'mtmp;try rewrite HT2 in HABMNM'N'mtmp.
	assert(HT := rule_4 (A :: B :: M :: N :: nil) (M :: N :: M' :: N' :: nil) (M :: N :: nil) 5 2 3 HABMNM'N'mtmp HMNmtmp HABMNMtmp Hincl); apply HT.
}

assert(HMNM'N'M : rk(M :: N :: M' :: N' ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max HMNM'N'eq HMNM'N'M4).
assert(HMNM'N'm : rk(M :: N :: M' :: N' ::  nil) >= 1) by (solve_hyps_min HMNM'N'eq HMNM'N'm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C H1 H2 H3 H4 M N A' B' C' M' N' ,
rk(A :: B :: C ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 ::  nil) = 4 -> rk(A :: H1 :: H2 :: H3 :: H4 ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(H1 :: H2 :: H3 :: H4 :: M ::  nil) = 4 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N ::  nil) = 4 -> rk(M :: N ::  nil) = 2 -> rk(H1 :: H2 :: H3 :: H4 :: A' ::  nil) = 5 ->
rk(A :: B :: C :: A' :: B' ::  nil) = 5 -> rk(A :: B :: C :: A' :: C' ::  nil) = 5 -> rk(A :: B :: C :: B' :: C' ::  nil) = 5 ->
rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: A' :: B' :: C' ::  nil) = 5 -> rk(A :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(B :: C :: A' :: B' :: C' ::  nil) = 5 -> rk(H1 :: H2 :: H3 :: H4 :: M' ::  nil) = 4 -> rk(A' :: B' :: C' :: M' ::  nil) = 3 ->
rk(H1 :: H2 :: H3 :: H4 :: N' ::  nil) = 4 -> rk(A' :: B' :: C' :: N' ::  nil) = 3 -> rk(M' :: N' ::  nil) = 2 ->
rk(A :: B :: M :: N :: M' :: N' ::  nil) = 5 -> 
	 rk(M :: N :: M' :: N' ::  nil) = 4  .
Proof.

intros A B C H1 H2 H3 H4 M N A' B' C' M' N' 
HABCeq HH1H2H3H4eq HAH1H2H3H4eq HABCMeq HH1H2H3H4Meq HABCNeq HH1H2H3H4Neq HMNeq HH1H2H3H4A'eq HABCA'B'eq
HABCA'C'eq HABCB'C'eq HA'B'C'eq HABA'B'C'eq HACA'B'C'eq HBCA'B'C'eq HH1H2H3H4M'eq HA'B'C'M'eq HH1H2H3H4N'eq HA'B'C'N'eq
HM'N'eq HABMNM'N'eq .
repeat split.

	apply LMNM'N' with (A := A) (B := B) (C := C) (H1 := H1) (H2 := H2) (H3 := H3) (H4 := H4) (M := M) (N := N) (A' := A') (B' := B') (C' := C') (M' := M') (N' := N') ; assumption.
Qed .
