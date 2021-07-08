Load "preamble4D.v".


(* dans la couche 0 *)
Lemma LABCMN : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

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

(* dans constructLemma(), requis par LMQ *)
(* dans constructLemma(), requis par LA''B''C''MNQ *)
(* dans la couche 0 *)
Lemma LABCA''B''C''MNQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q ::  nil) = 5.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA''B''C''MNQ requis par la preuve de (?)ABCA''B''C''MNQ pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA''B'' requis par la preuve de (?)ABCA''B''C''MNQ pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA''B'' requis par la preuve de (?)ABCA''B'' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA''B'' requis par la preuve de (?)ABCA''B'' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA''B''m3 : rk(A :: B :: C :: A'' :: B'' :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A'' :: B'' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A'' :: B'' :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -1 et -2*)
assert(HABCA''B''m4 : rk(A :: B :: C :: A'' :: B'' :: nil) >= 4).
{
	assert(HC''Mtmp : rk(C'' :: nil) <= 1) by (solve_hyps_max HC''eq HC''M1).
	assert(HABCA''B''C''mtmp : rk(A :: B :: C :: A'' :: B'' :: C'' :: nil) >= 5) by (solve_hyps_min HABCA''B''C''eq HABCA''B''C''m5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: B :: C :: A'' :: B'' :: nil) (C'' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A'' :: B'' :: C'' :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A'' :: B'' :: C'' :: nil) ((A :: B :: C :: A'' :: B'' :: nil) ++ (C'' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA''B''C''mtmp;try rewrite HT2 in HABCA''B''C''mtmp.
	assert(HT := rule_2 (A :: B :: C :: A'' :: B'' :: nil) (C'' :: nil) (nil) 5 0 1 HABCA''B''C''mtmp Hmtmp HC''Mtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA''B''C''MNQ requis par la preuve de (?)ABCA''B''C''MNQ pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA''B''C''MNQ requis par la preuve de (?)ABCA''B''C''MNQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA''B''C''MNQm3 : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCA''B''C''MNQm4 : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 4).
{
	assert(HABCA''B''mtmp : rk(A :: B :: C :: A'' :: B'' :: nil) >= 4) by (solve_hyps_min HABCA''B''eq HABCA''B''m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A'' :: B'' :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A'' :: B'' :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) 4 4 HABCA''B''mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA''B''C''MNQm5 : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 5).
{
	assert(HABCA''B''C''mtmp : rk(A :: B :: C :: A'' :: B'' :: C'' :: nil) >= 5) by (solve_hyps_min HABCA''B''C''eq HABCA''B''C''m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A'' :: B'' :: C'' :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A'' :: B'' :: C'' :: nil) (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) 5 5 HABCA''B''C''mtmp Hcomp Hincl);apply HT.
}

assert(HABCA''B''C''MNQM : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCA''B''C''MNQm : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q ::  nil) >= 1) by (solve_hyps_min HABCA''B''C''MNQeq HABCA''B''C''MNQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA''B''C''MNQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A'' :: B'' :: C'' :: M :: N :: Q ::  nil) = 4.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A''B''C''MNQ requis par la preuve de (?)A''B''C''MNQ pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A''B''C''MQ requis par la preuve de (?)A''B''C''MNQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A''B''C''MQ requis par la preuve de (?)A''B''C''MQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A''B''C''MQ requis par la preuve de (?)A''B''C''MQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA''B''C''MQm3 : rk(A'' :: B'' :: C'' :: M :: Q :: nil) >= 3).
{
	assert(HA''B''C''mtmp : rk(A'' :: B'' :: C'' :: nil) >= 3) by (solve_hyps_min HA''B''C''eq HA''B''C''m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: M :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: M :: Q :: nil) 3 3 HA''B''C''mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA''B''C''MQM4 : rk(A'' :: B'' :: C'' :: M :: Q :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HA''B''C''QMtmp : rk(A'' :: B'' :: C'' :: Q :: nil) <= 3) by (solve_hyps_max HA''B''C''Qeq HA''B''C''QM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A'' :: B'' :: C'' :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A'' :: B'' :: C'' :: M :: Q :: nil) (M :: A'' :: B'' :: C'' :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A'' :: B'' :: C'' :: Q :: nil) ((M :: nil) ++ (A'' :: B'' :: C'' :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A'' :: B'' :: C'' :: Q :: nil) (nil) 1 3 0 HMMtmp HA''B''C''QMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A''B''C''MNQ requis par la preuve de (?)A''B''C''MNQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A''B''C''MNQ requis par la preuve de (?)A''B''C''MNQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA''B''C''MNQm3 : rk(A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 3).
{
	assert(HA''B''C''mtmp : rk(A'' :: B'' :: C'' :: nil) >= 3) by (solve_hyps_min HA''B''C''eq HA''B''C''m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: M :: N :: Q :: nil) 3 3 HA''B''C''mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -4*)
assert(HA''B''C''MNQM4 : rk(A'' :: B'' :: C'' :: M :: N :: Q :: nil) <= 4).
{
	assert(HA''B''C''NMtmp : rk(A'' :: B'' :: C'' :: N :: nil) <= 3) by (solve_hyps_max HA''B''C''Neq HA''B''C''NM3).
	assert(HA''B''C''MQMtmp : rk(A'' :: B'' :: C'' :: M :: Q :: nil) <= 4) by (solve_hyps_max HA''B''C''MQeq HA''B''C''MQM4).
	assert(HA''B''C''mtmp : rk(A'' :: B'' :: C'' :: nil) >= 3) by (solve_hyps_min HA''B''C''eq HA''B''C''m3).
	assert(Hincl : incl (A'' :: B'' :: C'' :: nil) (list_inter (A'' :: B'' :: C'' :: N :: nil) (A'' :: B'' :: C'' :: M :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A'' :: B'' :: C'' :: M :: N :: Q :: nil) (A'' :: B'' :: C'' :: N :: A'' :: B'' :: C'' :: M :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A'' :: B'' :: C'' :: N :: A'' :: B'' :: C'' :: M :: Q :: nil) ((A'' :: B'' :: C'' :: N :: nil) ++ (A'' :: B'' :: C'' :: M :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A'' :: B'' :: C'' :: N :: nil) (A'' :: B'' :: C'' :: M :: Q :: nil) (A'' :: B'' :: C'' :: nil) 3 4 3 HA''B''C''NMtmp HA''B''C''MQMtmp HA''B''C''mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q ::  de rang :  5 et 5 	 AiB : M :: N ::  de rang :  2 et 2 	 A : A :: B :: C :: M :: N ::   de rang : 3 et 3 *)
assert(HA''B''C''MNQm4 : rk(A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 4).
{
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(HABCA''B''C''MNQeq : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) = 5) by (apply LABCA''B''C''MNQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HABCA''B''C''MNQmtmp : rk(A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 5) by (solve_hyps_min HABCA''B''C''MNQeq HABCA''B''C''MNQm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: C :: M :: N :: nil) (A'' :: B'' :: C'' :: M :: N :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) (A :: B :: C :: M :: N :: A'' :: B'' :: C'' :: M :: N :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: A'' :: B'' :: C'' :: M :: N :: Q :: nil) ((A :: B :: C :: M :: N :: nil) ++ (A'' :: B'' :: C'' :: M :: N :: Q :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA''B''C''MNQmtmp;try rewrite HT2 in HABCA''B''C''MNQmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: N :: nil) (A'' :: B'' :: C'' :: M :: N :: Q :: nil) (M :: N :: nil) 5 2 3 HABCA''B''C''MNQmtmp HMNmtmp HABCMNMtmp Hincl); apply HT.
}

assert(HA''B''C''MNQM : rk(A'' :: B'' :: C'' :: M :: N :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA''B''C''MNQm : rk(A'' :: B'' :: C'' :: M :: N :: Q ::  nil) >= 1) by (solve_hyps_min HA''B''C''MNQeq HA''B''C''MNQm1).
intuition.
Qed.

(* dans constructLemma(), requis par LMQ *)
(* dans la couche 0 *)
Lemma LA''B''C''NQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A'' :: B'' :: C'' :: N :: Q ::  nil) = 3.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A''B''C''NQ requis par la preuve de (?)A''B''C''NQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A''B''C''NQ requis par la preuve de (?)A''B''C''NQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A''B''C''NQ requis par la preuve de (?)A''B''C''NQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA''B''C''NQm3 : rk(A'' :: B'' :: C'' :: N :: Q :: nil) >= 3).
{
	assert(HA''B''C''mtmp : rk(A'' :: B'' :: C'' :: nil) >= 3) by (solve_hyps_min HA''B''C''eq HA''B''C''m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A'' :: B'' :: C'' :: nil) (A'' :: B'' :: C'' :: N :: Q :: nil) 3 3 HA''B''C''mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA''B''C''NQM4 : rk(A'' :: B'' :: C'' :: N :: Q :: nil) <= 4).
{
	assert(HNMtmp : rk(N :: nil) <= 1) by (solve_hyps_max HNeq HNM1).
	assert(HA''B''C''QMtmp : rk(A'' :: B'' :: C'' :: Q :: nil) <= 3) by (solve_hyps_max HA''B''C''Qeq HA''B''C''QM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (N :: nil) (A'' :: B'' :: C'' :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A'' :: B'' :: C'' :: N :: Q :: nil) (N :: A'' :: B'' :: C'' :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (N :: A'' :: B'' :: C'' :: Q :: nil) ((N :: nil) ++ (A'' :: B'' :: C'' :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (N :: nil) (A'' :: B'' :: C'' :: Q :: nil) (nil) 1 3 0 HNMtmp HA''B''C''QMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA''B''C''NQM3 : rk(A'' :: B'' :: C'' :: N :: Q :: nil) <= 3).
{
	assert(HA''B''C''NMtmp : rk(A'' :: B'' :: C'' :: N :: nil) <= 3) by (solve_hyps_max HA''B''C''Neq HA''B''C''NM3).
	assert(HA''B''C''QMtmp : rk(A'' :: B'' :: C'' :: Q :: nil) <= 3) by (solve_hyps_max HA''B''C''Qeq HA''B''C''QM3).
	assert(HA''B''C''mtmp : rk(A'' :: B'' :: C'' :: nil) >= 3) by (solve_hyps_min HA''B''C''eq HA''B''C''m3).
	assert(Hincl : incl (A'' :: B'' :: C'' :: nil) (list_inter (A'' :: B'' :: C'' :: N :: nil) (A'' :: B'' :: C'' :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A'' :: B'' :: C'' :: N :: Q :: nil) (A'' :: B'' :: C'' :: N :: A'' :: B'' :: C'' :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A'' :: B'' :: C'' :: N :: A'' :: B'' :: C'' :: Q :: nil) ((A'' :: B'' :: C'' :: N :: nil) ++ (A'' :: B'' :: C'' :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A'' :: B'' :: C'' :: N :: nil) (A'' :: B'' :: C'' :: Q :: nil) (A'' :: B'' :: C'' :: nil) 3 3 3 HA''B''C''NMtmp HA''B''C''QMtmp HA''B''C''mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA''B''C''NQM : rk(A'' :: B'' :: C'' :: N :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA''B''C''NQm : rk(A'' :: B'' :: C'' :: N :: Q ::  nil) >= 1) by (solve_hyps_min HA''B''C''NQeq HA''B''C''NQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(M :: Q ::  nil) = 2.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour MQ requis par la preuve de (?)MQ pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HMQm2 : rk(M :: Q :: nil) >= 2).
{
	assert(HA''B''C''NQeq : rk(A'' :: B'' :: C'' :: N :: Q :: nil) = 3) by (apply LA''B''C''NQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HA''B''C''NQMtmp : rk(A'' :: B'' :: C'' :: N :: Q :: nil) <= 3) by (solve_hyps_max HA''B''C''NQeq HA''B''C''NQM3).
	assert(HA''B''C''MNQeq : rk(A'' :: B'' :: C'' :: M :: N :: Q :: nil) = 4) by (apply LA''B''C''MNQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HA''B''C''MNQmtmp : rk(A'' :: B'' :: C'' :: M :: N :: Q :: nil) >= 4) by (solve_hyps_min HA''B''C''MNQeq HA''B''C''MNQm4).
	assert(HQmtmp : rk(Q :: nil) >= 1) by (solve_hyps_min HQeq HQm1).
	assert(Hincl : incl (Q :: nil) (list_inter (M :: Q :: nil) (A'' :: B'' :: C'' :: N :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A'' :: B'' :: C'' :: M :: N :: Q :: nil) (M :: Q :: A'' :: B'' :: C'' :: N :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: Q :: A'' :: B'' :: C'' :: N :: Q :: nil) ((M :: Q :: nil) ++ (A'' :: B'' :: C'' :: N :: Q :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HA''B''C''MNQmtmp;try rewrite HT2 in HA''B''C''MNQmtmp.
	assert(HT := rule_2 (M :: Q :: nil) (A'' :: B'' :: C'' :: N :: Q :: nil) (Q :: nil) 4 1 3 HA''B''C''MNQmtmp HQmtmp HA''B''C''NQMtmp Hincl);apply HT.
}

assert(HMQM : rk(M :: Q ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max HMQeq HMQM2).
assert(HMQm : rk(M :: Q ::  nil) >= 1) by (solve_hyps_min HMQeq HMQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA'B'C'MQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A' :: B' :: C' :: M :: Q ::  nil) = 3.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'MQ requis par la preuve de (?)A'B'C'MQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'MQ requis par la preuve de (?)A'B'C'MQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'MQ requis par la preuve de (?)A'B'C'MQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'MQm3 : rk(A' :: B' :: C' :: M :: Q :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: Q :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA'B'C'MQM4 : rk(A' :: B' :: C' :: M :: Q :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HA'B'C'QMtmp : rk(A' :: B' :: C' :: Q :: nil) <= 3) by (solve_hyps_max HA'B'C'Qeq HA'B'C'QM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A' :: B' :: C' :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: Q :: nil) (M :: A' :: B' :: C' :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A' :: B' :: C' :: Q :: nil) ((M :: nil) ++ (A' :: B' :: C' :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A' :: B' :: C' :: Q :: nil) (nil) 1 3 0 HMMtmp HA'B'C'QMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'MQM3 : rk(A' :: B' :: C' :: M :: Q :: nil) <= 3).
{
	assert(HA'B'C'MMtmp : rk(A' :: B' :: C' :: M :: nil) <= 3) by (solve_hyps_max HA'B'C'Meq HA'B'C'MM3).
	assert(HA'B'C'QMtmp : rk(A' :: B' :: C' :: Q :: nil) <= 3) by (solve_hyps_max HA'B'C'Qeq HA'B'C'QM3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: Q :: nil) (A' :: B' :: C' :: M :: A' :: B' :: C' :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M :: A' :: B' :: C' :: Q :: nil) ((A' :: B' :: C' :: M :: nil) ++ (A' :: B' :: C' :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: Q :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'MMtmp HA'B'C'QMtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA'B'C'MQM : rk(A' :: B' :: C' :: M :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA'B'C'MQm : rk(A' :: B' :: C' :: M :: Q ::  nil) >= 1) by (solve_hyps_min HA'B'C'MQeq HA'B'C'MQm1).
intuition.
Qed.

(* dans constructLemma(), requis par LA'B'C'MNQ *)
(* dans la couche 0 *)
Lemma LABCA'B'C'MNQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q ::  nil) = 5.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B'C'MNQ requis par la preuve de (?)ABCA'B'C'MNQ pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B'C'MNQ pour la règle 5  *)
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

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA'B'C'MNQ requis par la preuve de (?)ABCA'B'C'MNQ pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA'B'C'MNQ requis par la preuve de (?)ABCA'B'C'MNQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNQm3 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCA'B'C'MNQm4 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) >= 4).
{
	assert(HABCA'B'mtmp : rk(A :: B :: C :: A' :: B' :: nil) >= 4) by (solve_hyps_min HABCA'B'eq HABCA'B'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) 4 4 HABCA'B'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNQm5 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) >= 5).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) 5 5 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCA'B'C'MNQM : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCA'B'C'MNQm : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q ::  nil) >= 1) by (solve_hyps_min HABCA'B'C'MNQeq HABCA'B'C'MNQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LA'B'C'MNQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(A' :: B' :: C' :: M :: N :: Q ::  nil) = 4.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'MNQ requis par la preuve de (?)A'B'C'MNQ pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'MNQ requis par la preuve de (?)A'B'C'MNQ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'MNQ requis par la preuve de (?)A'B'C'MNQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'MNQm3 : rk(A' :: B' :: C' :: M :: N :: Q :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: Q :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HA'B'C'MNQM4 : rk(A' :: B' :: C' :: M :: N :: Q :: nil) <= 4).
{
	assert(HNMtmp : rk(N :: nil) <= 1) by (solve_hyps_max HNeq HNM1).
	assert(HA'B'C'MQeq : rk(A' :: B' :: C' :: M :: Q :: nil) = 3) by (apply LA'B'C'MQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HA'B'C'MQMtmp : rk(A' :: B' :: C' :: M :: Q :: nil) <= 3) by (solve_hyps_max HA'B'C'MQeq HA'B'C'MQM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (N :: nil) (A' :: B' :: C' :: M :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: N :: Q :: nil) (N :: A' :: B' :: C' :: M :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (N :: A' :: B' :: C' :: M :: Q :: nil) ((N :: nil) ++ (A' :: B' :: C' :: M :: Q :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (N :: nil) (A' :: B' :: C' :: M :: Q :: nil) (nil) 1 3 0 HNMtmp HA'B'C'MQMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: A' :: B' :: C' :: M :: N :: Q ::  de rang :  5 et 5 	 AiB : M :: N ::  de rang :  2 et 2 	 A : A :: B :: C :: M :: N ::   de rang : 3 et 3 *)
assert(HA'B'C'MNQm4 : rk(A' :: B' :: C' :: M :: N :: Q :: nil) >= 4).
{
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(HABCA'B'C'MNQeq : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) = 5) by (apply LABCA'B'C'MNQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HABCA'B'C'MNQmtmp : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) >= 5) by (solve_hyps_min HABCA'B'C'MNQeq HABCA'B'C'MNQm5).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: C :: M :: N :: nil) (A' :: B' :: C' :: M :: N :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: M :: N :: Q :: nil) (A :: B :: C :: M :: N :: A' :: B' :: C' :: M :: N :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: A' :: B' :: C' :: M :: N :: Q :: nil) ((A :: B :: C :: M :: N :: nil) ++ (A' :: B' :: C' :: M :: N :: Q :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'MNQmtmp;try rewrite HT2 in HABCA'B'C'MNQmtmp.
	assert(HT := rule_4 (A :: B :: C :: M :: N :: nil) (A' :: B' :: C' :: M :: N :: Q :: nil) (M :: N :: nil) 5 2 3 HABCA'B'C'MNQmtmp HMNmtmp HABCMNMtmp Hincl); apply HT.
}

assert(HA'B'C'MNQM : rk(A' :: B' :: C' :: M :: N :: Q ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA'B'C'MNQm : rk(A' :: B' :: C' :: M :: N :: Q ::  nil) >= 1) by (solve_hyps_min HA'B'C'MNQeq HA'B'C'MNQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNQ : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> rk(M :: N :: Q ::  nil) = 3.
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNQ requis par la preuve de (?)MNQ pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNQ requis par la preuve de (?)MNQ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HMNQm2 : rk(M :: N :: Q :: nil) >= 2).
{
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: Q :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: Q :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A' :: B' :: C' :: M :: N :: Q ::  de rang :  4 et 4 	 AiB : M :: Q ::  de rang :  2 et 2 	 A : A' :: B' :: C' :: M :: Q ::   de rang : 3 et 3 *)
assert(HMNQm3 : rk(M :: N :: Q :: nil) >= 3).
{
	assert(HA'B'C'MQeq : rk(A' :: B' :: C' :: M :: Q :: nil) = 3) by (apply LA'B'C'MQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HA'B'C'MQMtmp : rk(A' :: B' :: C' :: M :: Q :: nil) <= 3) by (solve_hyps_max HA'B'C'MQeq HA'B'C'MQM3).
	assert(HA'B'C'MNQeq : rk(A' :: B' :: C' :: M :: N :: Q :: nil) = 4) by (apply LA'B'C'MNQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HA'B'C'MNQmtmp : rk(A' :: B' :: C' :: M :: N :: Q :: nil) >= 4) by (solve_hyps_min HA'B'C'MNQeq HA'B'C'MNQm4).
	assert(HMQeq : rk(M :: Q :: nil) = 2) by (apply LMQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption).
	assert(HMQmtmp : rk(M :: Q :: nil) >= 2) by (solve_hyps_min HMQeq HMQm2).
	assert(Hincl : incl (M :: Q :: nil) (list_inter (A' :: B' :: C' :: M :: Q :: nil) (M :: N :: Q :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: N :: Q :: nil) (A' :: B' :: C' :: M :: Q :: M :: N :: Q :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M :: Q :: M :: N :: Q :: nil) ((A' :: B' :: C' :: M :: Q :: nil) ++ (M :: N :: Q :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HA'B'C'MNQmtmp;try rewrite HT2 in HA'B'C'MNQmtmp.
	assert(HT := rule_4 (A' :: B' :: C' :: M :: Q :: nil) (M :: N :: Q :: nil) (M :: Q :: nil) 4 2 3 HA'B'C'MNQmtmp HMQmtmp HA'B'C'MQMtmp Hincl); apply HT.
}

assert(HMNQM : rk(M :: N :: Q ::  nil) <= 3) (* dim : 4 *) by (solve_hyps_max HMNQeq HMNQM3).
assert(HMNQm : rk(M :: N :: Q ::  nil) >= 1) by (solve_hyps_min HMNQeq HMNQm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C A' B' C' A'' B'' C'' M N Q ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A'' :: B'' :: C'' ::  nil) = 3 -> rk(A :: B :: C :: A'' :: B'' :: C'' ::  nil) = 5 -> rk(A' :: B' :: C' :: A'' :: B'' :: C'' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A' :: B' :: C' :: Q ::  nil) = 3 ->
rk(A'' :: B'' :: C'' :: Q ::  nil) = 3 -> 
	 rk(M :: N :: Q ::  nil) = 3  .
Proof.

intros A B C A' B' C' A'' B'' C'' M N Q 
HABCeq HA'B'C'eq HABCA'B'C'eq HA''B''C''eq HABCA''B''C''eq HA'B'C'A''B''C''eq HABCMeq HA'B'C'Meq HABCNeq HA''B''C''Neq
HMNeq HA'B'C'Qeq HA''B''C''Qeq .
repeat split.

	apply LMNQ with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (A'' := A'') (B'' := B'') (C'' := C'') (M := M) (N := N) (Q := Q) ; assumption.
Qed .
