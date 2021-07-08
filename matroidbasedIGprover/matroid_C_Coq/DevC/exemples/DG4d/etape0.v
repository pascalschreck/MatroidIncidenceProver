Load "preamble4D.v".


(* dans la couche 0 *)
Lemma LABCMN : forall A B C A' B' C' M N ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C A' B' C' M N 
HABCeq HA'B'C'eq HABCA'B'C'eq HABCMeq HA'B'C'Meq HABCNeq HA'B'C'Neq .

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
Lemma LA'B'C'MN : forall A B C A' B' C' M N ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(A' :: B' :: C' :: M :: N ::  nil) = 3.
Proof.

intros A B C A' B' C' M N 
HABCeq HA'B'C'eq HABCA'B'C'eq HABCMeq HA'B'C'Meq HABCNeq HA'B'C'Neq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour A'B'C'MN requis par la preuve de (?)A'B'C'MN pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour A'B'C'MN requis par la preuve de (?)A'B'C'MN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour A'B'C'MN requis par la preuve de (?)A'B'C'MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HA'B'C'MNm3 : rk(A' :: B' :: C' :: M :: N :: nil) >= 3).
{
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: nil) (A' :: B' :: C' :: M :: N :: nil) 3 3 HA'B'C'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HA'B'C'MNM4 : rk(A' :: B' :: C' :: M :: N :: nil) <= 4).
{
	assert(HMMtmp : rk(M :: nil) <= 1) by (solve_hyps_max HMeq HMM1).
	assert(HA'B'C'NMtmp : rk(A' :: B' :: C' :: N :: nil) <= 3) by (solve_hyps_max HA'B'C'Neq HA'B'C'NM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (M :: nil) (A' :: B' :: C' :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: N :: nil) (M :: A' :: B' :: C' :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (M :: A' :: B' :: C' :: N :: nil) ((M :: nil) ++ (A' :: B' :: C' :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (M :: nil) (A' :: B' :: C' :: N :: nil) (nil) 1 3 0 HMMtmp HA'B'C'NMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HA'B'C'MNM3 : rk(A' :: B' :: C' :: M :: N :: nil) <= 3).
{
	assert(HA'B'C'MMtmp : rk(A' :: B' :: C' :: M :: nil) <= 3) by (solve_hyps_max HA'B'C'Meq HA'B'C'MM3).
	assert(HA'B'C'NMtmp : rk(A' :: B' :: C' :: N :: nil) <= 3) by (solve_hyps_max HA'B'C'Neq HA'B'C'NM3).
	assert(HA'B'C'mtmp : rk(A' :: B' :: C' :: nil) >= 3) by (solve_hyps_min HA'B'C'eq HA'B'C'm3).
	assert(Hincl : incl (A' :: B' :: C' :: nil) (list_inter (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A' :: B' :: C' :: M :: N :: nil) (A' :: B' :: C' :: M :: A' :: B' :: C' :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: M :: A' :: B' :: C' :: N :: nil) ((A' :: B' :: C' :: M :: nil) ++ (A' :: B' :: C' :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: M :: nil) (A' :: B' :: C' :: N :: nil) (A' :: B' :: C' :: nil) 3 3 3 HA'B'C'MMtmp HA'B'C'NMtmp HA'B'C'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HA'B'C'MNM : rk(A' :: B' :: C' :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HA'B'C'MNm : rk(A' :: B' :: C' :: M :: N ::  nil) >= 1) by (solve_hyps_min HA'B'C'MNeq HA'B'C'MNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCA'B'C'MN : forall A B C A' B' C' M N ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' :: M :: N ::  nil) = 5.
Proof.

intros A B C A' B' C' M N 
HABCeq HA'B'C'eq HABCA'B'C'eq HABCMeq HA'B'C'Meq HABCNeq HA'B'C'Neq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B'C'MN requis par la preuve de (?)ABCA'B'C'MN pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCA'B' requis par la preuve de (?)ABCA'B'C'MN pour la règle 5  *)
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

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABCA'B'C'MN requis par la preuve de (?)ABCA'B'C'MN pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCA'B'C'MN requis par la preuve de (?)ABCA'B'C'MN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNm3 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) >= 3).
{
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCA'B'C'MNm4 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) >= 4).
{
	assert(HABCA'B'mtmp : rk(A :: B :: C :: A' :: B' :: nil) >= 4) by (solve_hyps_min HABCA'B'eq HABCA'B'm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) 4 4 HABCA'B'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'MNm5 : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) >= 5).
{
	assert(HABCA'B'C'mtmp : rk(A :: B :: C :: A' :: B' :: C' :: nil) >= 5) by (solve_hyps_min HABCA'B'C'eq HABCA'B'C'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: A' :: B' :: C' :: nil) (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) 5 5 HABCA'B'C'mtmp Hcomp Hincl);apply HT.
}

assert(HABCA'B'C'MNM : rk(A :: B :: C :: A' :: B' :: C' :: M :: N ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCA'B'C'MNm : rk(A :: B :: C :: A' :: B' :: C' :: M :: N ::  nil) >= 1) by (solve_hyps_min HABCA'B'C'MNeq HABCA'B'C'MNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMN : forall A B C A' B' C' M N ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A' :: B' :: C' :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 1.
Proof.

intros A B C A' B' C' M N 
HABCeq HA'B'C'eq HABCA'B'C'eq HABCMeq HA'B'C'Meq HABCNeq HA'B'C'Neq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour MN requis par la preuve de (?)MN pour la règle 3  *)
(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HMNM1 : rk(M :: N :: nil) <= 1).
{
	assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) ; assumption).
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	assert(HA'B'C'MNeq : rk(A' :: B' :: C' :: M :: N :: nil) = 3) by (apply LA'B'C'MN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) ; assumption).
	assert(HA'B'C'MNMtmp : rk(A' :: B' :: C' :: M :: N :: nil) <= 3) by (solve_hyps_max HA'B'C'MNeq HA'B'C'MNM3).
	assert(HABCA'B'C'MNeq : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) = 5) by (apply LABCA'B'C'MN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) ; assumption).
	assert(HABCA'B'C'MNmtmp : rk(A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) >= 5) by (solve_hyps_min HABCA'B'C'MNeq HABCA'B'C'MNm5).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: C :: M :: N :: nil) (A' :: B' :: C' :: M :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: M :: N :: nil) (A :: B :: C :: M :: N :: A' :: B' :: C' :: M :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: A' :: B' :: C' :: M :: N :: nil) ((A :: B :: C :: M :: N :: nil) ++ (A' :: B' :: C' :: M :: N :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'MNmtmp;try rewrite HT2 in HABCA'B'C'MNmtmp.
	assert(HT := rule_3 (A :: B :: C :: M :: N :: nil) (A' :: B' :: C' :: M :: N :: nil) (M :: N :: nil) 3 3 5 HABCMNMtmp HA'B'C'MNMtmp HABCA'B'C'MNmtmp Hincl);apply HT.
}


assert(HMNM : rk(M :: N ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max HMNeq HMNM2).
assert(HMNm : rk(M :: N ::  nil) >= 1) by (solve_hyps_min HMNeq HMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C A' B' C' M N ,
rk(A :: B :: C ::  nil) = 3 -> rk(A' :: B' :: C' ::  nil) = 3 -> rk(A :: B :: C :: A' :: B' :: C' ::  nil) = 5 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(A' :: B' :: C' :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(A' :: B' :: C' :: N ::  nil) = 3 -> 
	 rk(M :: N ::  nil) = 1  .
Proof.

intros A B C A' B' C' M N 
HABCeq HA'B'C'eq HABCA'B'C'eq HABCMeq HA'B'C'Meq HABCNeq HA'B'C'Neq .
repeat split.

	apply LMN with (A := A) (B := B) (C := C) (A' := A') (B' := B') (C' := C') (M := M) (N := N) ; assumption.
Qed .
