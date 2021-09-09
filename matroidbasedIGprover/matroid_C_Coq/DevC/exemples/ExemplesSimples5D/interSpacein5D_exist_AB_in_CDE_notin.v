Load "preamble5D.v".


(* dans la couche 0 *)
Lemma LCA' : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: A' ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CA' requis par la preuve de (?)CA' pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HCA'm2 : rk(C :: A' :: nil) >= 2).
{
	assert(HA'B'C'D'E'Mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'eq HA'B'C'D'E'M5).
	assert(HCA'B'C'D'E'mtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'eq HCA'B'C'D'E'm6).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (C :: A' :: nil) (A' :: B' :: C' :: D' :: E' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: A' :: B' :: C' :: D' :: E' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: A' :: B' :: C' :: D' :: E' :: nil) ((C :: A' :: nil) ++ (A' :: B' :: C' :: D' :: E' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCA'B'C'D'E'mtmp;try rewrite HT2 in HCA'B'C'D'E'mtmp.
	assert(HT := rule_2 (C :: A' :: nil) (A' :: B' :: C' :: D' :: E' :: nil) (A' :: nil) 6 1 5 HCA'B'C'D'E'mtmp HA'mtmp HA'B'C'D'E'Mtmp Hincl);apply HT.
}

assert(HCA'M : rk(C :: A' ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HCA'eq HCA'M2).
assert(HCA'm : rk(C :: A' ::  nil) >= 1) by (solve_hyps_min HCA'eq HCA'm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LEA' : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(E :: A' ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EA' requis par la preuve de (?)EA' pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HEA'm2 : rk(E :: A' :: nil) >= 2).
{
	assert(HA'B'C'D'E'Mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'eq HA'B'C'D'E'M5).
	assert(HEA'B'C'D'E'mtmp : rk(E :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HEA'B'C'D'E'eq HEA'B'C'D'E'm6).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (E :: A' :: nil) (A' :: B' :: C' :: D' :: E' :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (E :: A' :: B' :: C' :: D' :: E' :: nil) (E :: A' :: A' :: B' :: C' :: D' :: E' :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A' :: A' :: B' :: C' :: D' :: E' :: nil) ((E :: A' :: nil) ++ (A' :: B' :: C' :: D' :: E' :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HEA'B'C'D'E'mtmp;try rewrite HT2 in HEA'B'C'D'E'mtmp.
	assert(HT := rule_2 (E :: A' :: nil) (A' :: B' :: C' :: D' :: E' :: nil) (A' :: nil) 6 1 5 HEA'B'C'D'E'mtmp HA'mtmp HA'B'C'D'E'Mtmp Hincl);apply HT.
}

assert(HEA'M : rk(E :: A' ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HEA'eq HEA'M2).
assert(HEA'm : rk(E :: A' ::  nil) >= 1) by (solve_hyps_min HEA'eq HEA'm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAF *)
(* dans la couche 0 *)
Lemma LABCDEF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: F ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDEF requis par la preuve de (?)ABCDEF pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCDF requis par la preuve de (?)ABCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDF requis par la preuve de (?)ABCDF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDF requis par la preuve de (?)ACDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDFM3 : rk(A :: C :: D :: F :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: F :: nil) (A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: nil) ((A :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HAMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDF requis par la preuve de (?)ABCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDFM4 : rk(A :: B :: C :: D :: F :: nil) <= 4).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HACDFMtmp : rk(A :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HACDFeq HACDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: F :: nil) (B :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: C :: D :: F :: nil) ((B :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: C :: D :: F :: nil) (nil) 1 3 0 HBMtmp HACDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEF requis par la preuve de (?)ABCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDEFM5 : rk(A :: B :: C :: D :: E :: F :: nil) <= 5).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HABCDFMtmp : rk(A :: B :: C :: D :: F :: nil) <= 4) by (solve_hyps_max HABCDFeq HABCDFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: nil) (E :: A :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: B :: C :: D :: F :: nil) ((E :: nil) ++ (A :: B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: B :: C :: D :: F :: nil) (nil) 1 4 0 HEMtmp HABCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFm5 : rk(A :: B :: C :: D :: E :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEFM : rk(A :: B :: C :: D :: E :: F ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEFm : rk(A :: B :: C :: D :: E :: F ::  nil) >= 1) by (solve_hyps_min HABCDEFeq HABCDEFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAF *)
(* dans la couche 0 *)
Lemma LAF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: F ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEF requis par la preuve de (?)AF pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEFm3 : rk(B :: C :: D :: E :: F :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 5 0 2 HABCDEA'Fmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AF requis par la preuve de (?)AF pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 5*)
assert(HAFm2 : rk(A :: F :: nil) >= 2).
{
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(HABCDEFeq : rk(A :: B :: C :: D :: E :: F :: nil) = 5) by (apply LABCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEFmtmp : rk(A :: B :: C :: D :: E :: F :: nil) >= 5) by (solve_hyps_min HABCDEFeq HABCDEFm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: F :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: nil) (A :: F :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: F :: B :: C :: D :: E :: F :: nil) ((A :: F :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFmtmp;try rewrite HT2 in HABCDEFmtmp.
	assert(HT := rule_2 (A :: F :: nil) (B :: C :: D :: E :: F :: nil) (F :: nil) 5 1 4 HABCDEFmtmp HFmtmp HBCDEFMtmp Hincl);apply HT.
}

assert(HAFM : rk(A :: F ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HAFeq HAFM2).
assert(HAFm : rk(A :: F ::  nil) >= 1) by (solve_hyps_min HAFeq HAFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBF *)
(* dans la couche 0 *)
Lemma LBCDEF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: C :: D :: E :: F ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEFm3 : rk(B :: C :: D :: E :: F :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 5 0 2 HABCDEA'Fmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F ::  de rang :  5 et 5 	 AiB : F ::  de rang :  1 et 1 	 A : A :: F ::   de rang : 2 et 2 *)
assert(HBCDEFm4 : rk(B :: C :: D :: E :: F :: nil) >= 4).
{
	assert(HAFeq : rk(A :: F :: nil) = 2) by (apply LAF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAFMtmp : rk(A :: F :: nil) <= 2) by (solve_hyps_max HAFeq HAFM2).
	assert(HABCDEFeq : rk(A :: B :: C :: D :: E :: F :: nil) = 5) by (apply LABCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEFmtmp : rk(A :: B :: C :: D :: E :: F :: nil) >= 5) by (solve_hyps_min HABCDEFeq HABCDEFm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: F :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: nil) (A :: F :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: F :: B :: C :: D :: E :: F :: nil) ((A :: F :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFmtmp;try rewrite HT2 in HABCDEFmtmp.
	assert(HT := rule_4 (A :: F :: nil) (B :: C :: D :: E :: F :: nil) (F :: nil) 5 1 2 HABCDEFmtmp HFmtmp HAFMtmp Hincl); apply HT.
}

assert(HBCDEFM : rk(B :: C :: D :: E :: F ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HBCDEFeq HBCDEFM5).
assert(HBCDEFm : rk(B :: C :: D :: E :: F ::  nil) >= 1) by (solve_hyps_min HBCDEFeq HBCDEFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBF *)
(* dans la couche 0 *)
Lemma LBF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: F ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEF requis par la preuve de (?)BF pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'FM5 : rk(B :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HBCDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Fm4 : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEF requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEF requis par la preuve de (?)CDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEFM3 : rk(C :: D :: E :: F :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: nil) (E :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: C :: D :: F :: nil) ((E :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HEMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEFm2 : rk(C :: D :: E :: F :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Fmtmp : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HBCDEA'Feq HBCDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: F :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Fmtmp;try rewrite HT2 in HBCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: F :: nil) (nil) 4 0 2 HBCDEA'Fmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BF requis par la preuve de (?)BF pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 5*)
assert(HBFm2 : rk(B :: F :: nil) >= 2).
{
	assert(HCDEFMtmp : rk(C :: D :: E :: F :: nil) <= 3) by (solve_hyps_max HCDEFeq HCDEFM3).
	assert(HBCDEFeq : rk(B :: C :: D :: E :: F :: nil) = 4) by (apply LBCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEFmtmp : rk(B :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HBCDEFeq HBCDEFm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (B :: F :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: C :: D :: E :: F :: nil) ((B :: F :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFmtmp;try rewrite HT2 in HBCDEFmtmp.
	assert(HT := rule_2 (B :: F :: nil) (C :: D :: E :: F :: nil) (F :: nil) 4 1 3 HBCDEFmtmp HFmtmp HCDEFMtmp Hincl);apply HT.
}

assert(HBFM : rk(B :: F ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HBFeq HBFM2).
assert(HBFm : rk(B :: F ::  nil) >= 1) by (solve_hyps_min HBFeq HBFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCF *)
(* dans la couche 0 *)
Lemma LCA'B'C'D'E'F : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' :: F ::  nil) = 6.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour CA'B'C'D'E'F requis par la preuve de (?)CA'B'C'D'E'F pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour CA'B'C'D'E'F requis par la preuve de (?)CA'B'C'D'E'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCA'B'C'D'E'Fm5 : rk(C :: A' :: B' :: C' :: D' :: E' :: F :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: F :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCA'B'C'D'E'Fm6 : rk(C :: A' :: B' :: C' :: D' :: E' :: F :: nil) >= 6).
{
	assert(HCA'B'C'D'E'mtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'eq HCA'B'C'D'E'm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (C :: A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: F :: nil) 6 6 HCA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

assert(HCA'B'C'D'E'FM : rk(C :: A' :: B' :: C' :: D' :: E' :: F ::  nil) <= 6) by (apply rk_upper_dim).
assert(HCA'B'C'D'E'Fm : rk(C :: A' :: B' :: C' :: D' :: E' :: F ::  nil) >= 1) by (solve_hyps_min HCA'B'C'D'E'Feq HCA'B'C'D'E'Fm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: F ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CF requis par la preuve de (?)CF pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HCFm2 : rk(C :: F :: nil) >= 2).
{
	assert(HA'B'C'D'E'FMtmp : rk(A' :: B' :: C' :: D' :: E' :: F :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Feq HA'B'C'D'E'FM5).
	assert(HCA'B'C'D'E'Feq : rk(C :: A' :: B' :: C' :: D' :: E' :: F :: nil) = 6) by (apply LCA'B'C'D'E'F with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'B'C'D'E'Fmtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: F :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'Feq HCA'B'C'D'E'Fm6).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (C :: F :: nil) (A' :: B' :: C' :: D' :: E' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: A' :: B' :: C' :: D' :: E' :: F :: nil) (C :: F :: A' :: B' :: C' :: D' :: E' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: F :: A' :: B' :: C' :: D' :: E' :: F :: nil) ((C :: F :: nil) ++ (A' :: B' :: C' :: D' :: E' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCA'B'C'D'E'Fmtmp;try rewrite HT2 in HCA'B'C'D'E'Fmtmp.
	assert(HT := rule_2 (C :: F :: nil) (A' :: B' :: C' :: D' :: E' :: F :: nil) (F :: nil) 6 1 5 HCA'B'C'D'E'Fmtmp HFmtmp HA'B'C'D'E'FMtmp Hincl);apply HT.
}

assert(HCFM : rk(C :: F ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HCFeq HCFM2).
assert(HCFm : rk(C :: F ::  nil) >= 1) by (solve_hyps_min HCFeq HCFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACF *)
(* dans la couche 0 *)
Lemma LACDEF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: C :: D :: E :: F ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEF requis par la preuve de (?)ACDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ACDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)ACDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEF requis par la preuve de (?)ACDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDF requis par la preuve de (?)ACDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDFM3 : rk(A :: C :: D :: F :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: F :: nil) (A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: nil) ((A :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HAMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEFM4 : rk(A :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDFMtmp : rk(A :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HACDFeq HACDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: nil) (E :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: F :: nil) ((E :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HACDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEFm3 : rk(A :: C :: D :: E :: F :: nil) >= 3).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: A :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: F :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: F :: nil) (nil) 5 0 2 HABCDEA'Fmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F ::  de rang :  5 et 5 	 AiB : F ::  de rang :  1 et 1 	 A : B :: F ::   de rang : 2 et 2 *)
assert(HACDEFm4 : rk(A :: C :: D :: E :: F :: nil) >= 4).
{
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFMtmp : rk(B :: F :: nil) <= 2) by (solve_hyps_max HBFeq HBFM2).
	assert(HABCDEFeq : rk(A :: B :: C :: D :: E :: F :: nil) = 5) by (apply LABCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEFmtmp : rk(A :: B :: C :: D :: E :: F :: nil) >= 5) by (solve_hyps_min HABCDEFeq HABCDEFm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (A :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: nil) (B :: F :: A :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: A :: C :: D :: E :: F :: nil) ((B :: F :: nil) ++ (A :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFmtmp;try rewrite HT2 in HABCDEFmtmp.
	assert(HT := rule_4 (B :: F :: nil) (A :: C :: D :: E :: F :: nil) (F :: nil) 5 1 2 HABCDEFmtmp HFmtmp HBFMtmp Hincl); apply HT.
}

assert(HACDEFM : rk(A :: C :: D :: E :: F ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HACDEFeq HACDEFM5).
assert(HACDEFm : rk(A :: C :: D :: E :: F ::  nil) >= 1) by (solve_hyps_min HACDEFeq HACDEFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACF *)
(* dans la couche 0 *)
Lemma LCDEF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: D :: E :: F ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEF requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'FM5 : rk(B :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HBCDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Fm4 : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEF requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEF requis par la preuve de (?)CDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEFM3 : rk(C :: D :: E :: F :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: nil) (E :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: C :: D :: F :: nil) ((E :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HEMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEFm2 : rk(C :: D :: E :: F :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Fmtmp : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HBCDEA'Feq HBCDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: F :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Fmtmp;try rewrite HT2 in HBCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: F :: nil) (nil) 4 0 2 HBCDEA'Fmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: F ::  de rang :  4 et 4 	 AiB : F ::  de rang :  1 et 1 	 A : B :: F ::   de rang : 2 et 2 *)
assert(HCDEFm3 : rk(C :: D :: E :: F :: nil) >= 3).
{
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFMtmp : rk(B :: F :: nil) <= 2) by (solve_hyps_max HBFeq HBFM2).
	assert(HBCDEFeq : rk(B :: C :: D :: E :: F :: nil) = 4) by (apply LBCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEFmtmp : rk(B :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HBCDEFeq HBCDEFm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (B :: F :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: C :: D :: E :: F :: nil) ((B :: F :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFmtmp;try rewrite HT2 in HBCDEFmtmp.
	assert(HT := rule_4 (B :: F :: nil) (C :: D :: E :: F :: nil) (F :: nil) 4 1 2 HBCDEFmtmp HFmtmp HBFMtmp Hincl); apply HT.
}

assert(HCDEFM : rk(C :: D :: E :: F ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HCDEFeq HCDEFM4).
assert(HCDEFm : rk(C :: D :: E :: F ::  nil) >= 1) by (solve_hyps_min HCDEFeq HCDEFm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: C :: F ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACF requis par la preuve de (?)ACF pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACDF requis par la preuve de (?)ACF pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEA'F requis par la preuve de (?)ACDF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEA'F requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEF requis par la preuve de (?)ACDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDF requis par la preuve de (?)ACDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDFM3 : rk(A :: C :: D :: F :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: F :: nil) (A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: nil) ((A :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HAMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEFM4 : rk(A :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDFMtmp : rk(A :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HACDFeq HACDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: nil) (E :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: F :: nil) ((E :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HACDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEA'F requis par la preuve de (?)ACDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEA'FM5 : rk(A :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HACDEFMtmp : rk(A :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HACDEFeq HACDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (A :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: F :: nil) (A' :: A :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: A :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (A :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (A :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HACDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEA'Fm4 : rk(A :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: A :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: A' :: F :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: A' ::   de rang : 2 et 2 *)
assert(HACDFm2 : rk(A :: C :: D :: F :: nil) >= 2).
{
	assert(HEA'eq : rk(E :: A' :: nil) = 2) by (apply LEA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEA'Mtmp : rk(E :: A' :: nil) <= 2) by (solve_hyps_max HEA'eq HEA'M2).
	assert(HACDEA'Fmtmp : rk(A :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HACDEA'Feq HACDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: A' :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: F :: nil) (E :: A' :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A' :: A :: C :: D :: F :: nil) ((E :: A' :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEA'Fmtmp;try rewrite HT2 in HACDEA'Fmtmp.
	assert(HT := rule_4 (E :: A' :: nil) (A :: C :: D :: F :: nil) (nil) 4 0 2 HACDEA'Fmtmp Hmtmp HEA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACF requis par la preuve de (?)ACF pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HACFm2 : rk(A :: C :: F :: nil) >= 2).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HACDFmtmp : rk(A :: C :: D :: F :: nil) >= 2) by (solve_hyps_min HACDFeq HACDFm2).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (A :: C :: F :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: F :: nil) (A :: C :: F :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: F :: C :: D :: F :: nil) ((A :: C :: F :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDFmtmp;try rewrite HT2 in HACDFmtmp.
	assert(HT := rule_2 (A :: C :: F :: nil) (C :: D :: F :: nil) (C :: F :: nil) 2 2 2 HACDFmtmp HCFmtmp HCDFMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HACFm3 : rk(A :: C :: F :: nil) >= 3).
{
	assert(HCDEFeq : rk(C :: D :: E :: F :: nil) = 3) by (apply LCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEFMtmp : rk(C :: D :: E :: F :: nil) <= 3) by (solve_hyps_max HCDEFeq HCDEFM3).
	assert(HACDEFeq : rk(A :: C :: D :: E :: F :: nil) = 4) by (apply LACDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDEFmtmp : rk(A :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HACDEFeq HACDEFm4).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (A :: C :: F :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: nil) (A :: C :: F :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: F :: C :: D :: E :: F :: nil) ((A :: C :: F :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEFmtmp;try rewrite HT2 in HACDEFmtmp.
	assert(HT := rule_2 (A :: C :: F :: nil) (C :: D :: E :: F :: nil) (C :: F :: nil) 4 2 3 HACDEFmtmp HCFmtmp HCDEFMtmp Hincl);apply HT.
}

assert(HACFM : rk(A :: C :: F ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HACFeq HACFM3).
assert(HACFm : rk(A :: C :: F ::  nil) >= 1) by (solve_hyps_min HACFeq HACFm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: C :: F ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCF requis par la preuve de (?)BCF pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCDF requis par la preuve de (?)BCF pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'FM5 : rk(B :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HBCDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Fm4 : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: A' ::   de rang : 2 et 2 *)
assert(HBCDFm2 : rk(B :: C :: D :: F :: nil) >= 2).
{
	assert(HEA'eq : rk(E :: A' :: nil) = 2) by (apply LEA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEA'Mtmp : rk(E :: A' :: nil) <= 2) by (solve_hyps_max HEA'eq HEA'M2).
	assert(HBCDEA'Fmtmp : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HBCDEA'Feq HBCDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: A' :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (E :: A' :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A' :: B :: C :: D :: F :: nil) ((E :: A' :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Fmtmp;try rewrite HT2 in HBCDEA'Fmtmp.
	assert(HT := rule_4 (E :: A' :: nil) (B :: C :: D :: F :: nil) (nil) 4 0 2 HBCDEA'Fmtmp Hmtmp HEA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCF requis par la preuve de (?)BCF pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HBCFm2 : rk(B :: C :: F :: nil) >= 2).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HBCDFmtmp : rk(B :: C :: D :: F :: nil) >= 2) by (solve_hyps_min HBCDFeq HBCDFm2).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (B :: C :: F :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: F :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: F :: C :: D :: F :: nil) ((B :: C :: F :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDFmtmp;try rewrite HT2 in HBCDFmtmp.
	assert(HT := rule_2 (B :: C :: F :: nil) (C :: D :: F :: nil) (C :: F :: nil) 2 2 2 HBCDFmtmp HCFmtmp HCDFMtmp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HBCFm3 : rk(B :: C :: F :: nil) >= 3).
{
	assert(HCDEFeq : rk(C :: D :: E :: F :: nil) = 3) by (apply LCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEFMtmp : rk(C :: D :: E :: F :: nil) <= 3) by (solve_hyps_max HCDEFeq HCDEFM3).
	assert(HBCDEFeq : rk(B :: C :: D :: E :: F :: nil) = 4) by (apply LBCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEFmtmp : rk(B :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HBCDEFeq HBCDEFm4).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (B :: C :: F :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (B :: C :: F :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: F :: C :: D :: E :: F :: nil) ((B :: C :: F :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFmtmp;try rewrite HT2 in HBCDEFmtmp.
	assert(HT := rule_2 (B :: C :: F :: nil) (C :: D :: E :: F :: nil) (C :: F :: nil) 4 2 3 HBCDEFmtmp HCFmtmp HCDEFMtmp Hincl);apply HT.
}

assert(HBCFM : rk(B :: C :: F ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HBCFeq HBCFM3).
assert(HBCFm : rk(B :: C :: F ::  nil) >= 1) by (solve_hyps_min HBCFeq HBCFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACDF *)
(* dans la couche 0 *)
Lemma LEF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(E :: F ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EF requis par la preuve de (?)EF pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : C :: D :: E :: F ::  de rang :  3 et 3 	 AiB : F ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HEFm2 : rk(E :: F :: nil) >= 2).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HCDEFeq : rk(C :: D :: E :: F :: nil) = 3) by (apply LCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEFmtmp : rk(C :: D :: E :: F :: nil) >= 3) by (solve_hyps_min HCDEFeq HCDEFm3).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (C :: D :: F :: nil) (E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: nil) (C :: D :: F :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: E :: F :: nil) ((C :: D :: F :: nil) ++ (E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEFmtmp;try rewrite HT2 in HCDEFmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (E :: F :: nil) (F :: nil) 3 1 2 HCDEFmtmp HFmtmp HCDFMtmp Hincl); apply HT.
}

assert(HEFM : rk(E :: F ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HEFeq HEFM2).
assert(HEFm : rk(E :: F ::  nil) >= 1) by (solve_hyps_min HEFeq HEFm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACDF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: C :: D :: F ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACDF requis par la preuve de (?)ACDF pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEA'F requis par la preuve de (?)ACDF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEA'F requis par la preuve de (?)ACDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEF requis par la preuve de (?)ACDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACDF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDF requis par la preuve de (?)ACDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACDFM3 : rk(A :: C :: D :: F :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: F :: nil) (A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: nil) ((A :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HAMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEF requis par la preuve de (?)ACDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEFM4 : rk(A :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HACDFMtmp : rk(A :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HACDFeq HACDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: nil) (E :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A :: C :: D :: F :: nil) ((E :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (A :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HACDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEA'F requis par la preuve de (?)ACDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEA'FM5 : rk(A :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HACDEFMtmp : rk(A :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HACDEFeq HACDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (A :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: F :: nil) (A' :: A :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: A :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (A :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (A :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HACDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEA'Fm4 : rk(A :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: A :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: A' :: F :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: A' ::   de rang : 2 et 2 *)
assert(HACDFm2 : rk(A :: C :: D :: F :: nil) >= 2).
{
	assert(HEA'eq : rk(E :: A' :: nil) = 2) by (apply LEA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEA'Mtmp : rk(E :: A' :: nil) <= 2) by (solve_hyps_max HEA'eq HEA'M2).
	assert(HACDEA'Fmtmp : rk(A :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HACDEA'Feq HACDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: A' :: nil) (A :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: F :: nil) (E :: A' :: A :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A' :: A :: C :: D :: F :: nil) ((E :: A' :: nil) ++ (A :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEA'Fmtmp;try rewrite HT2 in HACDEA'Fmtmp.
	assert(HT := rule_4 (E :: A' :: nil) (A :: C :: D :: F :: nil) (nil) 4 0 2 HACDEA'Fmtmp Hmtmp HEA'Mtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HACDFm3 : rk(A :: C :: D :: F :: nil) >= 3).
{
	assert(HEFeq : rk(E :: F :: nil) = 2) by (apply LEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEFMtmp : rk(E :: F :: nil) <= 2) by (solve_hyps_max HEFeq HEFM2).
	assert(HACDEFeq : rk(A :: C :: D :: E :: F :: nil) = 4) by (apply LACDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDEFmtmp : rk(A :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HACDEFeq HACDEFm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: C :: D :: F :: nil) (E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: nil) (A :: C :: D :: F :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: E :: F :: nil) ((A :: C :: D :: F :: nil) ++ (E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEFmtmp;try rewrite HT2 in HACDEFmtmp.
	assert(HT := rule_2 (A :: C :: D :: F :: nil) (E :: F :: nil) (F :: nil) 4 1 2 HACDEFmtmp HFmtmp HEFMtmp Hincl);apply HT.
}

assert(HACDFM : rk(A :: C :: D :: F ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HACDFeq HACDFM4).
assert(HACDFm : rk(A :: C :: D :: F ::  nil) >= 1) by (solve_hyps_min HACDFeq HACDFm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDF : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: C :: D :: F ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDF pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'FM5 : rk(B :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HBCDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Fm4 : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: A' ::   de rang : 2 et 2 *)
assert(HBCDFm2 : rk(B :: C :: D :: F :: nil) >= 2).
{
	assert(HEA'eq : rk(E :: A' :: nil) = 2) by (apply LEA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEA'Mtmp : rk(E :: A' :: nil) <= 2) by (solve_hyps_max HEA'eq HEA'M2).
	assert(HBCDEA'Fmtmp : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HBCDEA'Feq HBCDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: A' :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (E :: A' :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: A' :: B :: C :: D :: F :: nil) ((E :: A' :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Fmtmp;try rewrite HT2 in HBCDEA'Fmtmp.
	assert(HT := rule_4 (E :: A' :: nil) (B :: C :: D :: F :: nil) (nil) 4 0 2 HBCDEA'Fmtmp Hmtmp HEA'Mtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et 4*)
assert(HBCDFm3 : rk(B :: C :: D :: F :: nil) >= 3).
{
	assert(HEFeq : rk(E :: F :: nil) = 2) by (apply LEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEFMtmp : rk(E :: F :: nil) <= 2) by (solve_hyps_max HEFeq HEFM2).
	assert(HBCDEFeq : rk(B :: C :: D :: E :: F :: nil) = 4) by (apply LBCDEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEFmtmp : rk(B :: C :: D :: E :: F :: nil) >= 4) by (solve_hyps_min HBCDEFeq HBCDEFm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: C :: D :: F :: nil) (E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (B :: C :: D :: F :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: E :: F :: nil) ((B :: C :: D :: F :: nil) ++ (E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFmtmp;try rewrite HT2 in HBCDEFmtmp.
	assert(HT := rule_2 (B :: C :: D :: F :: nil) (E :: F :: nil) (F :: nil) 4 1 2 HBCDEFmtmp HFmtmp HEFMtmp Hincl);apply HT.
}

assert(HBCDFM : rk(B :: C :: D :: F ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HBCDFeq HBCDFM4).
assert(HBCDFm : rk(B :: C :: D :: F ::  nil) >= 1) by (solve_hyps_min HBCDFeq HBCDFm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCG *)
(* dans la couche 0 *)
Lemma LCA'B'C'D'E'G : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' :: G ::  nil) = 6.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour CA'B'C'D'E'G requis par la preuve de (?)CA'B'C'D'E'G pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour CA'B'C'D'E'G requis par la preuve de (?)CA'B'C'D'E'G pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCA'B'C'D'E'Gm5 : rk(C :: A' :: B' :: C' :: D' :: E' :: G :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: G :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: G :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCA'B'C'D'E'Gm6 : rk(C :: A' :: B' :: C' :: D' :: E' :: G :: nil) >= 6).
{
	assert(HCA'B'C'D'E'mtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'eq HCA'B'C'D'E'm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (C :: A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: G :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: A' :: B' :: C' :: D' :: E' :: nil) (C :: A' :: B' :: C' :: D' :: E' :: G :: nil) 6 6 HCA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

assert(HCA'B'C'D'E'GM : rk(C :: A' :: B' :: C' :: D' :: E' :: G ::  nil) <= 6) by (apply rk_upper_dim).
assert(HCA'B'C'D'E'Gm : rk(C :: A' :: B' :: C' :: D' :: E' :: G ::  nil) >= 1) by (solve_hyps_min HCA'B'C'D'E'Geq HCA'B'C'D'E'Gm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCG : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: G ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CG requis par la preuve de (?)CG pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HCGm2 : rk(C :: G :: nil) >= 2).
{
	assert(HA'B'C'D'E'GMtmp : rk(A' :: B' :: C' :: D' :: E' :: G :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Geq HA'B'C'D'E'GM5).
	assert(HCA'B'C'D'E'Geq : rk(C :: A' :: B' :: C' :: D' :: E' :: G :: nil) = 6) by (apply LCA'B'C'D'E'G with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'B'C'D'E'Gmtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: G :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'Geq HCA'B'C'D'E'Gm6).
	assert(HGmtmp : rk(G :: nil) >= 1) by (solve_hyps_min HGeq HGm1).
	assert(Hincl : incl (G :: nil) (list_inter (C :: G :: nil) (A' :: B' :: C' :: D' :: E' :: G :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: A' :: B' :: C' :: D' :: E' :: G :: nil) (C :: G :: A' :: B' :: C' :: D' :: E' :: G :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: G :: A' :: B' :: C' :: D' :: E' :: G :: nil) ((C :: G :: nil) ++ (A' :: B' :: C' :: D' :: E' :: G :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCA'B'C'D'E'Gmtmp;try rewrite HT2 in HCA'B'C'D'E'Gmtmp.
	assert(HT := rule_2 (C :: G :: nil) (A' :: B' :: C' :: D' :: E' :: G :: nil) (G :: nil) 6 1 5 HCA'B'C'D'E'Gmtmp HGmtmp HA'B'C'D'E'GMtmp Hincl);apply HT.
}

assert(HCGM : rk(C :: G ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HCGeq HCGM2).
assert(HCGm : rk(C :: G ::  nil) >= 1) by (solve_hyps_min HCGeq HCGm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAH *)
(* dans constructLemma(), requis par LADEH *)
(* dans constructLemma(), requis par LACDEFH *)
(* dans la couche 0 *)
Lemma LACDEFH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: C :: D :: E :: F :: H ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEH requis par la preuve de (?)ACDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEA'H requis par la preuve de (?)ADEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEA'H requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEH requis par la preuve de (?)ACDEA'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEH requis par la preuve de (?)ACDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEH requis par la preuve de (?)ADEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEHM3 : rk(A :: D :: E :: H :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: H :: nil) (A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: H :: nil) ((A :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HAMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEH requis par la preuve de (?)ACDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEHM4 : rk(A :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADEHMtmp : rk(A :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HADEHeq HADEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: H :: nil) (C :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: E :: H :: nil) ((C :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HADEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEA'H requis par la preuve de (?)ACDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEA'HM5 : rk(A :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HACDEHMtmp : rk(A :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HACDEHeq HACDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (A :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: H :: nil) (A' :: A :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: A :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (A :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (A :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HACDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEA'Hm4 : rk(A :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: A :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: A' :: H :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: A' ::   de rang : 2 et 2 *)
assert(HADEHm2 : rk(A :: D :: E :: H :: nil) >= 2).
{
	assert(HCA'eq : rk(C :: A' :: nil) = 2) by (apply LCA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'Mtmp : rk(C :: A' :: nil) <= 2) by (solve_hyps_max HCA'eq HCA'M2).
	assert(HACDEA'Hmtmp : rk(A :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HACDEA'Heq HACDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: A' :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: H :: nil) (C :: A' :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: A :: D :: E :: H :: nil) ((C :: A' :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEA'Hmtmp;try rewrite HT2 in HACDEA'Hmtmp.
	assert(HT := rule_4 (C :: A' :: nil) (A :: D :: E :: H :: nil) (nil) 4 0 2 HACDEA'Hmtmp Hmtmp HCA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEFH requis par la preuve de (?)ACDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ACDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ACDEFH requis par la preuve de (?)ACDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEFH requis par la preuve de (?)ACDEFH pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACDEH requis par la preuve de (?)ACDEFH pour la règle 1  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEHm3 : rk(A :: C :: D :: E :: H :: nil) >= 3).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: A :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: H :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEFH requis par la preuve de (?)ACDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEFHM5 : rk(A :: C :: D :: E :: F :: H :: nil) <= 5).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HACDEHMtmp : rk(A :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HACDEHeq HACDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (A :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: H :: nil) (F :: A :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: A :: C :: D :: E :: H :: nil) ((F :: nil) ++ (A :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (A :: C :: D :: E :: H :: nil) (nil) 1 4 0 HFMtmp HACDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACDEFHm2 : rk(A :: C :: D :: E :: F :: H :: nil) >= 2).
{
	assert(HAFeq : rk(A :: F :: nil) = 2) by (apply LAF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAFmtmp : rk(A :: F :: nil) >= 2) by (solve_hyps_min HAFeq HAFm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: F :: nil) (A :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: F :: nil) (A :: C :: D :: E :: F :: H :: nil) 2 2 HAFmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : B :: F ::   de rang : 2 et 2 *)
assert(HACDEFHm4 : rk(A :: C :: D :: E :: F :: H :: nil) >= 4).
{
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFMtmp : rk(B :: F :: nil) <= 2) by (solve_hyps_max HBFeq HBFM2).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (A :: C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (B :: F :: A :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: A :: C :: D :: E :: F :: H :: nil) ((B :: F :: nil) ++ (A :: C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (B :: F :: nil) (A :: C :: D :: E :: F :: H :: nil) (F :: nil) 5 1 2 HABCDEFHmtmp HFmtmp HBFMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HACDEFHM4 : rk(A :: C :: D :: E :: F :: H :: nil) <= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HADEHMtmp : rk(A :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HADEHeq HADEHM3).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: D :: F :: nil) (A :: D :: E :: H :: nil) (D :: nil) 2 3 1 HCDFMtmp HADEHMtmp HDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HACDEFHM : rk(A :: C :: D :: E :: F :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HACDEFHm : rk(A :: C :: D :: E :: F :: H ::  nil) >= 1) by (solve_hyps_min HACDEFHeq HACDEFHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LADEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: D :: E :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ADEH requis par la preuve de (?)ADEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ACDEA'H requis par la preuve de (?)ADEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEA'H requis par la preuve de (?)ACDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACDEH requis par la preuve de (?)ACDEA'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEH requis par la preuve de (?)ACDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEH requis par la preuve de (?)ADEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEHM3 : rk(A :: D :: E :: H :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: H :: nil) (A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: H :: nil) ((A :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HAMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ACDEH requis par la preuve de (?)ACDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEHM4 : rk(A :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HADEHMtmp : rk(A :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HADEHeq HADEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: H :: nil) (C :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: D :: E :: H :: nil) ((C :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HADEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ACDEA'H requis par la preuve de (?)ACDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HACDEA'HM5 : rk(A :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HACDEHMtmp : rk(A :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HACDEHeq HACDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (A :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: H :: nil) (A' :: A :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: A :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (A :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (A :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HACDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HACDEA'Hm4 : rk(A :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (B :: A' :: nil) (A :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: A :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: A :: C :: D :: E :: A' :: H :: nil) ((B :: A' :: nil) ++ (A :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (A :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: A' ::   de rang : 2 et 2 *)
assert(HADEHm2 : rk(A :: D :: E :: H :: nil) >= 2).
{
	assert(HCA'eq : rk(C :: A' :: nil) = 2) by (apply LCA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'Mtmp : rk(C :: A' :: nil) <= 2) by (solve_hyps_max HCA'eq HCA'M2).
	assert(HACDEA'Hmtmp : rk(A :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HACDEA'Heq HACDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: A' :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: A' :: H :: nil) (C :: A' :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: A :: D :: E :: H :: nil) ((C :: A' :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEA'Hmtmp;try rewrite HT2 in HACDEA'Hmtmp.
	assert(HT := rule_4 (C :: A' :: nil) (A :: D :: E :: H :: nil) (nil) 4 0 2 HACDEA'Hmtmp Hmtmp HCA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: C :: D :: E :: F :: H ::  de rang :  4 et 4 	 AiB : D ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HADEHm3 : rk(A :: D :: E :: H :: nil) >= 3).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HACDEFHeq : rk(A :: C :: D :: E :: F :: H :: nil) = 4) by (apply LACDEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDEFHmtmp : rk(A :: C :: D :: E :: F :: H :: nil) >= 4) by (solve_hyps_min HACDEFHeq HACDEFHm4).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACDEFHmtmp;try rewrite HT2 in HACDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: D :: E :: H :: nil) (D :: nil) 4 1 2 HACDEFHmtmp HDmtmp HCDFMtmp Hincl); apply HT.
}

assert(HADEHM : rk(A :: D :: E :: H ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HADEHeq HADEHM4).
assert(HADEHm : rk(A :: D :: E :: H ::  nil) >= 1) by (solve_hyps_min HADEHeq HADEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: H ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AH requis par la preuve de (?)AH pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HAHm2 : rk(A :: H :: nil) >= 2).
{
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(HADEHeq : rk(A :: D :: E :: H :: nil) = 3) by (apply LADEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HADEHmtmp : rk(A :: D :: E :: H :: nil) >= 3) by (solve_hyps_min HADEHeq HADEHm3).
	assert(HHmtmp : rk(H :: nil) >= 1) by (solve_hyps_min HHeq HHm1).
	assert(Hincl : incl (H :: nil) (list_inter (A :: H :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: H :: nil) (A :: H :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: H :: D :: E :: H :: nil) ((A :: H :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HADEHmtmp;try rewrite HT2 in HADEHmtmp.
	assert(HT := rule_2 (A :: H :: nil) (D :: E :: H :: nil) (H :: nil) 3 1 2 HADEHmtmp HHmtmp HDEHMtmp Hincl);apply HT.
}

assert(HAHM : rk(A :: H ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HAHeq HAHM2).
assert(HAHm : rk(A :: H ::  nil) >= 1) by (solve_hyps_min HAHeq HAHm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBH *)
(* dans constructLemma(), requis par LBDEH *)
(* dans constructLemma(), requis par LBCDEFH *)
(* dans la couche 0 *)
Lemma LBCDEFH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: C :: D :: E :: F :: H ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'HM5 : rk(B :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Hm4 : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: A' ::   de rang : 2 et 2 *)
assert(HBDEHm2 : rk(B :: D :: E :: H :: nil) >= 2).
{
	assert(HCA'eq : rk(C :: A' :: nil) = 2) by (apply LCA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'Mtmp : rk(C :: A' :: nil) <= 2) by (solve_hyps_max HCA'eq HCA'M2).
	assert(HBCDEA'Hmtmp : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HBCDEA'Heq HBCDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: A' :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (C :: A' :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: B :: D :: E :: H :: nil) ((C :: A' :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Hmtmp;try rewrite HT2 in HBCDEA'Hmtmp.
	assert(HT := rule_4 (C :: A' :: nil) (B :: D :: E :: H :: nil) (nil) 4 0 2 HBCDEA'Hmtmp Hmtmp HCA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEHm3 : rk(B :: C :: D :: E :: H :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFHM5 : rk(B :: C :: D :: E :: F :: H :: nil) <= 5).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (F :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: B :: C :: D :: E :: H :: nil) ((F :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HFMtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : A :: F ::   de rang : 2 et 2 *)
assert(HBCDEFHm4 : rk(B :: C :: D :: E :: F :: H :: nil) >= 4).
{
	assert(HAFeq : rk(A :: F :: nil) = 2) by (apply LAF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAFMtmp : rk(A :: F :: nil) <= 2) by (solve_hyps_max HAFeq HAFM2).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (A :: F :: B :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: F :: B :: C :: D :: E :: F :: H :: nil) ((A :: F :: nil) ++ (B :: C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil) (F :: nil) 5 1 2 HABCDEFHmtmp HFmtmp HAFMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HBCDEFHM4 : rk(B :: C :: D :: E :: F :: H :: nil) <= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: B :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: D :: F :: nil) (B :: D :: E :: H :: nil) (D :: nil) 2 3 1 HCDFMtmp HBDEHMtmp HDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HBCDEFHM : rk(B :: C :: D :: E :: F :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HBCDEFHm : rk(B :: C :: D :: E :: F :: H ::  nil) >= 1) by (solve_hyps_min HBCDEFHeq HBCDEFHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBDEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: D :: E :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BDEH requis par la preuve de (?)BDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'HM5 : rk(B :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Hm4 : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : C :: A' ::   de rang : 2 et 2 *)
assert(HBDEHm2 : rk(B :: D :: E :: H :: nil) >= 2).
{
	assert(HCA'eq : rk(C :: A' :: nil) = 2) by (apply LCA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'Mtmp : rk(C :: A' :: nil) <= 2) by (solve_hyps_max HCA'eq HCA'M2).
	assert(HBCDEA'Hmtmp : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HBCDEA'Heq HBCDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: A' :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (C :: A' :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: B :: D :: E :: H :: nil) ((C :: A' :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Hmtmp;try rewrite HT2 in HBCDEA'Hmtmp.
	assert(HT := rule_4 (C :: A' :: nil) (B :: D :: E :: H :: nil) (nil) 4 0 2 HBCDEA'Hmtmp Hmtmp HCA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : B :: C :: D :: E :: F :: H ::  de rang :  4 et 4 	 AiB : D ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HBDEHm3 : rk(B :: D :: E :: H :: nil) >= 3).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HBCDEFHeq : rk(B :: C :: D :: E :: F :: H :: nil) = 4) by (apply LBCDEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEFHmtmp : rk(B :: C :: D :: E :: F :: H :: nil) >= 4) by (solve_hyps_min HBCDEFHeq HBCDEFHm4).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: B :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFHmtmp;try rewrite HT2 in HBCDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (B :: D :: E :: H :: nil) (D :: nil) 4 1 2 HBCDEFHmtmp HDmtmp HCDFMtmp Hincl); apply HT.
}

assert(HBDEHM : rk(B :: D :: E :: H ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HBDEHeq HBDEHM4).
assert(HBDEHm : rk(B :: D :: E :: H ::  nil) >= 1) by (solve_hyps_min HBDEHeq HBDEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: H ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BH requis par la preuve de (?)BH pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HBHm2 : rk(B :: H :: nil) >= 2).
{
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(HBDEHeq : rk(B :: D :: E :: H :: nil) = 3) by (apply LBDEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBDEHmtmp : rk(B :: D :: E :: H :: nil) >= 3) by (solve_hyps_min HBDEHeq HBDEHm3).
	assert(HHmtmp : rk(H :: nil) >= 1) by (solve_hyps_min HHeq HHm1).
	assert(Hincl : incl (H :: nil) (list_inter (B :: H :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: H :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: H :: D :: E :: H :: nil) ((B :: H :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBDEHmtmp;try rewrite HT2 in HBDEHmtmp.
	assert(HT := rule_2 (B :: H :: nil) (D :: E :: H :: nil) (H :: nil) 3 1 2 HBDEHmtmp HHmtmp HDEHMtmp Hincl);apply HT.
}

assert(HBHM : rk(B :: H ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HBHeq HBHM2).
assert(HBHm : rk(B :: H ::  nil) >= 1) by (solve_hyps_min HBHeq HBHm1).
intuition.
Qed.

(* dans constructLemma(), requis par LEH *)
(* dans la couche 0 *)
Lemma LEA'B'C'D'E'H : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(E :: A' :: B' :: C' :: D' :: E' :: H ::  nil) = 6.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour EA'B'C'D'E'H requis par la preuve de (?)EA'B'C'D'E'H pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour EA'B'C'D'E'H requis par la preuve de (?)EA'B'C'D'E'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HEA'B'C'D'E'Hm5 : rk(E :: A' :: B' :: C' :: D' :: E' :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (E :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (E :: A' :: B' :: C' :: D' :: E' :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HEA'B'C'D'E'Hm6 : rk(E :: A' :: B' :: C' :: D' :: E' :: H :: nil) >= 6).
{
	assert(HEA'B'C'D'E'mtmp : rk(E :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HEA'B'C'D'E'eq HEA'B'C'D'E'm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (E :: A' :: B' :: C' :: D' :: E' :: nil) (E :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (E :: A' :: B' :: C' :: D' :: E' :: nil) (E :: A' :: B' :: C' :: D' :: E' :: H :: nil) 6 6 HEA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

assert(HEA'B'C'D'E'HM : rk(E :: A' :: B' :: C' :: D' :: E' :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HEA'B'C'D'E'Hm : rk(E :: A' :: B' :: C' :: D' :: E' :: H ::  nil) >= 1) by (solve_hyps_min HEA'B'C'D'E'Heq HEA'B'C'D'E'Hm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(E :: H ::  nil) = 2.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour EH requis par la preuve de (?)EH pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HEHm2 : rk(E :: H :: nil) >= 2).
{
	assert(HA'B'C'D'E'HMtmp : rk(A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Heq HA'B'C'D'E'HM5).
	assert(HEA'B'C'D'E'Heq : rk(E :: A' :: B' :: C' :: D' :: E' :: H :: nil) = 6) by (apply LEA'B'C'D'E'H with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEA'B'C'D'E'Hmtmp : rk(E :: A' :: B' :: C' :: D' :: E' :: H :: nil) >= 6) by (solve_hyps_min HEA'B'C'D'E'Heq HEA'B'C'D'E'Hm6).
	assert(HHmtmp : rk(H :: nil) >= 1) by (solve_hyps_min HHeq HHm1).
	assert(Hincl : incl (H :: nil) (list_inter (E :: H :: nil) (A' :: B' :: C' :: D' :: E' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (E :: A' :: B' :: C' :: D' :: E' :: H :: nil) (E :: H :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: H :: A' :: B' :: C' :: D' :: E' :: H :: nil) ((E :: H :: nil) ++ (A' :: B' :: C' :: D' :: E' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HEA'B'C'D'E'Hmtmp;try rewrite HT2 in HEA'B'C'D'E'Hmtmp.
	assert(HT := rule_2 (E :: H :: nil) (A' :: B' :: C' :: D' :: E' :: H :: nil) (H :: nil) 6 1 5 HEA'B'C'D'E'Hmtmp HHmtmp HA'B'C'D'E'HMtmp Hincl);apply HT.
}

assert(HEHM : rk(E :: H ::  nil) <= 2) (* dim : 5 *) by (solve_hyps_max HEHeq HEHM2).
assert(HEHm : rk(E :: H ::  nil) >= 1) by (solve_hyps_min HEHeq HEHm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCEH *)
(* dans constructLemma(), requis par LCDEH *)
(* dans constructLemma(), requis par LBCDEH *)
(* dans la couche 0 *)
Lemma LABCDEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDEH requis par la preuve de (?)ABCDEH pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEH requis par la preuve de (?)ABCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEH requis par la preuve de (?)ABDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEH requis par la preuve de (?)ADEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEHM3 : rk(A :: D :: E :: H :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: H :: nil) (A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: H :: nil) ((A :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HAMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEH requis par la preuve de (?)ABDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEHM4 : rk(A :: B :: D :: E :: H :: nil) <= 4).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HADEHMtmp : rk(A :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HADEHeq HADEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: H :: nil) (B :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: D :: E :: H :: nil) ((B :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: D :: E :: H :: nil) (nil) 1 3 0 HBMtmp HADEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEH requis par la preuve de (?)ABCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABCDEHM5 : rk(A :: B :: C :: D :: E :: H :: nil) <= 5).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HABDEHMtmp : rk(A :: B :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HABDEHeq HABDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (A :: B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: H :: nil) (C :: A :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A :: B :: D :: E :: H :: nil) ((C :: nil) ++ (A :: B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (A :: B :: D :: E :: H :: nil) (nil) 1 4 0 HCMtmp HABDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEHm5 : rk(A :: B :: C :: D :: E :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

assert(HABCDEHM : rk(A :: B :: C :: D :: E :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEHm : rk(A :: B :: C :: D :: E :: H ::  nil) >= 1) by (solve_hyps_min HABCDEHeq HABCDEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(B :: C :: D :: E :: H ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEHm3 : rk(B :: C :: D :: E :: H :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: H ::  de rang :  5 et 5 	 AiB : H ::  de rang :  1 et 1 	 A : A :: H ::   de rang : 2 et 2 *)
assert(HBCDEHm4 : rk(B :: C :: D :: E :: H :: nil) >= 4).
{
	assert(HAHeq : rk(A :: H :: nil) = 2) by (apply LAH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAHMtmp : rk(A :: H :: nil) <= 2) by (solve_hyps_max HAHeq HAHM2).
	assert(HABCDEHeq : rk(A :: B :: C :: D :: E :: H :: nil) = 5) by (apply LABCDEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEHmtmp : rk(A :: B :: C :: D :: E :: H :: nil) >= 5) by (solve_hyps_min HABCDEHeq HABCDEHm5).
	assert(HHmtmp : rk(H :: nil) >= 1) by (solve_hyps_min HHeq HHm1).
	assert(Hincl : incl (H :: nil) (list_inter (A :: H :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: H :: nil) (A :: H :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: H :: B :: C :: D :: E :: H :: nil) ((A :: H :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEHmtmp;try rewrite HT2 in HABCDEHmtmp.
	assert(HT := rule_4 (A :: H :: nil) (B :: C :: D :: E :: H :: nil) (H :: nil) 5 1 2 HABCDEHmtmp HHmtmp HAHMtmp Hincl); apply HT.
}

assert(HBCDEHM : rk(B :: C :: D :: E :: H ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HBCDEHeq HBCDEHM5).
assert(HBCDEHm : rk(B :: C :: D :: E :: H ::  nil) >= 1) by (solve_hyps_min HBCDEHeq HBCDEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCDEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: D :: E :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'HM5 : rk(B :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Hm4 : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEH requis par la preuve de (?)CDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEHM3 : rk(C :: D :: E :: H :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: H :: nil) (C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: E :: H :: nil) ((C :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HCMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEHm2 : rk(C :: D :: E :: H :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Hmtmp : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HBCDEA'Heq HBCDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: H :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Hmtmp;try rewrite HT2 in HBCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: H :: nil) (nil) 4 0 2 HBCDEA'Hmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: H ::  de rang :  4 et 4 	 AiB : H ::  de rang :  1 et 1 	 A : B :: H ::   de rang : 2 et 2 *)
assert(HCDEHm3 : rk(C :: D :: E :: H :: nil) >= 3).
{
	assert(HBHeq : rk(B :: H :: nil) = 2) by (apply LBH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBHMtmp : rk(B :: H :: nil) <= 2) by (solve_hyps_max HBHeq HBHM2).
	assert(HBCDEHeq : rk(B :: C :: D :: E :: H :: nil) = 4) by (apply LBCDEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDEHmtmp : rk(B :: C :: D :: E :: H :: nil) >= 4) by (solve_hyps_min HBCDEHeq HBCDEHm4).
	assert(HHmtmp : rk(H :: nil) >= 1) by (solve_hyps_min HHeq HHm1).
	assert(Hincl : incl (H :: nil) (list_inter (B :: H :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (B :: H :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: H :: C :: D :: E :: H :: nil) ((B :: H :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEHmtmp;try rewrite HT2 in HBCDEHmtmp.
	assert(HT := rule_4 (B :: H :: nil) (C :: D :: E :: H :: nil) (H :: nil) 4 1 2 HBCDEHmtmp HHmtmp HBHMtmp Hincl); apply HT.
}

assert(HCDEHM : rk(C :: D :: E :: H ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HCDEHeq HCDEHM4).
assert(HCDEHm : rk(C :: D :: E :: H ::  nil) >= 1) by (solve_hyps_min HCDEHeq HCDEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: E :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CEH requis par la preuve de (?)CEH pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour CDEFH requis par la preuve de (?)CEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEFH requis par la preuve de (?)CDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEHm3 : rk(B :: C :: D :: E :: H :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFHM5 : rk(B :: C :: D :: E :: F :: H :: nil) <= 5).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (F :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: B :: C :: D :: E :: H :: nil) ((F :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HFMtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : A :: F ::   de rang : 2 et 2 *)
assert(HBCDEFHm4 : rk(B :: C :: D :: E :: F :: H :: nil) >= 4).
{
	assert(HAFeq : rk(A :: F :: nil) = 2) by (apply LAF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAFMtmp : rk(A :: F :: nil) <= 2) by (solve_hyps_max HAFeq HAFM2).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (A :: F :: B :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: F :: B :: C :: D :: E :: F :: H :: nil) ((A :: F :: nil) ++ (B :: C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil) (F :: nil) 5 1 2 HABCDEFHmtmp HFmtmp HAFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEFH requis par la preuve de (?)CDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'HM5 : rk(B :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Hm4 : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEH requis par la preuve de (?)CDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEHM3 : rk(C :: D :: E :: H :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: H :: nil) (C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: E :: H :: nil) ((C :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HCMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEHm2 : rk(C :: D :: E :: H :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Hmtmp : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HBCDEA'Heq HBCDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: H :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Hmtmp;try rewrite HT2 in HBCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: H :: nil) (nil) 4 0 2 HBCDEA'Hmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour CDEFH requis par la preuve de (?)CDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HCDEFHM4 : rk(C :: D :: E :: F :: H :: nil) <= 4).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HCDEHMtmp : rk(C :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HCDEHeq HCDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: H :: nil) (F :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: C :: D :: E :: H :: nil) ((F :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (C :: D :: E :: H :: nil) (nil) 1 3 0 HFMtmp HCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: F :: H ::  de rang :  4 et 5 	 AiB : F ::  de rang :  1 et 1 	 A : B :: F ::   de rang : 2 et 2 *)
assert(HCDEFHm3 : rk(C :: D :: E :: F :: H :: nil) >= 3).
{
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFMtmp : rk(B :: F :: nil) <= 2) by (solve_hyps_max HBFeq HBFM2).
	assert(HBCDEFHmtmp : rk(B :: C :: D :: E :: F :: H :: nil) >= 4) by (solve_hyps_min HBCDEFHeq HBCDEFHm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (B :: F :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: C :: D :: E :: F :: H :: nil) ((B :: F :: nil) ++ (C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFHmtmp;try rewrite HT2 in HBCDEFHmtmp.
	assert(HT := rule_4 (B :: F :: nil) (C :: D :: E :: F :: H :: nil) (F :: nil) 4 1 2 HBCDEFHmtmp HFmtmp HBFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CEH requis par la preuve de (?)CEH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : C :: D :: E :: F :: H ::  de rang :  3 et 4 	 AiB : C ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HCEHm2 : rk(C :: E :: H :: nil) >= 2).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HCDEFHmtmp : rk(C :: D :: E :: F :: H :: nil) >= 3) by (solve_hyps_min HCDEFHeq HCDEFHm3).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (C :: D :: F :: nil) (C :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: H :: nil) (C :: D :: F :: C :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: C :: E :: H :: nil) ((C :: D :: F :: nil) ++ (C :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEFHmtmp;try rewrite HT2 in HCDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (C :: E :: H :: nil) (C :: nil) 3 1 2 HCDEFHmtmp HCmtmp HCDFMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et -4*)
assert(HCEHm3 : rk(C :: E :: H :: nil) >= 3).
{
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(HCDEHeq : rk(C :: D :: E :: H :: nil) = 3) by (apply LCDEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEHmtmp : rk(C :: D :: E :: H :: nil) >= 3) by (solve_hyps_min HCDEHeq HCDEHm3).
	assert(HEHeq : rk(E :: H :: nil) = 2) by (apply LEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEHmtmp : rk(E :: H :: nil) >= 2) by (solve_hyps_min HEHeq HEHm2).
	assert(Hincl : incl (E :: H :: nil) (list_inter (C :: E :: H :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: H :: nil) (C :: E :: H :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: E :: H :: D :: E :: H :: nil) ((C :: E :: H :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEHmtmp;try rewrite HT2 in HCDEHmtmp.
	assert(HT := rule_2 (C :: E :: H :: nil) (D :: E :: H :: nil) (E :: H :: nil) 3 2 2 HCDEHmtmp HEHmtmp HDEHMtmp Hincl);apply HT.
}

assert(HCEHM : rk(C :: E :: H ::  nil) <= 3) (* dim : 5 *) by (solve_hyps_max HCEHeq HCEHM3).
assert(HCEHm : rk(C :: E :: H ::  nil) >= 1) by (solve_hyps_min HCEHeq HCEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCEH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: E :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEH requis par la preuve de (?)ABCEH pour la règle 2  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCEH requis par la preuve de (?)ABCEH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 6 	 AiB : C ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABCEHm4 : rk(A :: B :: C :: E :: H :: nil) >= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: C :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: A :: B :: C :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: C :: E :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: C :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: C :: E :: H :: nil) (C :: nil) 5 1 2 HABCDEFHmtmp HCmtmp HCDFMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et -4*)
assert(HABCEHm5 : rk(A :: B :: C :: E :: H :: nil) >= 5).
{
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(HABCDEHeq : rk(A :: B :: C :: D :: E :: H :: nil) = 5) by (apply LABCDEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEHmtmp : rk(A :: B :: C :: D :: E :: H :: nil) >= 5) by (solve_hyps_min HABCDEHeq HABCDEHm5).
	assert(HEHeq : rk(E :: H :: nil) = 2) by (apply LEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEHmtmp : rk(E :: H :: nil) >= 2) by (solve_hyps_min HEHeq HEHm2).
	assert(Hincl : incl (E :: H :: nil) (list_inter (A :: B :: C :: E :: H :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: H :: nil) (A :: B :: C :: E :: H :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: E :: H :: D :: E :: H :: nil) ((A :: B :: C :: E :: H :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEHmtmp;try rewrite HT2 in HABCDEHmtmp.
	assert(HT := rule_2 (A :: B :: C :: E :: H :: nil) (D :: E :: H :: nil) (E :: H :: nil) 5 2 2 HABCDEHmtmp HEHmtmp HDEHMtmp Hincl);apply HT.
}

assert(HABCEHM : rk(A :: B :: C :: E :: H ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABCEHeq HABCEHM5).
assert(HABCEHm : rk(A :: B :: C :: E :: H ::  nil) >= 1) by (solve_hyps_min HABCEHeq HABCEHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAA'B'C'D'E'H : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour AA'B'C'D'E'H requis par la preuve de (?)AA'B'C'D'E'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour AA'B'C'D'E'H requis par la preuve de (?)AA'B'C'D'E'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAA'B'C'D'E'Hm5 : rk(A :: A' :: B' :: C' :: D' :: E' :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (A :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (A :: A' :: B' :: C' :: D' :: E' :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HAA'B'C'D'E'HM5 : rk(A :: A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5).
{
	assert(HAA'B'C'D'E'Mtmp : rk(A :: A' :: B' :: C' :: D' :: E' :: nil) <= 5) by (solve_hyps_max HAA'B'C'D'E'eq HAA'B'C'D'E'M5).
	assert(HA'B'C'D'E'HMtmp : rk(A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Heq HA'B'C'D'E'HM5).
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (list_inter (A :: A' :: B' :: C' :: D' :: E' :: nil) (A' :: B' :: C' :: D' :: E' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: A' :: B' :: C' :: D' :: E' :: H :: nil) (A :: A' :: B' :: C' :: D' :: E' :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B' :: C' :: D' :: E' :: A' :: B' :: C' :: D' :: E' :: H :: nil) ((A :: A' :: B' :: C' :: D' :: E' :: nil) ++ (A' :: B' :: C' :: D' :: E' :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: A' :: B' :: C' :: D' :: E' :: nil) (A' :: B' :: C' :: D' :: E' :: H :: nil) (A' :: B' :: C' :: D' :: E' :: nil) 5 5 5 HAA'B'C'D'E'Mtmp HA'B'C'D'E'HMtmp HA'B'C'D'E'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HAA'B'C'D'E'HM : rk(A :: A' :: B' :: C' :: D' :: E' :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HAA'B'C'D'E'Hm : rk(A :: A' :: B' :: C' :: D' :: E' :: H ::  nil) >= 1) by (solve_hyps_min HAA'B'C'D'E'Heq HAA'B'C'D'E'Hm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABA'B'C'D'E'H : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABA'B'C'D'E'H requis par la preuve de (?)ABA'B'C'D'E'H pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABA'B'C'D'E'H requis par la preuve de (?)ABA'B'C'D'E'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABA'B'C'D'E'Hm5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABA'B'C'D'E'HM5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5).
{
	assert(HBA'B'C'D'E'Mtmp : rk(B :: A' :: B' :: C' :: D' :: E' :: nil) <= 5) by (solve_hyps_max HBA'B'C'D'E'eq HBA'B'C'D'E'M5).
	assert(HAA'B'C'D'E'Heq : rk(A :: A' :: B' :: C' :: D' :: E' :: H :: nil) = 5) by (apply LAA'B'C'D'E'H with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAA'B'C'D'E'HMtmp : rk(A :: A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5) by (solve_hyps_max HAA'B'C'D'E'Heq HAA'B'C'D'E'HM5).
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (list_inter (B :: A' :: B' :: C' :: D' :: E' :: nil) (A :: A' :: B' :: C' :: D' :: E' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) (B :: A' :: B' :: C' :: D' :: E' :: A :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: B' :: C' :: D' :: E' :: A :: A' :: B' :: C' :: D' :: E' :: H :: nil) ((B :: A' :: B' :: C' :: D' :: E' :: nil) ++ (A :: A' :: B' :: C' :: D' :: E' :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: A' :: B' :: C' :: D' :: E' :: nil) (A :: A' :: B' :: C' :: D' :: E' :: H :: nil) (A' :: B' :: C' :: D' :: E' :: nil) 5 5 5 HBA'B'C'D'E'Mtmp HAA'B'C'D'E'HMtmp HA'B'C'D'E'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABA'B'C'D'E'HM : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABA'B'C'D'E'Hm : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H ::  nil) >= 1) by (solve_hyps_min HABA'B'C'D'E'Heq HABA'B'C'D'E'Hm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCEFH *)
(* dans la couche 0 *)
Lemma LCDEFH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: D :: E :: F :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour CDEFH requis par la preuve de (?)CDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEFH requis par la preuve de (?)CDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BDEH requis par la preuve de (?)BDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBDEHM3 : rk(B :: D :: E :: H :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: D :: E :: H :: nil) (B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: E :: H :: nil) ((B :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HBMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEH requis par la preuve de (?)BCDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEHM4 : rk(B :: C :: D :: E :: H :: nil) <= 4).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBDEHMtmp : rk(B :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HBDEHeq HBDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: H :: nil) (C :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: B :: D :: E :: H :: nil) ((C :: nil) ++ (B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (B :: D :: E :: H :: nil) (nil) 1 3 0 HCMtmp HBDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEHm3 : rk(B :: C :: D :: E :: H :: nil) >= 3).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEFH requis par la preuve de (?)BCDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFHM5 : rk(B :: C :: D :: E :: F :: H :: nil) <= 5).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (F :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: B :: C :: D :: E :: H :: nil) ((F :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HFMtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : A :: F ::   de rang : 2 et 2 *)
assert(HBCDEFHm4 : rk(B :: C :: D :: E :: F :: H :: nil) >= 4).
{
	assert(HAFeq : rk(A :: F :: nil) = 2) by (apply LAF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HAFMtmp : rk(A :: F :: nil) <= 2) by (solve_hyps_max HAFeq HAFM2).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (A :: F :: B :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: F :: B :: C :: D :: E :: F :: H :: nil) ((A :: F :: nil) ++ (B :: C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (A :: F :: nil) (B :: C :: D :: E :: F :: H :: nil) (F :: nil) 5 1 2 HABCDEFHmtmp HFmtmp HAFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEFH requis par la preuve de (?)CDEFH pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'H requis par la preuve de (?)BCDEA'H pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'HM5 : rk(B :: C :: D :: E :: A' :: H :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEHMtmp : rk(B :: C :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HBCDEHeq HBCDEHM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (A' :: B :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: H :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: H :: nil) (nil) 1 4 0 HA'Mtmp HBCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Hm4 : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (A :: A' :: B :: C :: D :: E :: A' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: H :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: H :: nil) (A' :: nil) 5 1 2 HABCDEA'Hmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEH requis par la preuve de (?)CDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEH requis par la preuve de (?)CDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEHM3 : rk(C :: D :: E :: H :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: H :: nil) (C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: E :: H :: nil) ((C :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HCMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEHm2 : rk(C :: D :: E :: H :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Hmtmp : rk(B :: C :: D :: E :: A' :: H :: nil) >= 4) by (solve_hyps_min HBCDEA'Heq HBCDEA'Hm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: H :: nil) (B :: A' :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: H :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Hmtmp;try rewrite HT2 in HBCDEA'Hmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: H :: nil) (nil) 4 0 2 HBCDEA'Hmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour CDEFH requis par la preuve de (?)CDEFH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HCDEFHM4 : rk(C :: D :: E :: F :: H :: nil) <= 4).
{
	assert(HFMtmp : rk(F :: nil) <= 1) by (solve_hyps_max HFeq HFM1).
	assert(HCDEHMtmp : rk(C :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HCDEHeq HCDEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (F :: nil) (C :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: H :: nil) (F :: C :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (F :: C :: D :: E :: H :: nil) ((F :: nil) ++ (C :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (F :: nil) (C :: D :: E :: H :: nil) (nil) 1 3 0 HFMtmp HCDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : B :: C :: D :: E :: F :: H ::  de rang :  4 et 5 	 AiB : F ::  de rang :  1 et 1 	 A : B :: F ::   de rang : 2 et 2 *)
assert(HCDEFHm3 : rk(C :: D :: E :: F :: H :: nil) >= 3).
{
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFMtmp : rk(B :: F :: nil) <= 2) by (solve_hyps_max HBFeq HBFM2).
	assert(HBCDEFHmtmp : rk(B :: C :: D :: E :: F :: H :: nil) >= 4) by (solve_hyps_min HBCDEFHeq HBCDEFHm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (B :: F :: nil) (C :: D :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: H :: nil) (B :: F :: C :: D :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: F :: C :: D :: E :: F :: H :: nil) ((B :: F :: nil) ++ (C :: D :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEFHmtmp;try rewrite HT2 in HBCDEFHmtmp.
	assert(HT := rule_4 (B :: F :: nil) (C :: D :: E :: F :: H :: nil) (F :: nil) 4 1 2 HBCDEFHmtmp HFmtmp HBFMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HCDEFHM3 : rk(C :: D :: E :: F :: H :: nil) <= 3).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: H :: nil) (C :: D :: F :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: D :: F :: nil) (D :: E :: H :: nil) (D :: nil) 2 2 1 HCDFMtmp HDEHMtmp HDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HCDEFHM : rk(C :: D :: E :: F :: H ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HCDEFHeq HCDEFHM5).
assert(HCDEFHm : rk(C :: D :: E :: F :: H ::  nil) >= 1) by (solve_hyps_min HCDEFHeq HCDEFHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCEFH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(C :: E :: F :: H ::  nil) = 3.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour CEFH requis par la preuve de (?)CEFH pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CEFH requis par la preuve de (?)CEFH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : C :: D :: E :: F :: H ::  de rang :  3 et 3 	 AiB : C :: F ::  de rang :  2 et 2 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HCEFHm3 : rk(C :: E :: F :: H :: nil) >= 3).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HCDEFHeq : rk(C :: D :: E :: F :: H :: nil) = 3) by (apply LCDEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEFHmtmp : rk(C :: D :: E :: F :: H :: nil) >= 3) by (solve_hyps_min HCDEFHeq HCDEFHm3).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (C :: D :: F :: nil) (C :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: H :: nil) (C :: D :: F :: C :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: C :: E :: F :: H :: nil) ((C :: D :: F :: nil) ++ (C :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCDEFHmtmp;try rewrite HT2 in HCDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (C :: E :: F :: H :: nil) (C :: F :: nil) 3 2 2 HCDEFHmtmp HCFmtmp HCDFMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCEFHM3 : rk(C :: E :: F :: H :: nil) <= 3).
{
	assert(HCDEFHeq : rk(C :: D :: E :: F :: H :: nil) = 3) by (apply LCDEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCDEFHMtmp : rk(C :: D :: E :: F :: H :: nil) <= 3) by (solve_hyps_max HCDEFHeq HCDEFHM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: E :: F :: H :: nil) (C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (C :: E :: F :: H :: nil) (C :: D :: E :: F :: H :: nil) 3 3 HCDEFHMtmp Hcomp Hincl);apply HT.
}

assert(HCEFHM : rk(C :: E :: F :: H ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HCEFHeq HCEFHM4).
assert(HCEFHm : rk(C :: E :: F :: H ::  nil) >= 1) by (solve_hyps_min HCEFHeq HCEFHm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCDEFH *)
(* dans la couche 0 *)
Lemma LABCDEFH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: F :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABDEH requis par la preuve de (?)ABCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'H requis par la preuve de (?)ABCDEA'H pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Hm5 : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABDEH requis par la preuve de (?)ABDEH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ADEH requis par la preuve de (?)ABDEH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ADEH requis par la preuve de (?)ADEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HADEHM3 : rk(A :: D :: E :: H :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HDEHMtmp : rk(D :: E :: H :: nil) <= 2) by (solve_hyps_max HDEHeq HDEHM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: D :: E :: H :: nil) (A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: E :: H :: nil) ((A :: nil) ++ (D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (D :: E :: H :: nil) (nil) 1 2 0 HAMtmp HDEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABDEH requis par la preuve de (?)ABDEH pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HABDEHM4 : rk(A :: B :: D :: E :: H :: nil) <= 4).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HADEHMtmp : rk(A :: D :: E :: H :: nil) <= 3) by (solve_hyps_max HADEHeq HADEHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (A :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: E :: H :: nil) (B :: A :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A :: D :: E :: H :: nil) ((B :: nil) ++ (A :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (A :: D :: E :: H :: nil) (nil) 1 3 0 HBMtmp HADEHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: H ::  de rang :  5 et 6 	 AiB :  de rang :  0 et 0 	 A : C :: A' ::   de rang : 2 et 2 *)
assert(HABDEHm3 : rk(A :: B :: D :: E :: H :: nil) >= 3).
{
	assert(HCA'eq : rk(C :: A' :: nil) = 2) by (apply LCA' with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCA'Mtmp : rk(C :: A' :: nil) <= 2) by (solve_hyps_max HCA'eq HCA'M2).
	assert(HABCDEA'Hmtmp : rk(A :: B :: C :: D :: E :: A' :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'Heq HABCDEA'Hm5).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: A' :: nil) (A :: B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: H :: nil) (C :: A' :: A :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: A' :: A :: B :: D :: E :: H :: nil) ((C :: A' :: nil) ++ (A :: B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Hmtmp;try rewrite HT2 in HABCDEA'Hmtmp.
	assert(HT := rule_4 (C :: A' :: nil) (A :: B :: D :: E :: H :: nil) (nil) 5 0 2 HABCDEA'Hmtmp Hmtmp HCA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFH requis par la preuve de (?)ABCDEFH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFHm5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HABCDEFHM5 : rk(A :: B :: C :: D :: E :: F :: H :: nil) <= 5).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABDEHMtmp : rk(A :: B :: D :: E :: H :: nil) <= 4) by (solve_hyps_max HABDEHeq HABDEHM4).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: D :: E :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: A :: B :: D :: E :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: D :: E :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: D :: E :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: D :: F :: nil) (A :: B :: D :: E :: H :: nil) (D :: nil) 2 4 1 HCDFMtmp HABDEHMtmp HDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEFHM : rk(A :: B :: C :: D :: E :: F :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEFHm : rk(A :: B :: C :: D :: E :: F :: H ::  nil) >= 1) by (solve_hyps_min HABCDEFHeq HABCDEFHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABA'B'C'D'E'FH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABA'B'C'D'E'FH requis par la preuve de (?)ABA'B'C'D'E'FH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABA'B'C'D'E'FH requis par la preuve de (?)ABA'B'C'D'E'FH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABA'B'C'D'E'FHm5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABA'B'C'D'E'FHM5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) <= 5).
{
	assert(HA'B'C'D'E'FMtmp : rk(A' :: B' :: C' :: D' :: E' :: F :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Feq HA'B'C'D'E'FM5).
	assert(HABA'B'C'D'E'Heq : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) = 5) by (apply LABA'B'C'D'E'H with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABA'B'C'D'E'HMtmp : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) <= 5) by (solve_hyps_max HABA'B'C'D'E'Heq HABA'B'C'D'E'HM5).
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (list_inter (A' :: B' :: C' :: D' :: E' :: F :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) (A' :: B' :: C' :: D' :: E' :: F :: A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: D' :: E' :: F :: A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) ((A' :: B' :: C' :: D' :: E' :: F :: nil) ++ (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: D' :: E' :: F :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: H :: nil) (A' :: B' :: C' :: D' :: E' :: nil) 5 5 5 HA'B'C'D'E'FMtmp HABA'B'C'D'E'HMtmp HA'B'C'D'E'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABA'B'C'D'E'FHM : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABA'B'C'D'E'FHm : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H ::  nil) >= 1) by (solve_hyps_min HABA'B'C'D'E'FHeq HABA'B'C'D'E'FHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCEGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: E :: G :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCEGH requis par la preuve de (?)ABCEGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABH requis par la preuve de (?)ABCEGH pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABEFH requis par la preuve de (?)ABH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABEFH requis par la preuve de (?)ABEFH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: H ::  de rang :  5 et 5 	 AiB : F ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABEFHm4 : rk(A :: B :: E :: F :: H :: nil) >= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFHeq : rk(A :: B :: C :: D :: E :: F :: H :: nil) = 5) by (apply LABCDEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCDEFHmtmp : rk(A :: B :: C :: D :: E :: F :: H :: nil) >= 5) by (solve_hyps_min HABCDEFHeq HABCDEFHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: E :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: H :: nil) (C :: D :: F :: A :: B :: E :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: E :: F :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: E :: F :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFHmtmp;try rewrite HT2 in HABCDEFHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: E :: F :: H :: nil) (F :: nil) 5 1 2 HABCDEFHmtmp HFmtmp HCDFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABH requis par la preuve de (?)ABH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 4*)
(* ensembles concernés AUB : A :: B :: E :: F :: H ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : E :: F ::   de rang : 2 et 2 *)
assert(HABHm2 : rk(A :: B :: H :: nil) >= 2).
{
	assert(HEFeq : rk(E :: F :: nil) = 2) by (apply LEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEFMtmp : rk(E :: F :: nil) <= 2) by (solve_hyps_max HEFeq HEFM2).
	assert(HABEFHmtmp : rk(A :: B :: E :: F :: H :: nil) >= 4) by (solve_hyps_min HABEFHeq HABEFHm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: F :: nil) (A :: B :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: F :: H :: nil) (E :: F :: A :: B :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: F :: A :: B :: H :: nil) ((E :: F :: nil) ++ (A :: B :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABEFHmtmp;try rewrite HT2 in HABEFHmtmp.
	assert(HT := rule_4 (E :: F :: nil) (A :: B :: H :: nil) (nil) 4 0 2 HABEFHmtmp Hmtmp HEFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCEGH requis par la preuve de (?)ABCEGH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCEGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCDEFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFGHm5 : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEGH requis par la preuve de (?)ABCEGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : C ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABCEGHm4 : rk(A :: B :: C :: E :: G :: H :: nil) >= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFGHmtmp : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEFGHeq HABCDEFGHm5).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: C :: E :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: G :: H :: nil) (C :: D :: F :: A :: B :: C :: E :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: C :: E :: G :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: C :: E :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFGHmtmp;try rewrite HT2 in HABCDEFGHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: C :: E :: G :: H :: nil) (C :: nil) 5 1 2 HABCDEFGHmtmp HCmtmp HCDFMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et 5*)
assert(HABCEGHM5 : rk(A :: B :: C :: E :: G :: H :: nil) <= 5).
{
	assert(HCEGMtmp : rk(C :: E :: G :: nil) <= 2) by (solve_hyps_max HCEGeq HCEGM2).
	assert(HABHMtmp : rk(A :: B :: H :: nil) <= 3) by (solve_hyps_max HABHeq HABHM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: E :: G :: nil) (A :: B :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: G :: H :: nil) (C :: E :: G :: A :: B :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: E :: G :: A :: B :: H :: nil) ((C :: E :: G :: nil) ++ (A :: B :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: E :: G :: nil) (A :: B :: H :: nil) (nil) 2 3 0 HCEGMtmp HABHMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCEGHm5 : rk(A :: B :: C :: E :: G :: H :: nil) >= 5).
{
	assert(HABCEHeq : rk(A :: B :: C :: E :: H :: nil) = 5) by (apply LABCEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCEHmtmp : rk(A :: B :: C :: E :: H :: nil) >= 5) by (solve_hyps_min HABCEHeq HABCEHm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: E :: H :: nil) (A :: B :: C :: E :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: E :: H :: nil) (A :: B :: C :: E :: G :: H :: nil) 5 5 HABCEHmtmp Hcomp Hincl);apply HT.
}

assert(HABCEGHM : rk(A :: B :: C :: E :: G :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCEGHm : rk(A :: B :: C :: E :: G :: H ::  nil) >= 1) by (solve_hyps_min HABCEGHeq HABCEGHm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCFGH *)
(* dans la couche 0 *)
Lemma LABCEFGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: E :: F :: G :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABCEFGH pour la règle 1  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCDEFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFGHm5 : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : C :: F ::  de rang :  2 et 2 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABCEFGHm5 : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFGHmtmp : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEFGHeq HABCDEFGHm5).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: G :: H :: nil) (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: C :: E :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFGHmtmp;try rewrite HT2 in HABCDEFGHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil) (C :: F :: nil) 5 2 2 HABCDEFGHmtmp HCFmtmp HCDFMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCEFGHM5 : rk(A :: B :: C :: E :: F :: G :: H :: nil) <= 5).
{
	assert(HCEFHeq : rk(C :: E :: F :: H :: nil) = 3) by (apply LCEFH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCEFHMtmp : rk(C :: E :: F :: H :: nil) <= 3) by (solve_hyps_max HCEFHeq HCEFHM3).
	assert(HABCEGHeq : rk(A :: B :: C :: E :: G :: H :: nil) = 5) by (apply LABCEGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCEGHMtmp : rk(A :: B :: C :: E :: G :: H :: nil) <= 5) by (solve_hyps_max HABCEGHeq HABCEGHM5).
	assert(HCEHeq : rk(C :: E :: H :: nil) = 3) by (apply LCEH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCEHmtmp : rk(C :: E :: H :: nil) >= 3) by (solve_hyps_min HCEHeq HCEHm3).
	assert(Hincl : incl (C :: E :: H :: nil) (list_inter (C :: E :: F :: H :: nil) (A :: B :: C :: E :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: F :: G :: H :: nil) (C :: E :: F :: H :: A :: B :: C :: E :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: E :: F :: H :: A :: B :: C :: E :: G :: H :: nil) ((C :: E :: F :: H :: nil) ++ (A :: B :: C :: E :: G :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: E :: F :: H :: nil) (A :: B :: C :: E :: G :: H :: nil) (C :: E :: H :: nil) 3 5 3 HCEFHMtmp HABCEGHMtmp HCEHmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCEFGHM : rk(A :: B :: C :: E :: F :: G :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCEFGHm : rk(A :: B :: C :: E :: F :: G :: H ::  nil) >= 1) by (solve_hyps_min HABCEFGHeq HABCEFGHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCFGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: F :: G :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCFGH requis par la preuve de (?)ABCFGH pour la règle 6  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCDEFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFGHm5 : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : C :: F ::  de rang :  2 et 2 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABCEFGHm5 : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFGHmtmp : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEFGHeq HABCDEFGHm5).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: G :: H :: nil) (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: C :: E :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFGHmtmp;try rewrite HT2 in HABCDEFGHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil) (C :: F :: nil) 5 2 2 HABCDEFGHmtmp HCFmtmp HCDFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABCFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABCDFGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABCDFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDFGHm2 : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 2).
{
	assert(HCDFmtmp : rk(C :: D :: F :: nil) >= 2) by (solve_hyps_min HCDFeq HCDFm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil) 2 2 HCDFmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDFGHm3 : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 3).
{
	assert(HACDFeq : rk(A :: C :: D :: F :: nil) = 3) by (apply LACDF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDFmtmp : rk(A :: C :: D :: F :: nil) >= 3) by (solve_hyps_min HACDFeq HACDFm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil) 3 3 HACDFmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCFGH requis par la preuve de (?)ABCFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: F :: G :: H ::  de rang :  2 et 6 	 AiB : A :: C :: F ::  de rang :  3 et 3 	 A : A :: C :: D :: F ::   de rang : 3 et 3 *)
assert(HABCFGHm2 : rk(A :: B :: C :: F :: G :: H :: nil) >= 2).
{
	assert(HACDFeq : rk(A :: C :: D :: F :: nil) = 3) by (apply LACDF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDFMtmp : rk(A :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HACDFeq HACDFM3).
	assert(HABCDFGHmtmp : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 2) by (solve_hyps_min HABCDFGHeq HABCDFGHm2).
	assert(HACFeq : rk(A :: C :: F :: nil) = 3) by (apply LACF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACFmtmp : rk(A :: C :: F :: nil) >= 3) by (solve_hyps_min HACFeq HACFm3).
	assert(Hincl : incl (A :: C :: F :: nil) (list_inter (A :: C :: D :: F :: nil) (A :: B :: C :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: F :: G :: H :: nil) (A :: C :: D :: F :: A :: B :: C :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: D :: F :: A :: B :: C :: F :: G :: H :: nil) ((A :: C :: D :: F :: nil) ++ (A :: B :: C :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDFGHmtmp;try rewrite HT2 in HABCDFGHmtmp.
	assert(HT := rule_4 (A :: C :: D :: F :: nil) (A :: B :: C :: F :: G :: H :: nil) (A :: C :: F :: nil) 2 3 3 HABCDFGHmtmp HACFmtmp HACDFMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: F :: G :: H ::  de rang :  3 et 6 	 AiB : B :: C :: F ::  de rang :  3 et 3 	 A : B :: C :: D :: F ::   de rang : 3 et 3 *)
assert(HABCFGHm3 : rk(A :: B :: C :: F :: G :: H :: nil) >= 3).
{
	assert(HBCDFeq : rk(B :: C :: D :: F :: nil) = 3) by (apply LBCDF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(HABCDFGHmtmp : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 3) by (solve_hyps_min HABCDFGHeq HABCDFGHm3).
	assert(HBCFeq : rk(B :: C :: F :: nil) = 3) by (apply LBCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCFmtmp : rk(B :: C :: F :: nil) >= 3) by (solve_hyps_min HBCFeq HBCFm3).
	assert(Hincl : incl (B :: C :: F :: nil) (list_inter (B :: C :: D :: F :: nil) (A :: B :: C :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: F :: G :: H :: nil) (B :: C :: D :: F :: A :: B :: C :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: A :: B :: C :: F :: G :: H :: nil) ((B :: C :: D :: F :: nil) ++ (A :: B :: C :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDFGHmtmp;try rewrite HT2 in HABCDFGHmtmp.
	assert(HT := rule_4 (B :: C :: D :: F :: nil) (A :: B :: C :: F :: G :: H :: nil) (B :: C :: F :: nil) 3 3 3 HABCDFGHmtmp HBCFmtmp HBCDFMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : E :: F ::   de rang : 2 et 2 *)
assert(HABCFGHm4 : rk(A :: B :: C :: F :: G :: H :: nil) >= 4).
{
	assert(HEFeq : rk(E :: F :: nil) = 2) by (apply LEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEFMtmp : rk(E :: F :: nil) <= 2) by (solve_hyps_max HEFeq HEFM2).
	assert(HABCEFGHmtmp : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCEFGHeq HABCEFGHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (E :: F :: nil) (A :: B :: C :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: F :: G :: H :: nil) (E :: F :: A :: B :: C :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: F :: A :: B :: C :: F :: G :: H :: nil) ((E :: F :: nil) ++ (A :: B :: C :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEFGHmtmp;try rewrite HT2 in HABCEFGHmtmp.
	assert(HT := rule_4 (E :: F :: nil) (A :: B :: C :: F :: G :: H :: nil) (F :: nil) 5 1 2 HABCEFGHmtmp HFmtmp HEFMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : C :: G ::  de rang :  2 et 2 	 A : C :: E :: G ::   de rang : 2 et 2 *)
assert(HABCFGHm5 : rk(A :: B :: C :: F :: G :: H :: nil) >= 5).
{
	assert(HCEGMtmp : rk(C :: E :: G :: nil) <= 2) by (solve_hyps_max HCEGeq HCEGM2).
	assert(HABCEFGHmtmp : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCEFGHeq HABCEFGHm5).
	assert(HCGeq : rk(C :: G :: nil) = 2) by (apply LCG with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCGmtmp : rk(C :: G :: nil) >= 2) by (solve_hyps_min HCGeq HCGm2).
	assert(Hincl : incl (C :: G :: nil) (list_inter (C :: E :: G :: nil) (A :: B :: C :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: F :: G :: H :: nil) (C :: E :: G :: A :: B :: C :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: E :: G :: A :: B :: C :: F :: G :: H :: nil) ((C :: E :: G :: nil) ++ (A :: B :: C :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEFGHmtmp;try rewrite HT2 in HABCEFGHmtmp.
	assert(HT := rule_4 (C :: E :: G :: nil) (A :: B :: C :: F :: G :: H :: nil) (C :: G :: nil) 5 2 2 HABCEFGHmtmp HCGmtmp HCEGMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCFGHM5 : rk(A :: B :: C :: F :: G :: H :: nil) <= 5).
{
	assert(HABCEFGHeq : rk(A :: B :: C :: E :: F :: G :: H :: nil) = 5) by (apply LABCEFGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCEFGHMtmp : rk(A :: B :: C :: E :: F :: G :: H :: nil) <= 5) by (solve_hyps_max HABCEFGHeq HABCEFGHM5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: F :: G :: H :: nil) (A :: B :: C :: E :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: C :: F :: G :: H :: nil) (A :: B :: C :: E :: F :: G :: H :: nil) 5 5 HABCEFGHMtmp Hcomp Hincl);apply HT.
}

assert(HABCFGHM : rk(A :: B :: C :: F :: G :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCFGHm : rk(A :: B :: C :: F :: G :: H ::  nil) >= 1) by (solve_hyps_min HABCFGHeq HABCFGHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABA'B'C'D'E'FGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) = 5.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABA'B'C'D'E'FGH requis par la preuve de (?)ABA'B'C'D'E'FGH pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABA'B'C'D'E'FGH requis par la preuve de (?)ABA'B'C'D'E'FGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABA'B'C'D'E'FGHm5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABA'B'C'D'E'FGHM5 : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) <= 5).
{
	assert(HA'B'C'D'E'GMtmp : rk(A' :: B' :: C' :: D' :: E' :: G :: nil) <= 5) by (solve_hyps_max HA'B'C'D'E'Geq HA'B'C'D'E'GM5).
	assert(HABA'B'C'D'E'FHeq : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) = 5) by (apply LABA'B'C'D'E'FH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABA'B'C'D'E'FHMtmp : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) <= 5) by (solve_hyps_max HABA'B'C'D'E'FHeq HABA'B'C'D'E'FHM5).
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (list_inter (A' :: B' :: C' :: D' :: E' :: G :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) (A' :: B' :: C' :: D' :: E' :: G :: A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B' :: C' :: D' :: E' :: G :: A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) ((A' :: B' :: C' :: D' :: E' :: G :: nil) ++ (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: B' :: C' :: D' :: E' :: G :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: H :: nil) (A' :: B' :: C' :: D' :: E' :: nil) 5 5 5 HA'B'C'D'E'GMtmp HABA'B'C'D'E'FHMtmp HA'B'C'D'E'mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABA'B'C'D'E'FGHM : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABA'B'C'D'E'FGHm : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) >= 1) by (solve_hyps_min HABA'B'C'D'E'FGHeq HABA'B'C'D'E'FGHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCA'B'C'D'E'FGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) = 6.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCA'B'C'D'E'FGH requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCA'B'C'D'E'FGH requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCB' requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEB'F requis par la preuve de (?)ABCB' pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEB'F requis par la preuve de (?)ABCDEB'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEB'Fm5 : rk(A :: B :: C :: D :: E :: B' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: B' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: B' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CDEF requis par la preuve de (?)ABCB' pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'F requis par la preuve de (?)ABCDEA'F pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'Fm5 : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: F :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AA' requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDEF requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCDF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCDF requis par la preuve de (?)BCDF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCDFM3 : rk(B :: C :: D :: F :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: F :: nil) (B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: nil) ((B :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HBMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDEF requis par la preuve de (?)BCDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEFM4 : rk(B :: C :: D :: E :: F :: nil) <= 4).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (B :: C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: F :: nil) (E :: B :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: B :: C :: D :: F :: nil) ((E :: nil) ++ (B :: C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (B :: C :: D :: F :: nil) (nil) 1 3 0 HEMtmp HBCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour BCDEA'F requis par la preuve de (?)BCDEA'F pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HBCDEA'FM5 : rk(B :: C :: D :: E :: A' :: F :: nil) <= 5).
{
	assert(HA'Mtmp : rk(A' :: nil) <= 1) by (solve_hyps_max HA'eq HA'M1).
	assert(HBCDEFMtmp : rk(B :: C :: D :: E :: F :: nil) <= 4) by (solve_hyps_max HBCDEFeq HBCDEFM4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A' :: nil) (B :: C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (A' :: B :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A' :: B :: C :: D :: E :: F :: nil) ((A' :: nil) ++ (B :: C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A' :: nil) (B :: C :: D :: E :: F :: nil) (nil) 1 4 0 HA'Mtmp HBCDEFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: F ::  de rang :  5 et 6 	 AiB : A' ::  de rang :  1 et 1 	 A : A :: A' ::   de rang : 1 et 2 *)
assert(HBCDEA'Fm4 : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4).
{
	assert(HAA'Mtmp : rk(A :: A' :: nil) <= 2) by (solve_hyps_max HAA'eq HAA'M2).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HA'mtmp : rk(A' :: nil) >= 1) by (solve_hyps_min HA'eq HA'm1).
	assert(Hincl : incl (A' :: nil) (list_inter (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: A' :: B :: C :: D :: E :: A' :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: A' :: B :: C :: D :: E :: A' :: F :: nil) ((A :: A' :: nil) ++ (B :: C :: D :: E :: A' :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_4 (A :: A' :: nil) (B :: C :: D :: E :: A' :: F :: nil) (A' :: nil) 5 1 2 HABCDEA'Fmtmp HA'mtmp HAA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BA' requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CDEF requis par la preuve de (?)CDEF pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CDEF requis par la preuve de (?)CDEF pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCDEFM3 : rk(C :: D :: E :: F :: nil) <= 3).
{
	assert(HEMtmp : rk(E :: nil) <= 1) by (solve_hyps_max HEeq HEM1).
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (E :: nil) (C :: D :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: D :: E :: F :: nil) (E :: C :: D :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: C :: D :: F :: nil) ((E :: nil) ++ (C :: D :: F :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (E :: nil) (C :: D :: F :: nil) (nil) 1 2 0 HEMtmp HCDFMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -1 et 5*)
(* ensembles concernés AUB : B :: C :: D :: E :: A' :: F ::  de rang :  4 et 5 	 AiB :  de rang :  0 et 0 	 A : B :: A' ::   de rang : 1 et 2 *)
assert(HCDEFm2 : rk(C :: D :: E :: F :: nil) >= 2).
{
	assert(HBA'Mtmp : rk(B :: A' :: nil) <= 2) by (solve_hyps_max HBA'eq HBA'M2).
	assert(HBCDEA'Fmtmp : rk(B :: C :: D :: E :: A' :: F :: nil) >= 4) by (solve_hyps_min HBCDEA'Feq HBCDEA'Fm4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: A' :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: E :: A' :: F :: nil) (B :: A' :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: A' :: C :: D :: E :: F :: nil) ((B :: A' :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDEA'Fmtmp;try rewrite HT2 in HBCDEA'Fmtmp.
	assert(HT := rule_4 (B :: A' :: nil) (C :: D :: E :: F :: nil) (nil) 4 0 2 HBCDEA'Fmtmp Hmtmp HBA'Mtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCB' requis par la preuve de (?)ABCB' pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABCB'm3 : rk(A :: B :: C :: B' :: nil) >= 3).
{
	assert(HCDEFMtmp : rk(C :: D :: E :: F :: nil) <= 3) by (solve_hyps_max HCDEFeq HCDEFM3).
	assert(HABCDEB'Fmtmp : rk(A :: B :: C :: D :: E :: B' :: F :: nil) >= 5) by (solve_hyps_min HABCDEB'Feq HABCDEB'Fm5).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: B :: C :: B' :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: B' :: F :: nil) (A :: B :: C :: B' :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: B' :: C :: D :: E :: F :: nil) ((A :: B :: C :: B' :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEB'Fmtmp;try rewrite HT2 in HABCDEB'Fmtmp.
	assert(HT := rule_2 (A :: B :: C :: B' :: nil) (C :: D :: E :: F :: nil) (C :: nil) 5 1 3 HABCDEB'Fmtmp HCmtmp HCDEFMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCA'B'C'D'E'FGH requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA'B'C'D'E'FGH requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA'B'C'D'E'FGH requis par la preuve de (?)ABCDEA'B'C'D'E'FGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'B'C'D'E'FGHm5 : rk(A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCA' requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCA' requis par la preuve de (?)ABCA' pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et 5*)
assert(HABCA'm3 : rk(A :: B :: C :: A' :: nil) >= 3).
{
	assert(HCDEFMtmp : rk(C :: D :: E :: F :: nil) <= 3) by (solve_hyps_max HCDEFeq HCDEFM3).
	assert(HABCDEA'Fmtmp : rk(A :: B :: C :: D :: E :: A' :: F :: nil) >= 5) by (solve_hyps_min HABCDEA'Feq HABCDEA'Fm5).
	assert(HCmtmp : rk(C :: nil) >= 1) by (solve_hyps_min HCeq HCm1).
	assert(Hincl : incl (C :: nil) (list_inter (A :: B :: C :: A' :: nil) (C :: D :: E :: F :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: F :: nil) (A :: B :: C :: A' :: C :: D :: E :: F :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: A' :: C :: D :: E :: F :: nil) ((A :: B :: C :: A' :: nil) ++ (C :: D :: E :: F :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'Fmtmp;try rewrite HT2 in HABCDEA'Fmtmp.
	assert(HT := rule_2 (A :: B :: C :: A' :: nil) (C :: D :: E :: F :: nil) (C :: nil) 5 1 3 HABCDEA'Fmtmp HCmtmp HCDEFMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEA' requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEA' requis par la preuve de (?)ABCDEA' pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEA'm5 : rk(A :: B :: C :: D :: E :: A' :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: A' :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCA'B'C'D'E'FGH requis par la preuve de (?)ABCA'B'C'D'E'FGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 6) *)
(* marque des antécédents AUB AiB A: 5 5 et 5*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  de rang :  5 et 6 	 AiB : A :: B :: C :: A' ::  de rang :  3 et 4 	 A : A :: B :: C :: D :: E :: A' ::   de rang : 5 et 6 *)
assert(HABCA'B'C'D'E'FGHm2 : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 2).
{
	assert(HABCDEA'Mtmp : rk(A :: B :: C :: D :: E :: A' :: nil) <= 6) by (solve_hyps_max HABCDEA'eq HABCDEA'M6).
	assert(HABCDEA'B'C'D'E'FGHmtmp : rk(A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEA'B'C'D'E'FGHeq HABCDEA'B'C'D'E'FGHm5).
	assert(HABCA'mtmp : rk(A :: B :: C :: A' :: nil) >= 3) by (solve_hyps_min HABCA'eq HABCA'm3).
	assert(Hincl : incl (A :: B :: C :: A' :: nil) (list_inter (A :: B :: C :: D :: E :: A' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) (A :: B :: C :: D :: E :: A' :: A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: A' :: A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) ((A :: B :: C :: D :: E :: A' :: nil) ++ (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEA'B'C'D'E'FGHmtmp;try rewrite HT2 in HABCDEA'B'C'D'E'FGHmtmp.
	assert(HT := rule_4 (A :: B :: C :: D :: E :: A' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) (A :: B :: C :: A' :: nil) 5 3 6 HABCDEA'B'C'D'E'FGHmtmp HABCA'mtmp HABCDEA'Mtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 5 *)
assert(HABCA'B'C'D'E'FGHm3 : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 3).
{
	assert(HABCB'mtmp : rk(A :: B :: C :: B' :: nil) >= 3) by (solve_hyps_min HABCB'eq HABCB'm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: B' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) 3 3 HABCB'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'D'E'FGHm5 : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 5).
{
	assert(HA'B'C'D'E'mtmp : rk(A' :: B' :: C' :: D' :: E' :: nil) >= 5) by (solve_hyps_min HA'B'C'D'E'eq HA'B'C'D'E'm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) 5 5 HA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCA'B'C'D'E'FGHm6 : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 6).
{
	assert(HCA'B'C'D'E'mtmp : rk(C :: A' :: B' :: C' :: D' :: E' :: nil) >= 6) by (solve_hyps_min HCA'B'C'D'E'eq HCA'B'C'D'E'm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (C :: A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: A' :: B' :: C' :: D' :: E' :: nil) (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) 6 6 HCA'B'C'D'E'mtmp Hcomp Hincl);apply HT.
}

assert(HABCA'B'C'D'E'FGHM : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCA'B'C'D'E'FGHm : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H ::  nil) >= 1) by (solve_hyps_min HABCA'B'C'D'E'FGHeq HABCA'B'C'D'E'FGHm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABFGH : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> rk(A :: B :: F :: G :: H ::  nil) = 4.
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABFGH requis par la preuve de (?)ABFGH pour la règle 3  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEFGH requis par la preuve de (?)ABCDEFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEFGHm5 : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: F :: G :: H :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCEFGH requis par la preuve de (?)ABCEFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 5 et 6) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : C :: F ::  de rang :  2 et 2 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABCEFGHm5 : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFGHmtmp : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEFGHeq HABCDEFGHm5).
	assert(HCFeq : rk(C :: F :: nil) = 2) by (apply LCF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HCFmtmp : rk(C :: F :: nil) >= 2) by (solve_hyps_min HCFeq HCFm2).
	assert(Hincl : incl (C :: F :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: G :: H :: nil) (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: C :: E :: F :: G :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: C :: E :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFGHmtmp;try rewrite HT2 in HABCDEFGHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: C :: E :: F :: G :: H :: nil) (C :: F :: nil) 5 2 2 HABCDEFGHmtmp HCFmtmp HCDFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour ABFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 6 pour ABEFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABEFGH requis par la preuve de (?)ABEFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 6) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: D :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : C :: D :: F ::   de rang : 2 et 2 *)
assert(HABEFGHm4 : rk(A :: B :: E :: F :: G :: H :: nil) >= 4).
{
	assert(HCDFMtmp : rk(C :: D :: F :: nil) <= 2) by (solve_hyps_max HCDFeq HCDFM2).
	assert(HABCDEFGHmtmp : rk(A :: B :: C :: D :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCDEFGHeq HABCDEFGHm5).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (C :: D :: F :: nil) (A :: B :: E :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: F :: G :: H :: nil) (C :: D :: F :: A :: B :: E :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: D :: F :: A :: B :: E :: F :: G :: H :: nil) ((C :: D :: F :: nil) ++ (A :: B :: E :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEFGHmtmp;try rewrite HT2 in HABCDEFGHmtmp.
	assert(HT := rule_4 (C :: D :: F :: nil) (A :: B :: E :: F :: G :: H :: nil) (F :: nil) 5 1 2 HABCDEFGHmtmp HFmtmp HCDFMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour ABFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABCDFGH pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDFGH requis par la preuve de (?)ABCDFGH pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDFGHm2 : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 2).
{
	assert(HCDFmtmp : rk(C :: D :: F :: nil) >= 2) by (solve_hyps_min HCDFeq HCDFm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil) 2 2 HCDFmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDFGHm3 : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 3).
{
	assert(HACDFeq : rk(A :: C :: D :: F :: nil) = 3) by (apply LACDF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HACDFmtmp : rk(A :: C :: D :: F :: nil) >= 3) by (solve_hyps_min HACDFeq HACDFm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: D :: F :: nil) (A :: B :: C :: D :: F :: G :: H :: nil) 3 3 HACDFmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABFGH requis par la preuve de (?)ABFGH pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: D :: F :: G :: H ::  de rang :  3 et 6 	 AiB : B :: F ::  de rang :  2 et 2 	 A : B :: C :: D :: F ::   de rang : 3 et 3 *)
assert(HABFGHm2 : rk(A :: B :: F :: G :: H :: nil) >= 2).
{
	assert(HBCDFeq : rk(B :: C :: D :: F :: nil) = 3) by (apply LBCDF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBCDFMtmp : rk(B :: C :: D :: F :: nil) <= 3) by (solve_hyps_max HBCDFeq HBCDFM3).
	assert(HABCDFGHmtmp : rk(A :: B :: C :: D :: F :: G :: H :: nil) >= 3) by (solve_hyps_min HABCDFGHeq HABCDFGHm3).
	assert(HBFeq : rk(B :: F :: nil) = 2) by (apply LBF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HBFmtmp : rk(B :: F :: nil) >= 2) by (solve_hyps_min HBFeq HBFm2).
	assert(Hincl : incl (B :: F :: nil) (list_inter (B :: C :: D :: F :: nil) (A :: B :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: F :: G :: H :: nil) (B :: C :: D :: F :: A :: B :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: F :: A :: B :: F :: G :: H :: nil) ((B :: C :: D :: F :: nil) ++ (A :: B :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDFGHmtmp;try rewrite HT2 in HABCDFGHmtmp.
	assert(HT := rule_4 (B :: C :: D :: F :: nil) (A :: B :: F :: G :: H :: nil) (B :: F :: nil) 3 2 3 HABCDFGHmtmp HBFmtmp HBCDFMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: B :: E :: F :: G :: H ::  de rang :  4 et 6 	 AiB : F ::  de rang :  1 et 1 	 A : E :: F ::   de rang : 2 et 2 *)
assert(HABFGHm3 : rk(A :: B :: F :: G :: H :: nil) >= 3).
{
	assert(HEFeq : rk(E :: F :: nil) = 2) by (apply LEF with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HEFMtmp : rk(E :: F :: nil) <= 2) by (solve_hyps_max HEFeq HEFM2).
	assert(HABEFGHmtmp : rk(A :: B :: E :: F :: G :: H :: nil) >= 4) by (solve_hyps_min HABEFGHeq HABEFGHm4).
	assert(HFmtmp : rk(F :: nil) >= 1) by (solve_hyps_min HFeq HFm1).
	assert(Hincl : incl (F :: nil) (list_inter (E :: F :: nil) (A :: B :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: E :: F :: G :: H :: nil) (E :: F :: A :: B :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (E :: F :: A :: B :: F :: G :: H :: nil) ((E :: F :: nil) ++ (A :: B :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABEFGHmtmp;try rewrite HT2 in HABEFGHmtmp.
	assert(HT := rule_4 (E :: F :: nil) (A :: B :: F :: G :: H :: nil) (F :: nil) 4 1 2 HABEFGHmtmp HFmtmp HEFMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: E :: F :: G :: H ::  de rang :  5 et 6 	 AiB : G ::  de rang :  1 et 1 	 A : C :: E :: G ::   de rang : 2 et 2 *)
assert(HABFGHm4 : rk(A :: B :: F :: G :: H :: nil) >= 4).
{
	assert(HCEGMtmp : rk(C :: E :: G :: nil) <= 2) by (solve_hyps_max HCEGeq HCEGM2).
	assert(HABCEFGHmtmp : rk(A :: B :: C :: E :: F :: G :: H :: nil) >= 5) by (solve_hyps_min HABCEFGHeq HABCEFGHm5).
	assert(HGmtmp : rk(G :: nil) >= 1) by (solve_hyps_min HGeq HGm1).
	assert(Hincl : incl (G :: nil) (list_inter (C :: E :: G :: nil) (A :: B :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: E :: F :: G :: H :: nil) (C :: E :: G :: A :: B :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: E :: G :: A :: B :: F :: G :: H :: nil) ((C :: E :: G :: nil) ++ (A :: B :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCEFGHmtmp;try rewrite HT2 in HABCEFGHmtmp.
	assert(HT := rule_4 (C :: E :: G :: nil) (A :: B :: F :: G :: H :: nil) (G :: nil) 5 1 2 HABCEFGHmtmp HGmtmp HCEGMtmp Hincl); apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HABFGHM4 : rk(A :: B :: F :: G :: H :: nil) <= 4).
{
	assert(HABCFGHeq : rk(A :: B :: C :: F :: G :: H :: nil) = 5) by (apply LABCFGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCFGHMtmp : rk(A :: B :: C :: F :: G :: H :: nil) <= 5) by (solve_hyps_max HABCFGHeq HABCFGHM5).
	assert(HABA'B'C'D'E'FGHeq : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) = 5) by (apply LABA'B'C'D'E'FGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABA'B'C'D'E'FGHMtmp : rk(A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) <= 5) by (solve_hyps_max HABA'B'C'D'E'FGHeq HABA'B'C'D'E'FGHM5).
	assert(HABCA'B'C'D'E'FGHeq : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) = 6) by (apply LABCA'B'C'D'E'FGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption).
	assert(HABCA'B'C'D'E'FGHmtmp : rk(A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) >= 6) by (solve_hyps_min HABCA'B'C'D'E'FGHeq HABCA'B'C'D'E'FGHm6).
	assert(Hincl : incl (A :: B :: F :: G :: H :: nil) (list_inter (A :: B :: C :: F :: G :: H :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) (A :: B :: C :: F :: G :: H :: A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: F :: G :: H :: A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) ((A :: B :: C :: F :: G :: H :: nil) ++ (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCA'B'C'D'E'FGHmtmp;try rewrite HT2 in HABCA'B'C'D'E'FGHmtmp.
	assert(HT := rule_3 (A :: B :: C :: F :: G :: H :: nil) (A :: B :: A' :: B' :: C' :: D' :: E' :: F :: G :: H :: nil) (A :: B :: F :: G :: H :: nil) 5 5 6 HABCFGHMtmp HABA'B'C'D'E'FGHMtmp HABCA'B'C'D'E'FGHmtmp Hincl);apply HT.
}


assert(HABFGHM : rk(A :: B :: F :: G :: H ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABFGHeq HABFGHM5).
assert(HABFGHm : rk(A :: B :: F :: G :: H ::  nil) >= 1) by (solve_hyps_min HABFGHeq HABFGHm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C D E A' B' C' D' E' F G H ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(A :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 ->
rk(B :: A' :: B' :: C' :: D' :: E' ::  nil) = 5 -> rk(C :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(D :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 ->
rk(E :: A' :: B' :: C' :: D' :: E' ::  nil) = 6 -> rk(C :: D :: F ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: F ::  nil) = 5 ->
rk(C :: E :: G ::  nil) = 2 -> rk(A' :: B' :: C' :: D' :: E' :: G ::  nil) = 5 -> rk(D :: E :: H ::  nil) = 2 ->
rk(A' :: B' :: C' :: D' :: E' :: H ::  nil) = 5 -> 
	 rk(A :: B :: F :: G :: H ::  nil) = 4  .
Proof.

intros A B C D E A' B' C' D' E' F G H 
HABCDEeq HA'B'C'D'E'eq HAA'B'C'D'E'eq HBA'B'C'D'E'eq HCA'B'C'D'E'eq HDA'B'C'D'E'eq HEA'B'C'D'E'eq HCDFeq HA'B'C'D'E'Feq HCEGeq
HA'B'C'D'E'Geq HDEHeq HA'B'C'D'E'Heq .
repeat split.

	apply LABFGH with (A := A) (B := B) (C := C) (D := D) (E := E) (A' := A') (B' := B') (C' := C') (D' := D') (E' := E') (F := F) (G := G) (H := H) ; assumption.
Qed .
