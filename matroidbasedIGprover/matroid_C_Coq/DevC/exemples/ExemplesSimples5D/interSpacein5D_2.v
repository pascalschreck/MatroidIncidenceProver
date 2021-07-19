Load "preamble5D.v".


(* dans la couche 0 *)
Lemma LABCDEIL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(A :: B :: C :: D :: E :: I :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIL requis par la preuve de (?)ABCDEIL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIL requis par la preuve de (?)ABCDEIL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEILm5 : rk(A :: B :: C :: D :: E :: I :: L :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: L :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HABCDEILM5 : rk(A :: B :: C :: D :: E :: I :: L :: nil) <= 5).
{
	assert(HABCDEIMtmp : rk(A :: B :: C :: D :: E :: I :: nil) <= 5) by (solve_hyps_max HABCDEIeq HABCDEIM5).
	assert(HABCDELMtmp : rk(A :: B :: C :: D :: E :: L :: nil) <= 5) by (solve_hyps_max HABCDELeq HABCDELM5).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: I :: nil) (A :: B :: C :: D :: E :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: L :: nil) (A :: B :: C :: D :: E :: I :: A :: B :: C :: D :: E :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: I :: A :: B :: C :: D :: E :: L :: nil) ((A :: B :: C :: D :: E :: I :: nil) ++ (A :: B :: C :: D :: E :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: I :: nil) (A :: B :: C :: D :: E :: L :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEIMtmp HABCDELMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEILM : rk(A :: B :: C :: D :: E :: I :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEILm : rk(A :: B :: C :: D :: E :: I :: L ::  nil) >= 1) by (solve_hyps_min HABCDEILeq HABCDEILm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIL requis par la preuve de (?)ApBpCpDpEpIL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIL requis par la preuve de (?)ApBpCpDpEpIL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpILm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -4*)
assert(HApBpCpDpEpILM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) <= 5).
{
	assert(HApBpCpDpEpIMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIeq HApBpCpDpEpIM5).
	assert(HApBpCpDpEpLMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpLeq HApBpCpDpEpLM5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpIMtmp HApBpCpDpEpLMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpILM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpILm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpILeq HApBpCpDpEpILm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(A :: B :: C :: D :: E :: I :: J :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJL requis par la preuve de (?)ABCDEIJL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJL requis par la preuve de (?)ABCDEIJL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEIJLm5 : rk(A :: B :: C :: D :: E :: I :: J :: L :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: L :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABCDEIJLM5 : rk(A :: B :: C :: D :: E :: I :: J :: L :: nil) <= 5).
{
	assert(HABCDEJMtmp : rk(A :: B :: C :: D :: E :: J :: nil) <= 5) by (solve_hyps_max HABCDEJeq HABCDEJM5).
	assert(HABCDEILeq : rk(A :: B :: C :: D :: E :: I :: L :: nil) = 5) by (apply LABCDEIL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HABCDEILMtmp : rk(A :: B :: C :: D :: E :: I :: L :: nil) <= 5) by (solve_hyps_max HABCDEILeq HABCDEILM5).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: J :: nil) (A :: B :: C :: D :: E :: I :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: L :: nil) (A :: B :: C :: D :: E :: J :: A :: B :: C :: D :: E :: I :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: J :: A :: B :: C :: D :: E :: I :: L :: nil) ((A :: B :: C :: D :: E :: J :: nil) ++ (A :: B :: C :: D :: E :: I :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: J :: nil) (A :: B :: C :: D :: E :: I :: L :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEJMtmp HABCDEILMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEIJLM : rk(A :: B :: C :: D :: E :: I :: J :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJLm : rk(A :: B :: C :: D :: E :: I :: J :: L ::  nil) >= 1) by (solve_hyps_min HABCDEIJLeq HABCDEIJLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIJL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJL requis par la preuve de (?)ApBpCpDpEpIJL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJL requis par la preuve de (?)ApBpCpDpEpIJL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpIJLm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpDpEpIJLM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) <= 5).
{
	assert(HApBpCpDpEpJMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpJeq HApBpCpDpEpJM5).
	assert(HApBpCpDpEpILeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) = 5) by (apply LApBpCpDpEpIL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HApBpCpDpEpILMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpILeq HApBpCpDpEpILM5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: J :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: J :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpJMtmp HApBpCpDpEpILMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpIJLM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJLm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJLeq HApBpCpDpEpIJLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJKL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(A :: B :: C :: D :: E :: I :: J :: K :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJKL requis par la preuve de (?)ABCDEIJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJKL requis par la preuve de (?)ABCDEIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEIJKLm5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HABCDEIJKLM5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) <= 5).
{
	assert(HABCDEKMtmp : rk(A :: B :: C :: D :: E :: K :: nil) <= 5) by (solve_hyps_max HABCDEKeq HABCDEKM5).
	assert(HABCDEIJLeq : rk(A :: B :: C :: D :: E :: I :: J :: L :: nil) = 5) by (apply LABCDEIJL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HABCDEIJLMtmp : rk(A :: B :: C :: D :: E :: I :: J :: L :: nil) <= 5) by (solve_hyps_max HABCDEIJLeq HABCDEIJLM5).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: K :: nil) (A :: B :: C :: D :: E :: I :: J :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) (A :: B :: C :: D :: E :: K :: A :: B :: C :: D :: E :: I :: J :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: K :: A :: B :: C :: D :: E :: I :: J :: L :: nil) ((A :: B :: C :: D :: E :: K :: nil) ++ (A :: B :: C :: D :: E :: I :: J :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: K :: nil) (A :: B :: C :: D :: E :: I :: J :: L :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEKMtmp HABCDEIJLMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEIJKLM : rk(A :: B :: C :: D :: E :: I :: J :: K :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJKLm : rk(A :: B :: C :: D :: E :: I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HABCDEIJKLeq HABCDEIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIJKL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJKL requis par la preuve de (?)ApBpCpDpEpIJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJKL requis par la preuve de (?)ApBpCpDpEpIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpIJKLm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et -4*)
assert(HApBpCpDpEpIJKLM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) <= 5).
{
	assert(HApBpCpDpEpKMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpKeq HApBpCpDpEpKM5).
	assert(HApBpCpDpEpIJLeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) = 5) by (apply LApBpCpDpEpIJL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HApBpCpDpEpIJLMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJLeq HApBpCpDpEpIJLM5).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: K :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: K :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpKMtmp HApBpCpDpEpIJLMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpIJKLM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJKLm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJKLeq HApBpCpDpEpIJKLm1).
intuition.
Qed.

(* dans constructLemma(), requis par LApBpCpDpEpM *)
(* dans la couche 0 *)
Lemma LApBpCpDpEpIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJKLM requis par la preuve de (?)ApBpCpDpEpIJKLM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJKLM requis par la preuve de (?)ApBpCpDpEpIJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpIJKLMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 -4 et -4*)
assert(HApBpCpDpEpIJKLMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) <= 5).
{
	assert(HApBpCpDpEpIJKLeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) = 5) by (apply LApBpCpDpEpIJKL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HApBpCpDpEpIJKLMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJKLeq HApBpCpDpEpIJKLM5).
	assert(HIJKLMMtmp : rk(I :: J :: K :: L :: M :: nil) <= 4) by (solve_hyps_max HIJKLMeq HIJKLMM4).
	assert(HIJKLmtmp : rk(I :: J :: K :: L :: nil) >= 4) by (solve_hyps_min HIJKLeq HIJKLm4).
	assert(Hincl : incl (I :: J :: K :: L :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: I :: J :: K :: L :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: I :: J :: K :: L :: M :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) ++ (I :: J :: K :: L :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil) (I :: J :: K :: L :: nil) 5 4 4 HApBpCpDpEpIJKLMtmp HIJKLMMtmp HIJKLmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HApBpCpDpEpIJKLMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJKLMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJKLMeq HApBpCpDpEpIJKLMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpM requis par la preuve de (?)ApBpCpDpEpM pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpM requis par la preuve de (?)ApBpCpDpEpM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HApBpCpDpEpMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) >= 5).
{
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpEpMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) <= 5).
{
	assert(HApBpCpDpEpIJKLMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) = 5) by (apply LApBpCpDpEpIJKLM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HApBpCpDpEpIJKLMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJKLMeq HApBpCpDpEpIJKLMM5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) 5 5 HApBpCpDpEpIJKLMMtmp Hcomp Hincl);apply HT.
}

assert(HApBpCpDpEpMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpMeq HApBpCpDpEpMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJKLM requis par la preuve de (?)ABCDEIJKLM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJKLM requis par la preuve de (?)ABCDEIJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEIJKLMm5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 -4 et -4*)
assert(HABCDEIJKLMM5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) <= 5).
{
	assert(HABCDEIJKLeq : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) = 5) by (apply LABCDEIJKL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HABCDEIJKLMtmp : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) <= 5) by (solve_hyps_max HABCDEIJKLeq HABCDEIJKLM5).
	assert(HIJKLMMtmp : rk(I :: J :: K :: L :: M :: nil) <= 4) by (solve_hyps_max HIJKLMeq HIJKLMM4).
	assert(HIJKLmtmp : rk(I :: J :: K :: L :: nil) >= 4) by (solve_hyps_min HIJKLeq HIJKLm4).
	assert(Hincl : incl (I :: J :: K :: L :: nil) (list_inter (A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: I :: J :: K :: L :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: L :: I :: J :: K :: L :: M :: nil) ((A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) ++ (I :: J :: K :: L :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil) (I :: J :: K :: L :: nil) 5 4 4 HABCDEIJKLMtmp HIJKLMMtmp HIJKLmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HABCDEIJKLMM : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJKLMm : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HABCDEIJKLMeq HABCDEIJKLMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> rk(A :: B :: C :: D :: E :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEM requis par la preuve de (?)ABCDEM pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEM requis par la preuve de (?)ABCDEM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCDEMm5 : rk(A :: B :: C :: D :: E :: M :: nil) >= 5).
{
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEMM5 : rk(A :: B :: C :: D :: E :: M :: nil) <= 5).
{
	assert(HABCDEIJKLMeq : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) = 5) by (apply LABCDEIJKLM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption).
	assert(HABCDEIJKLMMtmp : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) <= 5) by (solve_hyps_max HABCDEIJKLMeq HABCDEIJKLMM5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: M :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: C :: D :: E :: M :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) 5 5 HABCDEIJKLMMtmp Hcomp Hincl);apply HT.
}

assert(HABCDEMM : rk(A :: B :: C :: D :: E :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEMm : rk(A :: B :: C :: D :: E :: M ::  nil) >= 1) by (solve_hyps_min HABCDEMeq HABCDEMm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4 -> 
	 rk(A :: B :: C :: D :: E :: M ::  nil) = 5  /\ 
	 rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5  .
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HIJKLMeq .
repeat split.

	apply LABCDEM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption.

	apply LApBpCpDpEpM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ; assumption.
Qed .
