Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LABC : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HABCM : rk(A :: B :: C ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HABCeq HABCM3).
assert(HABCm : rk(A :: B :: C ::  nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCp : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HApBpCpM : rk(Ap :: Bp :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HApBpCpeq HApBpCpM3).
assert(HApBpCpm : rk(Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HApBpCpeq HApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HABCMM : rk(A :: B :: C :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMm : rk(A :: B :: C :: M ::  nil) >= 1) by (solve_hyps_min HABCMeq HABCMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HApBpCpMM : rk(Ap :: Bp :: Cp :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMm : rk(Ap :: Bp :: Cp :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpMeq HApBpCpMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HABCNM : rk(A :: B :: C :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCNm : rk(A :: B :: C :: N ::  nil) >= 1) by (solve_hyps_min HABCNeq HABCNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HApBpCpNM : rk(Ap :: Bp :: Cp :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpNm : rk(Ap :: Bp :: Cp :: N ::  nil) >= 1) by (solve_hyps_min HApBpCpNeq HApBpCpNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(M :: N ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HMNM : rk(M :: N ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HMNeq HMNM2).
assert(HMNm : rk(M :: N ::  nil) >= 1) by (solve_hyps_min HMNeq HMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMN requis par la preuve de (?)ABCMN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCMNm3 : rk(A :: B :: C :: M :: N :: nil) >= 3).
{
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCMNM3 : rk(A :: B :: C :: M :: N :: nil) <= 3).
{
	try assert(HABCMeq : rk(A :: B :: C :: M :: nil) = 3) by (apply LABCM with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	try assert(HABCNeq : rk(A :: B :: C :: N :: nil) = 3) by (apply LABCN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: nil) (A :: B :: C :: M :: A :: B :: C :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: N :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: N :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCNMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCMM1. try clear HABCMM2. try clear HABCMM3. try clear HABCMm4. try clear HABCMm3. try clear HABCMm2. try clear HABCMm1. try clear HABCNM1. try clear HABCNM2. try clear HABCNM3. try clear HABCNm4. try clear HABCNm3. try clear HABCNm2. try clear HABCNm1. 

assert(HABCMNM : rk(A :: B :: C :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNm : rk(A :: B :: C :: M :: N ::  nil) >= 1) by (solve_hyps_min HABCMNeq HABCMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMN requis par la preuve de (?)ApBpCpMN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMN requis par la preuve de (?)ApBpCpMN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpMNm3 : rk(Ap :: Bp :: Cp :: M :: N :: nil) >= 3).
{
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpMNM3 : rk(Ap :: Bp :: Cp :: M :: N :: nil) <= 3).
{
	try assert(HApBpCpMeq : rk(Ap :: Bp :: Cp :: M :: nil) = 3) by (apply LApBpCpM with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMMtmp : rk(Ap :: Bp :: Cp :: M :: nil) <= 3) by (solve_hyps_max HApBpCpMeq HApBpCpMM3).
	try assert(HApBpCpNeq : rk(Ap :: Bp :: Cp :: N :: nil) = 3) by (apply LApBpCpN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpNMtmp : rk(Ap :: Bp :: Cp :: N :: nil) <= 3) by (solve_hyps_max HApBpCpNeq HApBpCpNM3).
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: N :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: nil) (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: N :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: N :: nil) ((Ap :: Bp :: Cp :: M :: nil) ++ (Ap :: Bp :: Cp :: N :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpMMtmp HApBpCpNMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpMM1. try clear HApBpCpMM2. try clear HApBpCpMM3. try clear HApBpCpMm4. try clear HApBpCpMm3. try clear HApBpCpMm2. try clear HApBpCpMm1. try clear HApBpCpNM1. try clear HApBpCpNM2. try clear HApBpCpNM3. try clear HApBpCpNm4. try clear HApBpCpNm3. try clear HApBpCpNm2. try clear HApBpCpNm1. 

assert(HApBpCpMNM : rk(Ap :: Bp :: Cp :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNm : rk(Ap :: Bp :: Cp :: M :: N ::  nil) >= 1) by (solve_hyps_min HApBpCpMNeq HApBpCpMNm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABCP *)
(* dans constructLemma(), requis par LABCMNP *)
(* dans la couche 0 *)
Lemma LMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMNP requis par la preuve de (?)ABCMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCMNPm3 : rk(A :: B :: C :: M :: N :: P :: nil) >= 3).
{
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCMNPM3 : rk(A :: B :: C :: M :: N :: P :: nil) <= 3).
{
	try assert(HABCMNeq : rk(A :: B :: C :: M :: N :: nil) = 3) by (apply LABCMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMNMtmp : rk(A :: B :: C :: M :: N :: nil) <= 3) by (solve_hyps_max HABCMNeq HABCMNM3).
	try assert(HMNPeq : rk(M :: N :: P :: nil) = 2) by (apply LMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HMNPMtmp : rk(M :: N :: P :: nil) <= 2) by (solve_hyps_max HMNPeq HMNPM2).
	try assert(HMNeq : rk(M :: N :: nil) = 2) by (apply LMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (A :: B :: C :: M :: N :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: M :: N :: P :: nil) ((A :: B :: C :: M :: N :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: N :: nil) (M :: N :: P :: nil) (M :: N :: nil) 3 2 2 HABCMNMtmp HMNPMtmp HMNmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(A :: B :: C :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCP requis par la preuve de (?)ABCP pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCP requis par la preuve de (?)ABCP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCPm3 : rk(A :: B :: C :: P :: nil) >= 3).
{
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCPM3 : rk(A :: B :: C :: P :: nil) <= 3).
{
	try assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: C :: P :: nil) (A :: B :: C :: M :: N :: P :: nil) 3 3 HABCMNPMtmp Hcomp Hincl);apply HT.
}


assert(HABCPM : rk(A :: B :: C :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCPm : rk(A :: B :: C :: P ::  nil) >= 1) by (solve_hyps_min HABCPeq HABCPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMNP requis par la preuve de (?)ApBpCpMNP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMNP requis par la preuve de (?)ApBpCpMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpMNPm3 : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 3).
{
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpMNPM3 : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3).
{
	try assert(HApBpCpMNeq : rk(Ap :: Bp :: Cp :: M :: N :: nil) = 3) by (apply LApBpCpMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMNMtmp : rk(Ap :: Bp :: Cp :: M :: N :: nil) <= 3) by (solve_hyps_max HApBpCpMNeq HApBpCpMNM3).
	try assert(HMNPeq : rk(M :: N :: P :: nil) = 2) by (apply LMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HMNPMtmp : rk(M :: N :: P :: nil) <= 2) by (solve_hyps_max HMNPeq HMNPM2).
	try assert(HMNeq : rk(M :: N :: nil) = 2) by (apply LMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hincl : incl (M :: N :: nil) (list_inter (Ap :: Bp :: Cp :: M :: N :: nil) (M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: N :: M :: N :: P :: nil) ((Ap :: Bp :: Cp :: M :: N :: nil) ++ (M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: N :: nil) (M :: N :: P :: nil) (M :: N :: nil) 3 2 2 HApBpCpMNMtmp HMNPMtmp HMNmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HMNPM1. try clear HMNPM2. try clear HMNPM3. try clear HMNPm4. try clear HMNPm3. try clear HMNPm2. try clear HMNPm1. try clear HMNM1. try clear HMNM2. try clear HMNM3. try clear HMNm4. try clear HMNm3. try clear HMNm2. try clear HMNm1. 

assert(HApBpCpMNPM : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNPm : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMNPeq HApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(M :: N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HMNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpP requis par la preuve de (?)ApBpCpP pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpP requis par la preuve de (?)ApBpCpP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpPm3 : rk(Ap :: Bp :: Cp :: P :: nil) >= 3).
{
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpPM3 : rk(Ap :: Bp :: Cp :: P :: nil) <= 3).
{
	try assert(HApBpCpMNPeq : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) = 3) by (apply LApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMNPMtmp : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMNPeq HApBpCpMNPM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HApBpCpMNPMtmp Hcomp Hincl);apply HT.
}


assert(HApBpCpPM : rk(Ap :: Bp :: Cp :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpPm : rk(Ap :: Bp :: Cp :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpPeq HApBpCpPm1).
intuition.
Qed.

