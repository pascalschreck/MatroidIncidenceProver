Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LABC : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HABCM : rk(A :: B :: C ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HABCeq HABCM3).
assert(HABCm : rk(A :: B :: C ::  nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCp : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HApBpCpM : rk(Ap :: Bp :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HApBpCpeq HApBpCpM3).
assert(HApBpCpm : rk(Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HApBpCpeq HApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCp : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HABCApBpCpM : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpm : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HABCMM : rk(A :: B :: C :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMm : rk(A :: B :: C :: M ::  nil) >= 1) by (solve_hyps_min HABCMeq HABCMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HApBpCpMM : rk(Ap :: Bp :: Cp :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMm : rk(Ap :: Bp :: Cp :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpMeq HApBpCpMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HABCNM : rk(A :: B :: C :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCNm : rk(A :: B :: C :: N ::  nil) >= 1) by (solve_hyps_min HABCNeq HABCNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HApBpCpNM : rk(Ap :: Bp :: Cp :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpNm : rk(Ap :: Bp :: Cp :: N ::  nil) >= 1) by (solve_hyps_min HApBpCpNeq HApBpCpNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(M :: N ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HMNM : rk(M :: N ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HMNeq HMNM2).
assert(HMNm : rk(M :: N ::  nil) >= 1) by (solve_hyps_min HMNeq HMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HABCPM : rk(A :: B :: C :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCPm : rk(A :: B :: C :: P ::  nil) >= 1) by (solve_hyps_min HABCPeq HABCPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

assert(HApBpCpPM : rk(Ap :: Bp :: Cp :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpPm : rk(Ap :: Bp :: Cp :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpPeq HApBpCpPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCMP requis par la preuve de (?)ABCMP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCMPm3 : rk(A :: B :: C :: M :: P :: nil) >= 3).
{
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: M :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCMPM3 : rk(A :: B :: C :: M :: P :: nil) <= 3).
{
	try assert(HABCMeq : rk(A :: B :: C :: M :: nil) = 3) by (apply LABCM with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMMtmp : rk(A :: B :: C :: M :: nil) <= 3) by (solve_hyps_max HABCMeq HABCMM3).
	try assert(HABCPeq : rk(A :: B :: C :: P :: nil) = 3) by (apply LABCP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCPMtmp : rk(A :: B :: C :: P :: nil) <= 3) by (solve_hyps_max HABCPeq HABCPM3).
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: P :: nil) (A :: B :: C :: M :: A :: B :: C :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: A :: B :: C :: P :: nil) ((A :: B :: C :: M :: nil) ++ (A :: B :: C :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: M :: nil) (A :: B :: C :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCMMtmp HABCPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCMM1. try clear HABCMM2. try clear HABCMM3. try clear HABCMm4. try clear HABCMm3. try clear HABCMm2. try clear HABCMm1. try clear HABCPM1. try clear HABCPM2. try clear HABCPM3. try clear HABCPm4. try clear HABCPm3. try clear HABCPm2. try clear HABCPm1. 

assert(HABCMPM : rk(A :: B :: C :: M :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMPm : rk(A :: B :: C :: M :: P ::  nil) >= 1) by (solve_hyps_min HABCMPeq HABCMPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ApBpCpMP requis par la preuve de (?)ApBpCpMP pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ApBpCpMP requis par la preuve de (?)ApBpCpMP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpMPm3 : rk(Ap :: Bp :: Cp :: M :: P :: nil) >= 3).
{
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: nil) (Ap :: Bp :: Cp :: M :: P :: nil) 3 3 HApBpCpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpMPM3 : rk(Ap :: Bp :: Cp :: M :: P :: nil) <= 3).
{
	try assert(HApBpCpMeq : rk(Ap :: Bp :: Cp :: M :: nil) = 3) by (apply LApBpCpM with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMMtmp : rk(Ap :: Bp :: Cp :: M :: nil) <= 3) by (solve_hyps_max HApBpCpMeq HApBpCpMM3).
	try assert(HApBpCpPeq : rk(Ap :: Bp :: Cp :: P :: nil) = 3) by (apply LApBpCpP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpPMtmp : rk(Ap :: Bp :: Cp :: P :: nil) <= 3) by (solve_hyps_max HApBpCpPeq HApBpCpPM3).
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: P :: nil) (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: M :: Ap :: Bp :: Cp :: P :: nil) ((Ap :: Bp :: Cp :: M :: nil) ++ (Ap :: Bp :: Cp :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: M :: nil) (Ap :: Bp :: Cp :: P :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpMMtmp HApBpCpPMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpMM1. try clear HApBpCpMM2. try clear HApBpCpMM3. try clear HApBpCpMm4. try clear HApBpCpMm3. try clear HApBpCpMm2. try clear HApBpCpMm1. try clear HApBpCpPM1. try clear HApBpCpPM2. try clear HApBpCpPM3. try clear HApBpCpPm4. try clear HApBpCpPm3. try clear HApBpCpPm2. try clear HApBpCpPm1. 

assert(HApBpCpMPM : rk(Ap :: Bp :: Cp :: M :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMPm : rk(Ap :: Bp :: Cp :: M :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMPeq HApBpCpMPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

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
	try assert(HABCNeq : rk(A :: B :: C :: N :: nil) = 3) by (apply LABCN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCNMtmp : rk(A :: B :: C :: N :: nil) <= 3) by (solve_hyps_max HABCNeq HABCNM3).
	try assert(HABCMPeq : rk(A :: B :: C :: M :: P :: nil) = 3) by (apply LABCMP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMPMtmp : rk(A :: B :: C :: M :: P :: nil) <= 3) by (solve_hyps_max HABCMPeq HABCMPM3).
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hincl : incl (A :: B :: C :: nil) (list_inter (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: M :: N :: P :: nil) (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: N :: A :: B :: C :: M :: P :: nil) ((A :: B :: C :: N :: nil) ++ (A :: B :: C :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: N :: nil) (A :: B :: C :: M :: P :: nil) (A :: B :: C :: nil) 3 3 3 HABCNMtmp HABCMPMtmp HABCmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCNM1. try clear HABCNM2. try clear HABCNM3. try clear HABCNm4. try clear HABCNm3. try clear HABCNm2. try clear HABCNm1. 

assert(HABCMNPM : rk(A :: B :: C :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMNPm : rk(A :: B :: C :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCMNPeq HABCMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

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
	try assert(HApBpCpNeq : rk(Ap :: Bp :: Cp :: N :: nil) = 3) by (apply LApBpCpN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpNMtmp : rk(Ap :: Bp :: Cp :: N :: nil) <= 3) by (solve_hyps_max HApBpCpNeq HApBpCpNM3).
	try assert(HApBpCpMPeq : rk(Ap :: Bp :: Cp :: M :: P :: nil) = 3) by (apply LApBpCpMP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMPMtmp : rk(Ap :: Bp :: Cp :: M :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMPeq HApBpCpMPM3).
	try assert(HApBpCpeq : rk(Ap :: Bp :: Cp :: nil) = 3) by (apply LApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpmtmp : rk(Ap :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HApBpCpeq HApBpCpm3).
	assert(Hincl : incl (Ap :: Bp :: Cp :: nil) (list_inter (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: M :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: N :: Ap :: Bp :: Cp :: M :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: N :: Ap :: Bp :: Cp :: M :: P :: nil) ((Ap :: Bp :: Cp :: N :: nil) ++ (Ap :: Bp :: Cp :: M :: P :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: N :: nil) (Ap :: Bp :: Cp :: M :: P :: nil) (Ap :: Bp :: Cp :: nil) 3 3 3 HApBpCpNMtmp HApBpCpMPMtmp HApBpCpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpNM1. try clear HApBpCpNM2. try clear HApBpCpNM3. try clear HApBpCpNm4. try clear HApBpCpNm3. try clear HApBpCpNm2. try clear HApBpCpNm1. 

assert(HApBpCpMNPM : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMNPm : rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpMNPeq HApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCpMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpCpMNP requis par la preuve de (?)ABCApBpCpMNP pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpCpMNP requis par la preuve de (?)ABCApBpCpMNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpMNPm3 : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 3).
{
	try assert(HABCeq : rk(A :: B :: C :: nil) = 3) by (apply LABC with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCmtmp : rk(A :: B :: C :: nil) >= 3) by (solve_hyps_min HABCeq HABCm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) 3 3 HABCmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCApBpCpMNPm4 : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 4).
{
	try assert(HABCApBpCpeq : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LABCApBpCp with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCApBpCpmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) 4 4 HABCApBpCpmtmp Hcomp Hincl);apply HT.
}
try clear HABCApBpCpM1. try clear HABCApBpCpM2. try clear HABCApBpCpM3. try clear HABCApBpCpm4. try clear HABCApBpCpm3. try clear HABCApBpCpm2. try clear HABCApBpCpm1. 

assert(HABCApBpCpMNPM : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpMNPm : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) >= 1) by (solve_hyps_min HABCApBpCpMNPeq HABCApBpCpMNPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMNP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: P ::  nil) = 2 -> rk(N :: P ::  nil) = 2 ->
rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
HMPeq HNPeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour MNP requis par la preuve de (?)MNP pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HMNPm2 : rk(M :: N :: P :: nil) >= 2).
{
	try assert(HMNeq : rk(M :: N :: nil) = 2) by (apply LMN with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HMNmtmp : rk(M :: N :: nil) >= 2) by (solve_hyps_min HMNeq HMNm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (M :: N :: nil) (M :: N :: P :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (M :: N :: nil) (M :: N :: P :: nil) 2 2 HMNmtmp Hcomp Hincl);apply HT.
}
try clear HMNM1. try clear HMNM2. try clear HMNM3. try clear HMNm4. try clear HMNm3. try clear HMNm2. try clear HMNm1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HMNPM2 : rk(M :: N :: P :: nil) <= 2).
{
	try assert(HABCMNPeq : rk(A :: B :: C :: M :: N :: P :: nil) = 3) by (apply LABCMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCMNPMtmp : rk(A :: B :: C :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HABCMNPeq HABCMNPM3).
	try assert(HApBpCpMNPeq : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) = 3) by (apply LApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HApBpCpMNPMtmp : rk(Ap :: Bp :: Cp :: M :: N :: P :: nil) <= 3) by (solve_hyps_max HApBpCpMNPeq HApBpCpMNPM3).
	try assert(HABCApBpCpMNPeq : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) = 4) by (apply LABCApBpCpMNP with (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (M := M) (N := N) (P := P) ;try assumption).
	assert(HABCApBpCpMNPmtmp : rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) >= 4) by (solve_hyps_min HABCApBpCpMNPeq HABCApBpCpMNPm4).
	assert(Hincl : incl (M :: N :: P :: nil) (list_inter (A :: B :: C :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P :: nil) (A :: B :: C :: M :: N :: P :: Ap :: Bp :: Cp :: M :: N :: P :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: M :: N :: P :: Ap :: Bp :: Cp :: M :: N :: P :: nil) ((A :: B :: C :: M :: N :: P :: nil) ++ (Ap :: Bp :: Cp :: M :: N :: P :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpCpMNPmtmp;try rewrite HT2 in HABCApBpCpMNPmtmp.
	assert(HT := rule_3 (A :: B :: C :: M :: N :: P :: nil) (Ap :: Bp :: Cp :: M :: N :: P :: nil) (M :: N :: P :: nil) 3 3 4 HABCMNPMtmp HApBpCpMNPMtmp HABCApBpCpMNPmtmp Hincl);apply HT.
}


assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
intuition.
Qed.

