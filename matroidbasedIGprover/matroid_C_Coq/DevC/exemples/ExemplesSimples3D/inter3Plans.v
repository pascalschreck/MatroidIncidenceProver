Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LBCAp : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBCApM : rk(B :: C :: Ap ::  nil) <= 3) by (solve_hyps_max HBCApeq HBCApM3).
assert(HBCApm : rk(B :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HBCApeq HBCApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpAs : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBpCpAsM : rk(Bp :: Cp :: As ::  nil) <= 3) by (solve_hyps_max HBpCpAseq HBpCpAsM3).
assert(HBpCpAsm : rk(Bp :: Cp :: As ::  nil) >= 1) by (solve_hyps_min HBpCpAseq HBpCpAsm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCApBpCpAs : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBCApBpCpAsM : rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApBpCpAsm : rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) >= 1) by (solve_hyps_min HBCApBpCpAseq HBCApBpCpAsm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsM : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBsCsMM : rk(Bs :: Cs :: M ::  nil) <= 3) by (solve_hyps_max HBsCsMeq HBsCsMM3).
assert(HBsCsMm : rk(Bs :: Cs :: M ::  nil) >= 1) by (solve_hyps_min HBsCsMeq HBsCsMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCApN : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: N ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBCApNM : rk(B :: C :: Ap :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApNm : rk(B :: C :: Ap :: N ::  nil) >= 1) by (solve_hyps_min HBCApNeq HBCApNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpAsN : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As :: N ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBpCpAsNM : rk(Bp :: Cp :: As :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBpCpAsNm : rk(Bp :: Cp :: As :: N ::  nil) >= 1) by (solve_hyps_min HBpCpAsNeq HBpCpAsNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsMN : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M :: N ::  nil) = 4.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBsCsMNM : rk(Bs :: Cs :: M :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBsCsMNm : rk(Bs :: Cs :: M :: N ::  nil) >= 1) by (solve_hyps_min HBsCsMNeq HBsCsMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Y ::  nil) = 1.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HYM : rk(Y ::  nil) <= 1) by (solve_hyps_max HYeq HYM1).
assert(HYm : rk(Y ::  nil) >= 1) by (solve_hyps_min HYeq HYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCApY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: Y ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBCApYM : rk(B :: C :: Ap :: Y ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApYm : rk(B :: C :: Ap :: Y ::  nil) >= 1) by (solve_hyps_min HBCApYeq HBCApYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpAsY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As :: Y ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBpCpAsYM : rk(Bp :: Cp :: As :: Y ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBpCpAsYm : rk(Bp :: Cp :: As :: Y ::  nil) >= 1) by (solve_hyps_min HBpCpAsYeq HBpCpAsYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsMY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M :: Y ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBsCsMYM : rk(Bs :: Cs :: M :: Y ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBsCsMYm : rk(Bs :: Cs :: M :: Y ::  nil) >= 1) by (solve_hyps_min HBsCsMYeq HBsCsMYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCAp : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBCApM : rk(B :: C :: Ap ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApm : rk(B :: C :: Ap ::  ::  nil) >= 1) by (solve_hyps_min HBCApeq HBCApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpAs : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBpCpAsM : rk(Bp :: Cp :: As ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBpCpAsm : rk(Bp :: Cp :: As ::  ::  nil) >= 1) by (solve_hyps_min HBpCpAseq HBpCpAsm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsM : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

assert(HBsCsMM : rk(Bs :: Cs :: M ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBsCsMm : rk(Bs :: Cs :: M ::  ::  nil) >= 1) by (solve_hyps_min HBsCsMeq HBsCsMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCApN : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: N ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCApN requis par la preuve de (?)BCApN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCApN requis par la preuve de (?)BCApN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCApNm3 : rk(B :: C :: Ap :: N ::  :: nil) >= 3).
{
	try assert(HBCApeq : rk(B :: C :: Ap :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApmtmp : rk(B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HBCApeq HBCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Ap :: nil) (B :: C :: Ap :: N ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Ap :: nil) (B :: C :: Ap :: N ::  :: nil) 3 3 HBCApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCApNM3 : rk(B :: C :: Ap :: N ::  :: nil) <= 3).
{
	try assert(HBCApNeq : rk(B :: C :: Ap :: N :: nil) = 3) by (apply LBCApN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApNMtmp : rk(B :: C :: Ap :: N :: nil) <= 3) by (solve_hyps_max HBCApNeq HBCApNM3).
	try assert(HBCApeq : rk(B :: C :: Ap ::  :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApMtmp : rk(B :: C :: Ap ::  :: nil) <= 3) by (solve_hyps_max HBCApeq HBCApM3).
	try assert(HBCApeq : rk(B :: C :: Ap :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApmtmp : rk(B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HBCApeq HBCApm3).
	assert(Hincl : incl (B :: C :: Ap :: nil) (list_inter (B :: C :: Ap :: N :: nil) (B :: C :: Ap ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: N ::  :: nil) (B :: C :: Ap :: N :: B :: C :: Ap ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Ap :: N :: B :: C :: Ap ::  :: nil) ((B :: C :: Ap :: N :: nil) ++ (B :: C :: Ap ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: Ap :: N :: nil) (B :: C :: Ap ::  :: nil) (B :: C :: Ap :: nil) 3 3 3 HBCApNMtmp HBCApMtmp HBCApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBCApNM1. try clear HBCApNM2. try clear HBCApNM3. try clear HBCApNm4. try clear HBCApNm3. try clear HBCApNm2. try clear HBCApNm1. try clear HBCApM1. try clear HBCApM2. try clear HBCApM3. try clear HBCApm4. try clear HBCApm3. try clear HBCApm2. try clear HBCApm1. 

assert(HBCApNM : rk(B :: C :: Ap :: N ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApNm : rk(B :: C :: Ap :: N ::  ::  nil) >= 1) by (solve_hyps_min HBCApNeq HBCApNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpAsN : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As :: N ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BpCpAsN requis par la preuve de (?)BpCpAsN pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BpCpAsN requis par la preuve de (?)BpCpAsN pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBpCpAsNm3 : rk(Bp :: Cp :: As :: N ::  :: nil) >= 3).
{
	try assert(HBpCpAseq : rk(Bp :: Cp :: As :: nil) = 3) by (apply LBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsmtmp : rk(Bp :: Cp :: As :: nil) >= 3) by (solve_hyps_min HBpCpAseq HBpCpAsm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Bp :: Cp :: As :: nil) (Bp :: Cp :: As :: N ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bp :: Cp :: As :: nil) (Bp :: Cp :: As :: N ::  :: nil) 3 3 HBpCpAsmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBpCpAsNM3 : rk(Bp :: Cp :: As :: N ::  :: nil) <= 3).
{
	try assert(HBpCpAsNeq : rk(Bp :: Cp :: As :: N :: nil) = 3) by (apply LBpCpAsN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsNMtmp : rk(Bp :: Cp :: As :: N :: nil) <= 3) by (solve_hyps_max HBpCpAsNeq HBpCpAsNM3).
	try assert(HBpCpAseq : rk(Bp :: Cp :: As ::  :: nil) = 3) by (apply LBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsMtmp : rk(Bp :: Cp :: As ::  :: nil) <= 3) by (solve_hyps_max HBpCpAseq HBpCpAsM3).
	try assert(HBpCpAseq : rk(Bp :: Cp :: As :: nil) = 3) by (apply LBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsmtmp : rk(Bp :: Cp :: As :: nil) >= 3) by (solve_hyps_min HBpCpAseq HBpCpAsm3).
	assert(Hincl : incl (Bp :: Cp :: As :: nil) (list_inter (Bp :: Cp :: As :: N :: nil) (Bp :: Cp :: As ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bp :: Cp :: As :: N ::  :: nil) (Bp :: Cp :: As :: N :: Bp :: Cp :: As ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: As :: N :: Bp :: Cp :: As ::  :: nil) ((Bp :: Cp :: As :: N :: nil) ++ (Bp :: Cp :: As ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: As :: N :: nil) (Bp :: Cp :: As ::  :: nil) (Bp :: Cp :: As :: nil) 3 3 3 HBpCpAsNMtmp HBpCpAsMtmp HBpCpAsmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpCpAsNM1. try clear HBpCpAsNM2. try clear HBpCpAsNM3. try clear HBpCpAsNm4. try clear HBpCpAsNm3. try clear HBpCpAsNm2. try clear HBpCpAsNm1. try clear HBpCpAsM1. try clear HBpCpAsM2. try clear HBpCpAsM3. try clear HBpCpAsm4. try clear HBpCpAsm3. try clear HBpCpAsm2. try clear HBpCpAsm1. 

assert(HBpCpAsNM : rk(Bp :: Cp :: As :: N ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBpCpAsNm : rk(Bp :: Cp :: As :: N ::  ::  nil) >= 1) by (solve_hyps_min HBpCpAsNeq HBpCpAsNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsMY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M :: Y ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BsCsMY requis par la preuve de (?)BsCsMY pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BsCsMY requis par la preuve de (?)BsCsMY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBsCsMYm3 : rk(Bs :: Cs :: M :: Y ::  :: nil) >= 3).
{
	try assert(HBsCsMeq : rk(Bs :: Cs :: M :: nil) = 3) by (apply LBsCsM with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMmtmp : rk(Bs :: Cs :: M :: nil) >= 3) by (solve_hyps_min HBsCsMeq HBsCsMm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: Y ::  :: nil) 3 3 HBsCsMmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBsCsMYM3 : rk(Bs :: Cs :: M :: Y ::  :: nil) <= 3).
{
	try assert(HBsCsMYeq : rk(Bs :: Cs :: M :: Y :: nil) = 3) by (apply LBsCsMY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMYMtmp : rk(Bs :: Cs :: M :: Y :: nil) <= 3) by (solve_hyps_max HBsCsMYeq HBsCsMYM3).
	try assert(HBsCsMeq : rk(Bs :: Cs :: M ::  :: nil) = 3) by (apply LBsCsM with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMMtmp : rk(Bs :: Cs :: M ::  :: nil) <= 3) by (solve_hyps_max HBsCsMeq HBsCsMM3).
	try assert(HBsCsMeq : rk(Bs :: Cs :: M :: nil) = 3) by (apply LBsCsM with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMmtmp : rk(Bs :: Cs :: M :: nil) >= 3) by (solve_hyps_min HBsCsMeq HBsCsMm3).
	assert(Hincl : incl (Bs :: Cs :: M :: nil) (list_inter (Bs :: Cs :: M :: Y :: nil) (Bs :: Cs :: M ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bs :: Cs :: M :: Y ::  :: nil) (Bs :: Cs :: M :: Y :: Bs :: Cs :: M ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bs :: Cs :: M :: Y :: Bs :: Cs :: M ::  :: nil) ((Bs :: Cs :: M :: Y :: nil) ++ (Bs :: Cs :: M ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bs :: Cs :: M :: Y :: nil) (Bs :: Cs :: M ::  :: nil) (Bs :: Cs :: M :: nil) 3 3 3 HBsCsMYMtmp HBsCsMMtmp HBsCsMmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBsCsMM1. try clear HBsCsMM2. try clear HBsCsMM3. try clear HBsCsMm4. try clear HBsCsMm3. try clear HBsCsMm2. try clear HBsCsMm1. 

assert(HBsCsMYM : rk(Bs :: Cs :: M :: Y ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBsCsMYm : rk(Bs :: Cs :: M :: Y ::  ::  nil) >= 1) by (solve_hyps_min HBsCsMYeq HBsCsMYm1).
intuition.
Qed.

(* dans constructLemma(), requis par LNY *)
(* dans la couche 0 *)
Lemma LBCApNY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: N :: Y ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCApNY requis par la preuve de (?)BCApNY pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCApNY requis par la preuve de (?)BCApNY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCApNYm3 : rk(B :: C :: Ap :: N :: Y ::  :: nil) >= 3).
{
	try assert(HBCApeq : rk(B :: C :: Ap :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApmtmp : rk(B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HBCApeq HBCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Ap :: nil) (B :: C :: Ap :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Ap :: nil) (B :: C :: Ap :: N :: Y ::  :: nil) 3 3 HBCApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCApNYM3 : rk(B :: C :: Ap :: N :: Y ::  :: nil) <= 3).
{
	try assert(HBCApYeq : rk(B :: C :: Ap :: Y :: nil) = 3) by (apply LBCApY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApYMtmp : rk(B :: C :: Ap :: Y :: nil) <= 3) by (solve_hyps_max HBCApYeq HBCApYM3).
	try assert(HBCApNeq : rk(B :: C :: Ap :: N ::  :: nil) = 3) by (apply LBCApN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApNMtmp : rk(B :: C :: Ap :: N ::  :: nil) <= 3) by (solve_hyps_max HBCApNeq HBCApNM3).
	try assert(HBCApeq : rk(B :: C :: Ap :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApmtmp : rk(B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HBCApeq HBCApm3).
	assert(Hincl : incl (B :: C :: Ap :: nil) (list_inter (B :: C :: Ap :: Y :: nil) (B :: C :: Ap :: N ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: N :: Y ::  :: nil) (B :: C :: Ap :: Y :: B :: C :: Ap :: N ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Ap :: Y :: B :: C :: Ap :: N ::  :: nil) ((B :: C :: Ap :: Y :: nil) ++ (B :: C :: Ap :: N ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: Ap :: Y :: nil) (B :: C :: Ap :: N ::  :: nil) (B :: C :: Ap :: nil) 3 3 3 HBCApYMtmp HBCApNMtmp HBCApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBCApYM1. try clear HBCApYM2. try clear HBCApYM3. try clear HBCApYm4. try clear HBCApYm3. try clear HBCApYm2. try clear HBCApYm1. 

assert(HBCApNYM : rk(B :: C :: Ap :: N :: Y ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApNYm : rk(B :: C :: Ap :: N :: Y ::  ::  nil) >= 1) by (solve_hyps_min HBCApNYeq HBCApNYm1).
intuition.
Qed.

(* dans constructLemma(), requis par LNY *)
(* dans la couche 0 *)
Lemma LBpCpAsNY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bp :: Cp :: As :: N :: Y ::  ::  nil) = 3.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BpCpAsNY requis par la preuve de (?)BpCpAsNY pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BpCpAsNY requis par la preuve de (?)BpCpAsNY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBpCpAsNYm3 : rk(Bp :: Cp :: As :: N :: Y ::  :: nil) >= 3).
{
	try assert(HBpCpAseq : rk(Bp :: Cp :: As :: nil) = 3) by (apply LBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsmtmp : rk(Bp :: Cp :: As :: nil) >= 3) by (solve_hyps_min HBpCpAseq HBpCpAsm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Bp :: Cp :: As :: nil) (Bp :: Cp :: As :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bp :: Cp :: As :: nil) (Bp :: Cp :: As :: N :: Y ::  :: nil) 3 3 HBpCpAsmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBpCpAsNYM3 : rk(Bp :: Cp :: As :: N :: Y ::  :: nil) <= 3).
{
	try assert(HBpCpAsYeq : rk(Bp :: Cp :: As :: Y :: nil) = 3) by (apply LBpCpAsY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsYMtmp : rk(Bp :: Cp :: As :: Y :: nil) <= 3) by (solve_hyps_max HBpCpAsYeq HBpCpAsYM3).
	try assert(HBpCpAsNeq : rk(Bp :: Cp :: As :: N ::  :: nil) = 3) by (apply LBpCpAsN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsNMtmp : rk(Bp :: Cp :: As :: N ::  :: nil) <= 3) by (solve_hyps_max HBpCpAsNeq HBpCpAsNM3).
	try assert(HBpCpAseq : rk(Bp :: Cp :: As :: nil) = 3) by (apply LBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsmtmp : rk(Bp :: Cp :: As :: nil) >= 3) by (solve_hyps_min HBpCpAseq HBpCpAsm3).
	assert(Hincl : incl (Bp :: Cp :: As :: nil) (list_inter (Bp :: Cp :: As :: Y :: nil) (Bp :: Cp :: As :: N ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bp :: Cp :: As :: N :: Y ::  :: nil) (Bp :: Cp :: As :: Y :: Bp :: Cp :: As :: N ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: As :: Y :: Bp :: Cp :: As :: N ::  :: nil) ((Bp :: Cp :: As :: Y :: nil) ++ (Bp :: Cp :: As :: N ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: As :: Y :: nil) (Bp :: Cp :: As :: N ::  :: nil) (Bp :: Cp :: As :: nil) 3 3 3 HBpCpAsYMtmp HBpCpAsNMtmp HBpCpAsmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpCpAsYM1. try clear HBpCpAsYM2. try clear HBpCpAsYM3. try clear HBpCpAsYm4. try clear HBpCpAsYm3. try clear HBpCpAsYm2. try clear HBpCpAsYm1. 

assert(HBpCpAsNYM : rk(Bp :: Cp :: As :: N :: Y ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBpCpAsNYm : rk(Bp :: Cp :: As :: N :: Y ::  ::  nil) >= 1) by (solve_hyps_min HBpCpAsNYeq HBpCpAsNYm1).
intuition.
Qed.

(* dans constructLemma(), requis par LNY *)
(* dans la couche 0 *)
Lemma LBCApBpCpAsNY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  ::  nil) = 4.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCApBpCpAsNY requis par la preuve de (?)BCApBpCpAsNY pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCApBpCpAsNY requis par la preuve de (?)BCApBpCpAsNY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCApBpCpAsNYm3 : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) >= 3).
{
	try assert(HBCApeq : rk(B :: C :: Ap :: nil) = 3) by (apply LBCAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApmtmp : rk(B :: C :: Ap :: nil) >= 3) by (solve_hyps_min HBCApeq HBCApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Ap :: nil) (B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Ap :: nil) (B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) 3 3 HBCApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCApBpCpAsNYm4 : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) >= 4).
{
	try assert(HBCApBpCpAseq : rk(B :: C :: Ap :: Bp :: Cp :: As :: nil) = 4) by (apply LBCApBpCpAs with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApBpCpAsmtmp : rk(B :: C :: Ap :: Bp :: Cp :: As :: nil) >= 4) by (solve_hyps_min HBCApBpCpAseq HBCApBpCpAsm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Ap :: Bp :: Cp :: As :: nil) (B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Ap :: Bp :: Cp :: As :: nil) (B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) 4 4 HBCApBpCpAsmtmp Hcomp Hincl);apply HT.
}
try clear HBCApBpCpAsM1. try clear HBCApBpCpAsM2. try clear HBCApBpCpAsM3. try clear HBCApBpCpAsm4. try clear HBCApBpCpAsm3. try clear HBCApBpCpAsm2. try clear HBCApBpCpAsm1. 

assert(HBCApBpCpAsNYM : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCApBpCpAsNYm : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  ::  nil) >= 1) by (solve_hyps_min HBCApBpCpAsNYeq HBCApBpCpAsNYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LNY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(N :: Y ::  ::  nil) = 2.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour NY requis par la preuve de (?)NY pour la règle 3  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour BsCsMNY requis par la preuve de (?)NY pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BsCsMNY requis par la preuve de (?)BsCsMNY pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BsCsMNY requis par la preuve de (?)BsCsMNY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBsCsMNYm3 : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 3).
{
	try assert(HBsCsMeq : rk(Bs :: Cs :: M :: nil) = 3) by (apply LBsCsM with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMmtmp : rk(Bs :: Cs :: M :: nil) >= 3) by (solve_hyps_min HBsCsMeq HBsCsMm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil) 3 3 HBsCsMmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBsCsMNYm4 : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 4).
{
	try assert(HBsCsMNeq : rk(Bs :: Cs :: M :: N :: nil) = 4) by (apply LBsCsMN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMNmtmp : rk(Bs :: Cs :: M :: N :: nil) >= 4) by (solve_hyps_min HBsCsMNeq HBsCsMNm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Bs :: Cs :: M :: N :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bs :: Cs :: M :: N :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil) 4 4 HBsCsMNmtmp Hcomp Hincl);apply HT.
}
try clear HBsCsMNM1. try clear HBsCsMNM2. try clear HBsCsMNM3. try clear HBsCsMNm4. try clear HBsCsMNm3. try clear HBsCsMNm2. try clear HBsCsMNm1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour NY requis par la preuve de (?)NY pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Bs :: Cs :: M :: N :: Y ::  ::  de rang :  4 et 4 	 AiB : Y ::  de rang :  1 et 1 	 A : Bs :: Cs :: M :: Y ::   de rang : 3 et 3 *)
assert(HNYm2 : rk(N :: Y ::  :: nil) >= 2).
{
	try assert(HBsCsMYeq : rk(Bs :: Cs :: M :: Y :: nil) = 3) by (apply LBsCsMY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMYMtmp : rk(Bs :: Cs :: M :: Y :: nil) <= 3) by (solve_hyps_max HBsCsMYeq HBsCsMYM3).
	assert(HBsCsMNYmtmp : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 4) by (solve_hyps_min HBsCsMNYeq HBsCsMNYm4).
	try assert(HYeq : rk(Y :: nil) = 1) by (apply LY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HYmtmp : rk(Y :: nil) >= 1) by (solve_hyps_min HYeq HYm1).
	assert(Hincl : incl (Y :: nil) (list_inter (Bs :: Cs :: M :: Y :: nil) (N :: Y ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bs :: Cs :: M :: N :: Y ::  :: nil) (Bs :: Cs :: M :: Y :: N :: Y ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bs :: Cs :: M :: Y :: N :: Y ::  :: nil) ((Bs :: Cs :: M :: Y :: nil) ++ (N :: Y ::  :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBsCsMNYmtmp;try rewrite HT2 in HBsCsMNYmtmp.
	assert(HT := rule_4 (Bs :: Cs :: M :: Y :: nil) (N :: Y ::  :: nil) (Y :: nil) 4 1 3 HBsCsMNYmtmp HYmtmp HBsCsMYMtmp Hincl); apply HT.
}
try clear HBsCsMYM1. try clear HBsCsMYM2. try clear HBsCsMYM3. try clear HBsCsMYm4. try clear HBsCsMYm3. try clear HBsCsMYm2. try clear HBsCsMYm1. try clear HYM1. try clear HYM2. try clear HYM3. try clear HYm4. try clear HYm3. try clear HYm2. try clear HYm1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HNYM2 : rk(N :: Y ::  :: nil) <= 2).
{
	try assert(HBCApNYeq : rk(B :: C :: Ap :: N :: Y ::  :: nil) = 3) by (apply LBCApNY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApNYMtmp : rk(B :: C :: Ap :: N :: Y ::  :: nil) <= 3) by (solve_hyps_max HBCApNYeq HBCApNYM3).
	try assert(HBpCpAsNYeq : rk(Bp :: Cp :: As :: N :: Y ::  :: nil) = 3) by (apply LBpCpAsNY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBpCpAsNYMtmp : rk(Bp :: Cp :: As :: N :: Y ::  :: nil) <= 3) by (solve_hyps_max HBpCpAsNYeq HBpCpAsNYM3).
	try assert(HBCApBpCpAsNYeq : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) = 4) by (apply LBCApBpCpAsNY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBCApBpCpAsNYmtmp : rk(B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) >= 4) by (solve_hyps_min HBCApBpCpAsNYeq HBCApBpCpAsNYm4).
	assert(Hincl : incl (N :: Y ::  :: nil) (list_inter (B :: C :: Ap :: N :: Y ::  :: nil) (Bp :: Cp :: As :: N :: Y ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Ap :: Bp :: Cp :: As :: N :: Y ::  :: nil) (B :: C :: Ap :: N :: Y ::  :: Bp :: Cp :: As :: N :: Y ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: Ap :: N :: Y ::  :: Bp :: Cp :: As :: N :: Y ::  :: nil) ((B :: C :: Ap :: N :: Y ::  :: nil) ++ (Bp :: Cp :: As :: N :: Y ::  :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCApBpCpAsNYmtmp;try rewrite HT2 in HBCApBpCpAsNYmtmp.
	assert(HT := rule_3 (B :: C :: Ap :: N :: Y ::  :: nil) (Bp :: Cp :: As :: N :: Y ::  :: nil) (N :: Y ::  :: nil) 3 3 4 HBCApNYMtmp HBpCpAsNYMtmp HBCApBpCpAsNYmtmp Hincl);apply HT.
}


assert(HNYM : rk(N :: Y ::  ::  nil) <= 3) by (solve_hyps_max HNYeq HNYM3).
assert(HNYm : rk(N :: Y ::  ::  nil) >= 1) by (solve_hyps_min HNYeq HNYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBsCsMNY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Bs :: Cs :: M :: N :: Y ::  ::  nil) = 4.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BsCsMNY requis par la preuve de (?)BsCsMNY pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BsCsMNY requis par la preuve de (?)BsCsMNY pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBsCsMNYm3 : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 3).
{
	try assert(HBsCsMeq : rk(Bs :: Cs :: M :: nil) = 3) by (apply LBsCsM with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMmtmp : rk(Bs :: Cs :: M :: nil) >= 3) by (solve_hyps_min HBsCsMeq HBsCsMm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bs :: Cs :: M :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil) 3 3 HBsCsMmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBsCsMNYm4 : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 4).
{
	try assert(HBsCsMNeq : rk(Bs :: Cs :: M :: N :: nil) = 4) by (apply LBsCsMN with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMNmtmp : rk(Bs :: Cs :: M :: N :: nil) >= 4) by (solve_hyps_min HBsCsMNeq HBsCsMNm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Bs :: Cs :: M :: N :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bs :: Cs :: M :: N :: nil) (Bs :: Cs :: M :: N :: Y ::  :: nil) 4 4 HBsCsMNmtmp Hcomp Hincl);apply HT.
}
try clear HBsCsMNM1. try clear HBsCsMNM2. try clear HBsCsMNM3. try clear HBsCsMNm4. try clear HBsCsMNm3. try clear HBsCsMNm2. try clear HBsCsMNm1. 

assert(HBsCsMNYM : rk(Bs :: Cs :: M :: N :: Y ::  ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBsCsMNYm : rk(Bs :: Cs :: M :: N :: Y ::  ::  nil) >= 1) by (solve_hyps_min HBsCsMNYeq HBsCsMNYm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LY : forall B C Ap Bp Cp As Bs Cs M N X Y  ,
rk(B :: C :: Ap ::  nil) = 3 -> rk(Bp :: Cp :: As ::  nil) = 3 -> rk(B :: C :: Ap :: Bp :: Cp :: As ::  nil) = 4 ->
rk(Bs :: Cs :: M ::  nil) = 3 -> rk(B :: C :: Ap :: Bs :: Cs :: M ::  nil) = 4 -> rk(Bp :: Cp :: As :: Bs :: Cs :: M ::  nil) = 4 ->
rk(B :: C :: Ap :: N ::  nil) = 3 -> rk(Bp :: Cp :: As :: N ::  nil) = 3 -> rk(Bs :: Cs :: M :: N ::  nil) = 4 ->
rk(B :: C :: Ap :: X ::  nil) = 3 -> rk(Bp :: Cp :: As :: X ::  nil) = 3 -> rk(Bs :: Cs :: M :: X ::  nil) = 4 ->
rk(B :: C :: Ap :: Y ::  nil) = 3 -> rk(Bp :: Cp :: As :: Y ::  nil) = 3 -> rk(Bs :: Cs :: M :: Y ::  nil) = 3 ->
rk(B :: C :: Ap ::  ::  nil) = 3 -> rk(Bp :: Cp :: As ::  ::  nil) = 3 -> rk(Bs :: Cs :: M ::  ::  nil) = 3 ->
rk(Y ::  ::  nil) = 1.
Proof.

intros B C Ap Bp Cp As Bs Cs M N X Y  
HBCApeq HBpCpAseq HBCApBpCpAseq HBsCsMeq HBCApBsCsMeq HBpCpAsBsCsMeq HBCApNeq HBpCpAsNeq HBsCsMNeq HBCApXeq
HBpCpAsXeq HBsCsMXeq HBCApYeq HBpCpAsYeq HBsCsMYeq HBCApeq HBpCpAseq HBsCsMeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Y requis par la preuve de (?)Y pour la règle 3  *)
(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HYM1 : rk(Y ::  :: nil) <= 1).
{
	try assert(HBsCsMYeq : rk(Bs :: Cs :: M :: Y ::  :: nil) = 3) by (apply LBsCsMY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMYMtmp : rk(Bs :: Cs :: M :: Y ::  :: nil) <= 3) by (solve_hyps_max HBsCsMYeq HBsCsMYM3).
	try assert(HNYeq : rk(N :: Y ::  :: nil) = 2) by (apply LNY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HNYMtmp : rk(N :: Y ::  :: nil) <= 2) by (solve_hyps_max HNYeq HNYM2).
	try assert(HBsCsMNYeq : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) = 4) by (apply LBsCsMNY with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HBsCsMNYmtmp : rk(Bs :: Cs :: M :: N :: Y ::  :: nil) >= 4) by (solve_hyps_min HBsCsMNYeq HBsCsMNYm4).
	assert(Hincl : incl (Y ::  :: nil) (list_inter (Bs :: Cs :: M :: Y ::  :: nil) (N :: Y ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bs :: Cs :: M :: N :: Y ::  :: nil) (Bs :: Cs :: M :: Y ::  :: N :: Y ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bs :: Cs :: M :: Y ::  :: N :: Y ::  :: nil) ((Bs :: Cs :: M :: Y ::  :: nil) ++ (N :: Y ::  :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBsCsMNYmtmp;try rewrite HT2 in HBsCsMNYmtmp.
	assert(HT := rule_3 (Bs :: Cs :: M :: Y ::  :: nil) (N :: Y ::  :: nil) (Y ::  :: nil) 3 2 4 HBsCsMYMtmp HNYMtmp HBsCsMNYmtmp Hincl);apply HT.
}


assert(HYM : rk(Y ::  ::  nil) <= 2) by (solve_hyps_max HYeq HYM2).
assert(HYm : rk(Y ::  ::  nil) >= 1) by (solve_hyps_min HYeq HYm1).
intuition.
Qed.

