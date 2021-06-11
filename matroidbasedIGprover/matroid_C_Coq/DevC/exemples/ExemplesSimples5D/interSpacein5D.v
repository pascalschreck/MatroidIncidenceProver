Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LABCDE : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEM : rk(A :: B :: C :: D :: E ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HABCDEeq HABCDEM5).
assert(HABCDEm : rk(A :: B :: C :: D :: E ::  nil) >= 1) by (solve_hyps_min HABCDEeq HABCDEm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEp : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpM : rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HApBpCpDpEpeq HApBpCpDpEpM5).
assert(HApBpCpDpEpm : rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEApBpCpDpEp : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEApBpCpDpEpM : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEApBpCpDpEpm : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) >= 1) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEI : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEIM : rk(A :: B :: C :: D :: E :: I ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIm : rk(A :: B :: C :: D :: E :: I ::  nil) >= 1) by (solve_hyps_min HABCDEIeq HABCDEIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpI : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpIM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIeq HApBpCpDpEpIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEJ : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: J ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEJM : rk(A :: B :: C :: D :: E :: J ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEJm : rk(A :: B :: C :: D :: E :: J ::  nil) >= 1) by (solve_hyps_min HABCDEJeq HABCDEJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpJ : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpJM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpJm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpJeq HApBpCpDpEpJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEK : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: K ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEKM : rk(A :: B :: C :: D :: E :: K ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEKm : rk(A :: B :: C :: D :: E :: K ::  nil) >= 1) by (solve_hyps_min HABCDEKeq HABCDEKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpK : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpKM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpKm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpKeq HApBpCpDpEpKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDELM : rk(A :: B :: C :: D :: E :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDELm : rk(A :: B :: C :: D :: E :: L ::  nil) >= 1) by (solve_hyps_min HABCDELeq HABCDELm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpLM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpLm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpLeq HApBpCpDpEpLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LIJKL : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(I :: J :: K :: L ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HIJKLM : rk(I :: J :: K :: L ::  nil) <= 4) (* dim : 5 *) by (solve_hyps_max HIJKLeq HIJKLM4).
assert(HIJKLm : rk(I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HIJKLeq HIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HABCDEMM : rk(A :: B :: C :: D :: E :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEMm : rk(A :: B :: C :: D :: E :: M ::  nil) >= 1) by (solve_hyps_min HABCDEMeq HABCDEMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

assert(HApBpCpDpEpMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpMeq HApBpCpDpEpMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: I :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIM requis par la preuve de (?)ABCDEIM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIM requis par la preuve de (?)ABCDEIM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEIMm5 : rk(A :: B :: C :: D :: E :: I :: M :: nil) >= 5).
{
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDEIMM5 : rk(A :: B :: C :: D :: E :: I :: M :: nil) <= 5).
{
	try assert(HABCDEIeq : rk(A :: B :: C :: D :: E :: I :: nil) = 5) by (apply LABCDEI with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEIMtmp : rk(A :: B :: C :: D :: E :: I :: nil) <= 5) by (solve_hyps_max HABCDEIeq HABCDEIM5).
	try assert(HABCDEMeq : rk(A :: B :: C :: D :: E :: M :: nil) = 5) by (apply LABCDEM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEMMtmp : rk(A :: B :: C :: D :: E :: M :: nil) <= 5) by (solve_hyps_max HABCDEMeq HABCDEMM5).
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: I :: nil) (A :: B :: C :: D :: E :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: M :: nil) (A :: B :: C :: D :: E :: I :: A :: B :: C :: D :: E :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: I :: A :: B :: C :: D :: E :: M :: nil) ((A :: B :: C :: D :: E :: I :: nil) ++ (A :: B :: C :: D :: E :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: I :: nil) (A :: B :: C :: D :: E :: M :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEIMtmp HABCDEMMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDEIM1. try clear HABCDEIM2. try clear HABCDEIM3. try clear HABCDEIM4. try clear HABCDEIM5. try clear HABCDEIM6. try clear HABCDEIM7. try clear HABCDEIm7. try clear HABCDEIm6. try clear HABCDEIm5. try clear HABCDEIm4. try clear HABCDEIm3. try clear HABCDEIm2. try clear HABCDEIm1. try clear HABCDEMM1. try clear HABCDEMM2. try clear HABCDEMM3. try clear HABCDEMM4. try clear HABCDEMM5. try clear HABCDEMM6. try clear HABCDEMM7. try clear HABCDEMm7. try clear HABCDEMm6. try clear HABCDEMm5. try clear HABCDEMm4. try clear HABCDEMm3. try clear HABCDEMm2. try clear HABCDEMm1. 

assert(HABCDEIMM : rk(A :: B :: C :: D :: E :: I :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIMm : rk(A :: B :: C :: D :: E :: I :: M ::  nil) >= 1) by (solve_hyps_min HABCDEIMeq HABCDEIMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIM requis par la preuve de (?)ApBpCpDpEpIM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIM requis par la preuve de (?)ApBpCpDpEpIM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpEpIMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) >= 5).
{
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpEpIMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) <= 5).
{
	try assert(HApBpCpDpEpIeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) = 5) by (apply LApBpCpDpEpI with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpIMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIeq HApBpCpDpEpIM5).
	try assert(HApBpCpDpEpMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) = 5) by (apply LApBpCpDpEpM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpMeq HApBpCpDpEpMM5).
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: I :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpIMtmp HApBpCpDpEpMMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpEpIM1. try clear HApBpCpDpEpIM2. try clear HApBpCpDpEpIM3. try clear HApBpCpDpEpIM4. try clear HApBpCpDpEpIM5. try clear HApBpCpDpEpIM6. try clear HApBpCpDpEpIM7. try clear HApBpCpDpEpIm7. try clear HApBpCpDpEpIm6. try clear HApBpCpDpEpIm5. try clear HApBpCpDpEpIm4. try clear HApBpCpDpEpIm3. try clear HApBpCpDpEpIm2. try clear HApBpCpDpEpIm1. try clear HApBpCpDpEpMM1. try clear HApBpCpDpEpMM2. try clear HApBpCpDpEpMM3. try clear HApBpCpDpEpMM4. try clear HApBpCpDpEpMM5. try clear HApBpCpDpEpMM6. try clear HApBpCpDpEpMM7. try clear HApBpCpDpEpMm7. try clear HApBpCpDpEpMm6. try clear HApBpCpDpEpMm5. try clear HApBpCpDpEpMm4. try clear HApBpCpDpEpMm3. try clear HApBpCpDpEpMm2. try clear HApBpCpDpEpMm1. 

assert(HApBpCpDpEpIMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIMeq HApBpCpDpEpIMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: I :: J :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJM requis par la preuve de (?)ABCDEIJM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJM requis par la preuve de (?)ABCDEIJM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEIJMm5 : rk(A :: B :: C :: D :: E :: I :: J :: M :: nil) >= 5).
{
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDEIJMM5 : rk(A :: B :: C :: D :: E :: I :: J :: M :: nil) <= 5).
{
	try assert(HABCDEJeq : rk(A :: B :: C :: D :: E :: J :: nil) = 5) by (apply LABCDEJ with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEJMtmp : rk(A :: B :: C :: D :: E :: J :: nil) <= 5) by (solve_hyps_max HABCDEJeq HABCDEJM5).
	try assert(HABCDEIMeq : rk(A :: B :: C :: D :: E :: I :: M :: nil) = 5) by (apply LABCDEIM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEIMMtmp : rk(A :: B :: C :: D :: E :: I :: M :: nil) <= 5) by (solve_hyps_max HABCDEIMeq HABCDEIMM5).
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: J :: nil) (A :: B :: C :: D :: E :: I :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: M :: nil) (A :: B :: C :: D :: E :: J :: A :: B :: C :: D :: E :: I :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: J :: A :: B :: C :: D :: E :: I :: M :: nil) ((A :: B :: C :: D :: E :: J :: nil) ++ (A :: B :: C :: D :: E :: I :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: J :: nil) (A :: B :: C :: D :: E :: I :: M :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEJMtmp HABCDEIMMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDEJM1. try clear HABCDEJM2. try clear HABCDEJM3. try clear HABCDEJM4. try clear HABCDEJM5. try clear HABCDEJM6. try clear HABCDEJM7. try clear HABCDEJm7. try clear HABCDEJm6. try clear HABCDEJm5. try clear HABCDEJm4. try clear HABCDEJm3. try clear HABCDEJm2. try clear HABCDEJm1. 

assert(HABCDEIJMM : rk(A :: B :: C :: D :: E :: I :: J :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJMm : rk(A :: B :: C :: D :: E :: I :: J :: M ::  nil) >= 1) by (solve_hyps_min HABCDEIJMeq HABCDEIJMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIJM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJM requis par la preuve de (?)ApBpCpDpEpIJM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJM requis par la preuve de (?)ApBpCpDpEpIJM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpEpIJMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) >= 5).
{
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpEpIJMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) <= 5).
{
	try assert(HApBpCpDpEpJeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) = 5) by (apply LApBpCpDpEpJ with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpJMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpJeq HApBpCpDpEpJM5).
	try assert(HApBpCpDpEpIMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) = 5) by (apply LApBpCpDpEpIM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpIMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIMeq HApBpCpDpEpIMM5).
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: J :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: J :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: J :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpJMtmp HApBpCpDpEpIMMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpEpJM1. try clear HApBpCpDpEpJM2. try clear HApBpCpDpEpJM3. try clear HApBpCpDpEpJM4. try clear HApBpCpDpEpJM5. try clear HApBpCpDpEpJM6. try clear HApBpCpDpEpJM7. try clear HApBpCpDpEpJm7. try clear HApBpCpDpEpJm6. try clear HApBpCpDpEpJm5. try clear HApBpCpDpEpJm4. try clear HApBpCpDpEpJm3. try clear HApBpCpDpEpJm2. try clear HApBpCpDpEpJm1. 

assert(HApBpCpDpEpIJMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJMeq HApBpCpDpEpIJMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJKM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: I :: J :: K :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJKM requis par la preuve de (?)ABCDEIJKM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJKM requis par la preuve de (?)ABCDEIJKM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEIJKMm5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) >= 5).
{
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDEIJKMM5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) <= 5).
{
	try assert(HABCDEKeq : rk(A :: B :: C :: D :: E :: K :: nil) = 5) by (apply LABCDEK with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEKMtmp : rk(A :: B :: C :: D :: E :: K :: nil) <= 5) by (solve_hyps_max HABCDEKeq HABCDEKM5).
	try assert(HABCDEIJMeq : rk(A :: B :: C :: D :: E :: I :: J :: M :: nil) = 5) by (apply LABCDEIJM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEIJMMtmp : rk(A :: B :: C :: D :: E :: I :: J :: M :: nil) <= 5) by (solve_hyps_max HABCDEIJMeq HABCDEIJMM5).
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: K :: nil) (A :: B :: C :: D :: E :: I :: J :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) (A :: B :: C :: D :: E :: K :: A :: B :: C :: D :: E :: I :: J :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: K :: A :: B :: C :: D :: E :: I :: J :: M :: nil) ((A :: B :: C :: D :: E :: K :: nil) ++ (A :: B :: C :: D :: E :: I :: J :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: K :: nil) (A :: B :: C :: D :: E :: I :: J :: M :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDEKMtmp HABCDEIJMMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDEKM1. try clear HABCDEKM2. try clear HABCDEKM3. try clear HABCDEKM4. try clear HABCDEKM5. try clear HABCDEKM6. try clear HABCDEKM7. try clear HABCDEKm7. try clear HABCDEKm6. try clear HABCDEKm5. try clear HABCDEKm4. try clear HABCDEKm3. try clear HABCDEKm2. try clear HABCDEKm1. 

assert(HABCDEIJKMM : rk(A :: B :: C :: D :: E :: I :: J :: K :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJKMm : rk(A :: B :: C :: D :: E :: I :: J :: K :: M ::  nil) >= 1) by (solve_hyps_min HABCDEIJKMeq HABCDEIJKMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIJKM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJKM requis par la preuve de (?)ApBpCpDpEpIJKM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJKM requis par la preuve de (?)ApBpCpDpEpIJKM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpEpIJKMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) >= 5).
{
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpEpIJKMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) <= 5).
{
	try assert(HApBpCpDpEpKeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) = 5) by (apply LApBpCpDpEpK with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpKMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpKeq HApBpCpDpEpKM5).
	try assert(HApBpCpDpEpIJMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) = 5) by (apply LApBpCpDpEpIJM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpIJMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJMeq HApBpCpDpEpIJMM5).
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: K :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: K :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: K :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpKMtmp HApBpCpDpEpIJMMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpEpKM1. try clear HApBpCpDpEpKM2. try clear HApBpCpDpEpKM3. try clear HApBpCpDpEpKM4. try clear HApBpCpDpEpKM5. try clear HApBpCpDpEpKM6. try clear HApBpCpDpEpKM7. try clear HApBpCpDpEpKm7. try clear HApBpCpDpEpKm6. try clear HApBpCpDpEpKm5. try clear HApBpCpDpEpKm4. try clear HApBpCpDpEpKm3. try clear HApBpCpDpEpKm2. try clear HApBpCpDpEpKm1. 

assert(HApBpCpDpEpIJKMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJKMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJKMeq HApBpCpDpEpIJKMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEIJKLM requis par la preuve de (?)ABCDEIJKLM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEIJKLM requis par la preuve de (?)ABCDEIJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEIJKLMm5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) >= 5).
{
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDEIJKLMM5 : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) <= 5).
{
	try assert(HABCDELeq : rk(A :: B :: C :: D :: E :: L :: nil) = 5) by (apply LABCDEL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDELMtmp : rk(A :: B :: C :: D :: E :: L :: nil) <= 5) by (solve_hyps_max HABCDELeq HABCDELM5).
	try assert(HABCDEIJKMeq : rk(A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) = 5) by (apply LABCDEIJKM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEIJKMMtmp : rk(A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) <= 5) by (solve_hyps_max HABCDEIJKMeq HABCDEIJKMM5).
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (list_inter (A :: B :: C :: D :: E :: L :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) (A :: B :: C :: D :: E :: L :: A :: B :: C :: D :: E :: I :: J :: K :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: L :: A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) ((A :: B :: C :: D :: E :: L :: nil) ++ (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: E :: L :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: M :: nil) (A :: B :: C :: D :: E :: nil) 5 5 5 HABCDELMtmp HABCDEIJKMMtmp HABCDEmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDELM1. try clear HABCDELM2. try clear HABCDELM3. try clear HABCDELM4. try clear HABCDELM5. try clear HABCDELM6. try clear HABCDELM7. try clear HABCDELm7. try clear HABCDELm6. try clear HABCDELm5. try clear HABCDELm4. try clear HABCDELm3. try clear HABCDELm2. try clear HABCDELm1. 

assert(HABCDEIJKLMM : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEIJKLMm : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HABCDEIJKLMeq HABCDEIJKLMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpEpIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) = 5.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ApBpCpDpEpIJKLM requis par la preuve de (?)ApBpCpDpEpIJKLM pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ApBpCpDpEpIJKLM requis par la preuve de (?)ApBpCpDpEpIJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpEpIJKLMm5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) >= 5).
{
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) 5 5 HApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpEpIJKLMM5 : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) <= 5).
{
	try assert(HApBpCpDpEpLeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) = 5) by (apply LApBpCpDpEpL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpLMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpLeq HApBpCpDpEpLM5).
	try assert(HApBpCpDpEpIJKMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) = 5) by (apply LApBpCpDpEpIJKM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpIJKMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJKMeq HApBpCpDpEpIJKMM5).
	try assert(HApBpCpDpEpeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 5) by (apply LApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpmtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 5) by (solve_hyps_min HApBpCpDpEpeq HApBpCpDpEpm5).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: Ep :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: L :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: Ep :: L :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) ((Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: Ep :: L :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: nil) 5 5 5 HApBpCpDpEpLMtmp HApBpCpDpEpIJKMMtmp HApBpCpDpEpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpEpLM1. try clear HApBpCpDpEpLM2. try clear HApBpCpDpEpLM3. try clear HApBpCpDpEpLM4. try clear HApBpCpDpEpLM5. try clear HApBpCpDpEpLM6. try clear HApBpCpDpEpLM7. try clear HApBpCpDpEpLm7. try clear HApBpCpDpEpLm6. try clear HApBpCpDpEpLm5. try clear HApBpCpDpEpLm4. try clear HApBpCpDpEpLm3. try clear HApBpCpDpEpLm2. try clear HApBpCpDpEpLm1. 

assert(HApBpCpDpEpIJKLMM : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HApBpCpDpEpIJKLMm : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpDpEpIJKLMeq HApBpCpDpEpIJKLMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDEApBpCpDpEpIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) = 6.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 5 <= rg <= 6 pour ABCDEApBpCpDpEpIJKLM requis par la preuve de (?)ABCDEApBpCpDpEpIJKLM pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 6 pour ABCDEApBpCpDpEpIJKLM requis par la preuve de (?)ABCDEApBpCpDpEpIJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEApBpCpDpEpIJKLMm5 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) >= 5).
{
	try assert(HABCDEeq : rk(A :: B :: C :: D :: E :: nil) = 5) by (apply LABCDE with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEmtmp : rk(A :: B :: C :: D :: E :: nil) >= 5) by (solve_hyps_min HABCDEeq HABCDEm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) 5 5 HABCDEmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDEApBpCpDpEpIJKLMm6 : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) >= 6).
{
	try assert(HABCDEApBpCpDpEpeq : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) = 6) by (apply LABCDEApBpCpDpEp with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEApBpCpDpEpmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpeq HABCDEApBpCpDpEpm6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: nil) (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) 6 6 HABCDEApBpCpDpEpmtmp Hcomp Hincl);apply HT.
}
try clear HABCDEApBpCpDpEpM1. try clear HABCDEApBpCpDpEpM2. try clear HABCDEApBpCpDpEpM3. try clear HABCDEApBpCpDpEpM4. try clear HABCDEApBpCpDpEpM5. try clear HABCDEApBpCpDpEpM6. try clear HABCDEApBpCpDpEpM7. try clear HABCDEApBpCpDpEpm7. try clear HABCDEApBpCpDpEpm6. try clear HABCDEApBpCpDpEpm5. try clear HABCDEApBpCpDpEpm4. try clear HABCDEApBpCpDpEpm3. try clear HABCDEApBpCpDpEpm2. try clear HABCDEApBpCpDpEpm1. 

assert(HABCDEApBpCpDpEpIJKLMM : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) <= 6) by (apply rk_upper_dim).
assert(HABCDEApBpCpDpEpIJKLMm : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HABCDEApBpCpDpEpIJKLMeq HABCDEApBpCpDpEpIJKLMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LIJKLM : forall A B C D E Ap Bp Cp Dp Ep I J K L M ,
rk(A :: B :: C :: D :: E ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep ::  nil) = 6 ->
rk(A :: B :: C :: D :: E :: I ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: I ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: J ::  nil) = 5 ->
rk(Ap :: Bp :: Cp :: Dp :: Ep :: J ::  nil) = 5 -> rk(A :: B :: C :: D :: E :: K ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: K ::  nil) = 5 ->
rk(A :: B :: C :: D :: E :: L ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: L ::  nil) = 5 -> rk(I :: J :: K :: L ::  nil) = 4 ->
rk(A :: B :: C :: D :: E :: M ::  nil) = 5 -> rk(Ap :: Bp :: Cp :: Dp :: Ep :: M ::  nil) = 5 -> rk(I :: J :: K :: M ::  nil) = 4 ->
rk(I :: J :: L :: M ::  nil) = 4 -> rk(I :: K :: L :: M ::  nil) = 4 -> rk(J :: K :: L :: M ::  nil) = 4 ->
rk(I :: J :: K :: L :: M ::  nil) = 4.
Proof.

intros A B C D E Ap Bp Cp Dp Ep I J K L M 
HABCDEeq HApBpCpDpEpeq HABCDEApBpCpDpEpeq HABCDEIeq HApBpCpDpEpIeq HABCDEJeq HApBpCpDpEpJeq HABCDEKeq HApBpCpDpEpKeq HABCDELeq
HApBpCpDpEpLeq HIJKLeq HABCDEMeq HApBpCpDpEpMeq HIJKMeq HIJLMeq HIKLMeq HJKLMeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour IJKLM requis par la preuve de (?)IJKLM pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour IJKLM requis par la preuve de (?)IJKLM pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HIJKLMm4 : rk(I :: J :: K :: L :: M :: nil) >= 4).
{
	try assert(HIJKLeq : rk(I :: J :: K :: L :: nil) = 4) by (apply LIJKL with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HIJKLmtmp : rk(I :: J :: K :: L :: nil) >= 4) by (solve_hyps_min HIJKLeq HIJKLm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (I :: J :: K :: L :: nil) (I :: J :: K :: L :: M :: nil) 4 4 HIJKLmtmp Hcomp Hincl);apply HT.
}
try clear HIJKLM1. try clear HIJKLM2. try clear HIJKLM3. try clear HIJKLM4. try clear HIJKLM5. try clear HIJKLM6. try clear HIJKLM7. try clear HIJKLm7. try clear HIJKLm6. try clear HIJKLm5. try clear HIJKLm4. try clear HIJKLm3. try clear HIJKLm2. try clear HIJKLm1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HIJKLMM4 : rk(I :: J :: K :: L :: M :: nil) <= 4).
{
	try assert(HABCDEIJKLMeq : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) = 5) by (apply LABCDEIJKLM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEIJKLMMtmp : rk(A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) <= 5) by (solve_hyps_max HABCDEIJKLMeq HABCDEIJKLMM5).
	try assert(HApBpCpDpEpIJKLMeq : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) = 5) by (apply LApBpCpDpEpIJKLM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HApBpCpDpEpIJKLMMtmp : rk(Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) <= 5) by (solve_hyps_max HApBpCpDpEpIJKLMeq HApBpCpDpEpIJKLMM5).
	try assert(HABCDEApBpCpDpEpIJKLMeq : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) = 6) by (apply LABCDEApBpCpDpEpIJKLM with (A := A) (B := B) (C := C) (D := D) (E := E) (Ap := Ap) (Bp := Bp) (Cp := Cp) (Dp := Dp) (Ep := Ep) (I := I) (J := J) (K := K) (L := L) (M := M) ;try assumption).
	assert(HABCDEApBpCpDpEpIJKLMmtmp : rk(A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) >= 6) by (solve_hyps_min HABCDEApBpCpDpEpIJKLMeq HABCDEApBpCpDpEpIJKLMm6).
	assert(Hincl : incl (I :: J :: K :: L :: M :: nil) (list_inter (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: E :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) ((A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) ++ (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDEApBpCpDpEpIJKLMmtmp;try rewrite HT2 in HABCDEApBpCpDpEpIJKLMmtmp.
	assert(HT := rule_3 (A :: B :: C :: D :: E :: I :: J :: K :: L :: M :: nil) (Ap :: Bp :: Cp :: Dp :: Ep :: I :: J :: K :: L :: M :: nil) (I :: J :: K :: L :: M :: nil) 5 5 6 HABCDEIJKLMMtmp HApBpCpDpEpIJKLMMtmp HABCDEApBpCpDpEpIJKLMmtmp Hincl);apply HT.
}


assert(HIJKLMM : rk(I :: J :: K :: L :: M ::  nil) <= 5) (* dim : 5 *) by (solve_hyps_max HIJKLMeq HIJKLMM5).
assert(HIJKLMm : rk(I :: J :: K :: L :: M ::  nil) >= 1) by (solve_hyps_min HIJKLMeq HIJKLMm1).
intuition.
Qed.

