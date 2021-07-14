Load "preamble2D.v".


(* dans la couche 0 *)
Lemma LMNP : forall A B C M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(A :: B :: M ::  nil) = 2 -> rk(A :: C :: N ::  nil) = 2 ->
rk(B :: C :: P ::  nil) = 2 -> rk(M :: N :: P ::  nil) >= 1/\rk(M :: N :: P ::  nil) <= 3.
Proof.

intros A B C M N P 
HABCeq HABMeq HACNeq HBCPeq .

assert(HMNPM : rk(M :: N :: P ::  nil) <= 3) by (solve_hyps_max HMNPeq HMNPM3).
assert(HMNPm : rk(M :: N :: P ::  nil) >= 1) by (solve_hyps_min HMNPeq HMNPm1).
split. intuition. intuition. 
Qed.

