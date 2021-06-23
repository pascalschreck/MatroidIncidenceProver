Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LP : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPM : rk(P ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HPeq HPM1).
assert(HPm : rk(P ::  nil) >= 1) by (solve_hyps_min HPeq HPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQ : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQM : rk(Q ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HQeq HQM1).
assert(HQm : rk(Q ::  nil) >= 1) by (solve_hyps_min HQeq HQm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LR : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(R ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HRM : rk(R ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HReq HRM1).
assert(HRm : rk(R ::  nil) >= 1) by (solve_hyps_min HReq HRm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQR : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPQRM : rk(P :: Q :: R ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPQReq HPQRM3).
assert(HPQRm : rk(P :: Q :: R ::  nil) >= 1) by (solve_hyps_min HPQReq HPQRm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPpM : rk(Pp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HPpeq HPpM1).
assert(HPpm : rk(Pp ::  nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPPpM : rk(P :: Pp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPPpeq HPPpM2).
assert(HPPpm : rk(P :: Pp ::  nil) >= 1) by (solve_hyps_min HPPpeq HPPpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Qp ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQpM : rk(Qp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HQpeq HQpM1).
assert(HQpm : rk(Qp ::  nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQQpM : rk(Q :: Qp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQQpeq HQQpM2).
assert(HQQpm : rk(Q :: Qp ::  nil) >= 1) by (solve_hyps_min HQQpeq HQQpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LRp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Rp ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HRpM : rk(Rp ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HRpeq HRpM1).
assert(HRpm : rk(Rp ::  nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LRRp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(R :: Rp ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HRRpM : rk(R :: Rp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HRRpeq HRRpM2).
assert(HRRpm : rk(R :: Rp ::  nil) >= 1) by (solve_hyps_min HRRpeq HRRpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpRp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPpQpRpM : rk(Pp :: Qp :: Rp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpRpeq HPpQpRpM3).
assert(HPpQpRpm : rk(Pp :: Qp :: Rp ::  nil) >= 1) by (solve_hyps_min HPpQpRpeq HPpQpRpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRPpQpRp : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPQRPpQpRpM : rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpRpm : rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) >= 1) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Oo ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HOoM : rk(Oo ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max HOoeq HOoM1).
assert(HOom : rk(Oo ::  nil) >= 1) by (solve_hyps_min HOoeq HOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPOo *)
(* dans la couche 0 *)
Lemma LPQROo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPQROoM : rk(P :: Q :: R :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQROom : rk(P :: Q :: R :: Oo ::  nil) >= 1) by (solve_hyps_min HPQROoeq HPQROom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour POo requis par la preuve de (?)POo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HPOom2 : rk(P :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Q :: R :: nil) (P :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: P :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: P :: Oo :: nil) ((P :: Q :: R :: nil) ++ (P :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (P :: Oo :: nil) (P :: nil) 4 1 3 HPQROomtmp HPmtmp HPQRMtmp Hincl); apply HT.
}


assert(HPOoM : rk(P :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPOoeq HPOoM2).
assert(HPOom : rk(P :: Oo ::  nil) >= 1) by (solve_hyps_min HPOoeq HPOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QOo requis par la preuve de (?)QOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : Q ::  de rang :  1 et 1 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HQOom2 : rk(Q :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HQeq : rk(Q :: nil) = 1) by (apply LQ with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQmtmp : rk(Q :: nil) >= 1) by (solve_hyps_min HQeq HQm1).
	assert(Hincl : incl (Q :: nil) (list_inter (P :: Q :: R :: nil) (Q :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Q :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Q :: Oo :: nil) ((P :: Q :: R :: nil) ++ (Q :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (Q :: Oo :: nil) (Q :: nil) 4 1 3 HPQROomtmp HQmtmp HPQRMtmp Hincl); apply HT.
}


assert(HQOoM : rk(Q :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQOoeq HQOoM2).
assert(HQOom : rk(Q :: Oo ::  nil) >= 1) by (solve_hyps_min HQOoeq HQOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQOo *)
(* dans la couche 0 *)
Lemma LROo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(R :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ROo requis par la preuve de (?)ROo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : R ::  de rang :  1 et 1 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HROom2 : rk(R :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HReq : rk(R :: nil) = 1) by (apply LR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRmtmp : rk(R :: nil) >= 1) by (solve_hyps_min HReq HRm1).
	assert(Hincl : incl (R :: nil) (list_inter (P :: Q :: R :: nil) (R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: R :: Oo :: nil) ((P :: Q :: R :: nil) ++ (R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (R :: Oo :: nil) (R :: nil) 4 1 3 HPQROomtmp HRmtmp HPQRMtmp Hincl); apply HT.
}


assert(HROoM : rk(R :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HROoeq HROoM2).
assert(HROom : rk(R :: Oo ::  nil) >= 1) by (solve_hyps_min HROoeq HROom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQOo requis par la preuve de (?)PQOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PQ requis par la preuve de (?)PQOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQOo requis par la preuve de (?)PQOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : P :: Q ::  de rang :  1 et 2 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HPQOom2 : rk(P :: Q :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(HPQmtmp : rk(P :: Q :: nil) >= 1) by (solve_hyps_min HPQeq HPQm1).
	assert(Hincl : incl (P :: Q :: nil) (list_inter (P :: Q :: R :: nil) (P :: Q :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: P :: Q :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: P :: Q :: Oo :: nil) ((P :: Q :: R :: nil) ++ (P :: Q :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (P :: Q :: Oo :: nil) (P :: Q :: nil) 4 1 3 HPQROomtmp HPQmtmp HPQRMtmp Hincl); apply HT.
}
try clear HPQM1. try clear HPQM2. try clear HPQM3. try clear HPQm4. try clear HPQm3. try clear HPQm2. try clear HPQm1. 

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPQOom3 : rk(P :: Q :: Oo :: nil) >= 3).
{
	try assert(HROoeq : rk(R :: Oo :: nil) = 2) by (apply LROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HROoMtmp : rk(R :: Oo :: nil) <= 2) by (solve_hyps_max HROoeq HROoM2).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HOoeq : rk(Oo :: nil) = 1) by (apply LOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (P :: Q :: Oo :: nil) (R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: Oo :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Oo :: R :: Oo :: nil) ((P :: Q :: Oo :: nil) ++ (R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_2 (P :: Q :: Oo :: nil) (R :: Oo :: nil) (Oo :: nil) 4 1 2 HPQROomtmp HOomtmp HROoMtmp Hincl);apply HT.
}
try clear HROoM1. try clear HROoM2. try clear HROoM3. try clear HROom4. try clear HROom3. try clear HROom2. try clear HROom1. 

assert(HPQOoM : rk(P :: Q :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPQOoeq HPQOoM3).
assert(HPQOom : rk(P :: Q :: Oo ::  nil) >= 1) by (solve_hyps_min HPQOoeq HPQOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPROo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PROo requis par la preuve de (?)PROo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PR requis par la preuve de (?)PROo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PROo requis par la preuve de (?)PROo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : P :: R ::  de rang :  1 et 2 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HPROom2 : rk(P :: R :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(HPRmtmp : rk(P :: R :: nil) >= 1) by (solve_hyps_min HPReq HPRm1).
	assert(Hincl : incl (P :: R :: nil) (list_inter (P :: Q :: R :: nil) (P :: R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: P :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: P :: R :: Oo :: nil) ((P :: Q :: R :: nil) ++ (P :: R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (P :: R :: Oo :: nil) (P :: R :: nil) 4 1 3 HPQROomtmp HPRmtmp HPQRMtmp Hincl); apply HT.
}
try clear HPRM1. try clear HPRM2. try clear HPRM3. try clear HPRm4. try clear HPRm3. try clear HPRm2. try clear HPRm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : Q :: Oo ::   de rang : 2 et 2 *)
assert(HPROom3 : rk(P :: R :: Oo :: nil) >= 3).
{
	try assert(HQOoeq : rk(Q :: Oo :: nil) = 2) by (apply LQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQOoMtmp : rk(Q :: Oo :: nil) <= 2) by (solve_hyps_max HQOoeq HQOoM2).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HOoeq : rk(Oo :: nil) = 1) by (apply LOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Q :: Oo :: nil) (P :: R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (Q :: Oo :: P :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Oo :: P :: R :: Oo :: nil) ((Q :: Oo :: nil) ++ (P :: R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (Q :: Oo :: nil) (P :: R :: Oo :: nil) (Oo :: nil) 4 1 2 HPQROomtmp HOomtmp HQOoMtmp Hincl); apply HT.
}


assert(HPROoM : rk(P :: R :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPROoeq HPROoM3).
assert(HPROom : rk(P :: R :: Oo ::  nil) >= 1) by (solve_hyps_min HPROoeq HPROom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQROo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QROo requis par la preuve de (?)QROo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QR requis par la preuve de (?)QROo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QROo requis par la preuve de (?)QROo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 5 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : Q :: R ::  de rang :  1 et 2 	 A : P :: Q :: R ::   de rang : 3 et 3 *)
assert(HQROom2 : rk(Q :: R :: Oo :: nil) >= 2).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRMtmp : rk(P :: Q :: R :: nil) <= 3) by (solve_hyps_max HPQReq HPQRM3).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(HQRmtmp : rk(Q :: R :: nil) >= 1) by (solve_hyps_min HQReq HQRm1).
	assert(Hincl : incl (Q :: R :: nil) (list_inter (P :: Q :: R :: nil) (Q :: R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Q :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: Q :: R :: Oo :: nil) ((P :: Q :: R :: nil) ++ (Q :: R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Q :: R :: nil) (Q :: R :: Oo :: nil) (Q :: R :: nil) 4 1 3 HPQROomtmp HQRmtmp HPQRMtmp Hincl); apply HT.
}
try clear HQRM1. try clear HQRM2. try clear HQRM3. try clear HQRm4. try clear HQRm3. try clear HQRm2. try clear HQRm1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Oo ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : P :: Oo ::   de rang : 2 et 2 *)
assert(HQROom3 : rk(Q :: R :: Oo :: nil) >= 3).
{
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOoMtmp : rk(P :: Oo :: nil) <= 2) by (solve_hyps_max HPOoeq HPOoM2).
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	try assert(HOoeq : rk(Oo :: nil) = 1) by (apply LOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (P :: Oo :: nil) (Q :: R :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: nil) (P :: Oo :: Q :: R :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Oo :: Q :: R :: Oo :: nil) ((P :: Oo :: nil) ++ (Q :: R :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROomtmp;try rewrite HT2 in HPQROomtmp.
	assert(HT := rule_4 (P :: Oo :: nil) (Q :: R :: Oo :: nil) (Oo :: nil) 4 1 2 HPQROomtmp HOomtmp HPOoMtmp Hincl); apply HT.
}


assert(HQROoM : rk(Q :: R :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HQROoeq HQROoM3).
assert(HQROom : rk(Q :: R :: Oo ::  nil) >= 1) by (solve_hyps_min HQROoeq HQROom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpOo *)
(* dans la couche 0 *)
Lemma LPpQpRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPpQpRpOoM : rk(Pp :: Qp :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpOom : rk(Pp :: Qp :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PpOo requis par la preuve de (?)PpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : Pp :: Qp :: Rp ::   de rang : 3 et 3 *)
assert(HPpOom2 : rk(Pp :: Oo :: nil) >= 2).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpMtmp : rk(Pp :: Qp :: Rp :: nil) <= 3) by (solve_hyps_max HPpQpRpeq HPpQpRpM3).
	try assert(HPpQpRpOoeq : rk(Pp :: Qp :: Rp :: Oo :: nil) = 4) by (apply LPpQpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (Pp :: Qp :: Rp :: nil) (Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: Pp :: Oo :: nil) ((Pp :: Qp :: Rp :: nil) ++ (Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOomtmp;try rewrite HT2 in HPpQpRpOomtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: nil) (Pp :: Oo :: nil) (Pp :: nil) 4 1 3 HPpQpRpOomtmp HPpmtmp HPpQpRpMtmp Hincl); apply HT.
}


assert(HPpOoM : rk(Pp :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPpOoeq HPpOoM2).
assert(HPpOom : rk(Pp :: Oo ::  nil) >= 1) by (solve_hyps_min HPpOoeq HPpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPPpOoM : rk(P :: Pp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPPpOoeq HPPpOoM3).
assert(HPPpOom : rk(P :: Pp :: Oo ::  nil) >= 1) by (solve_hyps_min HPPpOoeq HPPpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Qp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QpOo requis par la preuve de (?)QpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo ::  de rang :  4 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Pp :: Qp :: Rp ::   de rang : 3 et 3 *)
assert(HQpOom2 : rk(Qp :: Oo :: nil) >= 2).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpMtmp : rk(Pp :: Qp :: Rp :: nil) <= 3) by (solve_hyps_max HPpQpRpeq HPpQpRpM3).
	try assert(HPpQpRpOoeq : rk(Pp :: Qp :: Rp :: Oo :: nil) = 4) by (apply LPpQpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Pp :: Qp :: Rp :: nil) (Qp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Qp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: Qp :: Oo :: nil) ((Pp :: Qp :: Rp :: nil) ++ (Qp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOomtmp;try rewrite HT2 in HPpQpRpOomtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: nil) (Qp :: Oo :: nil) (Qp :: nil) 4 1 3 HPpQpRpOomtmp HQpmtmp HPpQpRpMtmp Hincl); apply HT.
}


assert(HQpOoM : rk(Qp :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQpOoeq HQpOoM2).
assert(HQpOom : rk(Qp :: Oo ::  nil) >= 1) by (solve_hyps_min HQpOoeq HQpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQQpOoM : rk(Q :: Qp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HQQpOoeq HQQpOoM3).
assert(HQQpOom : rk(Q :: Qp :: Oo ::  nil) >= 1) by (solve_hyps_min HQQpOoeq HQQpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Rp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour RpOo requis par la preuve de (?)RpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Pp :: Qp :: Rp :: Oo ::  de rang :  4 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : Pp :: Qp :: Rp ::   de rang : 3 et 3 *)
assert(HRpOom2 : rk(Rp :: Oo :: nil) >= 2).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpMtmp : rk(Pp :: Qp :: Rp :: nil) <= 3) by (solve_hyps_max HPpQpRpeq HPpQpRpM3).
	try assert(HPpQpRpOoeq : rk(Pp :: Qp :: Rp :: Oo :: nil) = 4) by (apply LPpQpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpOomtmp : rk(Pp :: Qp :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPpQpRpOoeq HPpQpRpOom4).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Pp :: Qp :: Rp :: nil) (Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: Oo :: nil) (Pp :: Qp :: Rp :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: Rp :: Oo :: nil) ((Pp :: Qp :: Rp :: nil) ++ (Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpOomtmp;try rewrite HT2 in HPpQpRpOomtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: nil) (Rp :: Oo :: nil) (Rp :: nil) 4 1 3 HPpQpRpOomtmp HRpmtmp HPpQpRpMtmp Hincl); apply HT.
}
try clear HPpQpRpOoM1. try clear HPpQpRpOoM2. try clear HPpQpRpOoM3. try clear HPpQpRpOom4. try clear HPpQpRpOom3. try clear HPpQpRpOom2. try clear HPpQpRpOom1. 

assert(HRpOoM : rk(Rp :: Oo ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HRpOoeq HRpOoM2).
assert(HRpOom : rk(Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HRpOoeq HRpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPRpOo *)
(* dans la couche 0 *)
Lemma LPRRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRRpOo requis par la preuve de (?)PRRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpOom3 : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QRp requis par la preuve de (?)PRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRRpOo requis par la preuve de (?)PRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour RRpOo requis par la preuve de (?)PRRpOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRRpOo requis par la preuve de (?)PRRpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HPRRpOoM3 : rk(P :: R :: Rp :: Oo :: nil) <= 3).
{
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: nil) (P :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Rp :: Oo :: nil) ((P :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (R :: Rp :: Oo :: nil) (nil) 1 2 0 HPMtmp HRRpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Rp :: Oo ::  de rang :  3 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : Q :: Rp ::   de rang : 1 et 2 *)
assert(HPRRpOom2 : rk(P :: R :: Rp :: Oo :: nil) >= 2).
{
	assert(HQRpMtmp : rk(Q :: Rp :: nil) <= 2) by (solve_hyps_max HQRpeq HQRpM2).
	assert(HPQRRpOomtmp : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HPQRRpOoeq HPQRRpOom3).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Q :: Rp :: nil) (P :: R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Rp :: Oo :: nil) (Q :: Rp :: P :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Rp :: P :: R :: Rp :: Oo :: nil) ((Q :: Rp :: nil) ++ (P :: R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRRpOomtmp;try rewrite HT2 in HPQRRpOomtmp.
	assert(HT := rule_4 (Q :: Rp :: nil) (P :: R :: Rp :: Oo :: nil) (Rp :: nil) 3 1 2 HPQRRpOomtmp HRpmtmp HQRpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRRpOom3 : rk(P :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPROoeq : rk(P :: R :: Oo :: nil) = 3) by (apply LPROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROomtmp : rk(P :: R :: Oo :: nil) >= 3) by (solve_hyps_min HPROoeq HPROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Oo :: nil) (P :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Oo :: nil) (P :: R :: Rp :: Oo :: nil) 3 3 HPROomtmp Hcomp Hincl);apply HT.
}


assert(HPRRpOoM : rk(P :: R :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRRpOom : rk(P :: R :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPRRpOoeq HPRRpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPRpOo *)
(* dans la couche 0 *)
Lemma LRRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(R :: Rp :: Oo ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HRRpOoM : rk(R :: Rp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HRRpOoeq HRRpOoM3).
assert(HRRpOom : rk(R :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HRRpOoeq HRRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRpOo requis par la preuve de (?)PRpOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRpOo requis par la preuve de (?)PRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRpOom2 : rk(P :: Rp :: Oo :: nil) >= 2).
{
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOomtmp : rk(P :: Oo :: nil) >= 2) by (solve_hyps_min HPOoeq HPOom2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Oo :: nil) (P :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Oo :: nil) (P :: Rp :: Oo :: nil) 2 2 HPOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPRpOom3 : rk(P :: Rp :: Oo :: nil) >= 3).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRRpOoeq : rk(P :: R :: Rp :: Oo :: nil) = 3) by (apply LPRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRRpOomtmp : rk(P :: R :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HPRRpOoeq HPRRpOom3).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (P :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: nil) (P :: Rp :: Oo :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Rp :: Oo :: R :: Rp :: Oo :: nil) ((P :: Rp :: Oo :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRRpOomtmp;try rewrite HT2 in HPRRpOomtmp.
	assert(HT := rule_2 (P :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil) (Rp :: Oo :: nil) 3 2 2 HPRRpOomtmp HRpOomtmp HRRpOoMtmp Hincl);apply HT.
}


assert(HPRpOoM : rk(P :: Rp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPRpOoeq HPRpOoM3).
assert(HPRpOom : rk(P :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPRpOoeq HPRpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LQRpOo *)
(* dans la couche 0 *)
Lemma LQRRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QRRpOo requis par la preuve de (?)QRRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)QRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpOom3 : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour PRp requis par la preuve de (?)QRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QRRpOo requis par la preuve de (?)QRRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRRpOo requis par la preuve de (?)QRRpOo pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HQRRpOoM3 : rk(Q :: R :: Rp :: Oo :: nil) <= 3).
{
	try assert(HQeq : rk(Q :: nil) = 1) by (apply LQ with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Rp :: Oo :: nil) (Q :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: R :: Rp :: Oo :: nil) ((Q :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (R :: Rp :: Oo :: nil) (nil) 1 2 0 HQMtmp HRRpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Rp :: Oo ::  de rang :  3 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : P :: Rp ::   de rang : 1 et 2 *)
assert(HQRRpOom2 : rk(Q :: R :: Rp :: Oo :: nil) >= 2).
{
	assert(HPRpMtmp : rk(P :: Rp :: nil) <= 2) by (solve_hyps_max HPRpeq HPRpM2).
	assert(HPQRRpOomtmp : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HPQRRpOoeq HPQRRpOom3).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (P :: Rp :: nil) (Q :: R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Rp :: Oo :: nil) (P :: Rp :: Q :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Rp :: Q :: R :: Rp :: Oo :: nil) ((P :: Rp :: nil) ++ (Q :: R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRRpOomtmp;try rewrite HT2 in HPQRRpOomtmp.
	assert(HT := rule_4 (P :: Rp :: nil) (Q :: R :: Rp :: Oo :: nil) (Rp :: nil) 3 1 2 HPQRRpOomtmp HRpmtmp HPRpMtmp Hincl); apply HT.
}
try clear HPRpM1. try clear HPRpM2. try clear HPRpM3. try clear HPRpm4. try clear HPRpm3. try clear HPRpm2. try clear HPRpm1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQRRpOom3 : rk(Q :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HQROoeq : rk(Q :: R :: Oo :: nil) = 3) by (apply LQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQROomtmp : rk(Q :: R :: Oo :: nil) >= 3) by (solve_hyps_min HQROoeq HQROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Q :: R :: Oo :: nil) (Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: R :: Oo :: nil) (Q :: R :: Rp :: Oo :: nil) 3 3 HQROomtmp Hcomp Hincl);apply HT.
}


assert(HQRRpOoM : rk(Q :: R :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRRpOom : rk(Q :: R :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HQRRpOoeq HQRRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QRpOo requis par la preuve de (?)QRpOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QRpOo requis par la preuve de (?)QRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQRpOom2 : rk(Q :: Rp :: Oo :: nil) >= 2).
{
	try assert(HQOoeq : rk(Q :: Oo :: nil) = 2) by (apply LQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQOomtmp : rk(Q :: Oo :: nil) >= 2) by (solve_hyps_min HQOoeq HQOom2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Oo :: nil) (Q :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Oo :: nil) (Q :: Rp :: Oo :: nil) 2 2 HQOomtmp Hcomp Hincl);apply HT.
}
try clear HQOoM1. try clear HQOoM2. try clear HQOoM3. try clear HQOom4. try clear HQOom3. try clear HQOom2. try clear HQOom1. 

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HQRpOom3 : rk(Q :: Rp :: Oo :: nil) >= 3).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HQRRpOoeq : rk(Q :: R :: Rp :: Oo :: nil) = 3) by (apply LQRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRRpOomtmp : rk(Q :: R :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HQRRpOoeq HQRRpOom3).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (Q :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Rp :: Oo :: nil) (Q :: Rp :: Oo :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Rp :: Oo :: R :: Rp :: Oo :: nil) ((Q :: Rp :: Oo :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRRpOomtmp;try rewrite HT2 in HQRRpOomtmp.
	assert(HT := rule_2 (Q :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil) (Rp :: Oo :: nil) 3 2 2 HQRRpOomtmp HRpOomtmp HRRpOoMtmp Hincl);apply HT.
}


assert(HQRpOoM : rk(Q :: Rp :: Oo ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HQRpOoeq HQRpOoM3).
assert(HQRpOom : rk(Q :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HQRpOoeq HQRpOom1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQRpOo *)
(* dans la couche 0 *)
Lemma LPQRRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Rp :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpOom3 : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpOom4 : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 4).
{
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Rp :: Oo :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}


assert(HPQRRpOoM : rk(P :: Q :: R :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRRpOom : rk(P :: Q :: R :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPQRRpOoeq HPQRRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Rp :: Oo ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRpOo requis par la preuve de (?)PQRpOo pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQRpOo requis par la preuve de (?)PQRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRpOo pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRRpOo requis par la preuve de (?)PQRRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpOom3 : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: Oo :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRpOo requis par la preuve de (?)PQRpOo pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Rp :: Oo ::  de rang :  3 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : R :: Rp ::   de rang : 2 et 2 *)
assert(HPQRpOom2 : rk(P :: Q :: Rp :: Oo :: nil) >= 2).
{
	try assert(HRRpeq : rk(R :: Rp :: nil) = 2) by (apply LRRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpMtmp : rk(R :: Rp :: nil) <= 2) by (solve_hyps_max HRRpeq HRRpM2).
	assert(HPQRRpOomtmp : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HPQRRpOoeq HPQRRpOom3).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (R :: Rp :: nil) (P :: Q :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Rp :: Oo :: nil) (R :: Rp :: P :: Q :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: P :: Q :: Rp :: Oo :: nil) ((R :: Rp :: nil) ++ (P :: Q :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRRpOomtmp;try rewrite HT2 in HPQRRpOomtmp.
	assert(HT := rule_4 (R :: Rp :: nil) (P :: Q :: Rp :: Oo :: nil) (Rp :: nil) 3 1 2 HPQRRpOomtmp HRpmtmp HRRpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRpOom3 : rk(P :: Q :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Rp :: Oo :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPQRpOom4 : rk(P :: Q :: Rp :: Oo :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPQRRpOoeq : rk(P :: Q :: R :: Rp :: Oo :: nil) = 4) by (apply LPQRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRRpOomtmp : rk(P :: Q :: R :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPQRRpOoeq HPQRRpOom4).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (P :: Q :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Rp :: Oo :: nil) (P :: Q :: Rp :: Oo :: R :: Rp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Rp :: Oo :: R :: Rp :: Oo :: nil) ((P :: Q :: Rp :: Oo :: nil) ++ (R :: Rp :: Oo :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRRpOomtmp;try rewrite HT2 in HPQRRpOomtmp.
	assert(HT := rule_2 (P :: Q :: Rp :: Oo :: nil) (R :: Rp :: Oo :: nil) (Rp :: Oo :: nil) 4 2 2 HPQRRpOomtmp HRpOomtmp HRRpOoMtmp Hincl);apply HT.
}


assert(HPQRpOoM : rk(P :: Q :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRpOom : rk(P :: Q :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPQRpOoeq HPQRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpRpOo : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Rp :: Oo ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PPpRpOo requis par la preuve de (?)PPpRpOo pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpRpOo requis par la preuve de (?)PPpRpOo pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpRpOo requis par la preuve de (?)PPpRpOo pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpRpOom2 : rk(P :: Pp :: Rp :: Oo :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Rp :: Oo :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPPpRpOoM3 : rk(P :: Pp :: Rp :: Oo :: nil) <= 3).
{
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Rp :: nil) (P :: Pp :: Oo :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Rp :: Oo :: nil) (Rp :: P :: Pp :: Oo :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Rp :: P :: Pp :: Oo :: nil) ((Rp :: nil) ++ (P :: Pp :: Oo :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Rp :: nil) (P :: Pp :: Oo :: nil) (nil) 1 2 0 HRpMtmp HPPpOoMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpRpOom3 : rk(P :: Pp :: Rp :: Oo :: nil) >= 3).
{
	try assert(HPRpOoeq : rk(P :: Rp :: Oo :: nil) = 3) by (apply LPRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRpOomtmp : rk(P :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HPRpOoeq HPRpOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Rp :: Oo :: nil) (P :: Pp :: Rp :: Oo :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Rp :: Oo :: nil) (P :: Pp :: Rp :: Oo :: nil) 3 3 HPRpOomtmp Hcomp Hincl);apply HT.
}


assert(HPPpRpOoM : rk(P :: Pp :: Rp :: Oo ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpRpOom : rk(P :: Pp :: Rp :: Oo ::  nil) >= 1) by (solve_hyps_min HPPpRpOoeq HPPpRpOom1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(alpha ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HalphaM : rk(alpha ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max Halphaeq HalphaM1).
assert(Halpham : rk(alpha ::  nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LQalpha *)
(* dans la couche 0 *)
Lemma LPQRalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQRalpha requis par la preuve de (?)PQRalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour PRalpha requis par la preuve de (?)PQRalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRalpha requis par la preuve de (?)PQRalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HPQRalphaM3 : rk(P :: Q :: R :: alpha :: nil) <= 3).
{
	try assert(HQeq : rk(Q :: nil) = 1) by (apply LQ with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: alpha :: nil) (Q :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: P :: R :: alpha :: nil) ((Q :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HQMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRalpham3 : rk(P :: Q :: R :: alpha :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: alpha :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


assert(HPQRalphaM : rk(P :: Q :: R :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRalpham : rk(P :: Q :: R :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRalphaeq HPQRalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LQalpha *)
(* dans la couche 0 *)
Lemma LPRalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPRalphaM : rk(P :: R :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPRalphaeq HPRalphaM3).
assert(HPRalpham : rk(P :: R :: alpha ::  nil) >= 1) by (solve_hyps_min HPRalphaeq HPRalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qalpha requis par la preuve de (?)Qalpha pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HQalpham2 : rk(Q :: alpha :: nil) >= 2).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPQRalphaeq : rk(P :: Q :: R :: alpha :: nil) = 3) by (apply LPQRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRalphamtmp : rk(P :: Q :: R :: alpha :: nil) >= 3) by (solve_hyps_min HPQRalphaeq HPQRalpham3).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (Q :: alpha :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: alpha :: nil) (Q :: alpha :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: alpha :: P :: R :: alpha :: nil) ((Q :: alpha :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRalphamtmp;try rewrite HT2 in HPQRalphamtmp.
	assert(HT := rule_2 (Q :: alpha :: nil) (P :: R :: alpha :: nil) (alpha :: nil) 3 1 2 HPQRalphamtmp Halphamtmp HPRalphaMtmp Hincl);apply HT.
}


assert(HQalphaM : rk(Q :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQalphaeq HQalphaM2).
assert(HQalpham : rk(Q :: alpha ::  nil) >= 1) by (solve_hyps_min HQalphaeq HQalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpalpha *)
(* dans constructLemma(), requis par LPRPpalpha *)
(* dans la couche 0 *)
Lemma LPRPpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpOoalpha requis par la preuve de (?)PRPpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpOoalpham2 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpOoalpham3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPROoeq : rk(P :: R :: Oo :: nil) = 3) by (apply LPROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROomtmp : rk(P :: R :: Oo :: nil) >= 3) by (solve_hyps_min HPROoeq HPROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Oo :: nil) (P :: R :: Pp :: Oo :: alpha :: nil) 3 3 HPROomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPRPpOoalphaM3 : rk(P :: R :: Pp :: Oo :: alpha :: nil) <= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: R :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (P :: R :: alpha :: nil) (P :: nil) 2 2 1 HPPpOoMtmp HPRalphaMtmp HPmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPRPpOoalphaM : rk(P :: R :: Pp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpOoalpham : rk(P :: R :: Pp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpOoalphaeq HPRPpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpalpha requis par la preuve de (?)PRPpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPRPpalphaM3 : rk(P :: R :: Pp :: alpha :: nil) <= 3).
{
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpMtmp : rk(Pp :: nil) <= 1) by (solve_hyps_max HPpeq HPpM1).
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: alpha :: nil) (Pp :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: P :: R :: alpha :: nil) ((Pp :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HPpMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpalpham2 : rk(P :: R :: Pp :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Oo :: alpha ::  de rang :  3 et 3 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpalpham3 : rk(P :: R :: Pp :: alpha :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPRPpOoalphaeq : rk(P :: R :: Pp :: Oo :: alpha :: nil) = 3) by (apply LPRPpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpOoalphamtmp : rk(P :: R :: Pp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpOoalphaeq HPRPpOoalpham3).
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: R :: Pp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: R :: Pp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: R :: Pp :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpOoalphamtmp;try rewrite HT2 in HPRPpOoalphamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: R :: Pp :: alpha :: nil) (P :: Pp :: nil) 3 2 2 HPRPpOoalphamtmp HPPpmtmp HPPpOoMtmp Hincl); apply HT.
}


assert(HPRPpalphaM : rk(P :: R :: Pp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpalpham : rk(P :: R :: Pp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpalphaeq HPRPpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Ppalpha requis par la preuve de (?)Ppalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HPpalpham2 : rk(Pp :: alpha :: nil) >= 2).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPRPpalphaeq : rk(P :: R :: Pp :: alpha :: nil) = 3) by (apply LPRPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpalphamtmp : rk(P :: R :: Pp :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpalphaeq HPRPpalpham3).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: alpha :: nil) (P :: R :: alpha :: Pp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpalphamtmp;try rewrite HT2 in HPRPpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Pp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRPpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}


assert(HPpalphaM : rk(Pp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPpalphaeq HPpalphaM2).
assert(HPpalpham : rk(Pp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpalphaeq HPpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalpha *)
(* dans la couche 0 *)
Lemma LPpQpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour PpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalpha requis par la preuve de (?)PpQpRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HPpQpRpalphaM3 : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3).
{
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpMtmp : rk(Qp :: nil) <= 1) by (solve_hyps_max HQpeq HQpM1).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Qp :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: nil) (Qp :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Qp :: Pp :: Rp :: alpha :: nil) ((Qp :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Qp :: nil) (Pp :: Rp :: alpha :: nil) (nil) 1 2 0 HQpMtmp HPpRpalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpRpalpham3 : rk(Pp :: Qp :: Rp :: alpha :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (Pp :: Qp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (Pp :: Qp :: Rp :: alpha :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


assert(HPpQpRpalphaM : rk(Pp :: Qp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpalpham : rk(Pp :: Qp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpQpRpalphaeq HPpQpRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalpha *)
(* dans la couche 0 *)
Lemma LPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Rp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPpRpalphaM : rk(Pp :: Rp :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM3).
assert(HPpRpalpham : rk(Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpRpalphaeq HPpRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpalpha requis par la preuve de (?)PpQpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOoalpha requis par la preuve de (?)PpQpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpOoalpha requis par la preuve de (?)QPpQpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpOoalpha requis par la preuve de (?)PQPpQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpOoalpha requis par la preuve de (?)PQPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalpham2 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalpham3 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOoalpha requis par la preuve de (?)QPpQpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOoalpha requis par la preuve de (?)QPpQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpOoalpham2 : rk(Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Oo :: alpha ::  de rang :  3 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpOoalpham3 : rk(Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpQpOoalphamtmp : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPQPpQpOoalphaeq HPQPpQpOoalpham3).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpOoalphamtmp;try rewrite HT2 in HPQPpQpOoalphamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: nil) (Pp :: Oo :: nil) 3 2 2 HPQPpQpOoalphamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpQpOoalphaM1. try clear HPQPpQpOoalphaM2. try clear HPQPpQpOoalphaM3. try clear HPQPpQpOoalpham4. try clear HPQPpQpOoalpham3. try clear HPQPpQpOoalpham2. try clear HPQPpQpOoalpham1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpalpha requis par la preuve de (?)PpQpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: alpha ::  de rang :  3 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPpQpalpham2 : rk(Pp :: Qp :: alpha :: nil) >= 2).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQPpQpOoalphamtmp : rk(Q :: Pp :: Qp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HQPpQpOoalphaeq HQPpQpOoalpham3).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: nil) ((Q :: Qp :: Oo :: nil) ++ (Pp :: Qp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOoalphamtmp;try rewrite HT2 in HQPpQpOoalphamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: nil) (Qp :: nil) 3 1 2 HQPpQpOoalphamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQPpQpOoalphaM1. try clear HQPpQpOoalphaM2. try clear HQPpQpOoalphaM3. try clear HQPpQpOoalpham4. try clear HQPpQpOoalpham3. try clear HQPpQpOoalpham2. try clear HQPpQpOoalpham1. 

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPpQpalpham3 : rk(Pp :: Qp :: alpha :: nil) >= 3).
{
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	try assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpalphamtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpRpalphaeq HPpQpRpalpham3).
	try assert(HPpalphaeq : rk(Pp :: alpha :: nil) = 2) by (apply LPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpalphamtmp : rk(Pp :: alpha :: nil) >= 2) by (solve_hyps_min HPpalphaeq HPpalpham2).
	assert(Hincl : incl (Pp :: alpha :: nil) (list_inter (Pp :: Qp :: alpha :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: nil) (Pp :: Qp :: alpha :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: alpha :: Pp :: Rp :: alpha :: nil) ((Pp :: Qp :: alpha :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPpQpRpalphamtmp;try rewrite HT2 in HPpQpRpalphamtmp.
	assert(HT := rule_2 (Pp :: Qp :: alpha :: nil) (Pp :: Rp :: alpha :: nil) (Pp :: alpha :: nil) 3 2 2 HPpQpRpalphamtmp HPpalphamtmp HPpRpalphaMtmp Hincl);apply HT.
}


assert(HPpQpalphaM : rk(Pp :: Qp :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpalphaeq HPpQpalphaM3).
assert(HPpQpalpham : rk(Pp :: Qp :: alpha ::  nil) >= 1) by (solve_hyps_min HPpQpalphaeq HPpQpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LRpalpha *)
(* dans constructLemma(), requis par LPRRpalpha *)
(* dans la couche 0 *)
Lemma LPRRpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Rp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRRpOoalpha requis par la preuve de (?)PRRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRRpOoalpham2 : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HRRpeq : rk(R :: Rp :: nil) = 2) by (apply LRRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (R :: Rp :: nil) (P :: R :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (R :: Rp :: nil) (P :: R :: Rp :: Oo :: alpha :: nil) 2 2 HRRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRRpOoalpham3 : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPROoeq : rk(P :: R :: Oo :: nil) = 3) by (apply LPROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROomtmp : rk(P :: R :: Oo :: nil) >= 3) by (solve_hyps_min HPROoeq HPROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Oo :: nil) (P :: R :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Oo :: nil) (P :: R :: Rp :: Oo :: alpha :: nil) 3 3 HPROomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPRRpOoalphaM3 : rk(P :: R :: Rp :: Oo :: alpha :: nil) <= 3).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HReq : rk(R :: nil) = 1) by (apply LR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRmtmp : rk(R :: nil) >= 1) by (solve_hyps_min HReq HRm1).
	assert(Hincl : incl (R :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: alpha :: nil) (R :: Rp :: Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: alpha :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (R :: Rp :: Oo :: nil) (P :: R :: alpha :: nil) (R :: nil) 2 2 1 HRRpOoMtmp HPRalphaMtmp HRmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPRRpOoalphaM : rk(P :: R :: Rp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRRpOoalpham : rk(P :: R :: Rp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPRRpOoalphaeq HPRRpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRRpalpha requis par la preuve de (?)PQRRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRRpalpham3 : rk(P :: Q :: R :: Rp :: alpha :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Rp :: alpha :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour QRp requis par la preuve de (?)PRRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRRpalpha requis par la preuve de (?)PRRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPRRpalphaM3 : rk(P :: R :: Rp :: alpha :: nil) <= 3).
{
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpMtmp : rk(Rp :: nil) <= 1) by (solve_hyps_max HRpeq HRpM1).
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Rp :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: alpha :: nil) (Rp :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Rp :: P :: R :: alpha :: nil) ((Rp :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Rp :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HRpMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : P :: Q :: R :: Rp :: alpha ::  de rang :  3 et 4 	 AiB : Rp ::  de rang :  1 et 1 	 A : Q :: Rp ::   de rang : 1 et 2 *)
assert(HPRRpalpham2 : rk(P :: R :: Rp :: alpha :: nil) >= 2).
{
	assert(HQRpMtmp : rk(Q :: Rp :: nil) <= 2) by (solve_hyps_max HQRpeq HQRpM2).
	assert(HPQRRpalphamtmp : rk(P :: Q :: R :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPQRRpalphaeq HPQRRpalpham3).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Q :: Rp :: nil) (P :: R :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Rp :: alpha :: nil) (Q :: Rp :: P :: R :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Rp :: P :: R :: Rp :: alpha :: nil) ((Q :: Rp :: nil) ++ (P :: R :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRRpalphamtmp;try rewrite HT2 in HPQRRpalphamtmp.
	assert(HT := rule_4 (Q :: Rp :: nil) (P :: R :: Rp :: alpha :: nil) (Rp :: nil) 3 1 2 HPQRRpalphamtmp HRpmtmp HQRpMtmp Hincl); apply HT.
}
try clear HPQRRpalphaM1. try clear HPQRRpalphaM2. try clear HPQRRpalphaM3. try clear HPQRRpalpham4. try clear HPQRRpalpham3. try clear HPQRRpalpham2. try clear HPQRRpalpham1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Rp :: Oo :: alpha ::  de rang :  3 et 3 	 AiB : R :: Rp ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPRRpalpham3 : rk(P :: R :: Rp :: alpha :: nil) >= 3).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRRpOoalphaeq : rk(P :: R :: Rp :: Oo :: alpha :: nil) = 3) by (apply LPRRpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRRpOoalphamtmp : rk(P :: R :: Rp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPRRpOoalphaeq HPRRpOoalpham3).
	try assert(HRRpeq : rk(R :: Rp :: nil) = 2) by (apply LRRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hincl : incl (R :: Rp :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: Oo :: alpha :: nil) (R :: Rp :: Oo :: P :: R :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: Rp :: alpha :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRRpOoalphamtmp;try rewrite HT2 in HPRRpOoalphamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: R :: Rp :: alpha :: nil) (R :: Rp :: nil) 3 2 2 HPRRpOoalphamtmp HRRpmtmp HRRpOoMtmp Hincl); apply HT.
}


assert(HPRRpalphaM : rk(P :: R :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRRpalpham : rk(P :: R :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRRpalphaeq HPRRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Rp :: alpha ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Rpalpha requis par la preuve de (?)Rpalpha pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Rp :: alpha ::  de rang :  3 et 3 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HRpalpham2 : rk(Rp :: alpha :: nil) >= 2).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPRRpalphaeq : rk(P :: R :: Rp :: alpha :: nil) = 3) by (apply LPRRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRRpalphamtmp : rk(P :: R :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPRRpalphaeq HPRRpalpham3).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Rp :: alpha :: nil) (P :: R :: alpha :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Rp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRRpalphamtmp;try rewrite HT2 in HPRRpalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Rp :: alpha :: nil) (alpha :: nil) 3 1 2 HPRRpalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}


assert(HRpalphaM : rk(Rp :: alpha ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HRpalphaeq HRpalphaM2).
assert(HRpalpham : rk(Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HRpalphaeq HRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpRpalpha *)
(* dans la couche 0 *)
Lemma LPQPpRpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpRpOoalphabeta requis par la preuve de (?)PQPpRpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpRpOoalphabeta requis par la preuve de (?)PQPpRpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpRpOoalphabeta requis par la preuve de (?)PQPpRpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpRpOoalphabetam2 : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpRpOoalphabetam3 : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpRpOoalphabetam4 : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) >= 4).
{
	try assert(HPQRpOoeq : rk(P :: Q :: Rp :: Oo :: nil) = 4) by (apply LPQRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRpOomtmp : rk(P :: Q :: Rp :: Oo :: nil) >= 4) by (solve_hyps_min HPQRpOoeq HPQRpOom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Rp :: Oo :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Rp :: Oo :: nil) (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) 4 4 HPQRpOomtmp Hcomp Hincl);apply HT.
}


assert(HPQPpRpOoalphabetaM : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpRpOoalphabetam : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HPQPpRpOoalphabetaeq HPQPpRpOoalphabetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpRpalpha *)
(* dans constructLemma(), requis par LPQPpOobeta *)
(* dans la couche 0 *)
Lemma LPQbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPQbetaM : rk(P :: Q :: beta ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPQbetaeq HPQbetaM3).
assert(HPQbetam : rk(P :: Q :: beta ::  nil) >= 1) by (solve_hyps_min HPQbetaeq HPQbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQPpOobeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Pp :: Oo :: beta ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOobeta requis par la preuve de (?)PQPpOobeta pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOobeta requis par la preuve de (?)PQPpOobeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOobeta requis par la preuve de (?)PQPpOobeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOobetam2 : rk(P :: Q :: Pp :: Oo :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOobetam3 : rk(P :: Q :: Pp :: Oo :: beta :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: beta :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPQPpOobetaM3 : rk(P :: Q :: Pp :: Oo :: beta :: nil) <= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQbetaeq : rk(P :: Q :: beta :: nil) = 2) by (apply LPQbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: beta :: nil) (P :: Pp :: Oo :: P :: Q :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: beta :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Pp :: Oo :: nil) (P :: Q :: beta :: nil) (P :: nil) 2 2 1 HPPpOoMtmp HPQbetaMtmp HPmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPQPpOobetaM : rk(P :: Q :: Pp :: Oo :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpOobetam : rk(P :: Q :: Pp :: Oo :: beta ::  nil) >= 1) by (solve_hyps_min HPQPpOobetaeq HPQPpOobetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpRpalpha requis par la preuve de (?)PPpRpalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPPpRpalphaM3 : rk(P :: Pp :: Rp :: alpha :: nil) <= 3).
{
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: alpha :: nil) ((P :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (Pp :: Rp :: alpha :: nil) (nil) 1 2 0 HPMtmp HPpRpalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpRpalpham2 : rk(P :: Pp :: Rp :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPPpRpalpham3 : rk(P :: Pp :: Rp :: alpha :: nil) >= 3).
{
	try assert(HPQPpOobetaeq : rk(P :: Q :: Pp :: Oo :: beta :: nil) = 3) by (apply LPQPpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQPpOobetaMtmp : rk(P :: Q :: Pp :: Oo :: beta :: nil) <= 3) by (solve_hyps_max HPQPpOobetaeq HPQPpOobetaM3).
	try assert(HPQPpRpOoalphabetaeq : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) = 4) by (apply LPQPpRpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQPpRpOoalphabetamtmp : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPQPpRpOoalphabetaeq HPQPpRpOoalphabetam4).
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) (P :: Pp :: Rp :: alpha :: P :: Q :: Pp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: alpha :: P :: Q :: Pp :: Oo :: beta :: nil) ((P :: Pp :: Rp :: alpha :: nil) ++ (P :: Q :: Pp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpRpOoalphabetamtmp;try rewrite HT2 in HPQPpRpOoalphabetamtmp.
	assert(HT := rule_2 (P :: Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Oo :: beta :: nil) (P :: Pp :: nil) 4 2 3 HPQPpRpOoalphabetamtmp HPPpmtmp HPQPpOobetaMtmp Hincl);apply HT.
}


assert(HPPpRpalphaM : rk(P :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpRpalpham : rk(P :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpRpalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: Rp :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpOoalpha requis par la preuve de (?)PRPpRpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpRpOoalpham2 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpRpOoalpham3 : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPROoeq : rk(P :: R :: Oo :: nil) = 3) by (apply LPROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROomtmp : rk(P :: R :: Oo :: nil) >= 3) by (solve_hyps_min HPROoeq HPROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Oo :: nil) (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) 3 3 HPROomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpRpalpha requis par la preuve de (?)PRPpRpalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpRpalpham2 : rk(P :: R :: Pp :: Rp :: alpha :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Rp :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Rp :: alpha :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Rp :: Oo :: alpha ::  de rang :  3 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpRpalpham3 : rk(P :: R :: Pp :: Rp :: alpha :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPRPpRpOoalphamtmp : rk(P :: R :: Pp :: Rp :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPRPpRpOoalphaeq HPRPpRpOoalpham3).
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: Oo :: alpha :: nil) (P :: Pp :: Oo :: P :: R :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: R :: Pp :: Rp :: alpha :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: R :: Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpRpOoalphamtmp;try rewrite HT2 in HPRPpRpOoalphamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: nil) 3 2 2 HPRPpRpOoalphamtmp HPPpmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPRPpRpOoalphaM1. try clear HPRPpRpOoalphaM2. try clear HPRPpRpOoalphaM3. try clear HPRPpRpOoalpham4. try clear HPRPpRpOoalpham3. try clear HPRPpRpOoalpham2. try clear HPRPpRpOoalpham1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPRPpRpalphaM3 : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Pp :: Rp :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Rp :: alpha :: nil) (P :: R :: alpha :: Pp :: Rp :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Pp :: Rp :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Pp :: Rp :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: alpha :: nil) (Pp :: Rp :: alpha :: nil) (alpha :: nil) 2 2 1 HPRalphaMtmp HPpRpalphaMtmp Halphamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPRPpRpalphaM : rk(P :: R :: Pp :: Rp :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpRpalpham : rk(P :: R :: Pp :: Rp :: alpha ::  nil) >= 1) by (solve_hyps_min HPRPpRpalphaeq HPRPpRpalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPOoalpha *)
(* dans la couche 0 *)
Lemma LPQPpOoalphabeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Pp :: Oo :: alpha :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOoalphabeta requis par la preuve de (?)PQPpOoalphabeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOoalphabeta requis par la preuve de (?)PQPpOoalphabeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOoalphabeta requis par la preuve de (?)PQPpOoalphabeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetam2 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetam3 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Rp :: Oo :: alpha :: beta ::  de rang :  4 et 4 	 AiB : Pp :: alpha ::  de rang :  2 et 2 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HPQPpOoalphabetam4 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: nil) >= 4).
{
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	try assert(HPQPpRpOoalphabetaeq : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) = 4) by (apply LPQPpRpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQPpRpOoalphabetamtmp : rk(P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPQPpRpOoalphabetaeq HPQPpRpOoalphabetam4).
	try assert(HPpalphaeq : rk(Pp :: alpha :: nil) = 2) by (apply LPpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpalphamtmp : rk(Pp :: alpha :: nil) >= 2) by (solve_hyps_min HPpalphaeq HPpalpham2).
	assert(Hincl : incl (Pp :: alpha :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Rp :: Oo :: alpha :: beta :: nil) (Pp :: Rp :: alpha :: P :: Q :: Pp :: Oo :: alpha :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: P :: Q :: Pp :: Oo :: alpha :: beta :: nil) ((Pp :: Rp :: alpha :: nil) ++ (P :: Q :: Pp :: Oo :: alpha :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpRpOoalphabetamtmp;try rewrite HT2 in HPQPpRpOoalphabetamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: nil) (Pp :: alpha :: nil) 4 2 2 HPQPpRpOoalphabetamtmp HPpalphamtmp HPpRpalphaMtmp Hincl); apply HT.
}
try clear HPpalphaM1. try clear HPpalphaM2. try clear HPpalphaM3. try clear HPpalpham4. try clear HPpalpham3. try clear HPpalpham2. try clear HPpalpham1. 

assert(HPQPpOoalphabetaM : rk(P :: Q :: Pp :: Oo :: alpha :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQPpOoalphabetam : rk(P :: Q :: Pp :: Oo :: alpha :: beta ::  nil) >= 1) by (solve_hyps_min HPQPpOoalphabetaeq HPQPpOoalphabetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour POoalpha requis par la preuve de (?)POoalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour POoalpha requis par la preuve de (?)POoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPOoalpham2 : rk(P :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOomtmp : rk(P :: Oo :: nil) >= 2) by (solve_hyps_min HPOoeq HPOom2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Oo :: nil) (P :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Oo :: nil) (P :: Oo :: alpha :: nil) 2 2 HPOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPOoalpham3 : rk(P :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPQPpOobetaeq : rk(P :: Q :: Pp :: Oo :: beta :: nil) = 3) by (apply LPQPpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQPpOobetaMtmp : rk(P :: Q :: Pp :: Oo :: beta :: nil) <= 3) by (solve_hyps_max HPQPpOobetaeq HPQPpOobetaM3).
	try assert(HPQPpOoalphabetaeq : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: nil) = 4) by (apply LPQPpOoalphabeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQPpOoalphabetamtmp : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: nil) >= 4) by (solve_hyps_min HPQPpOoalphabetaeq HPQPpOoalphabetam4).
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOomtmp : rk(P :: Oo :: nil) >= 2) by (solve_hyps_min HPOoeq HPOom2).
	assert(Hincl : incl (P :: Oo :: nil) (list_inter (P :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: alpha :: beta :: nil) (P :: Oo :: alpha :: P :: Q :: Pp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Oo :: alpha :: P :: Q :: Pp :: Oo :: beta :: nil) ((P :: Oo :: alpha :: nil) ++ (P :: Q :: Pp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOoalphabetamtmp;try rewrite HT2 in HPQPpOoalphabetamtmp.
	assert(HT := rule_2 (P :: Oo :: alpha :: nil) (P :: Q :: Pp :: Oo :: beta :: nil) (P :: Oo :: nil) 4 2 3 HPQPpOoalphabetamtmp HPOomtmp HPQPpOobetaMtmp Hincl);apply HT.
}


assert(HPOoalphaM : rk(P :: Oo :: alpha ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPOoalphaeq HPOoalphaM3).
assert(HPOoalpham : rk(P :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPOoalphaeq HPOoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQOoalpha *)
(* dans la couche 0 *)
Lemma LPQROoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQROoalpha requis par la preuve de (?)PQROoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQROoalpha requis par la preuve de (?)PQROoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQROoalpham3 : rk(P :: Q :: R :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Oo :: alpha :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQROoalpham4 : rk(P :: Q :: R :: Oo :: alpha :: nil) >= 4).
{
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}


assert(HPQROoalphaM : rk(P :: Q :: R :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQROoalpham : rk(P :: Q :: R :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQROoalphaeq HPQROoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQOoalpha *)
(* dans la couche 0 *)
Lemma LPROoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PROoalpha requis par la preuve de (?)PROoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PROoalpha requis par la preuve de (?)PROoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PROoalpha requis par la preuve de (?)PROoalpha pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPROoalphaM3 : rk(P :: R :: Oo :: alpha :: nil) <= 3).
{
	try assert(HOoeq : rk(Oo :: nil) = 1) by (apply LOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (P :: R :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Oo :: alpha :: nil) (Oo :: P :: R :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: P :: R :: alpha :: nil) ((Oo :: nil) ++ (P :: R :: alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (P :: R :: alpha :: nil) (nil) 1 2 0 HOoMtmp HPRalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HOoM1. try clear HOoM2. try clear HOoM3. try clear HOom4. try clear HOom3. try clear HOom2. try clear HOom1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPROoalpham2 : rk(P :: R :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOomtmp : rk(P :: Oo :: nil) >= 2) by (solve_hyps_min HPOoeq HPOom2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Oo :: nil) (P :: R :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Oo :: nil) (P :: R :: Oo :: alpha :: nil) 2 2 HPOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPROoalpham3 : rk(P :: R :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPROoeq : rk(P :: R :: Oo :: nil) = 3) by (apply LPROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROomtmp : rk(P :: R :: Oo :: nil) >= 3) by (solve_hyps_min HPROoeq HPROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: R :: Oo :: nil) (P :: R :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: R :: Oo :: nil) (P :: R :: Oo :: alpha :: nil) 3 3 HPROomtmp Hcomp Hincl);apply HT.
}


assert(HPROoalphaM : rk(P :: R :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPROoalpham : rk(P :: R :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPROoalphaeq HPROoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQOoalpha requis par la preuve de (?)PQOoalpha pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQOoalpha requis par la preuve de (?)PQOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQOoalpha requis par la preuve de (?)PQOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQOoalpham2 : rk(P :: Q :: Oo :: alpha :: nil) >= 2).
{
	try assert(HPOoeq : rk(P :: Oo :: nil) = 2) by (apply LPOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOomtmp : rk(P :: Oo :: nil) >= 2) by (solve_hyps_min HPOoeq HPOom2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Oo :: nil) (P :: Q :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Oo :: nil) (P :: Q :: Oo :: alpha :: nil) 2 2 HPOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQOoalpham3 : rk(P :: Q :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Oo :: alpha :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPQOoalpham4 : rk(P :: Q :: Oo :: alpha :: nil) >= 4).
{
	try assert(HPROoalphaeq : rk(P :: R :: Oo :: alpha :: nil) = 3) by (apply LPROoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPROoalphaMtmp : rk(P :: R :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HPROoalphaeq HPROoalphaM3).
	try assert(HPQROoalphaeq : rk(P :: Q :: R :: Oo :: alpha :: nil) = 4) by (apply LPQROoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROoalphamtmp : rk(P :: Q :: R :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQROoalphaeq HPQROoalpham4).
	try assert(HPOoalphaeq : rk(P :: Oo :: alpha :: nil) = 3) by (apply LPOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPOoalphamtmp : rk(P :: Oo :: alpha :: nil) >= 3) by (solve_hyps_min HPOoalphaeq HPOoalpham3).
	assert(Hincl : incl (P :: Oo :: alpha :: nil) (list_inter (P :: Q :: Oo :: alpha :: nil) (P :: R :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Oo :: alpha :: nil) (P :: Q :: Oo :: alpha :: P :: R :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: Oo :: alpha :: P :: R :: Oo :: alpha :: nil) ((P :: Q :: Oo :: alpha :: nil) ++ (P :: R :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQROoalphamtmp;try rewrite HT2 in HPQROoalphamtmp.
	assert(HT := rule_2 (P :: Q :: Oo :: alpha :: nil) (P :: R :: Oo :: alpha :: nil) (P :: Oo :: alpha :: nil) 4 3 3 HPQROoalphamtmp HPOoalphamtmp HPROoalphaMtmp Hincl);apply HT.
}


assert(HPQOoalphaM : rk(P :: Q :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQOoalpham : rk(P :: Q :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQOoalphaeq HPQOoalpham1).
intuition.
Qed.

(* dans constructLemma(), requis par LQQpOoalpha *)
(* dans la couche 0 *)
Lemma LPQRQpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRQpOoalpha requis par la preuve de (?)PQRQpOoalpha pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRQpOoalpha requis par la preuve de (?)PQRQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRQpOoalpham3 : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRQpOoalpham4 : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 4).
{
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Qp :: Oo :: alpha :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}


assert(HPQRQpOoalphaM : rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRQpOoalpham : rk(P :: Q :: R :: Qp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HPQRQpOoalphaeq HPQRQpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpOoalpha : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Qp :: Oo :: alpha ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpOoalpha requis par la preuve de (?)QQpOoalpha pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQQpOoalpham2 : rk(Q :: Qp :: Oo :: alpha :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Oo :: alpha :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Oo :: alpha :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HQQpOoalphaM3 : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HalphaMtmp : rk(alpha :: nil) <= 1) by (solve_hyps_max Halphaeq HalphaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: Qp :: Oo :: nil) (alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: nil) ((Q :: Qp :: Oo :: nil) ++ (alpha :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: Qp :: Oo :: nil) (alpha :: nil) (nil) 2 1 0 HQQpOoMtmp HalphaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Qp :: Oo :: alpha ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : P :: R :: alpha ::   de rang : 2 et 2 *)
assert(HQQpOoalpham3 : rk(Q :: Qp :: Oo :: alpha :: nil) >= 3).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HPQRQpOoalphaeq : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) = 4) by (apply LPQRQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRQpOoalphamtmp : rk(P :: Q :: R :: Qp :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQRQpOoalphaeq HPQRQpOoalpham4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Qp :: Oo :: alpha :: nil) (P :: R :: alpha :: Q :: Qp :: Oo :: alpha :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: Qp :: Oo :: alpha :: nil) ((P :: R :: alpha :: nil) ++ (Q :: Qp :: Oo :: alpha :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRQpOoalphamtmp;try rewrite HT2 in HPQRQpOoalphamtmp.
	assert(HT := rule_4 (P :: R :: alpha :: nil) (Q :: Qp :: Oo :: alpha :: nil) (alpha :: nil) 4 1 2 HPQRQpOoalphamtmp Halphamtmp HPRalphaMtmp Hincl); apply HT.
}


assert(HQQpOoalphaM : rk(Q :: Qp :: Oo :: alpha ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpOoalpham : rk(Q :: Qp :: Oo :: alpha ::  nil) >= 1) by (solve_hyps_min HQQpOoalphaeq HQQpOoalpham1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(beta ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HbetaM : rk(beta ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max Hbetaeq HbetaM1).
assert(Hbetam : rk(beta ::  nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPbeta *)
(* dans constructLemma(), requis par LPPpQpbeta *)
(* dans constructLemma(), requis par LPPpQpRpOobeta *)
(* dans constructLemma(), requis par LPRPpQpRpOobeta *)
(* dans la couche 0 *)
Lemma LPQRPpQpRpOobeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpOobeta requis par la preuve de (?)PQRPpQpRpOobeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpOobeta requis par la preuve de (?)PQRPpQpRpOobeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOobetam3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOobetam4 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4).
{
	try assert(HPQRPpQpRpeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) = 4) by (apply LPQRPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 4 4 HPQRPpQpRpmtmp Hcomp Hincl);apply HT.
}


assert(HPQRPpQpRpOobetaM : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpRpOobetam : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) >= 1) by (solve_hyps_min HPQRPpQpRpOobetaeq HPQRPpQpRpOobetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpQpRpOobeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpOobeta requis par la preuve de (?)PRPpQpRpOobeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpOobeta requis par la preuve de (?)PRPpQpRpOobeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpOobeta requis par la preuve de (?)PRPpQpRpOobeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOobetam2 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOobetam3 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  de rang :  4 et 4 	 AiB : Qp :: Oo ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpQpRpOobetam4 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	try assert(HPQRPpQpRpOobetaeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) = 4) by (apply LPQRPpQpRpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpOobetamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpOobetaeq HPQRPpQpRpOobetam4).
	try assert(HQpOoeq : rk(Qp :: Oo :: nil) = 2) by (apply LQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpOomtmp : rk(Qp :: Oo :: nil) >= 2) by (solve_hyps_min HQpOoeq HQpOom2).
	assert(Hincl : incl (Qp :: Oo :: nil) (list_inter (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) ((Q :: Qp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpOobetamtmp;try rewrite HT2 in HPQRPpQpRpOobetamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) (Qp :: Oo :: nil) 4 2 2 HPQRPpQpRpOobetamtmp HQpOomtmp HQQpOoMtmp Hincl); apply HT.
}


assert(HPRPpQpRpOobetaM : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpRpOobetam : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) >= 1) by (solve_hyps_min HPRPpQpRpOobetaeq HPRPpQpRpOobetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpRpOobeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpOobeta requis par la preuve de (?)PPpQpRpOobeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpOobeta requis par la preuve de (?)PPpQpRpOobeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpOobeta requis par la preuve de (?)PPpQpRpOobeta pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOobetam2 : rk(P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOobetam3 : rk(P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: Oo :: beta ::  de rang :  4 et 4 	 AiB : Rp :: Oo ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPPpQpRpOobetam4 : rk(P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRPpQpRpOobetaeq : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) = 4) by (apply LPRPpQpRpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpQpRpOobetamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOobetaeq HPRPpQpRpOobetam4).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: beta :: nil) (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOobetamtmp;try rewrite HT2 in HPRPpQpRpOobetamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) (Rp :: Oo :: nil) 4 2 2 HPRPpQpRpOobetamtmp HRpOomtmp HRRpOoMtmp Hincl); apply HT.
}


assert(HPPpQpRpOobetaM : rk(P :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpRpOobetam : rk(P :: Pp :: Qp :: Rp :: Oo :: beta ::  nil) >= 1) by (solve_hyps_min HPPpQpRpOobetaeq HPPpQpRpOobetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Qp :: beta ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PPpQpbeta requis par la preuve de (?)PPpQpbeta pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PPpQpbeta requis par la preuve de (?)PPpQpbeta pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour PpQpbeta requis par la preuve de (?)PPpQpbeta pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpbeta requis par la preuve de (?)PPpQpbeta pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HPPpQpbetaM3 : rk(P :: Pp :: Qp :: beta :: nil) <= 3).
{
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: beta :: nil) (P :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Qp :: beta :: nil) ((P :: nil) ++ (Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (Pp :: Qp :: beta :: nil) (nil) 1 2 0 HPMtmp HPpQpbetaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpbetam2 : rk(P :: Pp :: Qp :: beta :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: beta :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: beta :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: Oo :: beta ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Rp :: Oo ::   de rang : 3 et 3 *)
assert(HPPpQpbetam3 : rk(P :: Pp :: Qp :: beta :: nil) >= 3).
{
	try assert(HPPpRpOoeq : rk(P :: Pp :: Rp :: Oo :: nil) = 3) by (apply LPPpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpRpOoMtmp : rk(P :: Pp :: Rp :: Oo :: nil) <= 3) by (solve_hyps_max HPPpRpOoeq HPPpRpOoM3).
	try assert(HPPpQpRpOobetaeq : rk(P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) = 4) by (apply LPPpQpRpOobeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpQpRpOobetamtmp : rk(P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) >= 4) by (solve_hyps_min HPPpQpRpOobetaeq HPPpQpRpOobetam4).
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: Oo :: beta :: nil) (P :: Pp :: Rp :: Oo :: P :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: Oo :: P :: Pp :: Qp :: beta :: nil) ((P :: Pp :: Rp :: Oo :: nil) ++ (P :: Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpOobetamtmp;try rewrite HT2 in HPPpQpRpOobetamtmp.
	assert(HT := rule_4 (P :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: beta :: nil) (P :: Pp :: nil) 4 2 3 HPPpQpRpOobetamtmp HPPpmtmp HPPpRpOoMtmp Hincl); apply HT.
}


assert(HPPpQpbetaM : rk(P :: Pp :: Qp :: beta ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpbetam : rk(P :: Pp :: Qp :: beta ::  nil) >= 1) by (solve_hyps_min HPPpQpbetaeq HPPpQpbetam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPbeta *)
(* dans la couche 0 *)
Lemma LPpQpbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HPpQpbetaM : rk(Pp :: Qp :: beta ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM3).
assert(HPpQpbetam : rk(Pp :: Qp :: beta ::  nil) >= 1) by (solve_hyps_min HPpQpbetaeq HPpQpbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPbeta : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: beta ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Pbeta requis par la preuve de (?)Pbeta pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPbetam2 : rk(P :: beta :: nil) >= 2).
{
	try assert(HPpQpbetaeq : rk(Pp :: Qp :: beta :: nil) = 2) by (apply LPpQpbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	try assert(HPPpQpbetaeq : rk(P :: Pp :: Qp :: beta :: nil) = 3) by (apply LPPpQpbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpQpbetamtmp : rk(P :: Pp :: Qp :: beta :: nil) >= 3) by (solve_hyps_min HPPpQpbetaeq HPPpQpbetam3).
	try assert(Hbetaeq : rk(beta :: nil) = 1) by (apply Lbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (P :: beta :: nil) (Pp :: Qp :: beta :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: beta :: nil) (P :: beta :: Pp :: Qp :: beta :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: beta :: Pp :: Qp :: beta :: nil) ((P :: beta :: nil) ++ (Pp :: Qp :: beta :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpbetamtmp;try rewrite HT2 in HPPpQpbetamtmp.
	assert(HT := rule_2 (P :: beta :: nil) (Pp :: Qp :: beta :: nil) (beta :: nil) 3 1 2 HPPpQpbetamtmp Hbetamtmp HPpQpbetaMtmp Hincl);apply HT.
}


assert(HPbetaM : rk(P :: beta ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HPbetaeq HPbetaM2).
assert(HPbetam : rk(P :: beta ::  nil) >= 1) by (solve_hyps_min HPbetaeq HPbetam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(gamma ::  nil) = 1.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HgammaM : rk(gamma ::  nil) <= 1) (* dim : 3 *) by (solve_hyps_max Hgammaeq HgammaM1).
assert(Hgammam : rk(gamma ::  nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LQgamma *)
(* dans constructLemma(), requis par LQQpRpgamma *)
(* dans constructLemma(), requis par LQQpRpOoalphagamma *)
(* dans constructLemma(), requis par LQPpQpRpOoalphagamma *)
(* dans constructLemma(), requis par LQRPpQpRpOoalphagamma *)
(* dans la couche 0 *)
Lemma LPQRPpQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpOoalphagamma requis par la preuve de (?)PQRPpQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpOoalphagamma requis par la preuve de (?)PQRPpQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HPQRPpQpRpeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) = 4) by (apply LPQRPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 4 4 HPQRPpQpRpmtmp Hcomp Hincl);apply HT.
}


assert(HPQRPpQpRpOoalphagammaM : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpRpOoalphagammam : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpRpOoalphagammaeq HPQRPpQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpRpOoalphagamma requis par la preuve de (?)QRPpQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpRpOoalphagamma requis par la preuve de (?)QRPpQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpOoalphagamma requis par la preuve de (?)QRPpQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpOoalphagamma requis par la preuve de (?)PQRPpQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpRpOoalphagamma requis par la preuve de (?)QRPpQpRpOoalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HQRPpQpRpOoalphagammam2 : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpRpOoalphagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPQRPpQpRpOoalphagammaeq HPQRPpQpRpOoalphagammam3).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (P :: Pp :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((P :: Pp :: nil) ++ (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpOoalphagammamtmp;try rewrite HT2 in HPQRPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: nil) 3 1 2 HPQRPpQpRpOoalphagammamtmp HPpmtmp HPPpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQRPpQpRpOoalphagammam3 : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpRpOoalphagammam4 : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQRPpQpRpOoalphagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LPQRPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpOoalphagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpOoalphagammaeq HPQRPpQpRpOoalphagammam4).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpOoalphagammamtmp;try rewrite HT2 in HPQRPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: Oo :: nil) 4 2 2 HPQRPpQpRpOoalphagammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQRPpQpRpOoalphagammaM1. try clear HPQRPpQpRpOoalphagammaM2. try clear HPQRPpQpRpOoalphagammaM3. try clear HPQRPpQpRpOoalphagammam4. try clear HPQRPpQpRpOoalphagammam3. try clear HPQRPpQpRpOoalphagammam2. try clear HPQRPpQpRpOoalphagammam1. 

assert(HQRPpQpRpOoalphagammaM : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpRpOoalphagammam : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpRpOoalphagammaeq HQRPpQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQPpQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpRpOoalphagamma requis par la preuve de (?)QPpQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpRpOoalphagamma requis par la preuve de (?)QPpQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpRpOoalphagamma requis par la preuve de (?)QPpQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpRpOoalphagammam2 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpRpOoalphagammam3 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Rp :: Oo ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpRpOoalphagammam4 : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HQRPpQpRpOoalphagammaeq : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LQRPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRPpQpRpOoalphagammamtmp : rk(Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpRpOoalphagammaeq HQRPpQpRpOoalphagammam4).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (R :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (R :: Rp :: Oo :: Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((R :: Rp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpRpOoalphagammamtmp;try rewrite HT2 in HQRPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Rp :: Oo :: nil) 4 2 2 HQRPpQpRpOoalphagammamtmp HRpOomtmp HRRpOoMtmp Hincl); apply HT.
}


assert(HQPpQpRpOoalphagammaM : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQPpQpRpOoalphagammam : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HQPpQpRpOoalphagammaeq HQPpQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpRpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpRpOoalphagamma requis par la preuve de (?)QQpRpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQQpRpOoalphagammam2 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQQpRpOoalphagammam3 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HQRpOoeq : rk(Q :: Rp :: Oo :: nil) = 3) by (apply LQRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRpOomtmp : rk(Q :: Rp :: Oo :: nil) >= 3) by (solve_hyps_min HQRpOoeq HQRpOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Q :: Rp :: Oo :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Rp :: Oo :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) 3 3 HQRpOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Rp :: alpha ::  de rang :  2 et 2 	 A : Pp :: Rp :: alpha ::   de rang : 2 et 2 *)
assert(HQQpRpOoalphagammam4 : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	try assert(HQPpQpRpOoalphagammaeq : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LQPpQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQPpQpRpOoalphagammamtmp : rk(Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HQPpQpRpOoalphagammaeq HQPpQpRpOoalphagammam4).
	try assert(HRpalphaeq : rk(Rp :: alpha :: nil) = 2) by (apply LRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpalphamtmp : rk(Rp :: alpha :: nil) >= 2) by (solve_hyps_min HRpalphaeq HRpalpham2).
	assert(Hincl : incl (Rp :: alpha :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpRpOoalphagammamtmp;try rewrite HT2 in HQPpQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Pp :: Rp :: alpha :: nil) (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Rp :: alpha :: nil) 4 2 2 HQPpQpRpOoalphagammamtmp HRpalphamtmp HPpRpalphaMtmp Hincl); apply HT.
}
try clear HRpalphaM1. try clear HRpalphaM2. try clear HRpalphaM3. try clear HRpalpham4. try clear HRpalpham3. try clear HRpalpham2. try clear HRpalpham1. 

assert(HQQpRpOoalphagammaM : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpRpOoalphagammam : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HQQpRpOoalphagammaeq HQQpRpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQQpRpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: Qp :: Rp :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour QpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QQpRpgamma requis par la preuve de (?)QQpRpgamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HQQpRpgammaM3 : rk(Q :: Qp :: Rp :: gamma :: nil) <= 3).
{
	try assert(HQeq : rk(Q :: nil) = 1) by (apply LQ with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQMtmp : rk(Q :: nil) <= 1) by (solve_hyps_max HQeq HQM1).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Q :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: gamma :: nil) (Q :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Rp :: gamma :: nil) ((Q :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Q :: nil) (Qp :: Rp :: gamma :: nil) (nil) 1 2 0 HQMtmp HQpRpgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQQpRpgammam2 : rk(Q :: Qp :: Rp :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Qp :: Rp :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Qp :: Rp :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: Qp :: Rp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HQQpRpgammam3 : rk(Q :: Qp :: Rp :: gamma :: nil) >= 3).
{
	try assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	try assert(HQQpRpOoalphagammaeq : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) = 4) by (apply LQQpRpOoalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpRpOoalphagammamtmp : rk(Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HQQpRpOoalphagammaeq HQQpRpOoalphagammam4).
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: Oo :: alpha :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: Q :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: Q :: Qp :: Rp :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (Q :: Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQQpRpOoalphagammamtmp;try rewrite HT2 in HQQpRpOoalphagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (Q :: Qp :: Rp :: gamma :: nil) (Q :: Qp :: nil) 4 2 3 HQQpRpOoalphagammamtmp HQQpmtmp HQQpOoalphaMtmp Hincl); apply HT.
}


assert(HQQpRpgammaM : rk(Q :: Qp :: Rp :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQQpRpgammam : rk(Q :: Qp :: Rp :: gamma ::  nil) >= 1) by (solve_hyps_min HQQpRpgammaeq HQQpRpgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LQgamma *)
(* dans la couche 0 *)
Lemma LQpRpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQpRpgammaM : rk(Qp :: Rp :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM3).
assert(HQpRpgammam : rk(Qp :: Rp :: gamma ::  nil) >= 1) by (solve_hyps_min HQpRpgammaeq HQpRpgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Qgamma requis par la preuve de (?)Qgamma pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HQgammam2 : rk(Q :: gamma :: nil) >= 2).
{
	try assert(HQpRpgammaeq : rk(Qp :: Rp :: gamma :: nil) = 2) by (apply LQpRpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	try assert(HQQpRpgammaeq : rk(Q :: Qp :: Rp :: gamma :: nil) = 3) by (apply LQQpRpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpRpgammamtmp : rk(Q :: Qp :: Rp :: gamma :: nil) >= 3) by (solve_hyps_min HQQpRpgammaeq HQQpRpgammam3).
	try assert(Hgammaeq : rk(gamma :: nil) = 1) by (apply Lgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: gamma :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Qp :: Rp :: gamma :: nil) (Q :: gamma :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: gamma :: Qp :: Rp :: gamma :: nil) ((Q :: gamma :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQQpRpgammamtmp;try rewrite HT2 in HQQpRpgammamtmp.
	assert(HT := rule_2 (Q :: gamma :: nil) (Qp :: Rp :: gamma :: nil) (gamma :: nil) 3 1 2 HQQpRpgammamtmp Hgammamtmp HQpRpgammaMtmp Hincl);apply HT.
}


assert(HQgammaM : rk(Q :: gamma ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HQgammaeq HQgammaM2).
assert(HQgammam : rk(Q :: gamma ::  nil) >= 1) by (solve_hyps_min HQgammaeq HQgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQgamma *)
(* dans la couche 0 *)
Lemma LPQRgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQRgamma requis par la preuve de (?)PQRgamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour QRgamma requis par la preuve de (?)PQRgamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRgamma requis par la preuve de (?)PQRgamma pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et 5*)
assert(HPQRgammaM3 : rk(P :: Q :: R :: gamma :: nil) <= 3).
{
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPMtmp : rk(P :: nil) <= 1) by (solve_hyps_max HPeq HPM1).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: gamma :: nil) (P :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: R :: gamma :: nil) ((P :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: nil) (Q :: R :: gamma :: nil) (nil) 1 2 0 HPMtmp HQRgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRgammam3 : rk(P :: Q :: R :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


assert(HPQRgammaM : rk(P :: Q :: R :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRgammam : rk(P :: Q :: R :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRgammaeq HPQRgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQgamma *)
(* dans la couche 0 *)
Lemma LQRgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

assert(HQRgammaM : rk(Q :: R :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HQRgammaeq HQRgammaM3).
assert(HQRgammam : rk(Q :: R :: gamma ::  nil) >= 1) by (solve_hyps_min HQRgammaeq HQRgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQgamma requis par la preuve de (?)PQgamma pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOogamma requis par la preuve de (?)PQgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOogamma requis par la preuve de (?)PQPpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOogamma requis par la preuve de (?)PQPpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOogammam2 : rk(P :: Q :: Pp :: Oo :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOogammam3 : rk(P :: Q :: Pp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PQgamma requis par la preuve de (?)PQgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQgammam2 : rk(P :: Q :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOogammamtmp : rk(P :: Q :: Pp :: Oo :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOogammaeq HPQPpOogammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOogammamtmp;try rewrite HT2 in HPQPpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOogammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOogammaM1. try clear HPQPpOogammaM2. try clear HPQPpOogammaM3. try clear HPQPpOogammam4. try clear HPQPpOogammam3. try clear HPQPpOogammam2. try clear HPQPpOogammam1. 

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HPQgammam3 : rk(P :: Q :: gamma :: nil) >= 3).
{
	try assert(HQRgammaeq : rk(Q :: R :: gamma :: nil) = 2) by (apply LQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	try assert(HPQRgammaeq : rk(P :: Q :: R :: gamma :: nil) = 3) by (apply LPQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRgammamtmp : rk(P :: Q :: R :: gamma :: nil) >= 3) by (solve_hyps_min HPQRgammaeq HPQRgammam3).
	try assert(HQgammaeq : rk(Q :: gamma :: nil) = 2) by (apply LQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQgammamtmp : rk(Q :: gamma :: nil) >= 2) by (solve_hyps_min HQgammaeq HQgammam2).
	assert(Hincl : incl (Q :: gamma :: nil) (list_inter (P :: Q :: gamma :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: gamma :: nil) (P :: Q :: gamma :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: gamma :: Q :: R :: gamma :: nil) ((P :: Q :: gamma :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRgammamtmp;try rewrite HT2 in HPQRgammamtmp.
	assert(HT := rule_2 (P :: Q :: gamma :: nil) (Q :: R :: gamma :: nil) (Q :: gamma :: nil) 3 2 2 HPQRgammamtmp HQgammamtmp HQRgammaMtmp Hincl);apply HT.
}
try clear HQgammaM1. try clear HQgammaM2. try clear HQgammaM3. try clear HQgammam4. try clear HQgammam3. try clear HQgammam2. try clear HQgammam1. 

assert(HPQgammaM : rk(P :: Q :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPQgammaeq HPQgammaM3).
assert(HPQgammam : rk(P :: Q :: gamma ::  nil) >= 1) by (solve_hyps_min HPQgammaeq HPQgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpgamma *)
(* dans constructLemma(), requis par LQRPpQpgamma *)
(* dans constructLemma(), requis par LQRPpQpOogamma *)
(* dans la couche 0 *)
Lemma LPQRPpQpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOogammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOogammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4).
{
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}


assert(HPQRPpQpOogammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOogammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpOogamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpOogamma requis par la preuve de (?)QRPpQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpOogamma requis par la preuve de (?)QRPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)QRPpQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOogamma requis par la preuve de (?)PQRPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOogammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpOogamma requis par la preuve de (?)QRPpQpOogamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HQRPpQpOogammam2 : rk(Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpOogammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam3).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (P :: Pp :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) ((P :: Pp :: nil) ++ (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOogammamtmp;try rewrite HT2 in HPQRPpQpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (Pp :: nil) 3 1 2 HPQRPpQpOogammamtmp HPpmtmp HPPpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQRPpQpOogammam3 : rk(Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HQROoeq : rk(Q :: R :: Oo :: nil) = 3) by (apply LQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQROomtmp : rk(Q :: R :: Oo :: nil) >= 3) by (solve_hyps_min HQROoeq HQROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Q :: R :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: R :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HQROomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpOogammam4 : rk(Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQRPpQpOogammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) = 4) by (apply LPQRPpQpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpOogammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam4).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOogammamtmp;try rewrite HT2 in HPQRPpQpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (Pp :: Oo :: nil) 4 2 2 HPQRPpQpOogammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}


assert(HQRPpQpOogammaM : rk(Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpOogammam : rk(Q :: R :: Pp :: Qp :: Oo :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpOogammaeq HQRPpQpOogammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Pp :: Qp :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpgamma requis par la preuve de (?)QRPpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpgamma requis par la preuve de (?)QRPpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpgamma requis par la preuve de (?)QRPpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpgamma requis par la preuve de (?)PQRPpQpgamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpgammam3 : rk(P :: Q :: R :: Pp :: Qp :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpgamma requis par la preuve de (?)QRPpQpgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HQRPpQpgammam2 : rk(Q :: R :: Pp :: Qp :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpgammamtmp : rk(P :: Q :: R :: Pp :: Qp :: gamma :: nil) >= 3) by (solve_hyps_min HPQRPpQpgammaeq HPQRPpQpgammam3).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: gamma :: nil) (P :: Pp :: Q :: R :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Q :: R :: Pp :: Qp :: gamma :: nil) ((P :: Pp :: nil) ++ (Q :: R :: Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpgammamtmp;try rewrite HT2 in HPQRPpQpgammamtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil) (Pp :: nil) 3 1 2 HPQRPpQpgammamtmp HPpmtmp HPPpMtmp Hincl); apply HT.
}
try clear HPQRPpQpgammaM1. try clear HPQRPpQpgammaM2. try clear HPQRPpQpgammaM3. try clear HPQRPpQpgammam4. try clear HPQRPpQpgammam3. try clear HPQRPpQpgammam2. try clear HPQRPpQpgammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpgammam3 : rk(Q :: R :: Pp :: Qp :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQRPpQpOogammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) = 4) by (apply LPQRPpQpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpOogammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOogammaeq HPQRPpQpOogammam4).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOogammamtmp;try rewrite HT2 in HPQRPpQpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil) (Pp :: nil) 4 1 2 HPQRPpQpOogammamtmp HPpmtmp HPPpOoMtmp Hincl); apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: Oo :: gamma ::  de rang :  4 et 4 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpgammam4 : rk(Q :: R :: Pp :: Qp :: gamma :: nil) >= 4).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	try assert(HQRPpQpOogammaeq : rk(Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) = 4) by (apply LQRPpQpOogamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRPpQpOogammamtmp : rk(Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpOogammaeq HQRPpQpOogammam4).
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: Oo :: gamma :: nil) (Q :: Qp :: Oo :: Q :: R :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Q :: R :: Pp :: Qp :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpOogammamtmp;try rewrite HT2 in HQRPpQpOogammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Q :: R :: Pp :: Qp :: gamma :: nil) (Q :: Qp :: nil) 4 2 2 HQRPpQpOogammamtmp HQQpmtmp HQQpOoMtmp Hincl); apply HT.
}


assert(HQRPpQpgammaM : rk(Q :: R :: Pp :: Qp :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpgammam : rk(Q :: R :: Pp :: Qp :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpgammaeq HQRPpQpgammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpgamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpgamma requis par la preuve de (?)PpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOogamma requis par la preuve de (?)PpQpgamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpOogamma requis par la preuve de (?)QPpQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpOogamma requis par la preuve de (?)PQPpQpOogamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpOogamma requis par la preuve de (?)PQPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOogammam2 : rk(P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOogammam3 : rk(P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOogamma requis par la preuve de (?)QPpQpOogamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOogamma requis par la preuve de (?)QPpQpOogamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpOogammam2 : rk(Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Oo :: gamma ::  de rang :  3 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpOogammam3 : rk(Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpQpOogammamtmp : rk(P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpQpOogammaeq HPQPpQpOogammam3).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Oo :: gamma :: nil) (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Oo :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpOogammamtmp;try rewrite HT2 in HPQPpQpOogammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: gamma :: nil) (Pp :: Oo :: nil) 3 2 2 HPQPpQpOogammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpQpOogammaM1. try clear HPQPpQpOogammaM2. try clear HPQPpQpOogammaM3. try clear HPQPpQpOogammam4. try clear HPQPpQpOogammam3. try clear HPQPpQpOogammam2. try clear HPQPpQpOogammam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour PpQpgamma requis par la preuve de (?)PpQpgamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: gamma ::  de rang :  3 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPpQpgammam2 : rk(Pp :: Qp :: gamma :: nil) >= 2).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQPpQpOogammamtmp : rk(Q :: Pp :: Qp :: Oo :: gamma :: nil) >= 3) by (solve_hyps_min HQPpQpOogammaeq HQPpQpOogammam3).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: gamma :: nil) (Q :: Qp :: Oo :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Pp :: Qp :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOogammamtmp;try rewrite HT2 in HQPpQpOogammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Pp :: Qp :: gamma :: nil) (Qp :: nil) 3 1 2 HQPpQpOogammamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQPpQpOogammaM1. try clear HQPpQpOogammaM2. try clear HQPpQpOogammaM3. try clear HQPpQpOogammam4. try clear HQPpQpOogammam3. try clear HQPpQpOogammam2. try clear HQPpQpOogammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: gamma ::  de rang :  4 et 4 	 AiB : gamma ::  de rang :  1 et 1 	 A : Q :: R :: gamma ::   de rang : 2 et 2 *)
assert(HPpQpgammam3 : rk(Pp :: Qp :: gamma :: nil) >= 3).
{
	try assert(HQRgammaeq : rk(Q :: R :: gamma :: nil) = 2) by (apply LQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	try assert(HQRPpQpgammaeq : rk(Q :: R :: Pp :: Qp :: gamma :: nil) = 4) by (apply LQRPpQpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRPpQpgammamtmp : rk(Q :: R :: Pp :: Qp :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpgammaeq HQRPpQpgammam4).
	try assert(Hgammaeq : rk(gamma :: nil) = 1) by (apply Lgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: R :: gamma :: nil) (Pp :: Qp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: gamma :: nil) (Q :: R :: gamma :: Pp :: Qp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: R :: gamma :: Pp :: Qp :: gamma :: nil) ((Q :: R :: gamma :: nil) ++ (Pp :: Qp :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpgammamtmp;try rewrite HT2 in HQRPpQpgammamtmp.
	assert(HT := rule_4 (Q :: R :: gamma :: nil) (Pp :: Qp :: gamma :: nil) (gamma :: nil) 4 1 2 HQRPpQpgammamtmp Hgammamtmp HQRgammaMtmp Hincl); apply HT.
}


assert(HPpQpgammaM : rk(Pp :: Qp :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HPpQpgammaeq HPpQpgammaM3).
assert(HPpQpgammam : rk(Pp :: Qp :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpgammaeq HPpQpgammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPQalphagamma *)
(* dans la couche 0 *)
Lemma LPQRalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRalphagamma requis par la preuve de (?)PQRalphagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRalphagamma requis par la preuve de (?)PQRalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRalphagammam3 : rk(P :: Q :: R :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: alpha :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPQRalphagammaM3 : rk(P :: Q :: R :: alpha :: gamma :: nil) <= 3).
{
	try assert(HPRalphaeq : rk(P :: R :: alpha :: nil) = 2) by (apply LPRalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRalphaMtmp : rk(P :: R :: alpha :: nil) <= 2) by (solve_hyps_max HPRalphaeq HPRalphaM2).
	try assert(HQRgammaeq : rk(Q :: R :: gamma :: nil) = 2) by (apply LQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	try assert(HReq : rk(R :: nil) = 1) by (apply LR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRmtmp : rk(R :: nil) >= 1) by (solve_hyps_min HReq HRm1).
	assert(Hincl : incl (R :: nil) (list_inter (P :: R :: alpha :: nil) (Q :: R :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: alpha :: gamma :: nil) (P :: R :: alpha :: Q :: R :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: alpha :: Q :: R :: gamma :: nil) ((P :: R :: alpha :: nil) ++ (Q :: R :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: R :: alpha :: nil) (Q :: R :: gamma :: nil) (R :: nil) 2 2 1 HPRalphaMtmp HQRgammaMtmp HRmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HRM1. try clear HRM2. try clear HRM3. try clear HRm4. try clear HRm3. try clear HRm2. try clear HRm1. 

assert(HPQRalphagammaM : rk(P :: Q :: R :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRalphagammam : rk(P :: Q :: R :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRalphagammaeq HPQRalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam2 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam3 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam4 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HPQOoalphaeq : rk(P :: Q :: Oo :: alpha :: nil) = 4) by (apply LPQOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOoalphamtmp : rk(P :: Q :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQOoalphaeq HPQOoalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 4 4 HPQOoalphamtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOoalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOoalphagamma requis par la preuve de (?)PQPpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOoalphagamma requis par la preuve de (?)PQPpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphagammam2 : rk(P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphagammam3 : rk(P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphagamma requis par la preuve de (?)PQalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQalphagammam2 : rk(P :: Q :: alpha :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOoalphagammamtmp : rk(P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOoalphagammaeq HPQPpOoalphagammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: alpha :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: alpha :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOoalphagammamtmp;try rewrite HT2 in HPQPpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOoalphagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOoalphagammaM1. try clear HPQPpOoalphagammaM2. try clear HPQPpOoalphagammaM3. try clear HPQPpOoalphagammam4. try clear HPQPpOoalphagammam3. try clear HPQPpOoalphagammam2. try clear HPQPpOoalphagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Qp :: Oo :: alpha :: gamma ::  de rang :  4 et 4 	 AiB : Q :: alpha ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HPQalphagammam3 : rk(P :: Q :: alpha :: gamma :: nil) >= 3).
{
	try assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	assert(HPQQpOoalphagammamtmp : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 4) by (solve_hyps_min HPQQpOoalphagammaeq HPQQpOoalphagammam4).
	try assert(HQalphaeq : rk(Q :: alpha :: nil) = 2) by (apply LQalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQalphamtmp : rk(Q :: alpha :: nil) >= 2) by (solve_hyps_min HQalphaeq HQalpham2).
	assert(Hincl : incl (Q :: alpha :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (P :: Q :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQQpOoalphagammamtmp;try rewrite HT2 in HPQQpOoalphagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: gamma :: nil) (Q :: alpha :: nil) 4 2 3 HPQQpOoalphagammamtmp HQalphamtmp HQQpOoalphaMtmp Hincl); apply HT.
}
try clear HPQQpOoalphagammaM1. try clear HPQQpOoalphagammaM2. try clear HPQQpOoalphagammaM3. try clear HPQQpOoalphagammam4. try clear HPQQpOoalphagammam3. try clear HPQQpOoalphagammam2. try clear HPQQpOoalphagammam1. 

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQalphagammaM3 : rk(P :: Q :: alpha :: gamma :: nil) <= 3).
{
	try assert(HPQRalphagammaeq : rk(P :: Q :: R :: alpha :: gamma :: nil) = 3) by (apply LPQRalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRalphagammaMtmp : rk(P :: Q :: R :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPQRalphagammaeq HPQRalphagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: alpha :: gamma :: nil) (P :: Q :: R :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P :: Q :: alpha :: gamma :: nil) (P :: Q :: R :: alpha :: gamma :: nil) 3 3 HPQRalphagammaMtmp Hcomp Hincl);apply HT.
}


assert(HPQalphagammaM : rk(P :: Q :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQalphagammam : rk(P :: Q :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQalphagammaeq HPQalphagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpalphagamma *)
(* dans la couche 0 *)
Lemma LPpQpRpalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpRpalphagamma requis par la preuve de (?)PpQpRpalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpRpalphagammam3 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPpQpRpalphagammaM3 : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) <= 3).
{
	try assert(HPpRpalphaeq : rk(Pp :: Rp :: alpha :: nil) = 2) by (apply LPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpRpalphaMtmp : rk(Pp :: Rp :: alpha :: nil) <= 2) by (solve_hyps_max HPpRpalphaeq HPpRpalphaM2).
	try assert(HQpRpgammaeq : rk(Qp :: Rp :: gamma :: nil) = 2) by (apply LQpRpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpRpgammaMtmp : rk(Qp :: Rp :: gamma :: nil) <= 2) by (solve_hyps_max HQpRpgammaeq HQpRpgammaM2).
	try assert(HRpeq : rk(Rp :: nil) = 1) by (apply LRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpmtmp : rk(Rp :: nil) >= 1) by (solve_hyps_min HRpeq HRpm1).
	assert(Hincl : incl (Rp :: nil) (list_inter (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: Rp :: alpha :: gamma :: nil) (Pp :: Rp :: alpha :: Qp :: Rp :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Rp :: alpha :: Qp :: Rp :: gamma :: nil) ((Pp :: Rp :: alpha :: nil) ++ (Qp :: Rp :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Rp :: alpha :: nil) (Qp :: Rp :: gamma :: nil) (Rp :: nil) 2 2 1 HPpRpalphaMtmp HQpRpgammaMtmp HRpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPpQpRpalphagammaM : rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpRpalphagammam : rk(Pp :: Qp :: Rp :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpRpalphagammaeq HPpQpRpalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: alpha :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOoalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpOoalphagamma requis par la preuve de (?)QPpQpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpOoalphagamma requis par la preuve de (?)PQPpQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpOoalphagamma requis par la preuve de (?)PQPpQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalphagammam2 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalphagammam3 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOoalphagamma requis par la preuve de (?)QPpQpOoalphagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOoalphagamma requis par la preuve de (?)QPpQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpOoalphagammam2 : rk(Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpOoalphagammam3 : rk(Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpQpOoalphagammamtmp : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpQpOoalphagammaeq HPQPpQpOoalphagammam3).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpOoalphagammamtmp;try rewrite HT2 in HPQPpQpOoalphagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) (Pp :: Oo :: nil) 3 2 2 HPQPpQpOoalphagammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpQpOoalphagammaM1. try clear HPQPpQpOoalphagammaM2. try clear HPQPpQpOoalphagammaM3. try clear HPQPpQpOoalphagammam4. try clear HPQPpQpOoalphagammam3. try clear HPQPpQpOoalphagammam2. try clear HPQPpQpOoalphagammam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpalphagamma requis par la preuve de (?)PpQpalphagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: alpha :: gamma ::  de rang :  3 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPpQpalphagammam2 : rk(Pp :: Qp :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQPpQpOoalphagammamtmp : rk(Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) >= 3) by (solve_hyps_min HQPpQpOoalphagammaeq HQPpQpOoalphagammam3).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: alpha :: gamma :: nil) (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Pp :: Qp :: alpha :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOoalphagammamtmp;try rewrite HT2 in HQPpQpOoalphagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: gamma :: nil) (Qp :: nil) 3 1 2 HQPpQpOoalphagammamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQPpQpOoalphagammaM1. try clear HQPpQpOoalphagammaM2. try clear HQPpQpOoalphagammaM3. try clear HQPpQpOoalphagammam4. try clear HQPpQpOoalphagammam3. try clear HQPpQpOoalphagammam2. try clear HQPpQpOoalphagammam1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphagammam3 : rk(Pp :: Qp :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphagammaM3 : rk(Pp :: Qp :: alpha :: gamma :: nil) <= 3).
{
	try assert(HPpQpRpalphagammaeq : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) = 3) by (apply LPpQpRpalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpalphagammaMtmp : rk(Pp :: Qp :: Rp :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpRpalphagammaeq HPpQpRpalphagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: gamma :: nil) 3 3 HPpQpRpalphagammaMtmp Hcomp Hincl);apply HT.
}


assert(HPpQpalphagammaM : rk(Pp :: Qp :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpalphagammam : rk(Pp :: Qp :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpalphagammaeq HPpQpalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQQpOoalphagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Qp :: Oo :: alpha :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQQpOoalphagamma requis par la preuve de (?)PQQpOoalphagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam2 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam3 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphagammam4 : rk(P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) >= 4).
{
	try assert(HPQOoalphaeq : rk(P :: Q :: Oo :: alpha :: nil) = 4) by (apply LPQOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOoalphamtmp : rk(P :: Q :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQOoalphaeq HPQOoalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: gamma :: nil) 4 4 HPQOoalphamtmp Hcomp Hincl);apply HT.
}


assert(HPQQpOoalphagammaM : rk(P :: Q :: Qp :: Oo :: alpha :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQQpOoalphagammam : rk(P :: Q :: Qp :: Oo :: alpha :: gamma ::  nil) >= 1) by (solve_hyps_min HPQQpOoalphagammaeq HPQQpOoalphagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOobetagamma requis par la preuve de (?)PQbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOobetagamma requis par la preuve de (?)PQPpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOobetagamma requis par la preuve de (?)PQPpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOobetagammam2 : rk(P :: Q :: Pp :: Oo :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOobetagammam3 : rk(P :: Q :: Pp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQbetagamma requis par la preuve de (?)PQbetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: beta :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQbetagammam2 : rk(P :: Q :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOobetagammamtmp : rk(P :: Q :: Pp :: Oo :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOobetagammaeq HPQPpOobetagammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOobetagammamtmp;try rewrite HT2 in HPQPpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: beta :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOobetagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOobetagammaM1. try clear HPQPpOobetagammaM2. try clear HPQPpOobetagammaM3. try clear HPQPpOobetagammam4. try clear HPQPpOobetagammam3. try clear HPQPpOobetagammam2. try clear HPQPpOobetagammam1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPQbetagammaM3 : rk(P :: Q :: beta :: gamma :: nil) <= 3).
{
	try assert(HPQbetaeq : rk(P :: Q :: beta :: nil) = 2) by (apply LPQbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	try assert(Hgammaeq : rk(gamma :: nil) = 1) by (apply Lgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HgammaMtmp : rk(gamma :: nil) <= 1) by (solve_hyps_max Hgammaeq HgammaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P :: Q :: beta :: nil) (gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: beta :: gamma :: nil) (P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: beta :: gamma :: nil) ((P :: Q :: beta :: nil) ++ (gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Q :: beta :: nil) (gamma :: nil) (nil) 2 1 0 HPQbetaMtmp HgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQbetagammam3 : rk(P :: Q :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQgammaeq : rk(P :: Q :: gamma :: nil) = 3) by (apply LPQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQgammamtmp : rk(P :: Q :: gamma :: nil) >= 3) by (solve_hyps_min HPQgammaeq HPQgammam3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: gamma :: nil) (P :: Q :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: gamma :: nil) (P :: Q :: beta :: gamma :: nil) 3 3 HPQgammamtmp Hcomp Hincl);apply HT.
}


assert(HPQbetagammaM : rk(P :: Q :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQbetagammam : rk(P :: Q :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQbetagammaeq HPQbetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPpQpbetagamma *)
(* dans constructLemma(), requis par LQRPpQpbetagamma *)
(* dans constructLemma(), requis par LQRPpQpOobetagamma *)
(* dans la couche 0 *)
Lemma LPQRPpQpOobetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOobetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOobetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQROoeq : rk(P :: Q :: R :: Oo :: nil) = 4) by (apply LPQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQROomtmp : rk(P :: Q :: R :: Oo :: nil) >= 4) by (solve_hyps_min HPQROoeq HPQROom4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Oo :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 4 4 HPQROomtmp Hcomp Hincl);apply HT.
}


assert(HPQRPpQpOobetagammaM : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpOobetagammam : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpOobetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpOobetagamma requis par la preuve de (?)QRPpQpOobetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpOobetagamma requis par la preuve de (?)QRPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)QRPpQpOobetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpOobetagamma requis par la preuve de (?)PQRPpQpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpOobetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpOobetagamma requis par la preuve de (?)QRPpQpOobetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HQRPpQpOobetagammam2 : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam3).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) ((P :: Pp :: nil) ++ (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOobetagammamtmp;try rewrite HT2 in HPQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (Pp :: nil) 3 1 2 HPQRPpQpOobetagammamtmp HPpmtmp HPPpMtmp Hincl); apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQRPpQpOobetagammam3 : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HQROoeq : rk(Q :: R :: Oo :: nil) = 3) by (apply LQROo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQROomtmp : rk(Q :: R :: Oo :: nil) >= 3) by (solve_hyps_min HQROoeq HQROom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Q :: R :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: R :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 3 3 HQROomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpOobetagammam4 : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQRPpQpOobetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpOobetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam4).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOobetagammamtmp;try rewrite HT2 in HPQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (Pp :: Oo :: nil) 4 2 2 HPQRPpQpOobetagammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}


assert(HQRPpQpOobetagammaM : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpOobetagammam : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpOobetagammaeq HQRPpQpOobetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LQRPpQpbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpbetagamma requis par la preuve de (?)PQRPpQpbetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpbetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QRPpQpbetagamma requis par la preuve de (?)QRPpQpbetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp ::   de rang : 2 et 2 *)
assert(HQRPpQpbetagammam2 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpMtmp : rk(P :: Pp :: nil) <= 2) by (solve_hyps_max HPPpeq HPPpM2).
	assert(HPQRPpQpbetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQRPpQpbetagammaeq HPQRPpQpbetagammam3).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (P :: Pp :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((P :: Pp :: nil) ++ (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpbetagammamtmp;try rewrite HT2 in HPQRPpQpbetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Pp :: nil) 3 1 2 HPQRPpQpbetagammamtmp HPpmtmp HPPpMtmp Hincl); apply HT.
}
try clear HPQRPpQpbetagammaM1. try clear HPQRPpQpbetagammaM2. try clear HPQRPpQpbetagammaM3. try clear HPQRPpQpbetagammam4. try clear HPQRPpQpbetagammam3. try clear HPQRPpQpbetagammam2. try clear HPQRPpQpbetagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpbetagammam3 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	try assert(HPQRPpQpOobetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpOobetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpOobetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpOobetagammaeq HPQRPpQpOobetagammam4).
	try assert(HPpeq : rk(Pp :: nil) = 1) by (apply LPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpmtmp : rk(Pp :: nil) >= 1) by (solve_hyps_min HPpeq HPpm1).
	assert(Hincl : incl (Pp :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpOobetagammamtmp;try rewrite HT2 in HPQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Pp :: nil) 4 1 2 HPQRPpQpOobetagammamtmp HPpmtmp HPPpOoMtmp Hincl); apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Q :: Qp ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HQRPpQpbetagammam4 : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	try assert(HQRPpQpOobetagammaeq : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) = 4) by (apply LQRPpQpOobetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRPpQpOobetagammamtmp : rk(Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpOobetagammaeq HQRPpQpOobetagammam4).
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hincl : incl (Q :: Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (Q :: Qp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Q :: R :: Pp :: Qp :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Q :: R :: Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpOobetagammamtmp;try rewrite HT2 in HQRPpQpOobetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Q :: Qp :: nil) 4 2 2 HQRPpQpOobetagammamtmp HQQpmtmp HQQpOoMtmp Hincl); apply HT.
}


assert(HQRPpQpbetagammaM : rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HQRPpQpbetagammam : rk(Q :: R :: Pp :: Qp :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HQRPpQpbetagammaeq HQRPpQpbetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpbetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOobetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpOobetagamma requis par la preuve de (?)QPpQpOobetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpOobetagamma requis par la preuve de (?)PQPpQpOobetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpOobetagamma requis par la preuve de (?)PQPpQpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOobetagammam2 : rk(P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOobetagammam3 : rk(P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOobetagamma requis par la preuve de (?)QPpQpOobetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOobetagamma requis par la preuve de (?)QPpQpOobetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpOobetagammam2 : rk(Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpOobetagammam3 : rk(Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpQpOobetagammamtmp : rk(P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpQpOobetagammaeq HPQPpQpOobetagammam3).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpOobetagammamtmp;try rewrite HT2 in HPQPpQpOobetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (Pp :: Oo :: nil) 3 2 2 HPQPpQpOobetagammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpQpOobetagammaM1. try clear HPQPpQpOobetagammaM2. try clear HPQPpQpOobetagammaM3. try clear HPQPpQpOobetagammam4. try clear HPQPpQpOobetagammam3. try clear HPQPpQpOobetagammam2. try clear HPQPpQpOobetagammam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpbetagamma requis par la preuve de (?)PpQpbetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPpQpbetagammam2 : rk(Pp :: Qp :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQPpQpOobetagammamtmp : rk(Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HQPpQpOobetagammaeq HQPpQpOobetagammam3).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: beta :: gamma :: nil) (Q :: Qp :: Oo :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Pp :: Qp :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOobetagammamtmp;try rewrite HT2 in HQPpQpOobetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Pp :: Qp :: beta :: gamma :: nil) (Qp :: nil) 3 1 2 HQPpQpOobetagammamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQPpQpOobetagammaM1. try clear HQPpQpOobetagammaM2. try clear HQPpQpOobetagammaM3. try clear HQPpQpOobetagammam4. try clear HQPpQpOobetagammam3. try clear HQPpQpOobetagammam2. try clear HQPpQpOobetagammam1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HPpQpbetagammaM3 : rk(Pp :: Qp :: beta :: gamma :: nil) <= 3).
{
	try assert(HPpQpbetaeq : rk(Pp :: Qp :: beta :: nil) = 2) by (apply LPpQpbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpbetaMtmp : rk(Pp :: Qp :: beta :: nil) <= 2) by (solve_hyps_max HPpQpbetaeq HPpQpbetaM2).
	try assert(Hgammaeq : rk(gamma :: nil) = 1) by (apply Lgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HgammaMtmp : rk(gamma :: nil) <= 1) by (solve_hyps_max Hgammaeq HgammaM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Pp :: Qp :: beta :: nil) (gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: beta :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: beta :: gamma :: nil) ((Pp :: Qp :: beta :: nil) ++ (gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Qp :: beta :: nil) (gamma :: nil) (nil) 2 1 0 HPpQpbetaMtmp HgammaMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : Q :: R :: Pp :: Qp :: beta :: gamma ::  de rang :  4 et 4 	 AiB : gamma ::  de rang :  1 et 1 	 A : Q :: R :: gamma ::   de rang : 2 et 2 *)
assert(HPpQpbetagammam3 : rk(Pp :: Qp :: beta :: gamma :: nil) >= 3).
{
	try assert(HQRgammaeq : rk(Q :: R :: gamma :: nil) = 2) by (apply LQRgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRgammaMtmp : rk(Q :: R :: gamma :: nil) <= 2) by (solve_hyps_max HQRgammaeq HQRgammaM2).
	try assert(HQRPpQpbetagammaeq : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) = 4) by (apply LQRPpQpbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQRPpQpbetagammamtmp : rk(Q :: R :: Pp :: Qp :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HQRPpQpbetagammaeq HQRPpQpbetagammam4).
	try assert(Hgammaeq : rk(gamma :: nil) = 1) by (apply Lgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Hgammamtmp : rk(gamma :: nil) >= 1) by (solve_hyps_min Hgammaeq Hgammam1).
	assert(Hincl : incl (gamma :: nil) (list_inter (Q :: R :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: R :: Pp :: Qp :: beta :: gamma :: nil) (Q :: R :: gamma :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: R :: gamma :: Pp :: Qp :: beta :: gamma :: nil) ((Q :: R :: gamma :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQRPpQpbetagammamtmp;try rewrite HT2 in HQRPpQpbetagammamtmp.
	assert(HT := rule_4 (Q :: R :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil) (gamma :: nil) 4 1 2 HQRPpQpbetagammamtmp Hgammamtmp HQRgammaMtmp Hincl); apply HT.
}


assert(HPpQpbetagammaM : rk(Pp :: Qp :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpbetagammam : rk(Pp :: Qp :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpbetagammaeq HPpQpbetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPalphabetagamma *)
(* dans la couche 0 *)
Lemma LPQalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam2 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam3 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam4 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQOoalphaeq : rk(P :: Q :: Oo :: alpha :: nil) = 4) by (apply LPQOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOoalphamtmp : rk(P :: Q :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQOoalphaeq HPQOoalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQOoalphamtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam2 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam3 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQalphabetagammam2 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOoalphabetagammamtmp : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOoalphabetagammaeq HPQPpOoalphabetagammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOoalphabetagammamtmp;try rewrite HT2 in HPQPpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOoalphabetagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOoalphabetagammaM1. try clear HPQPpOoalphabetagammaM2. try clear HPQPpOoalphabetagammaM3. try clear HPQPpOoalphabetagammam4. try clear HPQPpOoalphabetagammam3. try clear HPQPpOoalphabetagammam2. try clear HPQPpOoalphabetagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Q :: alpha ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HPQalphabetagammam3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	assert(HPQQpOoalphabetagammamtmp : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQQpOoalphabetagammaeq HPQQpOoalphabetagammam4).
	try assert(HQalphaeq : rk(Q :: alpha :: nil) = 2) by (apply LQalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQalphamtmp : rk(Q :: alpha :: nil) >= 2) by (solve_hyps_min HQalphaeq HQalpham2).
	assert(Hincl : incl (Q :: alpha :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQQpOoalphabetagammamtmp;try rewrite HT2 in HPQQpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (Q :: alpha :: nil) 4 2 3 HPQQpOoalphabetagammamtmp HQalphamtmp HQQpOoalphaMtmp Hincl); apply HT.
}
try clear HPQQpOoalphabetagammaM1. try clear HPQQpOoalphabetagammaM2. try clear HPQQpOoalphabetagammaM3. try clear HPQQpOoalphabetagammam4. try clear HPQQpOoalphabetagammam3. try clear HPQQpOoalphabetagammam2. try clear HPQQpOoalphabetagammam1. 

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPQalphabetagammaM3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) <= 3).
{
	try assert(HPQalphagammaeq : rk(P :: Q :: alpha :: gamma :: nil) = 3) by (apply LPQalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQalphagammaMtmp : rk(P :: Q :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPQalphagammaeq HPQalphagammaM3).
	try assert(HPQbetagammaeq : rk(P :: Q :: beta :: gamma :: nil) = 3) by (apply LPQbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQbetagammaMtmp : rk(P :: Q :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPQbetagammaeq HPQbetagammaM3).
	try assert(HPQgammaeq : rk(P :: Q :: gamma :: nil) = 3) by (apply LPQgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQgammamtmp : rk(P :: Q :: gamma :: nil) >= 3) by (solve_hyps_min HPQgammaeq HPQgammam3).
	assert(Hincl : incl (P :: Q :: gamma :: nil) (list_inter (P :: Q :: alpha :: gamma :: nil) (P :: Q :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: gamma :: P :: Q :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: alpha :: gamma :: P :: Q :: beta :: gamma :: nil) ((P :: Q :: alpha :: gamma :: nil) ++ (P :: Q :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P :: Q :: alpha :: gamma :: nil) (P :: Q :: beta :: gamma :: nil) (P :: Q :: gamma :: nil) 3 3 3 HPQalphagammaMtmp HPQbetagammaMtmp HPQgammamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPQalphabetagammaM : rk(P :: Q :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQalphabetagammam : rk(P :: Q :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQalphabetagammaeq HPQalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 6  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam2 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam3 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam4 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQOoalphaeq : rk(P :: Q :: Oo :: alpha :: nil) = 4) by (apply LPQOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOoalphamtmp : rk(P :: Q :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQOoalphaeq HPQOoalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQOoalphamtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam2 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam3 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQalphabetagammam2 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOoalphabetagammamtmp : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOoalphabetagammaeq HPQPpOoalphabetagammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOoalphabetagammamtmp;try rewrite HT2 in HPQPpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOoalphabetagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOoalphabetagammaM1. try clear HPQPpOoalphabetagammaM2. try clear HPQPpOoalphabetagammaM3. try clear HPQPpOoalphabetagammam4. try clear HPQPpOoalphabetagammam3. try clear HPQPpOoalphabetagammam2. try clear HPQPpOoalphabetagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Q :: alpha ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HPQalphabetagammam3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	assert(HPQQpOoalphabetagammamtmp : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQQpOoalphabetagammaeq HPQQpOoalphabetagammam4).
	try assert(HQalphaeq : rk(Q :: alpha :: nil) = 2) by (apply LQalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQalphamtmp : rk(Q :: alpha :: nil) >= 2) by (solve_hyps_min HQalphaeq HQalpham2).
	assert(Hincl : incl (Q :: alpha :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQQpOoalphabetagammamtmp;try rewrite HT2 in HPQQpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (Q :: alpha :: nil) 4 2 3 HPQQpOoalphabetagammamtmp HQalphamtmp HQQpOoalphaMtmp Hincl); apply HT.
}
try clear HPQQpOoalphabetagammaM1. try clear HPQQpOoalphabetagammaM2. try clear HPQQpOoalphabetagammaM3. try clear HPQQpOoalphabetagammam4. try clear HPQQpOoalphabetagammam3. try clear HPQQpOoalphabetagammam2. try clear HPQQpOoalphabetagammam1. 

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PQRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpOoalphabetagamma requis par la preuve de (?)PQRPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpOoalphabetagamma requis par la preuve de (?)PQRPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQRPpQpRpeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) = 4) by (apply LPQRPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQRPpQpRpmtmp Hcomp Hincl);apply HT.
}
try clear HPQRPpQpRpM1. try clear HPQRPpQpRpM2. try clear HPQRPpQpRpM3. try clear HPQRPpQpRpm4. try clear HPQRPpQpRpm3. try clear HPQRPpQpRpm2. try clear HPQRPpQpRpm1. 

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOoalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOoalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Qp :: Oo ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpQpRpOoalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HPQRPpQpRpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpOoalphabetagammaeq HPQRPpQpRpOoalphabetagammam4).
	try assert(HQpOoeq : rk(Qp :: Oo :: nil) = 2) by (apply LQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpOomtmp : rk(Qp :: Oo :: nil) >= 2) by (solve_hyps_min HQpOoeq HQpOom2).
	assert(Hincl : incl (Qp :: Oo :: nil) (list_inter (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Qp :: Oo :: nil) 4 2 2 HPQRPpQpRpOoalphabetagammamtmp HQpOomtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQpOoM1. try clear HQpOoM2. try clear HQpOoM3. try clear HQpOom4. try clear HQpOom3. try clear HQpOom2. try clear HQpOom1. try clear HPQRPpQpRpOoalphabetagammaM1. try clear HPQRPpQpRpOoalphabetagammaM2. try clear HPQRPpQpRpOoalphabetagammaM3. try clear HPQRPpQpRpOoalphabetagammam4. try clear HPQRPpQpRpOoalphabetagammam3. try clear HPQRPpQpRpOoalphabetagammam2. try clear HPQRPpQpRpOoalphabetagammam1. 

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : R :: Rp ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpQpRpalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	assert(HPRPpQpRpOoalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOoalphabetagammaeq HPRPpQpRpOoalphabetagammam4).
	try assert(HRRpeq : rk(R :: Rp :: nil) = 2) by (apply LRRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hincl : incl (R :: Rp :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (R :: Rp :: Oo :: P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (R :: Rp :: nil) 4 2 2 HPRPpQpRpOoalphabetagammamtmp HRRpmtmp HRRpOoMtmp Hincl); apply HT.
}


(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp :: Rp :: alpha ::  de rang :  3 et 3 	 A : P :: R :: Pp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpRpalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPRPpRpalphaeq : rk(P :: R :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpRpalphaMtmp : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpalphaeq HPRPpRpalphaM3).
	assert(HPRPpQpRpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam4).
	try assert(HPPpRpalphaeq : rk(P :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpRpalphamtmp : rk(P :: Pp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham3).
	assert(Hincl : incl (P :: Pp :: Rp :: alpha :: nil) (list_inter (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: Pp :: Rp :: alpha :: nil) 4 3 3 HPRPpQpRpalphabetagammamtmp HPPpRpalphamtmp HPRPpRpalphaMtmp Hincl); apply HT.
}
try clear HPRPpQpRpalphabetagammaM1. try clear HPRPpQpRpalphabetagammaM2. try clear HPRPpQpRpalphabetagammaM3. try clear HPRPpQpRpalphabetagammam4. try clear HPRPpQpRpalphabetagammam3. try clear HPRPpQpRpalphabetagammam2. try clear HPRPpQpRpalphabetagammam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour Palphabetagamma requis par la preuve de (?)Palphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : alpha ::  de rang :  1 et 1 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPalphabetagammam2 : rk(P :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	assert(HPPpQpRpalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam4).
	try assert(Halphaeq : rk(alpha :: nil) = 1) by (apply Lalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Halphamtmp : rk(alpha :: nil) >= 1) by (solve_hyps_min Halphaeq Halpham1).
	assert(Hincl : incl (alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpalphabetagammamtmp;try rewrite HT2 in HPPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: alpha :: beta :: gamma :: nil) (alpha :: nil) 4 1 3 HPPpQpRpalphabetagammamtmp Halphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : P :: beta ::  de rang :  2 et 2 	 A : P :: Q :: beta ::   de rang : 2 et 2 *)
assert(HPalphabetagammam3 : rk(P :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQbetaeq : rk(P :: Q :: beta :: nil) = 2) by (apply LPQbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	assert(HPQalphabetagammamtmp : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQalphabetagammaeq HPQalphabetagammam3).
	try assert(HPbetaeq : rk(P :: beta :: nil) = 2) by (apply LPbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPbetamtmp : rk(P :: beta :: nil) >= 2) by (solve_hyps_min HPbetaeq HPbetam2).
	assert(Hincl : incl (P :: beta :: nil) (list_inter (P :: Q :: beta :: nil) (P :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: alpha :: beta :: gamma :: nil) (P :: Q :: beta :: P :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: beta :: P :: alpha :: beta :: gamma :: nil) ((P :: Q :: beta :: nil) ++ (P :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQalphabetagammamtmp;try rewrite HT2 in HPQalphabetagammamtmp.
	assert(HT := rule_4 (P :: Q :: beta :: nil) (P :: alpha :: beta :: gamma :: nil) (P :: beta :: nil) 3 2 2 HPQalphabetagammamtmp HPbetamtmp HPQbetaMtmp Hincl); apply HT.
}
try clear HPbetaM1. try clear HPbetaM2. try clear HPbetaM3. try clear HPbetam4. try clear HPbetam3. try clear HPbetam2. try clear HPbetam1. 

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPalphabetagammaM3 : rk(P :: alpha :: beta :: gamma :: nil) <= 3).
{
	try assert(HPQalphabetagammaeq : rk(P :: Q :: alpha :: beta :: gamma :: nil) = 3) by (apply LPQalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQalphabetagammaMtmp : rk(P :: Q :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPQalphabetagammaeq HPQalphabetagammaM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P :: alpha :: beta :: gamma :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) 3 3 HPQalphabetagammaMtmp Hcomp Hincl);apply HT.
}


assert(HPalphabetagammaM : rk(P :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPalphabetagammam : rk(P :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPalphabetagammaeq HPalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPpQpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) = 3.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour QPpQpOoalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpQpOoalphabetagamma requis par la preuve de (?)QPpQpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpQpOoalphabetagamma requis par la preuve de (?)PQPpQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpQpOoalphabetagamma requis par la preuve de (?)PQPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalphabetagammam2 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpQpOoalphabetagammam3 : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour QPpQpOoalphabetagamma requis par la preuve de (?)QPpQpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour QPpQpOoalphabetagamma requis par la preuve de (?)QPpQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HQPpQpOoalphabetagammam2 : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Pp :: Oo ::  de rang :  2 et 2 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HQPpQpOoalphabetagammam3 : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpQpOoalphabetagammamtmp : rk(P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpQpOoalphabetagammaeq HPQPpQpOoalphabetagammam3).
	try assert(HPpOoeq : rk(Pp :: Oo :: nil) = 2) by (apply LPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpOomtmp : rk(Pp :: Oo :: nil) >= 2) by (solve_hyps_min HPpOoeq HPpOom2).
	assert(Hincl : incl (Pp :: Oo :: nil) (list_inter (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpQpOoalphabetagammamtmp;try rewrite HT2 in HPQPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (Pp :: Oo :: nil) 3 2 2 HPQPpQpOoalphabetagammamtmp HPpOomtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpQpOoalphabetagammaM1. try clear HPQPpQpOoalphabetagammaM2. try clear HPQPpQpOoalphabetagammaM3. try clear HPQPpQpOoalphabetagammam4. try clear HPQPpQpOoalphabetagammam3. try clear HPQPpQpOoalphabetagammam2. try clear HPQPpQpOoalphabetagammam1. 

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PpQpalphabetagamma requis par la preuve de (?)PpQpalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : Qp ::  de rang :  1 et 1 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPpQpalphabetagammam2 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	assert(HQPpQpOoalphabetagammamtmp : rk(Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HQPpQpOoalphabetagammaeq HQPpQpOoalphabetagammam3).
	try assert(HQpeq : rk(Qp :: nil) = 1) by (apply LQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpmtmp : rk(Qp :: nil) >= 1) by (solve_hyps_min HQpeq HQpm1).
	assert(Hincl : incl (Qp :: nil) (list_inter (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Q :: Pp :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HQPpQpOoalphabetagammamtmp;try rewrite HT2 in HQPpQpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) (Qp :: nil) 3 1 2 HQPpQpOoalphabetagammamtmp HQpmtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQPpQpOoalphabetagammaM1. try clear HQPpQpOoalphabetagammaM2. try clear HQPpQpOoalphabetagammaM3. try clear HQPpQpOoalphabetagammam4. try clear HQPpQpOoalphabetagammam3. try clear HQPpQpOoalphabetagammam2. try clear HQPpQpOoalphabetagammam1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPpQpalphabetagammam3 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: alpha :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpalphamtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HPpQpalphabetagammaM3 : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) <= 3).
{
	try assert(HPpQpalphagammaeq : rk(Pp :: Qp :: alpha :: gamma :: nil) = 3) by (apply LPpQpalphagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpalphagammaMtmp : rk(Pp :: Qp :: alpha :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpalphagammaeq HPpQpalphagammaM3).
	try assert(HPpQpbetagammaeq : rk(Pp :: Qp :: beta :: gamma :: nil) = 3) by (apply LPpQpbetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpbetagammaMtmp : rk(Pp :: Qp :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpbetagammaeq HPpQpbetagammaM3).
	try assert(HPpQpgammaeq : rk(Pp :: Qp :: gamma :: nil) = 3) by (apply LPpQpgamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpgammamtmp : rk(Pp :: Qp :: gamma :: nil) >= 3) by (solve_hyps_min HPpQpgammaeq HPpQpgammam3).
	assert(Hincl : incl (Pp :: Qp :: gamma :: nil) (list_inter (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: gamma :: Pp :: Qp :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: alpha :: gamma :: Pp :: Qp :: beta :: gamma :: nil) ((Pp :: Qp :: alpha :: gamma :: nil) ++ (Pp :: Qp :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Pp :: Qp :: alpha :: gamma :: nil) (Pp :: Qp :: beta :: gamma :: nil) (Pp :: Qp :: gamma :: nil) 3 3 3 HPpQpalphagammaMtmp HPpQpbetagammaMtmp HPpQpgammamtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HPpQpalphabetagammaM : rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPpQpalphabetagammam : rk(Pp :: Qp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPpQpalphabetagammaeq HPpQpalphabetagammam1).
intuition.
Qed.

(* dans constructLemma(), requis par LPPpQpalphabetagamma *)
(* dans constructLemma(), requis par LPPpQpRpalphabetagamma *)
(* dans constructLemma(), requis par LPRPpQpRpalphabetagamma *)
(* dans constructLemma(), requis par LPRPpQpRpOoalphabetagamma *)
(* dans la couche 0 *)
Lemma LPQRPpQpRpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQRPpQpRpOoalphabetagamma requis par la preuve de (?)PQRPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQRPpQpRpOoalphabetagamma requis par la preuve de (?)PQRPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphabetagammam3 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQReq : rk(P :: Q :: R :: nil) = 3) by (apply LPQR with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRmtmp : rk(P :: Q :: R :: nil) >= 3) by (solve_hyps_min HPQReq HPQRm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQRmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQRPpQpRpOoalphabetagammam4 : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQRPpQpRpeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) = 4) by (apply LPQRPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpmtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpeq HPQRPpQpRpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: R :: Pp :: Qp :: Rp :: nil) (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQRPpQpRpmtmp Hcomp Hincl);apply HT.
}
try clear HPQRPpQpRpM1. try clear HPQRPpQpRpM2. try clear HPQRPpQpRpM3. try clear HPQRPpQpRpm4. try clear HPQRPpQpRpm3. try clear HPQRPpQpRpm2. try clear HPQRPpQpRpm1. 

assert(HPQRPpQpRpOoalphabetagammaM : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQRPpQpRpOoalphabetagammam : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQRPpQpRpOoalphabetagammaeq HPQRPpQpRpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpQpRpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpOoalphabetagamma requis par la preuve de (?)PRPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOoalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpOoalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Qp :: Oo ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpQpRpOoalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HQQpOoeq : rk(Q :: Qp :: Oo :: nil) = 2) by (apply LQQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoMtmp : rk(Q :: Qp :: Oo :: nil) <= 2) by (solve_hyps_max HQQpOoeq HQQpOoM2).
	try assert(HPQRPpQpRpOoalphabetagammaeq : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPQRPpQpRpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQRPpQpRpOoalphabetagammamtmp : rk(P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQRPpQpRpOoalphabetagammaeq HPQRPpQpRpOoalphabetagammam4).
	try assert(HQpOoeq : rk(Qp :: Oo :: nil) = 2) by (apply LQpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQpOomtmp : rk(Qp :: Oo :: nil) >= 2) by (solve_hyps_min HQpOoeq HQpOom2).
	assert(Hincl : incl (Qp :: Oo :: nil) (list_inter (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPQRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Qp :: Oo :: nil) 4 2 2 HPQRPpQpRpOoalphabetagammamtmp HQpOomtmp HQQpOoMtmp Hincl); apply HT.
}
try clear HQpOoM1. try clear HQpOoM2. try clear HQpOoM3. try clear HQpOom4. try clear HQpOom3. try clear HQpOom2. try clear HQpOom1. 

assert(HPRPpQpRpOoalphabetagammaM : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpRpOoalphabetagammam : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPRPpQpRpOoalphabetagammaeq HPRPpQpRpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPRPpQpRpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PRPpQpRpalphabetagamma requis par la preuve de (?)PRPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam2 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPRPpQpRpalphabetagammam3 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : R :: Rp ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPRPpQpRpalphabetagammam4 : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRPpQpRpOoalphabetagammaeq : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPRPpQpRpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpQpRpOoalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOoalphabetagammaeq HPRPpQpRpOoalphabetagammam4).
	try assert(HRRpeq : rk(R :: Rp :: nil) = 2) by (apply LRRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpmtmp : rk(R :: Rp :: nil) >= 2) by (solve_hyps_min HRRpeq HRRpm2).
	assert(Hincl : incl (R :: Rp :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (R :: Rp :: Oo :: P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (R :: Rp :: nil) 4 2 2 HPRPpQpRpOoalphabetagammamtmp HRRpmtmp HRRpOoMtmp Hincl); apply HT.
}


assert(HPRPpQpRpalphabetagammaM : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPRPpQpRpalphabetagammam : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpRpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpalphabetagamma requis par la preuve de (?)PPpQpRpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp :: Rp :: alpha ::  de rang :  3 et 3 	 A : P :: R :: Pp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpRpalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPRPpRpalphaeq : rk(P :: R :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPRPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpRpalphaMtmp : rk(P :: R :: Pp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPRPpRpalphaeq HPRPpRpalphaM3).
	try assert(HPRPpQpRpalphabetagammaeq : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPRPpQpRpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpQpRpalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpalphabetagammaeq HPRPpQpRpalphabetagammam4).
	try assert(HPPpRpalphaeq : rk(P :: Pp :: Rp :: alpha :: nil) = 3) by (apply LPPpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpRpalphamtmp : rk(P :: Pp :: Rp :: alpha :: nil) >= 3) by (solve_hyps_min HPPpRpalphaeq HPPpRpalpham3).
	assert(Hincl : incl (P :: Pp :: Rp :: alpha :: nil) (list_inter (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: R :: Pp :: Rp :: alpha :: P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) ((P :: R :: Pp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (P :: R :: Pp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (P :: Pp :: Rp :: alpha :: nil) 4 3 3 HPRPpQpRpalphabetagammamtmp HPPpRpalphamtmp HPRPpRpalphaMtmp Hincl); apply HT.
}


assert(HPPpQpRpalphabetagammaM : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpRpalphabetagammam : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOoalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOoalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Rp :: Oo ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPPpQpRpOoalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRPpQpRpOoalphabetagammaeq : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPRPpQpRpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpQpRpOoalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOoalphabetagammaeq HPRPpQpRpOoalphabetagammam4).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Rp :: Oo :: nil) 4 2 2 HPRPpQpRpOoalphabetagammamtmp HRpOomtmp HRRpOoMtmp Hincl); apply HT.
}
try clear HRpOoM1. try clear HRpOoM2. try clear HRpOoM3. try clear HRpOom4. try clear HRpOom3. try clear HRpOom2. try clear HRpOom1. 

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpalphabetagamma requis par la preuve de (?)PPpQpalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpalphabetagammam2 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : P :: Pp ::  de rang :  2 et 2 	 A : P :: Pp :: Rp :: Oo ::   de rang : 3 et 3 *)
assert(HPPpQpalphabetagammam3 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPPpRpOoeq : rk(P :: Pp :: Rp :: Oo :: nil) = 3) by (apply LPPpRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpRpOoMtmp : rk(P :: Pp :: Rp :: Oo :: nil) <= 3) by (solve_hyps_max HPPpRpOoeq HPPpRpOoM3).
	assert(HPPpQpRpOoalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpOoalphabetagammaeq HPPpQpRpOoalphabetagammam4).
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hincl : incl (P :: Pp :: nil) (list_inter (P :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Pp :: Rp :: Oo :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Rp :: Oo :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: Pp :: Rp :: Oo :: nil) ++ (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Rp :: Oo :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: Pp :: nil) 4 2 3 HPPpQpRpOoalphabetagammamtmp HPPpmtmp HPPpRpOoMtmp Hincl); apply HT.
}
try clear HPPpQpRpOoalphabetagammaM1. try clear HPPpQpRpOoalphabetagammaM2. try clear HPPpQpRpOoalphabetagammaM3. try clear HPPpQpRpOoalphabetagammam4. try clear HPPpQpRpOoalphabetagammam3. try clear HPPpQpRpOoalphabetagammam2. try clear HPPpQpRpOoalphabetagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Pp :: Qp :: alpha ::  de rang :  3 et 3 	 A : Pp :: Qp :: Rp :: alpha ::   de rang : 3 et 3 *)
assert(HPPpQpalphabetagammam4 : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPpQpRpalphaeq : rk(Pp :: Qp :: Rp :: alpha :: nil) = 3) by (apply LPpQpRpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpalphaMtmp : rk(Pp :: Qp :: Rp :: alpha :: nil) <= 3) by (solve_hyps_max HPpQpRpalphaeq HPpQpRpalphaM3).
	try assert(HPPpQpRpalphabetagammaeq : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPPpQpRpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpQpRpalphabetagammamtmp : rk(P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpRpalphabetagammaeq HPPpQpRpalphabetagammam4).
	try assert(HPpQpalphaeq : rk(Pp :: Qp :: alpha :: nil) = 3) by (apply LPpQpalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpalphamtmp : rk(Pp :: Qp :: alpha :: nil) >= 3) by (solve_hyps_min HPpQpalphaeq HPpQpalpham3).
	assert(Hincl : incl (Pp :: Qp :: alpha :: nil) (list_inter (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: Rp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Pp :: Qp :: Rp :: alpha :: P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((Pp :: Qp :: Rp :: alpha :: nil) ++ (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpRpalphabetagammamtmp;try rewrite HT2 in HPPpQpRpalphabetagammamtmp.
	assert(HT := rule_4 (Pp :: Qp :: Rp :: alpha :: nil) (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: nil) 4 3 3 HPPpQpRpalphabetagammamtmp HPpQpalphamtmp HPpQpRpalphaMtmp Hincl); apply HT.
}


assert(HPPpQpalphabetagammaM : rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpalphabetagammam : rk(P :: Pp :: Qp :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPPpQpalphabetagammaeq HPPpQpalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPQQpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQQpOoalphabetagamma requis par la preuve de (?)PQQpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam2 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HQQpeq : rk(Q :: Qp :: nil) = 2) by (apply LQQp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpmtmp : rk(Q :: Qp :: nil) >= 2) by (solve_hyps_min HQQpeq HQQpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Q :: Qp :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HQQpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam3 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQQpOoalphabetagammam4 : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HPQOoalphaeq : rk(P :: Q :: Oo :: alpha :: nil) = 4) by (apply LPQOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOoalphamtmp : rk(P :: Q :: Oo :: alpha :: nil) >= 4) by (solve_hyps_min HPQOoalphaeq HPQOoalpham4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: alpha :: nil) (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) 4 4 HPQOoalphamtmp Hcomp Hincl);apply HT.
}


assert(HPQQpOoalphabetagammaM : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPQQpOoalphabetagammam : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPQQpOoalphabetagammaeq HPQQpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LPPpQpRpOoalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) = 4.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PPpQpRpOoalphabetagamma requis par la preuve de (?)PPpQpRpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOoalphabetagammam2 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPPpQpRpOoalphabetagammam3 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPpQpRpeq : rk(Pp :: Qp :: Rp :: nil) = 3) by (apply LPpQpRp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpRpmtmp : rk(Pp :: Qp :: Rp :: nil) >= 3) by (solve_hyps_min HPpQpRpeq HPpQpRpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Pp :: Qp :: Rp :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPpQpRpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Rp :: Oo ::  de rang :  2 et 2 	 A : R :: Rp :: Oo ::   de rang : 2 et 2 *)
assert(HPPpQpRpOoalphabetagammam4 : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4).
{
	try assert(HRRpOoeq : rk(R :: Rp :: Oo :: nil) = 2) by (apply LRRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRRpOoMtmp : rk(R :: Rp :: Oo :: nil) <= 2) by (solve_hyps_max HRRpOoeq HRRpOoM2).
	try assert(HPRPpQpRpOoalphabetagammaeq : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPRPpQpRpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPRPpQpRpOoalphabetagammamtmp : rk(P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPRPpQpRpOoalphabetagammaeq HPRPpQpRpOoalphabetagammam4).
	try assert(HRpOoeq : rk(Rp :: Oo :: nil) = 2) by (apply LRpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HRpOomtmp : rk(Rp :: Oo :: nil) >= 2) by (solve_hyps_min HRpOoeq HRpOom2).
	assert(Hincl : incl (Rp :: Oo :: nil) (list_inter (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: R :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (R :: Rp :: Oo :: P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) ((R :: Rp :: Oo :: nil) ++ (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPRPpQpRpOoalphabetagammamtmp;try rewrite HT2 in HPRPpQpRpOoalphabetagammamtmp.
	assert(HT := rule_4 (R :: Rp :: Oo :: nil) (P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma :: nil) (Rp :: Oo :: nil) 4 2 2 HPRPpQpRpOoalphabetagammamtmp HRpOomtmp HRRpOoMtmp Hincl); apply HT.
}
try clear HRpOoM1. try clear HRpOoM2. try clear HRpOoM3. try clear HRpOom4. try clear HRpOom3. try clear HRpOom2. try clear HRpOom1. 

assert(HPPpQpRpOoalphabetagammaM : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) <= 4) by (apply rk_upper_dim).
assert(HPPpQpRpOoalphabetagammam : rk(P :: Pp :: Qp :: Rp :: Oo :: alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min HPPpQpRpOoalphabetagammaeq HPPpQpRpOoalphabetagammam1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lalphabetagamma : forall P Q R Pp Qp Rp Oo alpha beta gamma ,
rk(P :: Q :: R ::  nil) = 3 -> rk(P :: Pp ::  nil) = 2 -> rk(Q :: Qp ::  nil) = 2 ->
rk(R :: Rp ::  nil) = 2 -> rk(Pp :: Qp :: Rp ::  nil) = 3 -> rk(P :: Q :: R :: Pp :: Qp :: Rp ::  nil) = 4 ->
rk(P :: Q :: R :: Oo ::  nil) = 4 -> rk(P :: Pp :: Oo ::  nil) = 2 -> rk(Q :: Qp :: Oo ::  nil) = 2 ->
rk(R :: Rp :: Oo ::  nil) = 2 -> rk(Pp :: Qp :: Rp :: Oo ::  nil) = 4 -> rk(P :: R :: alpha ::  nil) = 2 ->
rk(Pp :: Rp :: alpha ::  nil) = 2 -> rk(P :: Q :: beta ::  nil) = 2 -> rk(Pp :: Qp :: beta ::  nil) = 2 ->
rk(Q :: R :: gamma ::  nil) = 2 -> rk(Qp :: Rp :: gamma ::  nil) = 2 -> rk(alpha :: beta :: gamma ::  nil) = 2.
Proof.

intros P Q R Pp Qp Rp Oo alpha beta gamma 
HPQReq HPPpeq HQQpeq HRRpeq HPpQpRpeq HPQRPpQpRpeq HPQROoeq HPPpOoeq HQQpOoeq HRRpOoeq
HPpQpRpOoeq HPRalphaeq HPpRpalphaeq HPQbetaeq HPpQpbetaeq HQRgammaeq HQpRpgammaeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour alphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 3  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQPpOoalphabetagamma requis par la preuve de (?)PQPpOoalphabetagamma pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam2 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpeq : rk(P :: Pp :: nil) = 2) by (apply LPPp with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpmtmp : rk(P :: Pp :: nil) >= 2) by (solve_hyps_min HPPpeq HPPpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Pp :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 2 2 HPPpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HPQPpOoalphabetagammam3 : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HPQOoeq : rk(P :: Q :: Oo :: nil) = 3) by (apply LPQOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQOomtmp : rk(P :: Q :: Oo :: nil) >= 3) by (solve_hyps_min HPQOoeq HPQOom3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P :: Q :: Oo :: nil) (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) 3 3 HPQOomtmp Hcomp Hincl);apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour PQalphabetagamma requis par la preuve de (?)PQalphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Pp :: Oo :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : P ::  de rang :  1 et 1 	 A : P :: Pp :: Oo ::   de rang : 2 et 2 *)
assert(HPQalphabetagammam2 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPPpOoeq : rk(P :: Pp :: Oo :: nil) = 2) by (apply LPPpOo with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpOoMtmp : rk(P :: Pp :: Oo :: nil) <= 2) by (solve_hyps_max HPPpOoeq HPPpOoM2).
	assert(HPQPpOoalphabetagammamtmp : rk(P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQPpOoalphabetagammaeq HPQPpOoalphabetagammam3).
	try assert(HPeq : rk(P :: nil) = 1) by (apply LP with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPmtmp : rk(P :: nil) >= 1) by (solve_hyps_min HPeq HPm1).
	assert(Hincl : incl (P :: nil) (list_inter (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Pp :: Oo :: alpha :: beta :: gamma :: nil) (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Pp :: Oo :: P :: Q :: alpha :: beta :: gamma :: nil) ((P :: Pp :: Oo :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQPpOoalphabetagammamtmp;try rewrite HT2 in HPQPpOoalphabetagammamtmp.
	assert(HT := rule_4 (P :: Pp :: Oo :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (P :: nil) 3 1 2 HPQPpOoalphabetagammamtmp HPmtmp HPPpOoMtmp Hincl); apply HT.
}
try clear HPQPpOoalphabetagammaM1. try clear HPQPpOoalphabetagammaM2. try clear HPQPpOoalphabetagammaM3. try clear HPQPpOoalphabetagammam4. try clear HPQPpOoalphabetagammam3. try clear HPQPpOoalphabetagammam2. try clear HPQPpOoalphabetagammam1. 

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : P :: Q :: Qp :: Oo :: alpha :: beta :: gamma ::  de rang :  4 et 4 	 AiB : Q :: alpha ::  de rang :  2 et 2 	 A : Q :: Qp :: Oo :: alpha ::   de rang : 3 et 3 *)
assert(HPQalphabetagammam3 : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3).
{
	try assert(HQQpOoalphaeq : rk(Q :: Qp :: Oo :: alpha :: nil) = 3) by (apply LQQpOoalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQQpOoalphaMtmp : rk(Q :: Qp :: Oo :: alpha :: nil) <= 3) by (solve_hyps_max HQQpOoalphaeq HQQpOoalphaM3).
	try assert(HPQQpOoalphabetagammaeq : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) = 4) by (apply LPQQpOoalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQQpOoalphabetagammamtmp : rk(P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPQQpOoalphabetagammaeq HPQQpOoalphabetagammam4).
	try assert(HQalphaeq : rk(Q :: alpha :: nil) = 2) by (apply LQalpha with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HQalphamtmp : rk(Q :: alpha :: nil) >= 2) by (solve_hyps_min HQalphaeq HQalpham2).
	assert(Hincl : incl (Q :: alpha :: nil) (list_inter (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: Qp :: Oo :: alpha :: beta :: gamma :: nil) (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Q :: Qp :: Oo :: alpha :: P :: Q :: alpha :: beta :: gamma :: nil) ((Q :: Qp :: Oo :: alpha :: nil) ++ (P :: Q :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQQpOoalphabetagammamtmp;try rewrite HT2 in HPQQpOoalphabetagammamtmp.
	assert(HT := rule_4 (Q :: Qp :: Oo :: alpha :: nil) (P :: Q :: alpha :: beta :: gamma :: nil) (Q :: alpha :: nil) 4 2 3 HPQQpOoalphabetagammamtmp HQalphamtmp HQQpOoalphaMtmp Hincl); apply HT.
}


(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour alphabetagamma requis par la preuve de (?)alphabetagamma pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : P :: Q :: alpha :: beta :: gamma ::  de rang :  3 et 4 	 AiB : beta ::  de rang :  1 et 1 	 A : P :: Q :: beta ::   de rang : 2 et 2 *)
assert(Halphabetagammam2 : rk(alpha :: beta :: gamma :: nil) >= 2).
{
	try assert(HPQbetaeq : rk(P :: Q :: beta :: nil) = 2) by (apply LPQbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPQbetaMtmp : rk(P :: Q :: beta :: nil) <= 2) by (solve_hyps_max HPQbetaeq HPQbetaM2).
	assert(HPQalphabetagammamtmp : rk(P :: Q :: alpha :: beta :: gamma :: nil) >= 3) by (solve_hyps_min HPQalphabetagammaeq HPQalphabetagammam3).
	try assert(Hbetaeq : rk(beta :: nil) = 1) by (apply Lbeta with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(Hbetamtmp : rk(beta :: nil) >= 1) by (solve_hyps_min Hbetaeq Hbetam1).
	assert(Hincl : incl (beta :: nil) (list_inter (P :: Q :: beta :: nil) (alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Q :: alpha :: beta :: gamma :: nil) (P :: Q :: beta :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: Q :: beta :: alpha :: beta :: gamma :: nil) ((P :: Q :: beta :: nil) ++ (alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPQalphabetagammamtmp;try rewrite HT2 in HPQalphabetagammamtmp.
	assert(HT := rule_4 (P :: Q :: beta :: nil) (alpha :: beta :: gamma :: nil) (beta :: nil) 3 1 2 HPQalphabetagammamtmp Hbetamtmp HPQbetaMtmp Hincl); apply HT.
}
try clear HbetaM1. try clear HbetaM2. try clear HbetaM3. try clear Hbetam4. try clear Hbetam3. try clear Hbetam2. try clear Hbetam1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HalphabetagammaM2 : rk(alpha :: beta :: gamma :: nil) <= 2).
{
	try assert(HPalphabetagammaeq : rk(P :: alpha :: beta :: gamma :: nil) = 3) by (apply LPalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPalphabetagammaMtmp : rk(P :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPalphabetagammaeq HPalphabetagammaM3).
	try assert(HPpQpalphabetagammaeq : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) = 3) by (apply LPpQpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPpQpalphabetagammaMtmp : rk(Pp :: Qp :: alpha :: beta :: gamma :: nil) <= 3) by (solve_hyps_max HPpQpalphabetagammaeq HPpQpalphabetagammaM3).
	try assert(HPPpQpalphabetagammaeq : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) = 4) by (apply LPPpQpalphabetagamma with (P := P) (Q := Q) (R := R) (Pp := Pp) (Qp := Qp) (Rp := Rp) (Oo := Oo) (alpha := alpha) (beta := beta) (gamma := gamma) ;try assumption).
	assert(HPPpQpalphabetagammamtmp : rk(P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) >= 4) by (solve_hyps_min HPPpQpalphabetagammaeq HPPpQpalphabetagammam4).
	assert(Hincl : incl (alpha :: beta :: gamma :: nil) (list_inter (P :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P :: Pp :: Qp :: alpha :: beta :: gamma :: nil) (P :: alpha :: beta :: gamma :: Pp :: Qp :: alpha :: beta :: gamma :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P :: alpha :: beta :: gamma :: Pp :: Qp :: alpha :: beta :: gamma :: nil) ((P :: alpha :: beta :: gamma :: nil) ++ (Pp :: Qp :: alpha :: beta :: gamma :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HPPpQpalphabetagammamtmp;try rewrite HT2 in HPPpQpalphabetagammamtmp.
	assert(HT := rule_3 (P :: alpha :: beta :: gamma :: nil) (Pp :: Qp :: alpha :: beta :: gamma :: nil) (alpha :: beta :: gamma :: nil) 3 3 4 HPalphabetagammaMtmp HPpQpalphabetagammaMtmp HPPpQpalphabetagammamtmp Hincl);apply HT.
}


assert(HalphabetagammaM : rk(alpha :: beta :: gamma ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max Halphabetagammaeq HalphabetagammaM3).
assert(Halphabetagammam : rk(alpha :: beta :: gamma ::  nil) >= 1) by (solve_hyps_min Halphabetagammaeq Halphabetagammam1).
intuition.
Qed.

