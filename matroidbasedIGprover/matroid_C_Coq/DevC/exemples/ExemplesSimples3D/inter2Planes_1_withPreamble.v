Require Export List.
Require Export Lia.
Require Export Morphisms.

Parameter Point : Set.
Parameter eq_dec : forall A B : Point, {A = B} + {~ A = B}.

Definition equivlist (l l':list Point) := forall x, List.In x l <-> List.In x l'.

Ltac simplgen H := simpl in H;generalize H.

Ltac my_inS :=
  intuition;unfold incl in *;unfold equivlist in *;
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => split;intuition
  |[H : In _ (?P ::  _ ) |- _] => inversion H;clear H
  |[H : _ = _ |- _] => rewrite <-H
  |[H : In _ nil |- _] => inversion H
  end.

Parameter rk : list Point -> nat.
Parameter rk_compat : forall x x', equivlist x x' -> rk x = rk x'.

Global Instance rk_morph : Proper (equivlist ==> (@Logic.eq nat)) rk.
Proof.
intros;repeat red.
apply rk_compat.
Qed.

(*** Definition Inb ***)
Fixpoint Inb (a:Point) (l:list Point) {struct l} : bool :=
    match l with
      | nil => false
      | b :: m => if (eq_dec b a) then true else Inb a m
    end.

Lemma Inb_aux1 :
forall a l, Inb a l = true -> In a l.
Proof.
my_inS;induction l;my_inS.
- inversion H.
- simplgen H;case_eq(eq_dec a0 a);my_inS.
Qed.

Lemma Inb_aux2 :
forall a l, Inb a l = false -> ~In a l.
Proof.
my_inS;induction l;my_inS.
- rewrite H1 in *;simplgen H;case_eq(eq_dec a a);my_inS.
- simplgen H;case_eq(eq_dec a0 a);my_inS.
Qed.

(*** Definition list_inter ***)
Definition list_inter l1 l2 := filter (fun x : Point => Inb x l2) l1.

Lemma list_inter_split :
forall a l m, In a (list_inter l m) -> In a l /\ In a m.
Proof.
intros.
my_inS;induction l;my_inS.
- simplgen H;unfold list_inter;simpl;case_eq(Inb a0 m);my_inS.
- inversion H.
- simplgen H;unfold list_inter;simpl;case_eq(Inb a0 m);my_inS;apply Inb_aux1;my_inS.
Qed.

Lemma list_inter_closure :
forall a l m, In a m -> In a l -> In a (list_inter l m).
Proof.
my_inS;induction l;my_inS.
- simpl;case_eq(Inb a0 m);my_inS;assert(HH := Inb_aux2 a0 m H0);subst;my_inS.
- simpl;case_eq(Inb a0 m);my_inS.
Qed.

Ltac inv_unif :=
  unfold incl in *; try split; intros;
  repeat match goal with 
         | [H : In _ (?P ::  _ ) |- _] => inversion H;clear H
         | [H: _ = _ |- _] => rewrite <- H in *;try solve [contradiction|apply eq_sym in H;contradiction];clear H
         | [H : In _ nil |- _] => inversion H
         | [H : In _ (?L++?M) |- _] => apply in_app_iff in H; destruct H
         | [H :_ |- In _ (?L++?M) ] => apply in_app_iff
         | [H : In _ (list_inter _ _) |- _] => apply list_inter_split in H; destruct H
         | [H : _ |- In _ (list_inter _ _)] => apply list_inter_closure
         end.

Ltac solve_equivlist := first [apply in_eq | apply in_cons ; solve_equivlist].

Ltac my_inO := solve[inv_unif ; first[solve_equivlist | left;solve_equivlist | right;solve_equivlist]].

Parameter matroid1_a  : forall X, rk X >= 0.
Parameter matroid1_b : forall X, rk X <= length X.
Parameter matroid2 : forall X Y, incl X Y -> rk X <= rk Y.
Parameter matroid3 : forall X Y, rk(X ++ Y) + rk(list_inter X Y) <= rk X + rk Y.

(*** Lemmes matroides utiles ***)
Lemma matroid1_b_useful : forall (l : list Point) (m : nat), length l <= m -> rk l <= m.
Proof.
intros.
assert(HH := matroid1_b l).
lia.
Qed.

Lemma matroid3_useful : forall e e' ei : list Point,
 incl ei (list_inter e e') ->
 rk(e ++ e') + rk(ei) <= rk(e) + rk(e').
Proof.
intros.
assert (rk (e ++ e') + rk (list_inter e e') <= rk e + rk e').
apply matroid3.
assert (rk (ei) <= rk (list_inter e e')).
apply matroid2;auto.
lia.
Qed.

Lemma couple_equal : forall A B, rk(A :: B :: nil) = rk(B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma triple_equal_1 : forall A B C, rk(A :: B :: C :: nil) = rk(A :: C :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma triple_equal_2 : forall A B C, rk(A :: B :: C :: nil) = rk(B :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma triple_equal_3 : forall A B C, rk(A :: B :: C :: nil) = rk(B :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma triple_equal_4 : forall A B C, rk(A :: B :: C :: nil) = rk(C :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma triple_equal_5 : forall A B C, rk(A :: B :: C :: nil) = rk(C :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma rk_triple_max_3 : forall X Y Z : Point, rk(X :: Y :: Z :: nil) <= 3.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_quadruple_max_4 : forall W X Y Z : Point,rk(W :: X :: Y :: Z :: nil) <= 4.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma quadruple_equal_1 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(A :: B :: D :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_2 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(A :: C :: B :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_3 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(A :: C :: D :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_4 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(A :: D :: B :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_5 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(A :: D :: C :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_6 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: A :: C :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_7 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: A :: D :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_8 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: C :: A :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_9 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: C :: D :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_10 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: D :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_11 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(B :: D :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_12 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: A :: B :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_13 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: A :: D :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_14 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: B :: A :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_15 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: B :: D :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_16 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: D :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_17 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(C :: D :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_18 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: A :: B :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_19 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: A :: C :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_20 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: B :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_21 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: B :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_22 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: C :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_equal_23 : forall A B C D, rk(A :: B :: C :: D :: nil) = rk(D :: C :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Ltac clear_all_rk :=
repeat match goal with
| H : rk _ = _ |- _ => clear H
| H : rk _ >= _ |- _ => clear H
| H : rk _ <= _ |- _ => clear H
end.

Parameter rk_singleton_ge : forall A, rk (A :: nil)  >= 1.
Parameter rk_couple_ge : forall A B, ~ A = B -> rk(A :: B :: nil) >= 2.
Parameter rk_three_points_on_lines : forall A B, exists C, rk (A :: B :: C :: nil) = 2 /\ rk (B :: C :: nil) = 2 /\ rk (A :: C :: nil) = 2.
Parameter rk_inter : forall A B C D, rk(A :: B :: C :: D :: nil) <= 3 -> exists J : Point, rk(A :: B :: J :: nil) = 2 /\ rk (C :: D :: J :: nil) = 2.
Parameter rk_lower_dim : exists A0 A1 A2 A3, rk( A0 :: A1 :: A2 :: A3 :: nil) = 4.
Parameter rk_upper_dim : forall e, rk(e) <= 4.

Lemma rk_singleton_1 : forall A, rk(A :: nil) <= 1.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_singleton : forall A, rk(A :: nil) = 1.
Proof.
intros.
assert(H := rk_singleton_ge A).
assert(HH := rk_singleton_1 A).
lia.
Qed.

Lemma matroid1_b_useful2 : forall (l : list Point) (a : Point), length (a :: l) >= 1 -> rk (a :: l) >= 1.
Proof.
intros.
assert(HH := rk_singleton a).
assert(HH0 := matroid2 (a :: nil) (a :: l)).
assert(HH1 : incl (a :: nil) (a :: l));[my_inO|].
assert(HH2 := HH0 HH1).
lia.
Qed.

Lemma rk_couple_2 : forall A B, rk(A :: B :: nil) <= 2.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_couple : forall A B : Point,~ A = B -> rk(A :: B :: nil) = 2.
Proof.
intros.
assert(HH := rk_couple_2 A B).
assert(HH0 := rk_couple_ge A B H).
lia.
Qed.

Lemma rk_triple_3 : forall A B C : Point, rk (A :: B :: C :: nil) <= 3.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma couple_rk1 : forall A B, rk(A :: B :: nil) = 2 -> ~ A = B.
Proof.
intros.
intro.
rewrite H0 in H.
assert(HH : equivlist (B :: B :: nil) (B :: nil));[my_inO|].
rewrite HH in H.
assert(HH0 := rk_singleton_1 B).
lia.
Qed.

Lemma couple_rk2 : forall A B, rk(A :: B :: nil) = 1 -> A = B.
Proof.
intros.
case_eq(eq_dec A B).
intros.
assumption.
intros.
assert(HH := rk_couple A B n).
lia.
Qed.

Lemma rule_1 : forall A B AiB, forall MA MB mAiB, 
rk(A) <= MA -> rk(B) <= MB -> rk(AiB) >= mAiB -> incl AiB (list_inter A B) ->
rk(A ++ B) <= MA + MB - mAiB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_2 : forall A B AiB, forall mAuB mAiB MB, 
rk(A ++ B) >= mAuB -> rk(AiB) >= mAiB -> rk(B) <= MB -> incl AiB (list_inter A B) ->
rk(A) >= mAuB + mAiB - MB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_3 : forall A B AiB, forall MA MB mAuB, 
rk(A) <= MA -> rk(B) <= MB -> rk(A ++ B) >= mAuB -> incl AiB (list_inter A B) ->
rk(AiB) <= MA + MB - mAuB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_4 : forall A B AiB, forall mAuB mAiB MA, 
rk(A ++ B) >= mAuB -> rk(AiB) >= mAiB -> rk(A) <= MA -> incl AiB (list_inter A B) ->
rk(B) >= mAuB + mAiB - MA.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_5 : forall A B, forall mA mB, 
rk(A) >= mA -> mA >= mB -> incl A B ->
rk(B) >= mA.
Proof.
intros.
assert(HH := matroid2 A B H1).
lia.
Qed.

Lemma rule_6 : forall A B, forall MA MB, 
rk(B) <= MB -> MB <= MA -> incl A B ->
rk(A) <= MB.
Proof.
intros.
assert(HH := matroid2 A B H1).
lia.
Qed.

Lemma rule_7 : forall A B, forall mA mB, 
rk(B) >= mB -> mB >= mA -> incl B A ->
rk(A) >= mB.
Proof.
intros.
assert(HH := matroid2 B A H1).
lia.
Qed.

Lemma rule_8 : forall A B, forall MA MB, 
rk(A) <= MA -> MA <= MB -> incl B A ->
rk(B) <= MA.
Proof.
intros.
assert(HH := matroid2 B A H1).
lia.
Qed.

Parameter rk_pappus : forall A B C D E F G H I,
rk(A :: B :: nil) = 2 -> rk(A :: C :: nil) = 2 -> rk(A :: D :: nil) = 2 -> 
rk(A :: E :: nil) = 2 -> rk(A :: F :: nil) = 2 ->
rk(B :: C :: nil) = 2 -> rk(B :: D :: nil) = 2 -> rk(B :: E :: nil) = 2 ->
rk(B :: F :: nil) = 2 ->
rk(C :: D :: nil) = 2 -> rk(C :: E :: nil) = 2 -> rk(C :: F :: nil) = 2 ->
rk(D :: E :: nil) = 2 -> rk(D :: F :: nil) = 2 ->
rk(E :: F :: nil) = 2 ->
rk(A :: B :: C :: nil) = 2 -> rk(D :: E :: F :: nil) = 2 -> 
rk(A :: E :: G :: nil) = 2 -> rk(B :: D :: G :: nil) = 2 ->
rk(A :: F :: H :: nil) = 2 -> rk(C :: D :: H :: nil) = 2 ->
rk(B :: F :: I :: nil) = 2 -> rk(C :: E :: I :: nil) = 2 -> rk(G :: H :: I :: nil) = 2.

Ltac rk_couple_triple :=
  match goal with

| H : rk(?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: nil) = 2 => assumption
| H : rk(?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: nil) = 2 => rewrite couple_equal in H;assumption

| H : rk(?A :: ?B :: ?C :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => assumption
| H : rk(?A :: ?C :: ?B :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_1 in H;assumption
| H : rk(?B :: ?A :: ?C :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_2 in H;assumption
| H : rk(?B :: ?C :: ?A :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_3 in H;assumption
| H : rk(?C :: ?A :: ?B :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_4 in H;assumption
| H : rk(?C :: ?B :: ?A :: nil) = _ |-  rk(?A :: ?B :: ?C :: nil) = _ => rewrite <-triple_equal_5 in H;assumption
end.


Ltac clear_ineg_rk :=
repeat match goal with
| H : rk _ >= _ |- _ => clear H
| H : rk _ <= _ |- _ => clear H
end.


Ltac equalize_pts :=
repeat match goal with
| H : rk (?X0 :: ?X1 :: nil) = 1 |- _ => 
          let HH := fresh in assert(HH := couple_rk2 X0 X1 H);clear H;rewrite HH
end.

Ltac eliminate_hyps :=
repeat match goal with
| H : rk ?X = _, H0 : rk ?X >= _ |- _ => clear H0
| H : rk ?X = _, H0 : rk ?X <= _ |- _ => clear H0
| H : rk ?X >= _, H0 : rk ?X >= _ |- _ => clear H
| H : rk ?X <= _, H0 : rk ?X <= _ |- _ => clear H
| H : rk ?X >= ?Y, H0 : rk ?X <= ?Y |- _ =>  let HH := fresh in assert(HH : rk X = Y) by (lia)
end.

Lemma le_S_sym : forall n m : nat,
n >= S m -> n >= m.
Proof.
intros.
intuition.
Qed.

Lemma eq_to_ge : forall n m : nat,
n = m -> n >= m.
Proof.
intros.
lia.
Qed.

Lemma eq_to_le : forall n m : nat,
n = m -> n <= m.
Proof.
intros.
lia.
Qed.

Lemma eq_le_incl : forall n m, n = m -> n <= m.
Proof.
  intros; lia.
Qed.

Ltac solve_hyps_max H H0 :=
solve[apply matroid1_b_useful;simpl;repeat constructor
|apply rk_upper_dim
|apply eq_le_incl;apply H
|apply eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S;apply H0
|apply le_S;apply le_S;apply H0
|apply le_S;apply le_S;apply le_S;apply H0
|lia
].

Ltac solve_hyps_min H H0:=
solve[apply matroid1_b_useful2;simpl;repeat constructor
|apply matroid1_a
|apply eq_le_incl;apply H
|apply eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply le_S_sym;apply H0
|lia
].
 



(* dans la couche 0 *)
Lemma LABC : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HABCM : rk(A :: B :: C ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HABCeq HABCM3).
assert(HABCm : rk(A :: B :: C ::  nil) >= 1) by (solve_hyps_min HABCeq HABCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCp : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HApBpCpM : rk(Ap :: Bp :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HApBpCpeq HApBpCpM3).
assert(HApBpCpm : rk(Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HApBpCpeq HApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCApBpCp : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HABCApBpCpM : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpCpm : rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HABCApBpCpeq HABCApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HABCMM : rk(A :: B :: C :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCMm : rk(A :: B :: C :: M ::  nil) >= 1) by (solve_hyps_min HABCMeq HABCMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpM : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HApBpCpMM : rk(Ap :: Bp :: Cp :: M ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpMm : rk(Ap :: Bp :: Cp :: M ::  nil) >= 1) by (solve_hyps_min HApBpCpMeq HApBpCpMm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HABCNM : rk(A :: B :: C :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCNm : rk(A :: B :: C :: N ::  nil) >= 1) by (solve_hyps_min HABCNeq HABCNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: N ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HApBpCpNM : rk(Ap :: Bp :: Cp :: N ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpNm : rk(Ap :: Bp :: Cp :: N ::  nil) >= 1) by (solve_hyps_min HApBpCpNeq HApBpCpNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LMN : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: N ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HMNM : rk(M :: N ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HMNeq HMNM2).
assert(HMNm : rk(M :: N ::  nil) >= 1) by (solve_hyps_min HMNeq HMNm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HABCPM : rk(A :: B :: C :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCPm : rk(A :: B :: C :: P ::  nil) >= 1) by (solve_hyps_min HABCPeq HABCPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

assert(HApBpCpPM : rk(Ap :: Bp :: Cp :: P ::  nil) <= 4) by (apply rk_upper_dim).
assert(HApBpCpPm : rk(Ap :: Bp :: Cp :: P ::  nil) >= 1) by (solve_hyps_min HApBpCpPeq HApBpCpPm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCMP : forall A B C Ap Bp Cp M N P ,
rk(A :: B :: C ::  nil) = 3 -> rk(Ap :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4 ->
rk(A :: B :: C :: M ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M ::  nil) = 3 -> rk(A :: B :: C :: N ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: N ::  nil) = 3 -> rk(M :: N ::  nil) = 2 -> rk(A :: B :: C :: P ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 3.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(A :: B :: C :: Ap :: Bp :: Cp :: M :: N :: P ::  nil) = 4.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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
rk(Ap :: Bp :: Cp :: P ::  nil) = 3 -> rk(M :: N :: P ::  nil) = 2.
Proof.

intros A B C Ap Bp Cp M N P 
HABCeq HApBpCpeq HABCApBpCpeq HABCMeq HApBpCpMeq HABCNeq HApBpCpNeq HMNeq HABCPeq HApBpCpPeq
.

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

