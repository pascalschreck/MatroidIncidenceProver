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
Parameter rk_lower_dim : exists A0 A1 A2 A3 A4, rk( A0 :: A1 :: A2 :: A3 :: A4 ::nil) = 5.    (* modifié pour dim 4*)
Parameter rk_upper_dim : forall e, rk(e) <= 5.  (* modifié pour dim 4*)

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

Lemma l1_scheme : forall P1 P2 : Point,
                  forall P3 P4 : Point,
                  forall P5 : Point,
                  rk (P1 :: P2 :: P5 :: nil) = 3 ->
                  rk (P1 :: P3 :: P5 :: nil) = 2 ->
                  rk (P2 :: P4 :: P5 :: nil) = 2 ->
                  rk (P3 :: P5 :: nil) = 2 ->
                  rk (P4 :: P5 :: nil) = 2  ->  rk (P3 :: P4 :: P5 :: nil) = 3.
Proof.
intros P1 P2 P3 P4 P5 HP1P2P5eq HP1P3P5eq HP2P4P5eq HP3P5eq HP4P5eq.

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: nil) ((P1 :: P2 :: nil) ++ (P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP5Mtmp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 3 3 HP1P2P5mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5M;assert(HP1P2P3P4P5M : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	try assert(HP1P3P5Mtmp : rk(P1 :: P3 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P3P5eq HP1P3P5M).
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m).
	assert(Hincl : incl (P5 :: nil) (list_inter (P1 :: P3 :: P5 :: nil) (P2 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P5 :: P2 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P2 :: P4 :: P5 :: nil) ((P1 :: P3 :: P5 :: nil) ++ (P2 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P3 :: P5 :: nil) (P2 :: P4 :: P5 :: nil) (P5 :: nil) 2 2 1 HP1P3P5Mtmp HP2P4P5Mtmp HP5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P5m;assert(HP2P5m : rk(P2 :: P5 :: nil) >= 2).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P5mtmp : rk(P1 :: P2 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P5eq HP1P2P5m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P5 :: nil) (P1 :: P2 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P5 :: nil) ((P1 :: nil) ++ (P2 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P5mtmp;try rewrite HT2 in HP1P2P5mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P5 :: nil) (nil) 3 0 1 HP1P2P5mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP2P3P4P5M;assert(HP2P3P4P5M : rk(P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	try assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M).
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P3 :: nil) (P2 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: P5 :: nil) (P3 :: P2 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P2 :: P4 :: P5 :: nil) ((P3 :: nil) ++ (P2 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: nil) (P2 :: P4 :: P5 :: nil) (nil) 1 2 0 HP3Mtmp HP2P4P5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P4P5m;assert(HP2P3P4P5m : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP2P5mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P4P5m;assert(HP2P3P4P5m : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P3P5Mtmp : rk(P1 :: P3 :: P5 :: nil) <= 2) by (solve_hyps_max HP1P3P5eq HP1P3P5M).
	try assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m).
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hincl : incl (P3 :: P5 :: nil) (list_inter (P1 :: P3 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P3 :: P5 :: P2 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P5 :: P2 :: P3 :: P4 :: P5 :: nil) ((P1 :: P3 :: P5 :: nil) ++ (P2 :: P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5mtmp;try rewrite HT2 in HP1P2P3P4P5mtmp.
	assert(HT := rule_4 (P1 :: P3 :: P5 :: nil) (P2 :: P3 :: P4 :: P5 :: nil) (P3 :: P5 :: nil) 3 2 2 HP1P2P3P4P5mtmp HP3P5mtmp HP1P3P5Mtmp Hincl); apply HT.
}

try clear HP3P4P5m;assert(HP3P4P5m : rk(P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) 2 2 HP3P5mtmp Hcomp Hincl); apply HT.
}

try clear HP3P4P5m;assert(HP3P4P5m : rk(P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP2P4P5Mtmp : rk(P2 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP2P4P5eq HP2P4P5M).
	try assert(HP2P3P4P5mtmp : rk(P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP2P3P4P5eq HP2P3P4P5m).
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P2 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: P5 :: nil) (P2 :: P4 :: P5 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P4 :: P5 :: P3 :: P4 :: P5 :: nil) ((P2 :: P4 :: P5 :: nil) ++ (P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P4P5mtmp;try rewrite HT2 in HP2P3P4P5mtmp.
	assert(HT := rule_4 (P2 :: P4 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) (P4 :: P5 :: nil) 3 2 2 HP2P3P4P5mtmp HP4P5mtmp HP2P4P5Mtmp Hincl); apply HT.
}

assert(rk(P3 :: P4 :: P5 ::  nil) <= 3) by (clear_ineg_rk;try lia;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P3 :: P4 :: P5 ::  nil) >= 1) by (clear_ineg_rk;try lia;try solve[apply matroid1_b_useful2;simpl;intuition]).
lia.
Qed.

Lemma rABOo_scheme : forall P1 P2 : Point,
                     forall P3 P4 : Point,
                     rk (P1 :: P2 :: P3 :: P4 :: nil) >= 4 ->
                     forall P5 : Point,
                     rk (P3 :: P4 :: P5 :: nil) = 2 ->
                     rk (P3 :: P5 :: nil) = 2 -> rk (P1 :: P2 :: P3 :: P5 :: nil) >= 4.
Proof.
intros P1 P2 P3 P4 HP1P2P3P4m P5 HP3P4P5eq HP3P5eq. 

try clear HP1P2P3m;assert(HP1P2P3m : rk(P1 :: P2 :: P3 :: nil) >= 3).
{
	try assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: nil) (P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: nil) (P4 :: nil) (nil) 4 0 1 HP1P2P3P4mtmp Hmtmp HP4Mtmp Hincl); apply HT.
}

try clear HP2P3P4m;assert(HP2P3P4m : rk(P2 :: P3 :: P4 :: nil) >= 3).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: P4 :: nil) (nil) 4 0 1 HP1P2P3P4mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP3P4m;assert(HP3P4m : rk(P3 :: P4 :: nil) >= 2).
{
	try assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M).
	try assert(HP2P3P4mtmp : rk(P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP2P3P4eq HP2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P4 :: nil) (P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P4 :: nil) ((P2 :: nil) ++ (P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P4mtmp;try rewrite HT2 in HP2P3P4mtmp.
	assert(HT := rule_4 (P2 :: nil) (P3 :: P4 :: nil) (nil) 3 0 1 HP2P3P4mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP3P4Mtmp : rk(P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP3P4eq HP3P4M).
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) ((P1 :: P2 :: nil) ++ (P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P3 :: P4 :: nil) (nil) 4 0 2 HP1P2P3P4mtmp Hmtmp HP3P4Mtmp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5m;assert(HP1P2P3P4P5m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P5 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P5m;assert(HP1P2P3P5m : rk(P1 :: P2 :: P3 :: P5 :: nil) >= 4).
{
	try assert(HP3P4P5Mtmp : rk(P3 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP3P4P5eq HP3P4P5M).
	try assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m).
	try assert(HP3P5mtmp : rk(P3 :: P5 :: nil) >= 2) by (solve_hyps_min HP3P5eq HP3P5m).
	assert(Hincl : incl (P3 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P5 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P5 :: P3 :: P4 :: P5 :: nil) ((P1 :: P2 :: P3 :: P5 :: nil) ++ (P3 :: P4 :: P5 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5mtmp;try rewrite HT2 in HP1P2P3P4P5mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P5 :: nil) (P3 :: P4 :: P5 :: nil) (P3 :: P5 :: nil) 4 2 2 HP1P2P3P4P5mtmp HP3P5mtmp HP3P4P5Mtmp Hincl); apply HT.
}

assert(rk(P1 :: P2 :: P3 :: P5 ::  nil) <= 4) by (clear_ineg_rk;try lia;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P1 :: P2 :: P3 :: P5 ::  nil) >= 1) by (clear_ineg_rk;try lia;try solve[apply matroid1_b_useful2;simpl;intuition]).
lia.
Qed.

Lemma rk_line_unification : forall P1 P2 P3,
                            rk(P1 :: P2 :: nil) = 2 -> rk(P1 :: P3 :: nil) = 2 ->
                            rk(P2 :: P3 :: nil) = 2 -> rk(P1 :: P2 :: P3 :: nil) <= 2 ->
                            rk(P1 :: P2 :: P3 :: nil) = 2.
Proof.
intros P1 P2 P3 HP1P2eq HP1P3eq HP2P3eq HP1P2P3eq.

try clear HP1P2P3m;assert(HP1P2P3m : rk(P1 :: P2 :: P3 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

assert(rk(P1 :: P2 :: P3 ::  nil) <= 3) by (clear_ineg_rk;try lia;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P1 :: P2 :: P3 ::  nil) >= 1) by (clear_ineg_rk;try lia;try solve[apply matroid1_b_useful2;simpl;intuition]).
lia.
Qed.

(**********************************************************************************









*******************************************************************************

            fin du préambule

*******************************************************************************












***************************************************************************************)


(* dans la couche 0 *)
Lemma LABCD : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDM : rk(A :: B :: C :: D ::  nil) <= 4) by (solve_hyps_max HABCDeq HABCDM4).
assert(HABCDm : rk(A :: B :: C :: D ::  nil) >= 1) by (solve_hyps_min HABCDeq HABCDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDp : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HApBpCpDpM : rk(Ap :: Bp :: Cp :: Dp ::  nil) <= 4) by (solve_hyps_max HApBpCpDpeq HApBpCpDpM4).
assert(HApBpCpDpm : rk(Ap :: Bp :: Cp :: Dp ::  nil) >= 1) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDApBpCpDp : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDApBpCpDpM : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDApBpCpDpm : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) >= 1) by (solve_hyps_min HABCDApBpCpDpeq HABCDApBpCpDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDI : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: I ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDIM : rk(A :: B :: C :: D :: I ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDIm : rk(A :: B :: C :: D :: I ::  nil) >= 1) by (solve_hyps_min HABCDIeq HABCDIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpI : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HApBpCpDpIM : rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpIm : rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) >= 1) by (solve_hyps_min HApBpCpDpIeq HApBpCpDpIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDJ : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: J ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDJM : rk(A :: B :: C :: D :: J ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDJm : rk(A :: B :: C :: D :: J ::  nil) >= 1) by (solve_hyps_min HABCDJeq HABCDJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpJ : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HApBpCpDpJM : rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpJm : rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) >= 1) by (solve_hyps_min HApBpCpDpJeq HApBpCpDpJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDK : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: K ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDKM : rk(A :: B :: C :: D :: K ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDKm : rk(A :: B :: C :: D :: K ::  nil) >= 1) by (solve_hyps_min HABCDKeq HABCDKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpK : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HApBpCpDpKM : rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpKm : rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) >= 1) by (solve_hyps_min HApBpCpDpKeq HApBpCpDpKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LIJK : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(I :: J :: K ::  nil) = 3.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HIJKM : rk(I :: J :: K ::  nil) <= 3) by (solve_hyps_max HIJKeq HIJKM3).
assert(HIJKm : rk(I :: J :: K ::  nil) >= 1) by (solve_hyps_min HIJKeq HIJKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HABCDLM : rk(A :: B :: C :: D :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDLm : rk(A :: B :: C :: D :: L ::  nil) >= 1) by (solve_hyps_min HABCDLeq HABCDLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

assert(HApBpCpDpLM : rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpLm : rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpLeq HApBpCpDpLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDIL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: I :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCDIL requis par la preuve de (?)ABCDIL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDIL requis par la preuve de (?)ABCDIL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDILm4 : rk(A :: B :: C :: D :: I :: L :: nil) >= 4).
{
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: L :: nil) 4 4 HABCDmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDILM4 : rk(A :: B :: C :: D :: I :: L :: nil) <= 4).
{
	try assert(HABCDIeq : rk(A :: B :: C :: D :: I :: nil) = 4) by (apply LABCDI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDIMtmp : rk(A :: B :: C :: D :: I :: nil) <= 4) by (solve_hyps_max HABCDIeq HABCDIM4).
	try assert(HABCDLeq : rk(A :: B :: C :: D :: L :: nil) = 4) by (apply LABCDL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDLMtmp : rk(A :: B :: C :: D :: L :: nil) <= 4) by (solve_hyps_max HABCDLeq HABCDLM4).
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (list_inter (A :: B :: C :: D :: I :: nil) (A :: B :: C :: D :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: I :: L :: nil) (A :: B :: C :: D :: I :: A :: B :: C :: D :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: I :: A :: B :: C :: D :: L :: nil) ((A :: B :: C :: D :: I :: nil) ++ (A :: B :: C :: D :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: I :: nil) (A :: B :: C :: D :: L :: nil) (A :: B :: C :: D :: nil) 4 4 4 HABCDIMtmp HABCDLMtmp HABCDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDIM1. try clear HABCDIM2. try clear HABCDIM3. try clear HABCDIM4. try clear HABCDIM5. try clear HABCDIM6. try clear HABCDIM7. try clear HABCDIm7. try clear HABCDIm6. try clear HABCDIm5. try clear HABCDIm4. try clear HABCDIm3. try clear HABCDIm2. try clear HABCDIm1. try clear HABCDLM1. try clear HABCDLM2. try clear HABCDLM3. try clear HABCDLM4. try clear HABCDLM5. try clear HABCDLM6. try clear HABCDLM7. try clear HABCDLm7. try clear HABCDLm6. try clear HABCDLm5. try clear HABCDLm4. try clear HABCDLm3. try clear HABCDLm2. try clear HABCDLm1. 

assert(HABCDILM : rk(A :: B :: C :: D :: I :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDILm : rk(A :: B :: C :: D :: I :: L ::  nil) >= 1) by (solve_hyps_min HABCDILeq HABCDILm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpIL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: I :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ApBpCpDpIL requis par la preuve de (?)ApBpCpDpIL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ApBpCpDpIL requis par la preuve de (?)ApBpCpDpIL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpILm4 : rk(Ap :: Bp :: Cp :: Dp :: I :: L :: nil) >= 4).
{
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: L :: nil) 4 4 HApBpCpDpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpILM4 : rk(Ap :: Bp :: Cp :: Dp :: I :: L :: nil) <= 4).
{
	try assert(HApBpCpDpIeq : rk(Ap :: Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LApBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpIMtmp : rk(Ap :: Bp :: Cp :: Dp :: I :: nil) <= 4) by (solve_hyps_max HApBpCpDpIeq HApBpCpDpIM4).
	try assert(HApBpCpDpLeq : rk(Ap :: Bp :: Cp :: Dp :: L :: nil) = 4) by (apply LApBpCpDpL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpLMtmp : rk(Ap :: Bp :: Cp :: Dp :: L :: nil) <= 4) by (solve_hyps_max HApBpCpDpLeq HApBpCpDpLM4).
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: I :: nil) (Ap :: Bp :: Cp :: Dp :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: I :: L :: nil) (Ap :: Bp :: Cp :: Dp :: I :: Ap :: Bp :: Cp :: Dp :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: I :: Ap :: Bp :: Cp :: Dp :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: I :: nil) ++ (Ap :: Bp :: Cp :: Dp :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: I :: nil) (Ap :: Bp :: Cp :: Dp :: L :: nil) (Ap :: Bp :: Cp :: Dp :: nil) 4 4 4 HApBpCpDpIMtmp HApBpCpDpLMtmp HApBpCpDpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpIM1. try clear HApBpCpDpIM2. try clear HApBpCpDpIM3. try clear HApBpCpDpIM4. try clear HApBpCpDpIM5. try clear HApBpCpDpIM6. try clear HApBpCpDpIM7. try clear HApBpCpDpIm7. try clear HApBpCpDpIm6. try clear HApBpCpDpIm5. try clear HApBpCpDpIm4. try clear HApBpCpDpIm3. try clear HApBpCpDpIm2. try clear HApBpCpDpIm1. try clear HApBpCpDpLM1. try clear HApBpCpDpLM2. try clear HApBpCpDpLM3. try clear HApBpCpDpLM4. try clear HApBpCpDpLM5. try clear HApBpCpDpLM6. try clear HApBpCpDpLM7. try clear HApBpCpDpLm7. try clear HApBpCpDpLm6. try clear HApBpCpDpLm5. try clear HApBpCpDpLm4. try clear HApBpCpDpLm3. try clear HApBpCpDpLm2. try clear HApBpCpDpLm1. 

assert(HApBpCpDpILM : rk(Ap :: Bp :: Cp :: Dp :: I :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpILm : rk(Ap :: Bp :: Cp :: Dp :: I :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpILeq HApBpCpDpILm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDIJL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: I :: J :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCDIJL requis par la preuve de (?)ABCDIJL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDIJL requis par la preuve de (?)ABCDIJL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDIJLm4 : rk(A :: B :: C :: D :: I :: J :: L :: nil) >= 4).
{
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: J :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: J :: L :: nil) 4 4 HABCDmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDIJLM4 : rk(A :: B :: C :: D :: I :: J :: L :: nil) <= 4).
{
	try assert(HABCDJeq : rk(A :: B :: C :: D :: J :: nil) = 4) by (apply LABCDJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDJMtmp : rk(A :: B :: C :: D :: J :: nil) <= 4) by (solve_hyps_max HABCDJeq HABCDJM4).
	try assert(HABCDILeq : rk(A :: B :: C :: D :: I :: L :: nil) = 4) by (apply LABCDIL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDILMtmp : rk(A :: B :: C :: D :: I :: L :: nil) <= 4) by (solve_hyps_max HABCDILeq HABCDILM4).
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (list_inter (A :: B :: C :: D :: J :: nil) (A :: B :: C :: D :: I :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: I :: J :: L :: nil) (A :: B :: C :: D :: J :: A :: B :: C :: D :: I :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: J :: A :: B :: C :: D :: I :: L :: nil) ((A :: B :: C :: D :: J :: nil) ++ (A :: B :: C :: D :: I :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: J :: nil) (A :: B :: C :: D :: I :: L :: nil) (A :: B :: C :: D :: nil) 4 4 4 HABCDJMtmp HABCDILMtmp HABCDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDJM1. try clear HABCDJM2. try clear HABCDJM3. try clear HABCDJM4. try clear HABCDJM5. try clear HABCDJM6. try clear HABCDJM7. try clear HABCDJm7. try clear HABCDJm6. try clear HABCDJm5. try clear HABCDJm4. try clear HABCDJm3. try clear HABCDJm2. try clear HABCDJm1. 

assert(HABCDIJLM : rk(A :: B :: C :: D :: I :: J :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDIJLm : rk(A :: B :: C :: D :: I :: J :: L ::  nil) >= 1) by (solve_hyps_min HABCDIJLeq HABCDIJLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpIJL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ApBpCpDpIJL requis par la preuve de (?)ApBpCpDpIJL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ApBpCpDpIJL requis par la preuve de (?)ApBpCpDpIJL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpIJLm4 : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) >= 4).
{
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) 4 4 HApBpCpDpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpIJLM4 : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) <= 4).
{
	try assert(HApBpCpDpJeq : rk(Ap :: Bp :: Cp :: Dp :: J :: nil) = 4) by (apply LApBpCpDpJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpJMtmp : rk(Ap :: Bp :: Cp :: Dp :: J :: nil) <= 4) by (solve_hyps_max HApBpCpDpJeq HApBpCpDpJM4).
	try assert(HApBpCpDpILeq : rk(Ap :: Bp :: Cp :: Dp :: I :: L :: nil) = 4) by (apply LApBpCpDpIL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpILMtmp : rk(Ap :: Bp :: Cp :: Dp :: I :: L :: nil) <= 4) by (solve_hyps_max HApBpCpDpILeq HApBpCpDpILM4).
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: J :: nil) (Ap :: Bp :: Cp :: Dp :: I :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) (Ap :: Bp :: Cp :: Dp :: J :: Ap :: Bp :: Cp :: Dp :: I :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: J :: Ap :: Bp :: Cp :: Dp :: I :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: J :: nil) ++ (Ap :: Bp :: Cp :: Dp :: I :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: J :: nil) (Ap :: Bp :: Cp :: Dp :: I :: L :: nil) (Ap :: Bp :: Cp :: Dp :: nil) 4 4 4 HApBpCpDpJMtmp HApBpCpDpILMtmp HApBpCpDpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpJM1. try clear HApBpCpDpJM2. try clear HApBpCpDpJM3. try clear HApBpCpDpJM4. try clear HApBpCpDpJM5. try clear HApBpCpDpJM6. try clear HApBpCpDpJM7. try clear HApBpCpDpJm7. try clear HApBpCpDpJm6. try clear HApBpCpDpJm5. try clear HApBpCpDpJm4. try clear HApBpCpDpJm3. try clear HApBpCpDpJm2. try clear HApBpCpDpJm1. 

assert(HApBpCpDpIJLM : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpIJLm : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpIJLeq HApBpCpDpIJLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDIJKL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: I :: J :: K :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCDIJKL requis par la preuve de (?)ABCDIJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDIJKL requis par la preuve de (?)ABCDIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDIJKLm4 : rk(A :: B :: C :: D :: I :: J :: K :: L :: nil) >= 4).
{
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: nil) (A :: B :: C :: D :: I :: J :: K :: L :: nil) 4 4 HABCDmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HABCDIJKLM4 : rk(A :: B :: C :: D :: I :: J :: K :: L :: nil) <= 4).
{
	try assert(HABCDKeq : rk(A :: B :: C :: D :: K :: nil) = 4) by (apply LABCDK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDKMtmp : rk(A :: B :: C :: D :: K :: nil) <= 4) by (solve_hyps_max HABCDKeq HABCDKM4).
	try assert(HABCDIJLeq : rk(A :: B :: C :: D :: I :: J :: L :: nil) = 4) by (apply LABCDIJL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDIJLMtmp : rk(A :: B :: C :: D :: I :: J :: L :: nil) <= 4) by (solve_hyps_max HABCDIJLeq HABCDIJLM4).
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (list_inter (A :: B :: C :: D :: K :: nil) (A :: B :: C :: D :: I :: J :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: I :: J :: K :: L :: nil) (A :: B :: C :: D :: K :: A :: B :: C :: D :: I :: J :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: K :: A :: B :: C :: D :: I :: J :: L :: nil) ((A :: B :: C :: D :: K :: nil) ++ (A :: B :: C :: D :: I :: J :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: B :: C :: D :: K :: nil) (A :: B :: C :: D :: I :: J :: L :: nil) (A :: B :: C :: D :: nil) 4 4 4 HABCDKMtmp HABCDIJLMtmp HABCDmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HABCDKM1. try clear HABCDKM2. try clear HABCDKM3. try clear HABCDKM4. try clear HABCDKM5. try clear HABCDKM6. try clear HABCDKM7. try clear HABCDKm7. try clear HABCDKm6. try clear HABCDKm5. try clear HABCDKm4. try clear HABCDKm3. try clear HABCDKm2. try clear HABCDKm1. 

assert(HABCDIJKLM : rk(A :: B :: C :: D :: I :: J :: K :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDIJKLm : rk(A :: B :: C :: D :: I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HABCDIJKLeq HABCDIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBpCpDpIJKL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) = 4.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ApBpCpDpIJKL requis par la preuve de (?)ApBpCpDpIJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ApBpCpDpIJKL requis par la preuve de (?)ApBpCpDpIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HApBpCpDpIJKLm4 : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) >= 4).
{
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) 4 4 HApBpCpDpmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HApBpCpDpIJKLM4 : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) <= 4).
{
	try assert(HApBpCpDpKeq : rk(Ap :: Bp :: Cp :: Dp :: K :: nil) = 4) by (apply LApBpCpDpK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpKMtmp : rk(Ap :: Bp :: Cp :: Dp :: K :: nil) <= 4) by (solve_hyps_max HApBpCpDpKeq HApBpCpDpKM4).
	try assert(HApBpCpDpIJLeq : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) = 4) by (apply LApBpCpDpIJL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpIJLMtmp : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) <= 4) by (solve_hyps_max HApBpCpDpIJLeq HApBpCpDpIJLM4).
	try assert(HApBpCpDpeq : rk(Ap :: Bp :: Cp :: Dp :: nil) = 4) by (apply LApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(Hincl : incl (Ap :: Bp :: Cp :: Dp :: nil) (list_inter (Ap :: Bp :: Cp :: Dp :: K :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) (Ap :: Bp :: Cp :: Dp :: K :: Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Cp :: Dp :: K :: Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) ((Ap :: Bp :: Cp :: Dp :: K :: nil) ++ (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: Bp :: Cp :: Dp :: K :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: L :: nil) (Ap :: Bp :: Cp :: Dp :: nil) 4 4 4 HApBpCpDpKMtmp HApBpCpDpIJLMtmp HApBpCpDpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HApBpCpDpKM1. try clear HApBpCpDpKM2. try clear HApBpCpDpKM3. try clear HApBpCpDpKM4. try clear HApBpCpDpKM5. try clear HApBpCpDpKM6. try clear HApBpCpDpKM7. try clear HApBpCpDpKm7. try clear HApBpCpDpKm6. try clear HApBpCpDpKm5. try clear HApBpCpDpKm4. try clear HApBpCpDpKm3. try clear HApBpCpDpKm2. try clear HApBpCpDpKm1. 

assert(HApBpCpDpIJKLM : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HApBpCpDpIJKLm : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HApBpCpDpIJKLeq HApBpCpDpIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABCDApBpCpDpIJKL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) = 5.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour ABCDApBpCpDpIJKL requis par la preuve de (?)ABCDApBpCpDpIJKL pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour ABCDApBpCpDpIJKL requis par la preuve de (?)ABCDApBpCpDpIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDApBpCpDpIJKLm4 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) >= 4).
{
	try assert(HABCDeq : rk(A :: B :: C :: D :: nil) = 4) by (apply LABCD with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) 4 4 HABCDmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABCDApBpCpDpIJKLm5 : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) >= 5).
{
	try assert(HABCDApBpCpDpeq : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: nil) = 5) by (apply LABCDApBpCpDp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDApBpCpDpmtmp : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: nil) >= 5) by (solve_hyps_min HABCDApBpCpDpeq HABCDApBpCpDpm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: nil) (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) 5 5 HABCDApBpCpDpmtmp Hcomp Hincl);apply HT.
}
try clear HABCDApBpCpDpM1. try clear HABCDApBpCpDpM2. try clear HABCDApBpCpDpM3. try clear HABCDApBpCpDpM4. try clear HABCDApBpCpDpM5. try clear HABCDApBpCpDpM6. try clear HABCDApBpCpDpM7. try clear HABCDApBpCpDpm7. try clear HABCDApBpCpDpm6. try clear HABCDApBpCpDpm5. try clear HABCDApBpCpDpm4. try clear HABCDApBpCpDpm3. try clear HABCDApBpCpDpm2. try clear HABCDApBpCpDpm1. 

assert(HABCDApBpCpDpIJKLM : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HABCDApBpCpDpIJKLm : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HABCDApBpCpDpIJKLeq HABCDApBpCpDpIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LIJKL : forall A B C D Ap Bp Cp Dp I J K L ,
rk(A :: B :: C :: D ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp ::  nil) = 5 ->
rk(A :: B :: C :: D :: I ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(A :: B :: C :: D :: J ::  nil) = 4 ->
rk(Ap :: Bp :: Cp :: Dp :: J ::  nil) = 4 -> rk(A :: B :: C :: D :: K ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: K ::  nil) = 4 ->
rk(I :: J :: K ::  nil) = 3 -> rk(A :: B :: C :: D :: L ::  nil) = 4 -> rk(Ap :: Bp :: Cp :: Dp :: L ::  nil) = 4 ->
rk(I :: J :: L ::  nil) = 3 -> rk(I :: K :: L ::  nil) = 3 -> rk(J :: K :: L ::  nil) = 3 ->
rk(I :: J :: K :: L ::  nil) = 3.
Proof.

intros A B C D Ap Bp Cp Dp I J K L 
HABCDeq HApBpCpDpeq HABCDApBpCpDpeq HABCDIeq HApBpCpDpIeq HABCDJeq HApBpCpDpJeq HABCDKeq HApBpCpDpKeq HIJKeq
HABCDLeq HApBpCpDpLeq HIJLeq HIKLeq HJKLeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour IJKL requis par la preuve de (?)IJKL pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour IJKL requis par la preuve de (?)IJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HIJKLm3 : rk(I :: J :: K :: L :: nil) >= 3).
{
	try assert(HIJKeq : rk(I :: J :: K :: nil) = 3) by (apply LIJK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HIJKmtmp : rk(I :: J :: K :: nil) >= 3) by (solve_hyps_min HIJKeq HIJKm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (I :: J :: K :: nil) (I :: J :: K :: L :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (I :: J :: K :: nil) (I :: J :: K :: L :: nil) 3 3 HIJKmtmp Hcomp Hincl);apply HT.
}
try clear HIJKM1. try clear HIJKM2. try clear HIJKM3. try clear HIJKM4. try clear HIJKM5. try clear HIJKM6. try clear HIJKM7. try clear HIJKm7. try clear HIJKm6. try clear HIJKm5. try clear HIJKm4. try clear HIJKm3. try clear HIJKm2. try clear HIJKm1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HIJKLM3 : rk(I :: J :: K :: L :: nil) <= 3).
{
	try assert(HABCDIJKLeq : rk(A :: B :: C :: D :: I :: J :: K :: L :: nil) = 4) by (apply LABCDIJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDIJKLMtmp : rk(A :: B :: C :: D :: I :: J :: K :: L :: nil) <= 4) by (solve_hyps_max HABCDIJKLeq HABCDIJKLM4).
	try assert(HApBpCpDpIJKLeq : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) = 4) by (apply LApBpCpDpIJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HApBpCpDpIJKLMtmp : rk(Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) <= 4) by (solve_hyps_max HApBpCpDpIJKLeq HApBpCpDpIJKLM4).
	try assert(HABCDApBpCpDpIJKLeq : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) = 5) by (apply LABCDApBpCpDpIJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HABCDApBpCpDpIJKLmtmp : rk(A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) >= 5) by (solve_hyps_min HABCDApBpCpDpIJKLeq HABCDApBpCpDpIJKLm5).
	assert(Hincl : incl (I :: J :: K :: L :: nil) (list_inter (A :: B :: C :: D :: I :: J :: K :: L :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) (A :: B :: C :: D :: I :: J :: K :: L :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: C :: D :: I :: J :: K :: L :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) ((A :: B :: C :: D :: I :: J :: K :: L :: nil) ++ (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDApBpCpDpIJKLmtmp;try rewrite HT2 in HABCDApBpCpDpIJKLmtmp.
	assert(HT := rule_3 (A :: B :: C :: D :: I :: J :: K :: L :: nil) (Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L :: nil) (I :: J :: K :: L :: nil) 4 4 5 HABCDIJKLMtmp HApBpCpDpIJKLMtmp HABCDApBpCpDpIJKLmtmp Hincl);apply HT.
}


assert(HIJKLM : rk(I :: J :: K :: L ::  nil) <= 4) by (solve_hyps_max HIJKLeq HIJKLM4).
assert(HIJKLm : rk(I :: J :: K :: L ::  nil) >= 1) by (solve_hyps_min HIJKLeq HIJKLm1).
intuition.
Qed.

