
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

Lemma Desargues : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10,
rk(P1 :: P4 :: P7 :: nil) = 2 -> rk(P2 :: P5 :: P7 :: nil) = 2 -> rk(P3 :: P6 :: P7 :: nil) = 2 -> 
rk(P4 :: P5 :: P6 :: nil) = 3 -> rk(P1 :: P2 :: P3 :: nil) = 3 ->
rk(P1 :: P2 :: P3 :: P4 :: nil) = 4 -> 
rk(P4 :: P5 :: P10 :: nil) = 2 -> rk(P1 :: P2 :: P10 :: nil) = 2 ->
rk(P4 :: P6 :: P9 :: nil) = 2 -> rk(P1 :: P3 :: P9 :: nil) = 2 ->
rk(P5 :: P6 :: P8 :: nil) = 2 -> rk(P2 :: P3 :: P8 :: nil) = 2 ->
rk(P1 :: P4 :: nil) = 2 -> rk(P3 :: P6 :: nil) = 2 -> rk(P2 :: P5 :: nil) = 2 ->
rk (P8 :: P9 :: P10 :: nil) = 2.
Proof.
intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 HP1P4P7eq HP2P5P7eq HP3P6P7eq HP4P5P6eq HP1P2P3eq HP1P2P3P4eq HP4P5P10eq HP1P2P10eq HP4P6P9eq HP1P3P9eq HP5P6P8eq HP2P3P8eq HP1P4eq HP3P6eq HP2P5eq. 

try clear HP1P2m;assert(HP1P2m : rk(P1 :: P2 :: nil) >= 2).
{
	try assert(HP3Mtmp : rk(P3 :: nil) <= 1) by (solve_hyps_max HP3eq HP3M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: nil) (P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: P2 :: nil) ++ (P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_2 (P1 :: P2 :: nil) (P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP3Mtmp Hincl); apply HT.
}

try clear HP1P2P3P8P10m;assert(HP1P2P3P8P10m : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P10m;assert(HP1P2P3P8P10m : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P10M;assert(HP1P2P3P8P10M : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) <= 3).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP1P2P10Mtmp : rk(P1 :: P2 :: P10 :: nil) <= 2) by (solve_hyps_max HP1P2P10eq HP1P2P10M).
	try assert(HP2mtmp : rk(P2 :: nil) >= 1) by (solve_hyps_min HP2eq HP2m).
	assert(Hincl : incl (P2 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P10 :: nil) (P2 :: P3 :: P8 :: P1 :: P2 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P1 :: P2 :: P10 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P1 :: P2 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P10 :: nil) (P2 :: nil) 2 2 1 HP2P3P8Mtmp HP1P2P10Mtmp HP2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP1P3m;assert(HP1P3m : rk(P1 :: P3 :: nil) >= 2).
{
	try assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P2 :: P1 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P3 :: nil) ((P2 :: nil) ++ (P1 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P2 :: nil) (P1 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP2Mtmp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10m;assert(HP1P2P3P8P9P10m : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10m;assert(HP1P2P3P8P9P10m : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P8P9P10M;assert(HP1P2P3P8P9P10M : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) <= 3).
{
	try assert(HP1P3P9Mtmp : rk(P1 :: P3 :: P9 :: nil) <= 2) by (solve_hyps_max HP1P3P9eq HP1P3P9M).
	try assert(HP1P2P3P8P10Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P10 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P10eq HP1P2P3P8P10M).
	try assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m).
	assert(Hincl : incl (P1 :: P3 :: nil) (list_inter (P1 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P1 :: P3 :: P9 :: P1 :: P2 :: P3 :: P8 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P3 :: P9 :: P1 :: P2 :: P3 :: P8 :: P10 :: nil) ((P1 :: P3 :: P9 :: nil) ++ (P1 :: P2 :: P3 :: P8 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: P8 :: P10 :: nil) (P1 :: P3 :: nil) 2 3 2 HP1P3P9Mtmp HP1P2P3P8P10Mtmp HP1P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5m;assert(HP4P5m : rk(P4 :: P5 :: nil) >= 2).
{
	try assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M).
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: P5 :: nil) (P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: nil) ((P4 :: P5 :: nil) ++ (P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_2 (P4 :: P5 :: nil) (P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP6Mtmp Hincl); apply HT.
}

try clear HP4P5P6P8P9m;assert(HP4P5P6P8P9m : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8P9m;assert(HP4P5P6P8P9m : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8P9M;assert(HP4P5P6P8P9M : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P6P9Mtmp : rk(P4 :: P6 :: P9 :: nil) <= 2) by (solve_hyps_max HP4P6P9eq HP4P6P9M).
	try assert(HP6mtmp : rk(P6 :: nil) >= 1) by (solve_hyps_min HP6eq HP6m).
	assert(Hincl : incl (P6 :: nil) (list_inter (P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: P9 :: nil) (P5 :: P6 :: P8 :: P4 :: P6 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P8 :: P4 :: P6 :: P9 :: nil) ((P5 :: P6 :: P8 :: nil) ++ (P4 :: P6 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P9 :: nil) (P6 :: nil) 2 2 1 HP5P6P8Mtmp HP4P6P9Mtmp HP6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5P6P8M;assert(HP4P5P6P8M : rk(P4 :: P5 :: P6 :: P8 :: nil) <= 3).
{
	try assert(HP4Mtmp : rk(P4 :: nil) <= 1) by (solve_hyps_max HP4eq HP4M).
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P4 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) ((P4 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: nil) (P5 :: P6 :: P8 :: nil) (nil) 1 2 0 HP4Mtmp HP5P6P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP4P5P6P8m;assert(HP4P5P6P8m : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P6 :: P8 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P6P8m;assert(HP4P5P6P8m : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P8 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P7m;assert(HP1P2P3P4P7m : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P7 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3m;assert(HP2P3m : rk(P2 :: P3 :: nil) >= 2).
{
	try assert(HP1Mtmp : rk(P1 :: nil) <= 1) by (solve_hyps_max HP1eq HP1M).
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: nil) (P2 :: P3 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: nil) ((P1 :: nil) ++ (P2 :: P3 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3mtmp;try rewrite HT2 in HP1P2P3mtmp.
	assert(HT := rule_4 (P1 :: nil) (P2 :: P3 :: nil) (nil) 3 0 1 HP1P2P3mtmp Hmtmp HP1Mtmp Hincl); apply HT.
}

try clear HP2P3P7m;assert(HP2P3P7m : rk(P2 :: P3 :: P7 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P7 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P7 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P7m;assert(HP2P3P7m : rk(P2 :: P3 :: P7 :: nil) >= 3).
{
	try assert(HP1P4P7Mtmp : rk(P1 :: P4 :: P7 :: nil) <= 2) by (solve_hyps_max HP1P4P7eq HP1P4P7M).
	try assert(HP1P2P3P4P7mtmp : rk(P1 :: P2 :: P3 :: P4 :: P7 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P7eq HP1P2P3P4P7m).
	try assert(HP7mtmp : rk(P7 :: nil) >= 1) by (solve_hyps_min HP7eq HP7m).
	assert(Hincl : incl (P7 :: nil) (list_inter (P2 :: P3 :: P7 :: nil) (P1 :: P4 :: P7 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P7 :: nil) (P2 :: P3 :: P7 :: P1 :: P4 :: P7 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P7 :: P1 :: P4 :: P7 :: nil) ((P2 :: P3 :: P7 :: nil) ++ (P1 :: P4 :: P7 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P7mtmp;try rewrite HT2 in HP1P2P3P4P7mtmp.
	assert(HT := rule_2 (P2 :: P3 :: P7 :: nil) (P1 :: P4 :: P7 :: nil) (P7 :: nil) 4 1 2 HP1P2P3P4P7mtmp HP7mtmp HP1P4P7Mtmp Hincl); apply HT.
}

try clear HP2P3P5P7P8m;assert(HP2P3P5P7P8m : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P7P8m;assert(HP2P3P5P7P8m : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	try assert(HP2P3P7mtmp : rk(P2 :: P3 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P3P7eq HP2P3P7m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P5 :: P7 :: P8 :: nil) 3 3 HP2P3P7mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P7P8M;assert(HP2P3P5P7P8M : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) <= 3).
{
	try assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2mtmp : rk(P2 :: nil) >= 1) by (solve_hyps_min HP2eq HP2m).
	assert(Hincl : incl (P2 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P2 :: P3 :: P8 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P8 :: nil) (P2 :: nil) 2 2 1 HP2P5P7Mtmp HP2P3P8Mtmp HP2mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P5P8m;assert(HP2P3P5P8m : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P5P8M;assert(HP2P3P5P8M : rk(P2 :: P3 :: P5 :: P8 :: nil) <= 3).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P8 :: nil) (P5 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P2 :: P3 :: P8 :: nil) ((P5 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: nil) (P2 :: P3 :: P8 :: nil) (nil) 1 2 0 HP5Mtmp HP2P3P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P5P8m;assert(HP2P3P5P8m : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 3).
{
	try assert(HP2P5P7Mtmp : rk(P2 :: P5 :: P7 :: nil) <= 2) by (solve_hyps_max HP2P5P7eq HP2P5P7M).
	try assert(HP2P3P5P7P8mtmp : rk(P2 :: P3 :: P5 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P5P7P8eq HP2P3P5P7P8m).
	try assert(HP2P5mtmp : rk(P2 :: P5 :: nil) >= 2) by (solve_hyps_min HP2P5eq HP2P5m).
	assert(Hincl : incl (P2 :: P5 :: nil) (list_inter (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P7 :: P8 :: nil) (P2 :: P5 :: P7 :: P2 :: P3 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P5 :: P7 :: P2 :: P3 :: P5 :: P8 :: nil) ((P2 :: P5 :: P7 :: nil) ++ (P2 :: P3 :: P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P7P8mtmp;try rewrite HT2 in HP2P3P5P7P8mtmp.
	assert(HT := rule_4 (P2 :: P5 :: P7 :: nil) (P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P5 :: nil) 3 2 2 HP2P3P5P7P8mtmp HP2P5mtmp HP2P5P7Mtmp Hincl); apply HT.
}

try clear HP5P8m;assert(HP5P8m : rk(P5 :: P8 :: nil) >= 2).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2P3P5P8mtmp : rk(P2 :: P3 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P5P8eq HP2P3P5P8m).
	try assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m).
	assert(Hincl : incl (P8 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P5 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P5 :: P8 :: nil) (P2 :: P3 :: P8 :: P5 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P5 :: P8 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P5 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P5P8mtmp;try rewrite HT2 in HP2P3P5P8mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P8 :: nil) (P5 :: P8 :: nil) (P8 :: nil) 3 1 2 HP2P3P5P8mtmp HP8mtmp HP2P3P8Mtmp Hincl); apply HT.
}

try clear HP4P5P8m;assert(HP4P5P8m : rk(P4 :: P5 :: P8 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8m;assert(HP4P5P8m : rk(P4 :: P5 :: P8 :: nil) >= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P5P6P8mtmp : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P6P8eq HP4P5P6P8m).
	try assert(HP5P8mtmp : rk(P5 :: P8 :: nil) >= 2) by (solve_hyps_min HP5P8eq HP5P8m).
	assert(Hincl : incl (P5 :: P8 :: nil) (list_inter (P4 :: P5 :: P8 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P8 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P8 :: P5 :: P6 :: P8 :: nil) ((P4 :: P5 :: P8 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8mtmp;try rewrite HT2 in HP4P5P6P8mtmp.
	assert(HT := rule_2 (P4 :: P5 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) (P5 :: P8 :: nil) 3 2 2 HP4P5P6P8mtmp HP5P8mtmp HP5P6P8Mtmp Hincl); apply HT.
}

try clear HP4P5P8P9m;assert(HP4P5P8P9m : rk(P4 :: P5 :: P8 :: P9 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9m;assert(HP4P5P8P9m : rk(P4 :: P5 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: nil) 3 3 HP4P5P8mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9M;assert(HP4P5P8P9M : rk(P4 :: P5 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP4P5P6P8P9Mtmp : rk(P4 :: P5 :: P6 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P6P8P9eq HP4P5P6P8P9M).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P8 :: P9 :: nil) 3 3 HP4P5P6P8P9Mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10m;assert(HP4P5P8P9P10m : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) 2 2 HP4P5mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10m;assert(HP4P5P8P9P10m : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP4P5P8mtmp : rk(P4 :: P5 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P8eq HP4P5P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P8 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) 3 3 HP4P5P8mtmp Hcomp Hincl); apply HT.
}

try clear HP4P5P8P9P10M;assert(HP4P5P8P9P10M : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) <= 3).
{
	try assert(HP4P5P8P9Mtmp : rk(P4 :: P5 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P8P9eq HP4P5P8P9M).
	try assert(HP4P5P10Mtmp : rk(P4 :: P5 :: P10 :: nil) <= 2) by (solve_hyps_max HP4P5P10eq HP4P5P10M).
	try assert(HP4P5mtmp : rk(P4 :: P5 :: nil) >= 2) by (solve_hyps_min HP4P5eq HP4P5m).
	assert(Hincl : incl (P4 :: P5 :: nil) (list_inter (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P4 :: P5 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P8 :: P9 :: P4 :: P5 :: P10 :: nil) ((P4 :: P5 :: P8 :: P9 :: nil) ++ (P4 :: P5 :: P10 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P8 :: P9 :: nil) (P4 :: P5 :: P10 :: nil) (P4 :: P5 :: nil) 3 2 2 HP4P5P8P9Mtmp HP4P5P10Mtmp HP4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP1P2mtmp : rk(P1 :: P2 :: nil) >= 2) by (solve_hyps_min HP1P2eq HP1P2m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 2 2 HP1P2mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP1P2P3P4P5P8P9P10m;assert(HP1P2P3P4P5P8P9P10m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 4).
{
	try assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8m;assert(HP2P3P6P7P8m : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8m;assert(HP2P3P6P7P8m : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 3).
{
	try assert(HP2P3P7mtmp : rk(P2 :: P3 :: P7 :: nil) >= 3) by (solve_hyps_min HP2P3P7eq HP2P3P7m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: P7 :: nil) (P2 :: P3 :: P6 :: P7 :: P8 :: nil) 3 3 HP2P3P7mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P7P8M;assert(HP2P3P6P7P8M : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) <= 3).
{
	try assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m).
	assert(Hincl : incl (P3 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P7 :: P8 :: nil) (P3 :: P6 :: P7 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P2 :: P3 :: P8 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P8 :: nil) (P3 :: nil) 2 2 1 HP3P6P7Mtmp HP2P3P8Mtmp HP3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P6P8m;assert(HP2P3P6P8m : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P2 :: P3 :: P6 :: P8 :: nil) 2 2 HP2P3mtmp Hcomp Hincl); apply HT.
}

try clear HP2P3P6P8M;assert(HP2P3P6P8M : rk(P2 :: P3 :: P6 :: P8 :: nil) <= 3).
{
	try assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M).
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P2 :: P3 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P8 :: nil) (P6 :: P2 :: P3 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P2 :: P3 :: P8 :: nil) ((P6 :: nil) ++ (P2 :: P3 :: P8 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: nil) (P2 :: P3 :: P8 :: nil) (nil) 1 2 0 HP6Mtmp HP2P3P8Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

try clear HP2P3P6P8m;assert(HP2P3P6P8m : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP3P6P7Mtmp : rk(P3 :: P6 :: P7 :: nil) <= 2) by (solve_hyps_max HP3P6P7eq HP3P6P7M).
	try assert(HP2P3P6P7P8mtmp : rk(P2 :: P3 :: P6 :: P7 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P6P7P8eq HP2P3P6P7P8m).
	try assert(HP3P6mtmp : rk(P3 :: P6 :: nil) >= 2) by (solve_hyps_min HP3P6eq HP3P6m).
	assert(Hincl : incl (P3 :: P6 :: nil) (list_inter (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P7 :: P8 :: nil) (P3 :: P6 :: P7 :: P2 :: P3 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P6 :: P7 :: P2 :: P3 :: P6 :: P8 :: nil) ((P3 :: P6 :: P7 :: nil) ++ (P2 :: P3 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P6P7P8mtmp;try rewrite HT2 in HP2P3P6P7P8mtmp.
	assert(HT := rule_4 (P3 :: P6 :: P7 :: nil) (P2 :: P3 :: P6 :: P8 :: nil) (P3 :: P6 :: nil) 3 2 2 HP2P3P6P7P8mtmp HP3P6mtmp HP3P6P7Mtmp Hincl); apply HT.
}

try clear HP6P8m;assert(HP6P8m : rk(P6 :: P8 :: nil) >= 2).
{
	try assert(HP2P3P8Mtmp : rk(P2 :: P3 :: P8 :: nil) <= 2) by (solve_hyps_max HP2P3P8eq HP2P3P8M).
	try assert(HP2P3P6P8mtmp : rk(P2 :: P3 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP2P3P6P8eq HP2P3P6P8m).
	try assert(HP8mtmp : rk(P8 :: nil) >= 1) by (solve_hyps_min HP8eq HP8m).
	assert(Hincl : incl (P8 :: nil) (list_inter (P2 :: P3 :: P8 :: nil) (P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P2 :: P3 :: P6 :: P8 :: nil) (P2 :: P3 :: P8 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P3 :: P8 :: P6 :: P8 :: nil) ((P2 :: P3 :: P8 :: nil) ++ (P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP2P3P6P8mtmp;try rewrite HT2 in HP2P3P6P8mtmp.
	assert(HT := rule_4 (P2 :: P3 :: P8 :: nil) (P6 :: P8 :: nil) (P8 :: nil) 3 1 2 HP2P3P6P8mtmp HP8mtmp HP2P3P8Mtmp Hincl); apply HT.
}

try clear HP4P6m;assert(HP4P6m : rk(P4 :: P6 :: nil) >= 2).
{
	try assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M).
	try assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m).
	try assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P5 :: nil) (P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: nil) (P5 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P4 :: P6 :: nil) ((P5 :: nil) ++ (P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6mtmp;try rewrite HT2 in HP4P5P6mtmp.
	assert(HT := rule_4 (P5 :: nil) (P4 :: P6 :: nil) (nil) 3 0 1 HP4P5P6mtmp Hmtmp HP5Mtmp Hincl); apply HT.
}

try clear HP4P6P8m;assert(HP4P6P8m : rk(P4 :: P6 :: P8 :: nil) >= 2).
{
	try assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: nil) 2 2 HP4P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P6P8m;assert(HP4P6P8m : rk(P4 :: P6 :: P8 :: nil) >= 3).
{
	try assert(HP5P6P8Mtmp : rk(P5 :: P6 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P8eq HP5P6P8M).
	try assert(HP4P5P6P8mtmp : rk(P4 :: P5 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P5P6P8eq HP4P5P6P8m).
	try assert(HP6P8mtmp : rk(P6 :: P8 :: nil) >= 2) by (solve_hyps_min HP6P8eq HP6P8m).
	assert(Hincl : incl (P6 :: P8 :: nil) (list_inter (P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P8 :: P5 :: P6 :: P8 :: nil) ((P4 :: P6 :: P8 :: nil) ++ (P5 :: P6 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P8mtmp;try rewrite HT2 in HP4P5P6P8mtmp.
	assert(HT := rule_2 (P4 :: P6 :: P8 :: nil) (P5 :: P6 :: P8 :: nil) (P6 :: P8 :: nil) 3 2 2 HP4P5P6P8mtmp HP6P8mtmp HP5P6P8Mtmp Hincl); apply HT.
}

try clear HP4P6P8P9P10m;assert(HP4P6P8P9P10m : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P6mtmp : rk(P4 :: P6 :: nil) >= 2) by (solve_hyps_min HP4P6eq HP4P6m).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil) 2 2 HP4P6mtmp Hcomp Hincl); apply HT.
}

try clear HP4P6P8P9P10m;assert(HP4P6P8P9P10m : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 3).
{
	try assert(HP4P6P8mtmp : rk(P4 :: P6 :: P8 :: nil) >= 3) by (solve_hyps_min HP4P6P8eq HP4P6P8m).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P6 :: P8 :: nil) (P4 :: P6 :: P8 :: P9 :: P10 :: nil) 3 3 HP4P6P8mtmp Hcomp Hincl); apply HT.
}

try clear HP8P9P10m;assert(HP8P9P10m : rk(P8 :: P9 :: P10 :: nil) >= 2).
{
	try assert(HP4P6P9Mtmp : rk(P4 :: P6 :: P9 :: nil) <= 2) by (solve_hyps_max HP4P6P9eq HP4P6P9M).
	try assert(HP4P6P8P9P10mtmp : rk(P4 :: P6 :: P8 :: P9 :: P10 :: nil) >= 3) by (solve_hyps_min HP4P6P8P9P10eq HP4P6P8P9P10m).
	try assert(HP9mtmp : rk(P9 :: nil) >= 1) by (solve_hyps_min HP9eq HP9m).
	assert(Hincl : incl (P9 :: nil) (list_inter (P4 :: P6 :: P9 :: nil) (P8 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P6 :: P8 :: P9 :: P10 :: nil) (P4 :: P6 :: P9 :: P8 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P6 :: P9 :: P8 :: P9 :: P10 :: nil) ((P4 :: P6 :: P9 :: nil) ++ (P8 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P6P8P9P10mtmp;try rewrite HT2 in HP4P6P8P9P10mtmp.
	assert(HT := rule_4 (P4 :: P6 :: P9 :: nil) (P8 :: P9 :: P10 :: nil) (P9 :: nil) 3 1 2 HP4P6P8P9P10mtmp HP9mtmp HP4P6P9Mtmp Hincl); apply HT.
}

try clear HP8P9P10M;assert(HP8P9P10M : rk(P8 :: P9 :: P10 :: nil) <= 2).
{
	try assert(HP1P2P3P8P9P10Mtmp : rk(P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8P9P10eq HP1P2P3P8P9P10M).
	try assert(HP4P5P8P9P10Mtmp : rk(P4 :: P5 :: P8 :: P9 :: P10 :: nil) <= 3) by (solve_hyps_max HP4P5P8P9P10eq HP4P5P8P9P10M).
	try assert(HP1P2P3P4P5P8P9P10mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P8P9P10eq HP1P2P3P4P5P8P9P10m).
	assert(Hincl : incl (P8 :: P9 :: P10 :: nil) (list_inter (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: P4 :: P5 :: P8 :: P9 :: P10 :: nil) ((P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) ++ (P4 :: P5 :: P8 :: P9 :: P10 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P8P9P10mtmp;try rewrite HT2 in HP1P2P3P4P5P8P9P10mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P8 :: P9 :: P10 :: nil) (P4 :: P5 :: P8 :: P9 :: P10 :: nil) (P8 :: P9 :: P10 :: nil) 3 3 4 HP1P2P3P8P9P10Mtmp HP4P5P8P9P10Mtmp HP1P2P3P4P5P8P9P10mtmp Hincl); apply HT.
}

assert(rk(P8 :: P9 :: P10 ::  nil) <= 3) by (clear_ineg_rk;try lia;try apply rk_upper_dim;try solve[apply matroid1_b_useful;simpl;intuition]).
assert(rk(P8 :: P9 :: P10 ::  nil) >= 1) by (clear_ineg_rk;try lia;try solve[apply matroid1_b_useful2;simpl;intuition]).
lia.
Qed.












(* dans la couche 0 *)
Lemma LBCDAp : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApM : rk(B :: C :: D :: Ap ::  nil) <= 4) by (solve_hyps_max HBCDApeq HBCDApM4).
assert(HBCDApm : rk(B :: C :: D :: Ap ::  nil) >= 1) by (solve_hyps_min HBCDApeq HBCDApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpI : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBpCpDpIM : rk(Bp :: Cp :: Dp :: I ::  nil) <= 4) by (solve_hyps_max HBpCpDpIeq HBpCpDpIM4).
assert(HBpCpDpIm : rk(Bp :: Cp :: Dp :: I ::  nil) >= 1) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApBpCpDpI : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApBpCpDpIM : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApBpCpDpIm : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) >= 1) by (solve_hyps_min HBCDApBpCpDpIeq HBCDApBpCpDpIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApJ : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApJM : rk(B :: C :: D :: Ap :: J ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApJm : rk(B :: C :: D :: Ap :: J ::  nil) >= 1) by (solve_hyps_min HBCDApJeq HBCDApJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIJ : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBpCpDpIJM : rk(Bp :: Cp :: Dp :: I :: J ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIJm : rk(Bp :: Cp :: Dp :: I :: J ::  nil) >= 1) by (solve_hyps_min HBpCpDpIJeq HBpCpDpIJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApK : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: K ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApKM : rk(B :: C :: D :: Ap :: K ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApKm : rk(B :: C :: D :: Ap :: K ::  nil) >= 1) by (solve_hyps_min HBCDApKeq HBCDApKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIK : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBpCpDpIKM : rk(Bp :: Cp :: Dp :: I :: K ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIKm : rk(Bp :: Cp :: Dp :: I :: K ::  nil) >= 1) by (solve_hyps_min HBpCpDpIKeq HBpCpDpIKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: L ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApLM : rk(B :: C :: D :: Ap :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApLm : rk(B :: C :: D :: Ap :: L ::  nil) >= 1) by (solve_hyps_min HBCDApLeq HBCDApLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBpCpDpILM : rk(Bp :: Cp :: Dp :: I :: L ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpILm : rk(Bp :: Cp :: Dp :: I :: L ::  nil) >= 1) by (solve_hyps_min HBpCpDpILeq HBpCpDpILm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LJKL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(J :: K :: L ::  nil) = 3.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HJKLM : rk(J :: K :: L ::  nil) <= 3) by (solve_hyps_max HJKLeq HJKLM3).
assert(HJKLm : rk(J :: K :: L ::  nil) >= 1) by (solve_hyps_min HJKLeq HJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDAp : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBCDApM : rk(B :: C :: D :: Ap ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApm : rk(B :: C :: D :: Ap ::  ::  nil) >= 1) by (solve_hyps_min HBCDApeq HBCDApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpI : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

assert(HBpCpDpIM : rk(Bp :: Cp :: Dp :: I ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIm : rk(Bp :: Cp :: Dp :: I ::  ::  nil) >= 1) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApJ : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: J ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDApJ requis par la preuve de (?)BCDApJ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDApJ requis par la preuve de (?)BCDApJ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCDApJm4 : rk(B :: C :: D :: Ap :: J ::  :: nil) >= 4).
{
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J ::  :: nil) 4 4 HBCDApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCDApJM4 : rk(B :: C :: D :: Ap :: J ::  :: nil) <= 4).
{
	try assert(HBCDApJeq : rk(B :: C :: D :: Ap :: J :: nil) = 4) by (apply LBCDApJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApJMtmp : rk(B :: C :: D :: Ap :: J :: nil) <= 4) by (solve_hyps_max HBCDApJeq HBCDApJM4).
	try assert(HBCDApeq : rk(B :: C :: D :: Ap ::  :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApMtmp : rk(B :: C :: D :: Ap ::  :: nil) <= 4) by (solve_hyps_max HBCDApeq HBCDApM4).
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (list_inter (B :: C :: D :: Ap :: J :: nil) (B :: C :: D :: Ap ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: Ap :: J ::  :: nil) (B :: C :: D :: Ap :: J :: B :: C :: D :: Ap ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: Ap :: J :: B :: C :: D :: Ap ::  :: nil) ((B :: C :: D :: Ap :: J :: nil) ++ (B :: C :: D :: Ap ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: D :: Ap :: J :: nil) (B :: C :: D :: Ap ::  :: nil) (B :: C :: D :: Ap :: nil) 4 4 4 HBCDApJMtmp HBCDApMtmp HBCDApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBCDApJM1. try clear HBCDApJM2. try clear HBCDApJM3. try clear HBCDApJM4. try clear HBCDApJM5. try clear HBCDApJM6. try clear HBCDApJM7. try clear HBCDApJm7. try clear HBCDApJm6. try clear HBCDApJm5. try clear HBCDApJm4. try clear HBCDApJm3. try clear HBCDApJm2. try clear HBCDApJm1. try clear HBCDApM1. try clear HBCDApM2. try clear HBCDApM3. try clear HBCDApM4. try clear HBCDApM5. try clear HBCDApM6. try clear HBCDApM7. try clear HBCDApm7. try clear HBCDApm6. try clear HBCDApm5. try clear HBCDApm4. try clear HBCDApm3. try clear HBCDApm2. try clear HBCDApm1. 

assert(HBCDApJM : rk(B :: C :: D :: Ap :: J ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApJm : rk(B :: C :: D :: Ap :: J ::  ::  nil) >= 1) by (solve_hyps_min HBCDApJeq HBCDApJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIJ : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: J ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BpCpDpIJ requis par la preuve de (?)BpCpDpIJ pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BpCpDpIJ requis par la preuve de (?)BpCpDpIJ pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBpCpDpIJm4 : rk(Bp :: Cp :: Dp :: I :: J ::  :: nil) >= 4).
{
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J ::  :: nil) 4 4 HBpCpDpImtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBpCpDpIJM4 : rk(Bp :: Cp :: Dp :: I :: J ::  :: nil) <= 4).
{
	try assert(HBpCpDpIJeq : rk(Bp :: Cp :: Dp :: I :: J :: nil) = 4) by (apply LBpCpDpIJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIJMtmp : rk(Bp :: Cp :: Dp :: I :: J :: nil) <= 4) by (solve_hyps_max HBpCpDpIJeq HBpCpDpIJM4).
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I ::  :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIMtmp : rk(Bp :: Cp :: Dp :: I ::  :: nil) <= 4) by (solve_hyps_max HBpCpDpIeq HBpCpDpIM4).
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (list_inter (Bp :: Cp :: Dp :: I :: J :: nil) (Bp :: Cp :: Dp :: I ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bp :: Cp :: Dp :: I :: J ::  :: nil) (Bp :: Cp :: Dp :: I :: J :: Bp :: Cp :: Dp :: I ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: Dp :: I :: J :: Bp :: Cp :: Dp :: I ::  :: nil) ((Bp :: Cp :: Dp :: I :: J :: nil) ++ (Bp :: Cp :: Dp :: I ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: Dp :: I :: J :: nil) (Bp :: Cp :: Dp :: I ::  :: nil) (Bp :: Cp :: Dp :: I :: nil) 4 4 4 HBpCpDpIJMtmp HBpCpDpIMtmp HBpCpDpImtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpCpDpIJM1. try clear HBpCpDpIJM2. try clear HBpCpDpIJM3. try clear HBpCpDpIJM4. try clear HBpCpDpIJM5. try clear HBpCpDpIJM6. try clear HBpCpDpIJM7. try clear HBpCpDpIJm7. try clear HBpCpDpIJm6. try clear HBpCpDpIJm5. try clear HBpCpDpIJm4. try clear HBpCpDpIJm3. try clear HBpCpDpIJm2. try clear HBpCpDpIJm1. try clear HBpCpDpIM1. try clear HBpCpDpIM2. try clear HBpCpDpIM3. try clear HBpCpDpIM4. try clear HBpCpDpIM5. try clear HBpCpDpIM6. try clear HBpCpDpIM7. try clear HBpCpDpIm7. try clear HBpCpDpIm6. try clear HBpCpDpIm5. try clear HBpCpDpIm4. try clear HBpCpDpIm3. try clear HBpCpDpIm2. try clear HBpCpDpIm1. 

assert(HBpCpDpIJM : rk(Bp :: Cp :: Dp :: I :: J ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIJm : rk(Bp :: Cp :: Dp :: I :: J ::  ::  nil) >= 1) by (solve_hyps_min HBpCpDpIJeq HBpCpDpIJm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApJK : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: J :: K ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDApJK requis par la preuve de (?)BCDApJK pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDApJK requis par la preuve de (?)BCDApJK pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCDApJKm4 : rk(B :: C :: D :: Ap :: J :: K ::  :: nil) >= 4).
{
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J :: K ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J :: K ::  :: nil) 4 4 HBCDApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCDApJKM4 : rk(B :: C :: D :: Ap :: J :: K ::  :: nil) <= 4).
{
	try assert(HBCDApKeq : rk(B :: C :: D :: Ap :: K :: nil) = 4) by (apply LBCDApK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApKMtmp : rk(B :: C :: D :: Ap :: K :: nil) <= 4) by (solve_hyps_max HBCDApKeq HBCDApKM4).
	try assert(HBCDApJeq : rk(B :: C :: D :: Ap :: J ::  :: nil) = 4) by (apply LBCDApJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApJMtmp : rk(B :: C :: D :: Ap :: J ::  :: nil) <= 4) by (solve_hyps_max HBCDApJeq HBCDApJM4).
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (list_inter (B :: C :: D :: Ap :: K :: nil) (B :: C :: D :: Ap :: J ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: Ap :: J :: K ::  :: nil) (B :: C :: D :: Ap :: K :: B :: C :: D :: Ap :: J ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: Ap :: K :: B :: C :: D :: Ap :: J ::  :: nil) ((B :: C :: D :: Ap :: K :: nil) ++ (B :: C :: D :: Ap :: J ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: D :: Ap :: K :: nil) (B :: C :: D :: Ap :: J ::  :: nil) (B :: C :: D :: Ap :: nil) 4 4 4 HBCDApKMtmp HBCDApJMtmp HBCDApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBCDApKM1. try clear HBCDApKM2. try clear HBCDApKM3. try clear HBCDApKM4. try clear HBCDApKM5. try clear HBCDApKM6. try clear HBCDApKM7. try clear HBCDApKm7. try clear HBCDApKm6. try clear HBCDApKm5. try clear HBCDApKm4. try clear HBCDApKm3. try clear HBCDApKm2. try clear HBCDApKm1. 

assert(HBCDApJKM : rk(B :: C :: D :: Ap :: J :: K ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApJKm : rk(B :: C :: D :: Ap :: J :: K ::  ::  nil) >= 1) by (solve_hyps_min HBCDApJKeq HBCDApJKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIJK : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: J :: K ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BpCpDpIJK requis par la preuve de (?)BpCpDpIJK pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BpCpDpIJK requis par la preuve de (?)BpCpDpIJK pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBpCpDpIJKm4 : rk(Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) >= 4).
{
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) 4 4 HBpCpDpImtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBpCpDpIJKM4 : rk(Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) <= 4).
{
	try assert(HBpCpDpIKeq : rk(Bp :: Cp :: Dp :: I :: K :: nil) = 4) by (apply LBpCpDpIK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIKMtmp : rk(Bp :: Cp :: Dp :: I :: K :: nil) <= 4) by (solve_hyps_max HBpCpDpIKeq HBpCpDpIKM4).
	try assert(HBpCpDpIJeq : rk(Bp :: Cp :: Dp :: I :: J ::  :: nil) = 4) by (apply LBpCpDpIJ with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIJMtmp : rk(Bp :: Cp :: Dp :: I :: J ::  :: nil) <= 4) by (solve_hyps_max HBpCpDpIJeq HBpCpDpIJM4).
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (list_inter (Bp :: Cp :: Dp :: I :: K :: nil) (Bp :: Cp :: Dp :: I :: J ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) (Bp :: Cp :: Dp :: I :: K :: Bp :: Cp :: Dp :: I :: J ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: Dp :: I :: K :: Bp :: Cp :: Dp :: I :: J ::  :: nil) ((Bp :: Cp :: Dp :: I :: K :: nil) ++ (Bp :: Cp :: Dp :: I :: J ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: Dp :: I :: K :: nil) (Bp :: Cp :: Dp :: I :: J ::  :: nil) (Bp :: Cp :: Dp :: I :: nil) 4 4 4 HBpCpDpIKMtmp HBpCpDpIJMtmp HBpCpDpImtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpCpDpIKM1. try clear HBpCpDpIKM2. try clear HBpCpDpIKM3. try clear HBpCpDpIKM4. try clear HBpCpDpIKM5. try clear HBpCpDpIKM6. try clear HBpCpDpIKM7. try clear HBpCpDpIKm7. try clear HBpCpDpIKm6. try clear HBpCpDpIKm5. try clear HBpCpDpIKm4. try clear HBpCpDpIKm3. try clear HBpCpDpIKm2. try clear HBpCpDpIKm1. 

assert(HBpCpDpIJKM : rk(Bp :: Cp :: Dp :: I :: J :: K ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIJKm : rk(Bp :: Cp :: Dp :: I :: J :: K ::  ::  nil) >= 1) by (solve_hyps_min HBpCpDpIJKeq HBpCpDpIJKm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApJKL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: J :: K :: L ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDApJKL requis par la preuve de (?)BCDApJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDApJKL requis par la preuve de (?)BCDApJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCDApJKLm4 : rk(B :: C :: D :: Ap :: J :: K :: L ::  :: nil) >= 4).
{
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J :: K :: L ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: J :: K :: L ::  :: nil) 4 4 HBCDApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBCDApJKLM4 : rk(B :: C :: D :: Ap :: J :: K :: L ::  :: nil) <= 4).
{
	try assert(HBCDApLeq : rk(B :: C :: D :: Ap :: L :: nil) = 4) by (apply LBCDApL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApLMtmp : rk(B :: C :: D :: Ap :: L :: nil) <= 4) by (solve_hyps_max HBCDApLeq HBCDApLM4).
	try assert(HBCDApJKeq : rk(B :: C :: D :: Ap :: J :: K ::  :: nil) = 4) by (apply LBCDApJK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApJKMtmp : rk(B :: C :: D :: Ap :: J :: K ::  :: nil) <= 4) by (solve_hyps_max HBCDApJKeq HBCDApJKM4).
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (list_inter (B :: C :: D :: Ap :: L :: nil) (B :: C :: D :: Ap :: J :: K ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: Ap :: J :: K :: L ::  :: nil) (B :: C :: D :: Ap :: L :: B :: C :: D :: Ap :: J :: K ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: Ap :: L :: B :: C :: D :: Ap :: J :: K ::  :: nil) ((B :: C :: D :: Ap :: L :: nil) ++ (B :: C :: D :: Ap :: J :: K ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: D :: Ap :: L :: nil) (B :: C :: D :: Ap :: J :: K ::  :: nil) (B :: C :: D :: Ap :: nil) 4 4 4 HBCDApLMtmp HBCDApJKMtmp HBCDApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBCDApLM1. try clear HBCDApLM2. try clear HBCDApLM3. try clear HBCDApLM4. try clear HBCDApLM5. try clear HBCDApLM6. try clear HBCDApLM7. try clear HBCDApLm7. try clear HBCDApLm6. try clear HBCDApLm5. try clear HBCDApLm4. try clear HBCDApLm3. try clear HBCDApLm2. try clear HBCDApLm1. 

assert(HBCDApJKLM : rk(B :: C :: D :: Ap :: J :: K :: L ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApJKLm : rk(B :: C :: D :: Ap :: J :: K :: L ::  ::  nil) >= 1) by (solve_hyps_min HBCDApJKLeq HBCDApJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBpCpDpIJKL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) = 4.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BpCpDpIJKL requis par la preuve de (?)BpCpDpIJKL pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BpCpDpIJKL requis par la preuve de (?)BpCpDpIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBpCpDpIJKLm4 : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) >= 4).
{
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Bp :: Cp :: Dp :: I :: nil) (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) 4 4 HBpCpDpImtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HBpCpDpIJKLM4 : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) <= 4).
{
	try assert(HBpCpDpILeq : rk(Bp :: Cp :: Dp :: I :: L :: nil) = 4) by (apply LBpCpDpIL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpILMtmp : rk(Bp :: Cp :: Dp :: I :: L :: nil) <= 4) by (solve_hyps_max HBpCpDpILeq HBpCpDpILM4).
	try assert(HBpCpDpIJKeq : rk(Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) = 4) by (apply LBpCpDpIJK with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIJKMtmp : rk(Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) <= 4) by (solve_hyps_max HBpCpDpIJKeq HBpCpDpIJKM4).
	try assert(HBpCpDpIeq : rk(Bp :: Cp :: Dp :: I :: nil) = 4) by (apply LBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpImtmp : rk(Bp :: Cp :: Dp :: I :: nil) >= 4) by (solve_hyps_min HBpCpDpIeq HBpCpDpIm4).
	assert(Hincl : incl (Bp :: Cp :: Dp :: I :: nil) (list_inter (Bp :: Cp :: Dp :: I :: L :: nil) (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) (Bp :: Cp :: Dp :: I :: L :: Bp :: Cp :: Dp :: I :: J :: K ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: Cp :: Dp :: I :: L :: Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) ((Bp :: Cp :: Dp :: I :: L :: nil) ++ (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: Cp :: Dp :: I :: L :: nil) (Bp :: Cp :: Dp :: I :: J :: K ::  :: nil) (Bp :: Cp :: Dp :: I :: nil) 4 4 4 HBpCpDpILMtmp HBpCpDpIJKMtmp HBpCpDpImtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HBpCpDpILM1. try clear HBpCpDpILM2. try clear HBpCpDpILM3. try clear HBpCpDpILM4. try clear HBpCpDpILM5. try clear HBpCpDpILM6. try clear HBpCpDpILM7. try clear HBpCpDpILm7. try clear HBpCpDpILm6. try clear HBpCpDpILm5. try clear HBpCpDpILm4. try clear HBpCpDpILm3. try clear HBpCpDpILm2. try clear HBpCpDpILm1. 

assert(HBpCpDpIJKLM : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBpCpDpIJKLm : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) >= 1) by (solve_hyps_min HBpCpDpIJKLeq HBpCpDpIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCDApBpCpDpIJKL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) = 5.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour BCDApBpCpDpIJKL requis par la preuve de (?)BCDApBpCpDpIJKL pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour BCDApBpCpDpIJKL requis par la preuve de (?)BCDApBpCpDpIJKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCDApBpCpDpIJKLm4 : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) >= 4).
{
	try assert(HBCDApeq : rk(B :: C :: D :: Ap :: nil) = 4) by (apply LBCDAp with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApmtmp : rk(B :: C :: D :: Ap :: nil) >= 4) by (solve_hyps_min HBCDApeq HBCDApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: D :: Ap :: nil) (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) 4 4 HBCDApmtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCDApBpCpDpIJKLm5 : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) >= 5).
{
	try assert(HBCDApBpCpDpIeq : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: nil) = 5) by (apply LBCDApBpCpDpI with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApBpCpDpImtmp : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: nil) >= 5) by (solve_hyps_min HBCDApBpCpDpIeq HBCDApBpCpDpIm5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: nil) (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: nil) (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) 5 5 HBCDApBpCpDpImtmp Hcomp Hincl);apply HT.
}
try clear HBCDApBpCpDpIM1. try clear HBCDApBpCpDpIM2. try clear HBCDApBpCpDpIM3. try clear HBCDApBpCpDpIM4. try clear HBCDApBpCpDpIM5. try clear HBCDApBpCpDpIM6. try clear HBCDApBpCpDpIM7. try clear HBCDApBpCpDpIm7. try clear HBCDApBpCpDpIm6. try clear HBCDApBpCpDpIm5. try clear HBCDApBpCpDpIm4. try clear HBCDApBpCpDpIm3. try clear HBCDApBpCpDpIm2. try clear HBCDApBpCpDpIm1. 

assert(HBCDApBpCpDpIJKLM : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) <= 5) by (apply rk_upper_dim).
assert(HBCDApBpCpDpIJKLm : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  ::  nil) >= 1) by (solve_hyps_min HBCDApBpCpDpIJKLeq HBCDApBpCpDpIJKLm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LJKL : forall B C D Ap Bp Cp Dp I J K L  ,
rk(B :: C :: D :: Ap ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  nil) = 4 -> rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I ::  nil) = 5 ->
rk(B :: C :: D :: Ap :: J ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: J ::  nil) = 4 -> rk(B :: C :: D :: Ap :: K ::  nil) = 4 ->
rk(Bp :: Cp :: Dp :: I :: K ::  nil) = 4 -> rk(B :: C :: D :: Ap :: L ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I :: L ::  nil) = 4 ->
rk(J :: K :: L ::  nil) = 3 -> rk(B :: C :: D :: Ap ::  ::  nil) = 4 -> rk(Bp :: Cp :: Dp :: I ::  ::  nil) = 4 ->
rk(J :: K ::  ::  nil) = 3 -> rk(J :: L ::  ::  nil) = 3 -> rk(K :: L ::  ::  nil) = 3 ->
rk(J :: K :: L ::  ::  nil) = 3.
Proof.

intros B C D Ap Bp Cp Dp I J K L  
HBCDApeq HBpCpDpIeq HBCDApBpCpDpIeq HBCDApJeq HBpCpDpIJeq HBCDApKeq HBpCpDpIKeq HBCDApLeq HBpCpDpILeq HJKLeq
HBCDApeq HBpCpDpIeq HJKeq HJLeq HKLeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour JKL requis par la preuve de (?)JKL pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour JKL requis par la preuve de (?)JKL pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HJKLm3 : rk(J :: K :: L ::  :: nil) >= 3).
{
	try assert(HJKLeq : rk(J :: K :: L :: nil) = 3) by (apply LJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HJKLmtmp : rk(J :: K :: L :: nil) >= 3) by (solve_hyps_min HJKLeq HJKLm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (J :: K :: L :: nil) (J :: K :: L ::  :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (J :: K :: L :: nil) (J :: K :: L ::  :: nil) 3 3 HJKLmtmp Hcomp Hincl);apply HT.
}
try clear HJKLM1. try clear HJKLM2. try clear HJKLM3. try clear HJKLM4. try clear HJKLM5. try clear HJKLM6. try clear HJKLM7. try clear HJKLm7. try clear HJKLm6. try clear HJKLm5. try clear HJKLm4. try clear HJKLm3. try clear HJKLm2. try clear HJKLm1. 

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HJKLM3 : rk(J :: K :: L ::  :: nil) <= 3).
{
	try assert(HBCDApJKLeq : rk(B :: C :: D :: Ap :: J :: K :: L ::  :: nil) = 4) by (apply LBCDApJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApJKLMtmp : rk(B :: C :: D :: Ap :: J :: K :: L ::  :: nil) <= 4) by (solve_hyps_max HBCDApJKLeq HBCDApJKLM4).
	try assert(HBpCpDpIJKLeq : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) = 4) by (apply LBpCpDpIJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBpCpDpIJKLMtmp : rk(Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) <= 4) by (solve_hyps_max HBpCpDpIJKLeq HBpCpDpIJKLM4).
	try assert(HBCDApBpCpDpIJKLeq : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) = 5) by (apply LBCDApBpCpDpIJKL with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HBCDApBpCpDpIJKLmtmp : rk(B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) >= 5) by (solve_hyps_min HBCDApBpCpDpIJKLeq HBCDApBpCpDpIJKLm5).
	assert(Hincl : incl (J :: K :: L ::  :: nil) (list_inter (B :: C :: D :: Ap :: J :: K :: L ::  :: nil) (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: D :: Ap :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) (B :: C :: D :: Ap :: J :: K :: L ::  :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: D :: Ap :: J :: K :: L ::  :: Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) ((B :: C :: D :: Ap :: J :: K :: L ::  :: nil) ++ (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCDApBpCpDpIJKLmtmp;try rewrite HT2 in HBCDApBpCpDpIJKLmtmp.
	assert(HT := rule_3 (B :: C :: D :: Ap :: J :: K :: L ::  :: nil) (Bp :: Cp :: Dp :: I :: J :: K :: L ::  :: nil) (J :: K :: L ::  :: nil) 4 4 5 HBCDApJKLMtmp HBpCpDpIJKLMtmp HBCDApBpCpDpIJKLmtmp Hincl);apply HT.
}


assert(HJKLM : rk(J :: K :: L ::  ::  nil) <= 4) by (solve_hyps_max HJKLeq HJKLM4).
assert(HJKLm : rk(J :: K :: L ::  ::  nil) >= 1) by (solve_hyps_min HJKLeq HJKLm1).
intuition.
Qed.

