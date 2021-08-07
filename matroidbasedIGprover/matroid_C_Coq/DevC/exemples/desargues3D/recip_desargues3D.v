Load "preamble3D.v".


(* dans la couche 0 *)
Lemma LAB : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AB requis par la preuve de (?)AB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HABm2 : rk(A :: B :: nil) >= 2).
{
	assert(HACCpMtmp : rk(A :: C :: Cp :: nil) <= 3) by (solve_hyps_max HACCpeq HACCpM3).
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: nil) (A :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Cp :: nil) (A :: B :: A :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: A :: C :: Cp :: nil) ((A :: B :: nil) ++ (A :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCCpmtmp;try rewrite HT2 in HABCCpmtmp.
	assert(HT := rule_2 (A :: B :: nil) (A :: C :: Cp :: nil) (A :: nil) 4 1 3 HABCCpmtmp HAmtmp HACCpMtmp Hincl);apply HT.
}

assert(HABM : rk(A :: B ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HABeq HABM2).
assert(HABm : rk(A :: B ::  nil) >= 1) by (solve_hyps_min HABeq HABm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAC : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AC requis par la preuve de (?)AC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HACm2 : rk(A :: C :: nil) >= 2).
{
	assert(HABApMtmp : rk(A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HABApeq HABApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: C :: nil) (A :: B :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (A :: C :: A :: B :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: A :: B :: Ap :: nil) ((A :: C :: nil) ++ (A :: B :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_2 (A :: C :: nil) (A :: B :: Ap :: nil) (A :: nil) 4 1 3 HABCApmtmp HAmtmp HABApMtmp Hincl);apply HT.
}

assert(HACM : rk(A :: C ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HACeq HACM2).
assert(HACm : rk(A :: C ::  nil) >= 1) by (solve_hyps_min HACeq HACm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBC : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: C ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BC requis par la preuve de (?)BC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HBCm2 : rk(B :: C :: nil) >= 2).
{
	assert(HABApMtmp : rk(A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HABApeq HABApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (B :: C :: nil) (A :: B :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (B :: C :: A :: B :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: A :: B :: Ap :: nil) ((B :: C :: nil) ++ (A :: B :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_2 (B :: C :: nil) (A :: B :: Ap :: nil) (B :: nil) 4 1 3 HABCApmtmp HBmtmp HABApMtmp Hincl);apply HT.
}

assert(HBCM : rk(B :: C ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBCeq HBCM2).
assert(HBCm : rk(B :: C ::  nil) >= 1) by (solve_hyps_min HBCeq HBCm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: Ap ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AAp requis par la preuve de (?)AAp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: Ap ::  de rang :  3 et 3 	 AiB : A ::  de rang :  1 et 1 	 A : A :: B ::   de rang : 2 et 2 *)
assert(HAApm2 : rk(A :: Ap :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABMtmp : rk(A :: B :: nil) <= 2) by (solve_hyps_max HABeq HABM2).
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (A :: B :: nil) (A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: Ap :: nil) (A :: B :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: A :: Ap :: nil) ((A :: B :: nil) ++ (A :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABApmtmp;try rewrite HT2 in HABApmtmp.
	assert(HT := rule_4 (A :: B :: nil) (A :: Ap :: nil) (A :: nil) 3 1 2 HABApmtmp HAmtmp HABMtmp Hincl); apply HT.
}

assert(HAApM : rk(A :: Ap ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HAApeq HAApM2).
assert(HAApm : rk(A :: Ap ::  nil) >= 1) by (solve_hyps_min HAApeq HAApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: Ap ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABAp requis par la preuve de (?)OoABAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABAp requis par la preuve de (?)OoABAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABAp requis par la preuve de (?)OoABAp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABApM3 : rk(Oo :: A :: B :: Ap :: nil) <= 3).
{
	assert(HBMtmp : rk(B :: nil) <= 1) by (solve_hyps_max HBeq HBM1).
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (B :: nil) (Oo :: A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: nil) (B :: Oo :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Oo :: A :: Ap :: nil) ((B :: nil) ++ (Oo :: A :: Ap :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: nil) (Oo :: A :: Ap :: nil) (nil) 1 2 0 HBMtmp HOoAApMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApm2 : rk(Oo :: A :: B :: Ap :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApm3 : rk(Oo :: A :: B :: Ap :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABApM : rk(Oo :: A :: B :: Ap ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABApm : rk(Oo :: A :: B :: Ap ::  nil) >= 1) by (solve_hyps_min HOoABApeq HOoABApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Ap ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CAp requis par la preuve de (?)CAp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: Ap ::  de rang :  4 et 4 	 AiB : Ap ::  de rang :  1 et 1 	 A : A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HCApm2 : rk(C :: Ap :: nil) >= 2).
{
	assert(HABApMtmp : rk(A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HABApeq HABApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (A :: B :: Ap :: nil) (C :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (A :: B :: Ap :: C :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: C :: Ap :: nil) ((A :: B :: Ap :: nil) ++ (C :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: nil) (C :: Ap :: nil) (Ap :: nil) 4 1 3 HABCApmtmp HApmtmp HABApMtmp Hincl); apply HT.
}

assert(HCApM : rk(C :: Ap ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCApeq HCApM2).
assert(HCApm : rk(C :: Ap ::  nil) >= 1) by (solve_hyps_min HCApeq HCApm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACAp *)
(* dans la couche 0 *)
Lemma LACAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Ap ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCAp requis par la preuve de (?)ACAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BAp requis par la preuve de (?)BCAp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCAp requis par la preuve de (?)BCAp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: Ap ::  de rang :  4 et 4 	 AiB : B :: Ap ::  de rang :  1 et 2 	 A : A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HBCApm2 : rk(B :: C :: Ap :: nil) >= 2).
{
	assert(HABApMtmp : rk(A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HABApeq HABApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HBApmtmp : rk(B :: Ap :: nil) >= 1) by (solve_hyps_min HBApeq HBApm1).
	assert(Hincl : incl (B :: Ap :: nil) (list_inter (A :: B :: Ap :: nil) (B :: C :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (A :: B :: Ap :: B :: C :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: B :: C :: Ap :: nil) ((A :: B :: Ap :: nil) ++ (B :: C :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: nil) (B :: C :: Ap :: nil) (B :: Ap :: nil) 4 1 3 HABCApmtmp HBApmtmp HABApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACAp requis par la preuve de (?)ACAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour AAp requis par la preuve de (?)ACAp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACAp requis par la preuve de (?)ACAp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : A :: B :: C :: Ap ::  de rang :  4 et 4 	 AiB : A :: Ap ::  de rang :  1 et 2 	 A : A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HACApm2 : rk(A :: C :: Ap :: nil) >= 2).
{
	assert(HABApMtmp : rk(A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HABApeq HABApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HAApmtmp : rk(A :: Ap :: nil) >= 1) by (solve_hyps_min HAApeq HAApm1).
	assert(Hincl : incl (A :: Ap :: nil) (list_inter (A :: B :: Ap :: nil) (A :: C :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (A :: B :: Ap :: A :: C :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: A :: C :: Ap :: nil) ((A :: B :: Ap :: nil) ++ (A :: C :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: nil) (A :: C :: Ap :: nil) (A :: Ap :: nil) 4 1 3 HABCApmtmp HAApmtmp HABApMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 4 et 5*)
assert(HACApm3 : rk(A :: C :: Ap :: nil) >= 3).
{
	assert(HBCApMtmp : rk(B :: C :: Ap :: nil) <= 3) by (solve_hyps_max HBCApeq HBCApM3).
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hincl : incl (C :: Ap :: nil) (list_inter (A :: C :: Ap :: nil) (B :: C :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: nil) (A :: C :: Ap :: B :: C :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: Ap :: B :: C :: Ap :: nil) ((A :: C :: Ap :: nil) ++ (B :: C :: Ap :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApmtmp;try rewrite HT2 in HABCApmtmp.
	assert(HT := rule_2 (A :: C :: Ap :: nil) (B :: C :: Ap :: nil) (C :: Ap :: nil) 4 2 3 HABCApmtmp HCApmtmp HBCApMtmp Hincl);apply HT.
}

assert(HACApM : rk(A :: C :: Ap ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HACApeq HACApM3).
assert(HACApm : rk(A :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HACApeq HACApm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACAp *)
(* dans la couche 0 *)
Lemma LOoACApac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Ap :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACApac requis par la preuve de (?)OoACApac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACApac requis par la preuve de (?)OoACApac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApac requis par la preuve de (?)OoACApac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HOoACApacM3 : rk(Oo :: A :: C :: Ap :: ac :: nil) <= 3).
{
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HAmtmp : rk(A :: nil) >= 1) by (solve_hyps_min HAeq HAm1).
	assert(Hincl : incl (A :: nil) (list_inter (Oo :: A :: Ap :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: ac :: nil) (Oo :: A :: Ap :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: Ap :: A :: C :: ac :: nil) ((Oo :: A :: Ap :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: A :: Ap :: nil) (A :: C :: ac :: nil) (A :: nil) 2 2 1 HOoAApMtmp HACacMtmp HAmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApacm2 : rk(Oo :: A :: C :: Ap :: ac :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: ac :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApacm3 : rk(Oo :: A :: C :: Ap :: ac :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: ac :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

assert(HOoACApacM : rk(Oo :: A :: C :: Ap :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACApacm : rk(Oo :: A :: C :: Ap :: ac ::  nil) >= 1) by (solve_hyps_min HOoACApaceq HOoACApacm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoACAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Ap ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACApM3 : rk(Oo :: A :: C :: Ap :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Oo :: A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: nil) (C :: Oo :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Oo :: A :: Ap :: nil) ((C :: nil) ++ (Oo :: A :: Ap :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Oo :: A :: Ap :: nil) (nil) 1 2 0 HCMtmp HOoAApMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApm2 : rk(Oo :: A :: C :: Ap :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: Ap :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et -4*)
assert(HOoACApm3 : rk(Oo :: A :: C :: Ap :: nil) >= 3).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACApaceq : rk(Oo :: A :: C :: Ap :: ac :: nil) = 3) by (apply LOoACApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApacmtmp : rk(Oo :: A :: C :: Ap :: ac :: nil) >= 3) by (solve_hyps_min HOoACApaceq HOoACApacm3).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: ac :: nil) (Oo :: A :: C :: Ap :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: A :: C :: ac :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApacmtmp;try rewrite HT2 in HOoACApacmtmp.
	assert(HT := rule_2 (Oo :: A :: C :: Ap :: nil) (A :: C :: ac :: nil) (A :: C :: nil) 3 2 2 HOoACApacmtmp HACmtmp HACacMtmp Hincl);apply HT.
}

assert(HOoACApM : rk(Oo :: A :: C :: Ap ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACApm : rk(Oo :: A :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HOoACApeq HOoACApm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCAp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCAp requis par la preuve de (?)OoABCAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCAp requis par la preuve de (?)OoABCAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCAp requis par la preuve de (?)OoABCAp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApm2 : rk(Oo :: A :: B :: C :: Ap :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApm3 : rk(Oo :: A :: B :: C :: Ap :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApm4 : rk(Oo :: A :: B :: C :: Ap :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApM : rk(Oo :: A :: B :: C :: Ap ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApm : rk(Oo :: A :: B :: C :: Ap ::  nil) >= 1) by (solve_hyps_min HOoABCApeq HOoABCApm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABp *)
(* dans la couche 0 *)
Lemma LABp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: Bp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)ABp pour la règle 2  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)BCBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp ::  de rang :  4 et 4 	 AiB : B :: C ::  de rang :  2 et 2 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 4) by (solve_hyps_min HOoABCApBpeq HOoABCApBpm4).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (B :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpmtmp;try rewrite HT2 in HOoABCApBpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: nil) (B :: C :: nil) 4 2 4 HOoABCApBpmtmp HBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ABp requis par la preuve de (?)ABp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et 5*)
assert(HABpm2 : rk(A :: Bp :: nil) >= 2).
{
	assert(HBCBpMtmp : rk(B :: C :: Bp :: nil) <= 3) by (solve_hyps_max HBCBpeq HBCBpM3).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (A :: Bp :: nil) (B :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: nil) (A :: Bp :: B :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Bp :: B :: C :: Bp :: nil) ((A :: Bp :: nil) ++ (B :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpmtmp;try rewrite HT2 in HABCBpmtmp.
	assert(HT := rule_2 (A :: Bp :: nil) (B :: C :: Bp :: nil) (Bp :: nil) 4 1 3 HABCBpmtmp HBpmtmp HBCBpMtmp Hincl);apply HT.
}

assert(HABpM : rk(A :: Bp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HABpeq HABpM2).
assert(HABpm : rk(A :: Bp ::  nil) >= 1) by (solve_hyps_min HABpeq HABpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBBp *)
(* dans la couche 0 *)
Lemma LBBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: Bp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACBp requis par la preuve de (?)BBp pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApBp requis par la preuve de (?)ACBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApBp requis par la preuve de (?)OoACApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApBp requis par la preuve de (?)OoACApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApBpm2 : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApBpm3 : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACAp requis par la preuve de (?)ACBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACApM3 : rk(Oo :: A :: C :: Ap :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Oo :: A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: nil) (C :: Oo :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Oo :: A :: Ap :: nil) ((C :: nil) ++ (Oo :: A :: Ap :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Oo :: A :: Ap :: nil) (nil) 1 2 0 HCMtmp HOoAApMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApm2 : rk(Oo :: A :: C :: Ap :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: Ap :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACBp requis par la preuve de (?)ACBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Bp ::  de rang :  3 et 4 	 AiB : A :: C ::  de rang :  2 et 2 	 A : Oo :: A :: C :: Ap ::   de rang : 2 et 3 *)
assert(HACBpm2 : rk(A :: C :: Bp :: nil) >= 2).
{
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApBpmtmp : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HOoACApBpeq HOoACApBpm3).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (A :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Bp :: nil) (Oo :: A :: C :: Ap :: A :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: A :: C :: Bp :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (A :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApBpmtmp;try rewrite HT2 in HOoACApBpmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (A :: C :: Bp :: nil) (A :: C :: nil) 3 2 3 HOoACApBpmtmp HACmtmp HOoACApMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour BBp requis par la preuve de (?)BBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et 5*)
assert(HBBpm2 : rk(B :: Bp :: nil) >= 2).
{
	assert(HACBpMtmp : rk(A :: C :: Bp :: nil) <= 3) by (solve_hyps_max HACBpeq HACBpM3).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (B :: Bp :: nil) (A :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: nil) (B :: Bp :: A :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Bp :: nil) ((B :: Bp :: nil) ++ (A :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpmtmp;try rewrite HT2 in HABCBpmtmp.
	assert(HT := rule_2 (B :: Bp :: nil) (A :: C :: Bp :: nil) (Bp :: nil) 4 1 3 HABCBpmtmp HBpmtmp HACBpMtmp Hincl);apply HT.
}

assert(HBBpM : rk(B :: Bp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HBBpeq HBBpM2).
assert(HBBpm : rk(B :: Bp ::  nil) >= 1) by (solve_hyps_min HBBpeq HBBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABBp requis par la preuve de (?)OoABBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour OoABApBp requis par la preuve de (?)OoABBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HOoABApBpM3 : rk(Oo :: A :: B :: Ap :: Bp :: nil) <= 3).
{
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(HOoBBpMtmp : rk(Oo :: B :: Bp :: nil) <= 2) by (solve_hyps_max HOoBBpeq HOoBBpM2).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Oo :: A :: Ap :: nil) (Oo :: B :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: nil) (Oo :: A :: Ap :: Oo :: B :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: Ap :: Oo :: B :: Bp :: nil) ((Oo :: A :: Ap :: nil) ++ (Oo :: B :: Bp :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: A :: Ap :: nil) (Oo :: B :: Bp :: nil) (Oo :: nil) 2 2 1 HOoAApMtmp HOoBBpMtmp HOomtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpm2 : rk(Oo :: A :: B :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpm3 : rk(Oo :: A :: B :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABBp requis par la preuve de (?)OoABBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABBp requis par la preuve de (?)OoABBp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABBpM3 : rk(Oo :: A :: B :: Bp :: nil) <= 3).
{
	assert(HAMtmp : rk(A :: nil) <= 1) by (solve_hyps_max HAeq HAM1).
	assert(HOoBBpMtmp : rk(Oo :: B :: Bp :: nil) <= 2) by (solve_hyps_max HOoBBpeq HOoBBpM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (A :: nil) (Oo :: B :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Bp :: nil) (A :: Oo :: B :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Oo :: B :: Bp :: nil) ((A :: nil) ++ (Oo :: B :: Bp :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: nil) (Oo :: B :: Bp :: nil) (nil) 1 2 0 HAMtmp HOoBBpMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp ::  de rang :  3 et 3 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABBpm2 : rk(Oo :: A :: B :: Bp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpmtmp : rk(Oo :: A :: B :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HOoABApBpeq HOoABApBpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpmtmp;try rewrite HT2 in HOoABApBpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABApBpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABBpm3 : rk(Oo :: A :: B :: Bp :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABBpM : rk(Oo :: A :: B :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABBpm : rk(Oo :: A :: B :: Bp ::  nil) >= 1) by (solve_hyps_min HOoABBpeq HOoABBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Bp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CBp requis par la preuve de (?)CBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : A :: B :: C :: Bp ::  de rang :  4 et 4 	 AiB : Bp ::  de rang :  1 et 1 	 A : A :: B :: Bp ::   de rang : 3 et 3 *)
assert(HCBpm2 : rk(C :: Bp :: nil) >= 2).
{
	assert(HABBpMtmp : rk(A :: B :: Bp :: nil) <= 3) by (solve_hyps_max HABBpeq HABBpM3).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (A :: B :: Bp :: nil) (C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: nil) (A :: B :: Bp :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Bp :: C :: Bp :: nil) ((A :: B :: Bp :: nil) ++ (C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpmtmp;try rewrite HT2 in HABCBpmtmp.
	assert(HT := rule_4 (A :: B :: Bp :: nil) (C :: Bp :: nil) (Bp :: nil) 4 1 3 HABCBpmtmp HBpmtmp HABBpMtmp Hincl); apply HT.
}

assert(HCBpM : rk(C :: Bp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCBpeq HCBpM2).
assert(HCBpm : rk(C :: Bp ::  nil) >= 1) by (solve_hyps_min HCBpeq HCBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACBp requis par la preuve de (?)ACBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApBp requis par la preuve de (?)ACBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApBp requis par la preuve de (?)OoACApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApBp requis par la preuve de (?)OoACApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApBpm2 : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApBpm3 : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACAp requis par la preuve de (?)ACBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACApM3 : rk(Oo :: A :: C :: Ap :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Oo :: A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: nil) (C :: Oo :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Oo :: A :: Ap :: nil) ((C :: nil) ++ (Oo :: A :: Ap :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Oo :: A :: Ap :: nil) (nil) 1 2 0 HCMtmp HOoAApMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApm2 : rk(Oo :: A :: C :: Ap :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: Ap :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACBp requis par la preuve de (?)ACBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 5*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Bp ::  de rang :  3 et 4 	 AiB : A :: C ::  de rang :  2 et 2 	 A : Oo :: A :: C :: Ap ::   de rang : 2 et 3 *)
assert(HACBpm2 : rk(A :: C :: Bp :: nil) >= 2).
{
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApBpmtmp : rk(Oo :: A :: C :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HOoACApBpeq HOoACApBpm3).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (A :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Bp :: nil) (Oo :: A :: C :: Ap :: A :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: A :: C :: Bp :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (A :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApBpmtmp;try rewrite HT2 in HOoACApBpmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (A :: C :: Bp :: nil) (A :: C :: nil) 3 2 3 HOoACApBpmtmp HACmtmp HOoACApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Bp ::  de rang :  4 et 4 	 AiB : Bp ::  de rang :  1 et 1 	 A : B :: Bp ::   de rang : 2 et 2 *)
assert(HACBpm3 : rk(A :: C :: Bp :: nil) >= 3).
{
	assert(HBBpeq : rk(B :: Bp :: nil) = 2) by (apply LBBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpMtmp : rk(B :: Bp :: nil) <= 2) by (solve_hyps_max HBBpeq HBBpM2).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (B :: Bp :: nil) (A :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: nil) (B :: Bp :: A :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: A :: C :: Bp :: nil) ((B :: Bp :: nil) ++ (A :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpmtmp;try rewrite HT2 in HABCBpmtmp.
	assert(HT := rule_4 (B :: Bp :: nil) (A :: C :: Bp :: nil) (Bp :: nil) 4 1 2 HABCBpmtmp HBpmtmp HBBpMtmp Hincl); apply HT.
}

assert(HACBpM : rk(A :: C :: Bp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HACBpeq HACBpM3).
assert(HACBpm : rk(A :: C :: Bp ::  nil) >= 1) by (solve_hyps_min HACBpeq HACBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBCBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: C :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)BCBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour BCBp requis par la preuve de (?)BCBp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp ::  de rang :  4 et 4 	 AiB : B :: C ::  de rang :  2 et 2 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HBCBpm2 : rk(B :: C :: Bp :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 4) by (solve_hyps_min HOoABCApBpeq HOoABCApBpm4).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (B :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpmtmp;try rewrite HT2 in HOoABCApBpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: nil) (B :: C :: nil) 4 2 4 HOoABCApBpmtmp HBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Bp ::  de rang :  4 et 4 	 AiB : Bp ::  de rang :  1 et 1 	 A : A :: Bp ::   de rang : 2 et 2 *)
assert(HBCBpm3 : rk(B :: C :: Bp :: nil) >= 3).
{
	assert(HABpeq : rk(A :: Bp :: nil) = 2) by (apply LABp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABpMtmp : rk(A :: Bp :: nil) <= 2) by (solve_hyps_max HABpeq HABpM2).
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(HBpmtmp : rk(Bp :: nil) >= 1) by (solve_hyps_min HBpeq HBpm1).
	assert(Hincl : incl (Bp :: nil) (list_inter (A :: Bp :: nil) (B :: C :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Bp :: nil) (A :: Bp :: B :: C :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Bp :: B :: C :: Bp :: nil) ((A :: Bp :: nil) ++ (B :: C :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCBpmtmp;try rewrite HT2 in HABCBpmtmp.
	assert(HT := rule_4 (A :: Bp :: nil) (B :: C :: Bp :: nil) (Bp :: nil) 4 1 2 HABCBpmtmp HBpmtmp HABpMtmp Hincl); apply HT.
}

assert(HBCBpM : rk(B :: C :: Bp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HBCBpeq HBCBpM3).
assert(HBCBpm : rk(B :: C :: Bp ::  nil) >= 1) by (solve_hyps_min HBCBpeq HBCBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Ap :: Bp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour ApBp requis par la preuve de (?)ApBp pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et -4*)
assert(HApBpm2 : rk(Ap :: Bp :: nil) >= 2).
{
	assert(HApCpDpMtmp : rk(Ap :: Cp :: Dp :: nil) <= 3) by (solve_hyps_max HApCpDpeq HApCpDpM3).
	assert(HApBpCpDpmtmp : rk(Ap :: Bp :: Cp :: Dp :: nil) >= 4) by (solve_hyps_min HApBpCpDpeq HApBpCpDpm4).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (Ap :: Bp :: nil) (Ap :: Cp :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Ap :: Bp :: Cp :: Dp :: nil) (Ap :: Bp :: Ap :: Cp :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: Bp :: Ap :: Cp :: Dp :: nil) ((Ap :: Bp :: nil) ++ (Ap :: Cp :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HApBpCpDpmtmp;try rewrite HT2 in HApBpCpDpmtmp.
	assert(HT := rule_2 (Ap :: Bp :: nil) (Ap :: Cp :: Dp :: nil) (Ap :: nil) 4 1 3 HApBpCpDpmtmp HApmtmp HApCpDpMtmp Hincl);apply HT.
}

assert(HApBpM : rk(Ap :: Bp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HApBpeq HApBpM2).
assert(HApBpm : rk(Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HApBpeq HApBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABApBp *)
(* dans la couche 0 *)
Lemma LOoABApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: Ap :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBp requis par la preuve de (?)OoABApBp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HOoABApBpM3 : rk(Oo :: A :: B :: Ap :: Bp :: nil) <= 3).
{
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(HOoBBpMtmp : rk(Oo :: B :: Bp :: nil) <= 2) by (solve_hyps_max HOoBBpeq HOoBBpM2).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Oo :: A :: Ap :: nil) (Oo :: B :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: nil) (Oo :: A :: Ap :: Oo :: B :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: Ap :: Oo :: B :: Bp :: nil) ((Oo :: A :: Ap :: nil) ++ (Oo :: B :: Bp :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: A :: Ap :: nil) (Oo :: B :: Bp :: nil) (Oo :: nil) 2 2 1 HOoAApMtmp HOoBBpMtmp HOomtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpm2 : rk(Oo :: A :: B :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpm3 : rk(Oo :: A :: B :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABApBpM : rk(Oo :: A :: B :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABApBpm : rk(Oo :: A :: B :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HOoABApBpeq HOoABApBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LABApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: Ap :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABApBp requis par la preuve de (?)ABApBp pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApBp requis par la preuve de (?)ABApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABApBpm3 : rk(A :: B :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HABApBpM3 : rk(A :: B :: Ap :: Bp :: nil) <= 3).
{
	assert(HOoABApBpeq : rk(Oo :: A :: B :: Ap :: Bp :: nil) = 3) by (apply LOoABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApBpMtmp : rk(Oo :: A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HOoABApBpeq HOoABApBpM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: Ap :: Bp :: nil) 3 3 HOoABApBpMtmp Hcomp Hincl);apply HT.
}

assert(HABApBpM : rk(A :: B :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABApBpm : rk(A :: B :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HABApBpeq HABApBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCApBp *)
(* dans la couche 0 *)
Lemma LABCApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: C :: Ap :: Bp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBp requis par la preuve de (?)ABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBp requis par la preuve de (?)ABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpm3 : rk(A :: B :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpm4 : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HABCApBpM : rk(A :: B :: C :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpm : rk(A :: B :: C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HABCApBpeq HABCApBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Ap :: Bp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CApBp requis par la preuve de (?)CApBp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CApBp requis par la preuve de (?)CApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCApBpm2 : rk(C :: Ap :: Bp :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (C :: Ap :: Bp :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp ::  de rang :  4 et 4 	 AiB : Ap :: Bp ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HCApBpm3 : rk(C :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpeq : rk(A :: B :: C :: Ap :: Bp :: nil) = 4) by (apply LABCApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABCApBpmtmp : rk(A :: B :: C :: Ap :: Bp :: nil) >= 4) by (solve_hyps_min HABCApBpeq HABCApBpm4).
	assert(HApBpeq : rk(Ap :: Bp :: nil) = 2) by (apply LApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HApBpmtmp : rk(Ap :: Bp :: nil) >= 2) by (solve_hyps_min HApBpeq HApBpm2).
	assert(Hincl : incl (Ap :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (C :: Ap :: Bp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: nil) (A :: B :: Ap :: Bp :: C :: Ap :: Bp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: C :: Ap :: Bp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (C :: Ap :: Bp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpmtmp;try rewrite HT2 in HABCApBpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (C :: Ap :: Bp :: nil) (Ap :: Bp :: nil) 4 2 3 HABCApBpmtmp HApBpmtmp HABApBpMtmp Hincl); apply HT.
}

assert(HCApBpM : rk(C :: Ap :: Bp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCApBpeq HCApBpM3).
assert(HCApBpm : rk(C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HCApBpeq HCApBpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBp requis par la preuve de (?)OoABCApBp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpM : rk(Oo :: A :: B :: C :: Ap :: Bp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpm : rk(Oo :: A :: B :: C :: Ap :: Bp ::  nil) >= 1) by (solve_hyps_min HOoABCApBpeq HOoABCApBpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACCp *)
(* dans constructLemma(), requis par LOoACCpac *)
(* dans constructLemma(), requis par LOoACApCpac *)
(* dans la couche 0 *)
Lemma LOoCApac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: C :: Ap :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoCApac requis par la preuve de (?)OoCApac pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour Cac requis par la preuve de (?)OoCApac pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour CApCpac requis par la preuve de (?)Cac pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCApCpacM3 : rk(C :: Ap :: Cp :: ac :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HApCpacMtmp : rk(Ap :: Cp :: ac :: nil) <= 2) by (solve_hyps_max HApCpaceq HApCpacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Cp :: ac :: nil) (C :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Cp :: ac :: nil) ((C :: nil) ++ (Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Ap :: Cp :: ac :: nil) (nil) 1 2 0 HCMtmp HApCpacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCApCpacm2 : rk(C :: Ap :: Cp :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (C :: Ap :: Cp :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCApCpacm3 : rk(C :: Ap :: Cp :: ac :: nil) >= 3).
{
	assert(HCApCpmtmp : rk(C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HCApCpeq HCApCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: Cp :: nil) (C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: Cp :: nil) (C :: Ap :: Cp :: ac :: nil) 3 3 HCApCpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Cac requis par la preuve de (?)Cac pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HCacm2 : rk(C :: ac :: nil) >= 2).
{
	assert(HApCpacMtmp : rk(Ap :: Cp :: ac :: nil) <= 2) by (solve_hyps_max HApCpaceq HApCpacM2).
	assert(HCApCpacmtmp : rk(C :: Ap :: Cp :: ac :: nil) >= 3) by (solve_hyps_min HCApCpaceq HCApCpacm3).
	assert(Hacmtmp : rk(ac :: nil) >= 1) by (solve_hyps_min Haceq Hacm1).
	assert(Hincl : incl (ac :: nil) (list_inter (C :: ac :: nil) (Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Cp :: ac :: nil) (C :: ac :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: ac :: Ap :: Cp :: ac :: nil) ((C :: ac :: nil) ++ (Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApCpacmtmp;try rewrite HT2 in HCApCpacmtmp.
	assert(HT := rule_2 (C :: ac :: nil) (Ap :: Cp :: ac :: nil) (ac :: nil) 3 1 2 HCApCpacmtmp Hacmtmp HApCpacMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoCApac requis par la preuve de (?)OoCApac pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoCApac requis par la preuve de (?)OoCApac pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoCApacm2 : rk(Oo :: C :: Ap :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (Oo :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (Oo :: C :: Ap :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et -4*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: ac ::  de rang :  3 et 3 	 AiB : C :: ac ::  de rang :  2 et 2 	 A : A :: C :: ac ::   de rang : 2 et 2 *)
assert(HOoCApacm3 : rk(Oo :: C :: Ap :: ac :: nil) >= 3).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACApaceq : rk(Oo :: A :: C :: Ap :: ac :: nil) = 3) by (apply LOoACApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApacmtmp : rk(Oo :: A :: C :: Ap :: ac :: nil) >= 3) by (solve_hyps_min HOoACApaceq HOoACApacm3).
	assert(HCacmtmp : rk(C :: ac :: nil) >= 2) by (solve_hyps_min HCaceq HCacm2).
	assert(Hincl : incl (C :: ac :: nil) (list_inter (A :: C :: ac :: nil) (Oo :: C :: Ap :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: ac :: nil) (A :: C :: ac :: Oo :: C :: Ap :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: ac :: Oo :: C :: Ap :: ac :: nil) ((A :: C :: ac :: nil) ++ (Oo :: C :: Ap :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApacmtmp;try rewrite HT2 in HOoACApacmtmp.
	assert(HT := rule_4 (A :: C :: ac :: nil) (Oo :: C :: Ap :: ac :: nil) (C :: ac :: nil) 3 2 2 HOoACApacmtmp HCacmtmp HACacMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoCApacM3 : rk(Oo :: C :: Ap :: ac :: nil) <= 3).
{
	assert(HOoACApaceq : rk(Oo :: A :: C :: Ap :: ac :: nil) = 3) by (apply LOoACApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApacMtmp : rk(Oo :: A :: C :: Ap :: ac :: nil) <= 3) by (solve_hyps_max HOoACApaceq HOoACApacM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: C :: Ap :: ac :: nil) (Oo :: A :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Oo :: C :: Ap :: ac :: nil) (Oo :: A :: C :: Ap :: ac :: nil) 3 3 HOoACApacMtmp Hcomp Hincl);apply HT.
}

assert(HOoCApacM : rk(Oo :: C :: Ap :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoCApacm : rk(Oo :: C :: Ap :: ac ::  nil) >= 1) by (solve_hyps_min HOoCApaceq HOoCApacm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACApCpac *)
(* dans la couche 0 *)
Lemma LACApCpac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Ap :: Cp :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApCpac requis par la preuve de (?)ACApCpac pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApCpac requis par la preuve de (?)ACApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApCpac requis par la preuve de (?)ACApCpac pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApCpacm2 : rk(A :: C :: Ap :: Cp :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: Cp :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApCpacm3 : rk(A :: C :: Ap :: Cp :: ac :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: Cp :: ac :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HACApCpacM3 : rk(A :: C :: Ap :: Cp :: ac :: nil) <= 3).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HApCpacMtmp : rk(Ap :: Cp :: ac :: nil) <= 2) by (solve_hyps_max HApCpaceq HApCpacM2).
	assert(Hacmtmp : rk(ac :: nil) >= 1) by (solve_hyps_min Haceq Hacm1).
	assert(Hincl : incl (ac :: nil) (list_inter (A :: C :: ac :: nil) (Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Cp :: ac :: nil) (A :: C :: ac :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: ac :: Ap :: Cp :: ac :: nil) ((A :: C :: ac :: nil) ++ (Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: C :: ac :: nil) (Ap :: Cp :: ac :: nil) (ac :: nil) 2 2 1 HACacMtmp HApCpacMtmp Hacmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HACApCpacM : rk(A :: C :: Ap :: Cp :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApCpacm : rk(A :: C :: Ap :: Cp :: ac ::  nil) >= 1) by (solve_hyps_min HACApCpaceq HACApCpacm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACApCpac *)
(* dans constructLemma(), requis par LCApac *)
(* dans la couche 0 *)
Lemma LACApac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Ap :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ACApac requis par la preuve de (?)ACApac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ACApac requis par la preuve de (?)ACApac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApac requis par la preuve de (?)ACApac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HACApacM3 : rk(A :: C :: Ap :: ac :: nil) <= 3).
{
	assert(HApMtmp : rk(Ap :: nil) <= 1) by (solve_hyps_max HApeq HApM1).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Ap :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: ac :: nil) (Ap :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Ap :: A :: C :: ac :: nil) ((Ap :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Ap :: nil) (A :: C :: ac :: nil) (nil) 1 2 0 HApMtmp HACacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApacm2 : rk(A :: C :: Ap :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApacm3 : rk(A :: C :: Ap :: ac :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: ac :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

assert(HACApacM : rk(A :: C :: Ap :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApacm : rk(A :: C :: Ap :: ac ::  nil) >= 1) by (solve_hyps_min HACApaceq HACApacm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCApac *)
(* dans constructLemma(), requis par LCac *)
(* dans la couche 0 *)
Lemma LCApCpac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Ap :: Cp :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CApCpac requis par la preuve de (?)CApCpac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCApCpacM3 : rk(C :: Ap :: Cp :: ac :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HApCpacMtmp : rk(Ap :: Cp :: ac :: nil) <= 2) by (solve_hyps_max HApCpaceq HApCpacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Cp :: ac :: nil) (C :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Cp :: ac :: nil) ((C :: nil) ++ (Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Ap :: Cp :: ac :: nil) (nil) 1 2 0 HCMtmp HApCpacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCApCpacm2 : rk(C :: Ap :: Cp :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (C :: Ap :: Cp :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCApCpacm3 : rk(C :: Ap :: Cp :: ac :: nil) >= 3).
{
	assert(HCApCpmtmp : rk(C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HCApCpeq HCApCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: Cp :: nil) (C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: Cp :: nil) (C :: Ap :: Cp :: ac :: nil) 3 3 HCApCpmtmp Hcomp Hincl);apply HT.
}

assert(HCApCpacM : rk(C :: Ap :: Cp :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HCApCpacm : rk(C :: Ap :: Cp :: ac ::  nil) >= 1) by (solve_hyps_min HCApCpaceq HCApCpacm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: ac ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Cac requis par la preuve de (?)Cac pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HCacm2 : rk(C :: ac :: nil) >= 2).
{
	assert(HApCpacMtmp : rk(Ap :: Cp :: ac :: nil) <= 2) by (solve_hyps_max HApCpaceq HApCpacM2).
	assert(HCApCpaceq : rk(C :: Ap :: Cp :: ac :: nil) = 3) by (apply LCApCpac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApCpacmtmp : rk(C :: Ap :: Cp :: ac :: nil) >= 3) by (solve_hyps_min HCApCpaceq HCApCpacm3).
	assert(Hacmtmp : rk(ac :: nil) >= 1) by (solve_hyps_min Haceq Hacm1).
	assert(Hincl : incl (ac :: nil) (list_inter (C :: ac :: nil) (Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Ap :: Cp :: ac :: nil) (C :: ac :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: ac :: Ap :: Cp :: ac :: nil) ((C :: ac :: nil) ++ (Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCApCpacmtmp;try rewrite HT2 in HCApCpacmtmp.
	assert(HT := rule_2 (C :: ac :: nil) (Ap :: Cp :: ac :: nil) (ac :: nil) 3 1 2 HCApCpacmtmp Hacmtmp HApCpacMtmp Hincl);apply HT.
}

assert(HCacM : rk(C :: ac ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCaceq HCacM2).
assert(HCacm : rk(C :: ac ::  nil) >= 1) by (solve_hyps_min HCaceq HCacm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCApac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Ap :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CApac requis par la preuve de (?)CApac pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CApac requis par la preuve de (?)CApac pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCApacm2 : rk(C :: Ap :: ac :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (C :: Ap :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (C :: Ap :: ac :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : A :: C :: Ap :: ac ::  de rang :  3 et 3 	 AiB : C :: ac ::  de rang :  2 et 2 	 A : A :: C :: ac ::   de rang : 2 et 2 *)
assert(HCApacm3 : rk(C :: Ap :: ac :: nil) >= 3).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HACApaceq : rk(A :: C :: Ap :: ac :: nil) = 3) by (apply LACApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApacmtmp : rk(A :: C :: Ap :: ac :: nil) >= 3) by (solve_hyps_min HACApaceq HACApacm3).
	assert(HCaceq : rk(C :: ac :: nil) = 2) by (apply LCac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCacmtmp : rk(C :: ac :: nil) >= 2) by (solve_hyps_min HCaceq HCacm2).
	assert(Hincl : incl (C :: ac :: nil) (list_inter (A :: C :: ac :: nil) (C :: Ap :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: ac :: nil) (A :: C :: ac :: C :: Ap :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: C :: ac :: C :: Ap :: ac :: nil) ((A :: C :: ac :: nil) ++ (C :: Ap :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACApacmtmp;try rewrite HT2 in HACApacmtmp.
	assert(HT := rule_4 (A :: C :: ac :: nil) (C :: Ap :: ac :: nil) (C :: ac :: nil) 3 2 2 HACApacmtmp HCacmtmp HACacMtmp Hincl); apply HT.
}

assert(HCApacM : rk(C :: Ap :: ac ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCApaceq HCApacM3).
assert(HCApacm : rk(C :: Ap :: ac ::  nil) >= 1) by (solve_hyps_min HCApaceq HCApacm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoACApCpac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Ap :: Cp :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACApCpac pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACApCpac pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApCpacm2 : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApCpacm3 : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HOoACApCpacM3 : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) <= 3).
{
	assert(HOoCApaceq : rk(Oo :: C :: Ap :: ac :: nil) = 3) by (apply LOoCApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoCApacMtmp : rk(Oo :: C :: Ap :: ac :: nil) <= 3) by (solve_hyps_max HOoCApaceq HOoCApacM3).
	assert(HACApCpaceq : rk(A :: C :: Ap :: Cp :: ac :: nil) = 3) by (apply LACApCpac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApCpacMtmp : rk(A :: C :: Ap :: Cp :: ac :: nil) <= 3) by (solve_hyps_max HACApCpaceq HACApCpacM3).
	assert(HCApaceq : rk(C :: Ap :: ac :: nil) = 3) by (apply LCApac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApacmtmp : rk(C :: Ap :: ac :: nil) >= 3) by (solve_hyps_min HCApaceq HCApacm3).
	assert(Hincl : incl (C :: Ap :: ac :: nil) (list_inter (Oo :: C :: Ap :: ac :: nil) (A :: C :: Ap :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Cp :: ac :: nil) (Oo :: C :: Ap :: ac :: A :: C :: Ap :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: C :: Ap :: ac :: A :: C :: Ap :: Cp :: ac :: nil) ((Oo :: C :: Ap :: ac :: nil) ++ (A :: C :: Ap :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: C :: Ap :: ac :: nil) (A :: C :: Ap :: Cp :: ac :: nil) (C :: Ap :: ac :: nil) 3 3 3 HOoCApacMtmp HACApCpacMtmp HCApacmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HOoACApCpacM : rk(Oo :: A :: C :: Ap :: Cp :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACApCpacm : rk(Oo :: A :: C :: Ap :: Cp :: ac ::  nil) >= 1) by (solve_hyps_min HOoACApCpaceq HOoACApCpacm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoACCpac : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Cp :: ac ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACCpac requis par la preuve de (?)OoACCpac pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACCpac requis par la preuve de (?)OoACCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACCpac pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACApCpac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApCpac requis par la preuve de (?)OoACApCpac pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApCpacm2 : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApCpacm3 : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAC requis par la preuve de (?)OoACCpac pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACac requis par la preuve de (?)OoAC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACac requis par la preuve de (?)OoACac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACac requis par la preuve de (?)OoACac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACacM3 : rk(Oo :: A :: C :: ac :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: ac :: nil) ((Oo :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: C :: ac :: nil) (nil) 1 2 0 HOoMtmp HACacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACacm2 : rk(Oo :: A :: C :: ac :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: ac :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAC requis par la preuve de (?)OoAC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoACm2 : rk(Oo :: A :: C :: nil) >= 2).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACacmtmp : rk(Oo :: A :: C :: ac :: nil) >= 2) by (solve_hyps_min HOoACaceq HOoACacm2).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: A :: C :: ac :: nil) ((Oo :: A :: C :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACacmtmp;try rewrite HT2 in HOoACacmtmp.
	assert(HT := rule_2 (Oo :: A :: C :: nil) (A :: C :: ac :: nil) (A :: C :: nil) 2 2 2 HOoACacmtmp HACmtmp HACacMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACCpac requis par la preuve de (?)OoACCpac pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Cp :: ac ::  de rang :  3 et 4 	 AiB : Oo :: A :: C ::  de rang :  2 et 3 	 A : Oo :: A :: C :: Ap ::   de rang : 3 et 3 *)
assert(HOoACCpacm2 : rk(Oo :: A :: C :: Cp :: ac :: nil) >= 2).
{
	assert(HOoACApeq : rk(Oo :: A :: C :: Ap :: nil) = 3) by (apply LOoACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApCpacmtmp : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) >= 3) by (solve_hyps_min HOoACApCpaceq HOoACApCpacm3).
	assert(HOoACmtmp : rk(Oo :: A :: C :: nil) >= 2) by (solve_hyps_min HOoACeq HOoACm2).
	assert(Hincl : incl (Oo :: A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Cp :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Cp :: ac :: nil) (Oo :: A :: C :: Ap :: Oo :: A :: C :: Cp :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: Oo :: A :: C :: Cp :: ac :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (Oo :: A :: C :: Cp :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApCpacmtmp;try rewrite HT2 in HOoACApCpacmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Cp :: ac :: nil) (Oo :: A :: C :: nil) 3 2 3 HOoACApCpacmtmp HOoACmtmp HOoACApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACCpacm3 : rk(Oo :: A :: C :: Cp :: ac :: nil) >= 3).
{
	assert(HACCpmtmp : rk(A :: C :: Cp :: nil) >= 3) by (solve_hyps_min HACCpeq HACCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Cp :: nil) (Oo :: A :: C :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Cp :: nil) (Oo :: A :: C :: Cp :: ac :: nil) 3 3 HACCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACCpacM3 : rk(Oo :: A :: C :: Cp :: ac :: nil) <= 3).
{
	assert(HOoACApCpaceq : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) = 3) by (apply LOoACApCpac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApCpacMtmp : rk(Oo :: A :: C :: Ap :: Cp :: ac :: nil) <= 3) by (solve_hyps_max HOoACApCpaceq HOoACApCpacM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: C :: Cp :: ac :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Oo :: A :: C :: Cp :: ac :: nil) (Oo :: A :: C :: Ap :: Cp :: ac :: nil) 3 3 HOoACApCpacMtmp Hcomp Hincl);apply HT.
}

assert(HOoACCpacM : rk(Oo :: A :: C :: Cp :: ac ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACCpacm : rk(Oo :: A :: C :: Cp :: ac ::  nil) >= 1) by (solve_hyps_min HOoACCpaceq HOoACCpacm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACCp *)
(* dans la couche 0 *)
Lemma LOoABCCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Cp :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCCpbc requis par la preuve de (?)OoABCCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCCpbc requis par la preuve de (?)OoABCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCCpbc requis par la preuve de (?)OoABCCpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp :: bc ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCCpbcm2 : rk(Oo :: A :: B :: C :: Cp :: bc :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApCpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 3) by (solve_hyps_min HOoABCApCpbceq HOoABCApCpbcm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: bc :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpbcmtmp;try rewrite HT2 in HOoABCApCpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApCpbcmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  de rang :  4 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoABCCpbcm3 : rk(Oo :: A :: B :: C :: Cp :: bc :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HOoABCApBpCpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpbceq HOoABCApBpCpbcm4).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: bc :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpbcmtmp;try rewrite HT2 in HOoABCApBpCpbcmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil) (A :: B :: nil) 4 2 3 HOoABCApBpCpbcmtmp HABmtmp HABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCCpbcm4 : rk(Oo :: A :: B :: C :: Cp :: bc :: nil) >= 4).
{
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCCpbcM : rk(Oo :: A :: B :: C :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCCpbcm : rk(Oo :: A :: B :: C :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCCpbceq HOoABCCpbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACCp *)
(* dans la couche 0 *)
Lemma LOoABCCpacbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Cp :: ac :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCCpacbc requis par la preuve de (?)OoABCCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCCpacbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCCpacbc requis par la preuve de (?)OoABCCpacbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpacbc requis par la preuve de (?)OoABCCpacbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpacbc requis par la preuve de (?)OoABCApCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpacbc requis par la preuve de (?)OoABCApCpacbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpacbcm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpacbcm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCCpacbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCCpacbc requis par la preuve de (?)OoABCCpacbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCCpacbcm2 : rk(Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApCpacbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) >= 3) by (solve_hyps_min HOoABCApCpacbceq HOoABCApCpacbcm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: ac :: bc :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: ac :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpacbcmtmp;try rewrite HT2 in HOoABCApCpacbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApCpacbcmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc ::  de rang :  4 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoABCCpacbcm3 : rk(Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HOoABCApBpCpacbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpacbceq HOoABCApBpCpacbcm4).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: ac :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpacbcmtmp;try rewrite HT2 in HOoABCApBpCpacbcmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) (A :: B :: nil) 4 2 3 HOoABCApBpCpacbcmtmp HABmtmp HABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCCpacbcm4 : rk(Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) >= 4).
{
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCCpacbcM : rk(Oo :: A :: B :: C :: Cp :: ac :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCCpacbcm : rk(Oo :: A :: B :: C :: Cp :: ac :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCCpacbceq HOoABCCpacbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoACCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Cp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACCp requis par la preuve de (?)OoACCp pour la règle 3  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACCp requis par la preuve de (?)OoACCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApCp requis par la preuve de (?)OoACCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApCp requis par la preuve de (?)OoACApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApCp requis par la preuve de (?)OoACApCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApCpm2 : rk(Oo :: A :: C :: Ap :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApCpm3 : rk(Oo :: A :: C :: Ap :: Cp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Cp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAC requis par la preuve de (?)OoACCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACac requis par la preuve de (?)OoAC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACac requis par la preuve de (?)OoACac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACac requis par la preuve de (?)OoACac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACacM3 : rk(Oo :: A :: C :: ac :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: ac :: nil) ((Oo :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: C :: ac :: nil) (nil) 1 2 0 HOoMtmp HACacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACacm2 : rk(Oo :: A :: C :: ac :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: ac :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAC requis par la preuve de (?)OoAC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoACm2 : rk(Oo :: A :: C :: nil) >= 2).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACacmtmp : rk(Oo :: A :: C :: ac :: nil) >= 2) by (solve_hyps_min HOoACaceq HOoACacm2).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: A :: C :: ac :: nil) ((Oo :: A :: C :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACacmtmp;try rewrite HT2 in HOoACacmtmp.
	assert(HT := rule_2 (Oo :: A :: C :: nil) (A :: C :: ac :: nil) (A :: C :: nil) 2 2 2 HOoACacmtmp HACmtmp HACacMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACAp requis par la preuve de (?)OoACAp pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACApM3 : rk(Oo :: A :: C :: Ap :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Oo :: A :: Ap :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: nil) (C :: Oo :: A :: Ap :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Oo :: A :: Ap :: nil) ((C :: nil) ++ (Oo :: A :: Ap :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Oo :: A :: Ap :: nil) (nil) 1 2 0 HCMtmp HOoAApMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApm2 : rk(Oo :: A :: C :: Ap :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: Ap :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: Ap :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACCp requis par la preuve de (?)OoACCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 5*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Cp ::  de rang :  3 et 4 	 AiB : Oo :: A :: C ::  de rang :  2 et 3 	 A : Oo :: A :: C :: Ap ::   de rang : 2 et 3 *)
assert(HOoACCpm2 : rk(Oo :: A :: C :: Cp :: nil) >= 2).
{
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApCpmtmp : rk(Oo :: A :: C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HOoACApCpeq HOoACApCpm3).
	assert(HOoACmtmp : rk(Oo :: A :: C :: nil) >= 2) by (solve_hyps_min HOoACeq HOoACm2).
	assert(Hincl : incl (Oo :: A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Cp :: nil) (Oo :: A :: C :: Ap :: Oo :: A :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: Oo :: A :: C :: Cp :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (Oo :: A :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApCpmtmp;try rewrite HT2 in HOoACApCpmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Cp :: nil) (Oo :: A :: C :: nil) 3 2 3 HOoACApCpmtmp HOoACmtmp HOoACApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACCpm3 : rk(Oo :: A :: C :: Cp :: nil) >= 3).
{
	assert(HACCpmtmp : rk(A :: C :: Cp :: nil) >= 3) by (solve_hyps_min HACCpeq HACCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Cp :: nil) (Oo :: A :: C :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Cp :: nil) (Oo :: A :: C :: Cp :: nil) 3 3 HACCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HOoACCpM3 : rk(Oo :: A :: C :: Cp :: nil) <= 3).
{
	assert(HOoACCpaceq : rk(Oo :: A :: C :: Cp :: ac :: nil) = 3) by (apply LOoACCpac with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACCpacMtmp : rk(Oo :: A :: C :: Cp :: ac :: nil) <= 3) by (solve_hyps_max HOoACCpaceq HOoACCpacM3).
	assert(HOoABCCpbceq : rk(Oo :: A :: B :: C :: Cp :: bc :: nil) = 4) by (apply LOoABCCpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCCpbcMtmp : rk(Oo :: A :: B :: C :: Cp :: bc :: nil) <= 4) by (solve_hyps_max HOoABCCpbceq HOoABCCpbcM4).
	assert(HOoABCCpacbceq : rk(Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) = 4) by (apply LOoABCCpacbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCCpacbcmtmp : rk(Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) >= 4) by (solve_hyps_min HOoABCCpacbceq HOoABCCpacbcm4).
	assert(Hincl : incl (Oo :: A :: C :: Cp :: nil) (list_inter (Oo :: A :: C :: Cp :: ac :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Cp :: ac :: bc :: nil) (Oo :: A :: C :: Cp :: ac :: Oo :: A :: B :: C :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Cp :: ac :: Oo :: A :: B :: C :: Cp :: bc :: nil) ((Oo :: A :: C :: Cp :: ac :: nil) ++ (Oo :: A :: B :: C :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCCpacbcmtmp;try rewrite HT2 in HOoABCCpacbcmtmp.
	assert(HT := rule_3 (Oo :: A :: C :: Cp :: ac :: nil) (Oo :: A :: B :: C :: Cp :: bc :: nil) (Oo :: A :: C :: Cp :: nil) 3 4 4 HOoACCpacMtmp HOoABCCpbcMtmp HOoABCCpacbcmtmp Hincl);apply HT.
}


assert(HOoACCpM : rk(Oo :: A :: C :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACCpm : rk(Oo :: A :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HOoACCpeq HOoACCpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoBCCp *)
(* dans constructLemma(), requis par LOoBCCpbc *)
(* dans constructLemma(), requis par LOoBCBpCpbc *)
(* dans constructLemma(), requis par LOoCBpbc *)
(* dans la couche 0 *)
Lemma LOoBCBpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: B :: C :: Bp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBCBpbc requis par la preuve de (?)OoBCBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoBCBpbc requis par la preuve de (?)OoBCBpbc pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoBCBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBCBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoBCbcM3 : rk(Oo :: B :: C :: bc :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: bc :: nil) ((Oo :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (B :: C :: bc :: nil) (nil) 1 2 0 HOoMtmp HBCbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCbcm2 : rk(Oo :: B :: C :: bc :: nil) >= 2).
{
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (Oo :: B :: C :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (Oo :: B :: C :: bc :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoBCm2 : rk(Oo :: B :: C :: nil) >= 2).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoBCbcmtmp : rk(Oo :: B :: C :: bc :: nil) >= 2) by (solve_hyps_min HOoBCbceq HOoBCbcm2).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: B :: C :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: B :: C :: bc :: nil) ((Oo :: B :: C :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoBCbcmtmp;try rewrite HT2 in HOoBCbcmtmp.
	assert(HT := rule_2 (Oo :: B :: C :: nil) (B :: C :: bc :: nil) (B :: C :: nil) 2 2 2 HOoBCbcmtmp HBCmtmp HBCbcMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCBpbc requis par la preuve de (?)OoBCBpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: bc ::  de rang :  4 et 4 	 AiB : Oo :: B :: C ::  de rang :  2 et 3 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HOoBCBpbcm2 : rk(Oo :: B :: C :: Bp :: bc :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpbceq HOoABCApBpbcm4).
	assert(HOoBCmtmp : rk(Oo :: B :: C :: nil) >= 2) by (solve_hyps_min HOoBCeq HOoBCm2).
	assert(Hincl : incl (Oo :: B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Bp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Bp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Bp :: bc :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (Oo :: B :: C :: Bp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpbcmtmp;try rewrite HT2 in HOoABCApBpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Bp :: bc :: nil) (Oo :: B :: C :: nil) 4 2 4 HOoABCApBpbcmtmp HOoBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HOoBCBpbcM3 : rk(Oo :: B :: C :: Bp :: bc :: nil) <= 3).
{
	assert(HOoBBpMtmp : rk(Oo :: B :: Bp :: nil) <= 2) by (solve_hyps_max HOoBBpeq HOoBBpM2).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HBmtmp : rk(B :: nil) >= 1) by (solve_hyps_min HBeq HBm1).
	assert(Hincl : incl (B :: nil) (list_inter (Oo :: B :: Bp :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: Bp :: bc :: nil) (Oo :: B :: Bp :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: Bp :: B :: C :: bc :: nil) ((Oo :: B :: Bp :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: B :: Bp :: nil) (B :: C :: bc :: nil) (B :: nil) 2 2 1 HOoBBpMtmp HBCbcMtmp HBmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCBpbcm3 : rk(Oo :: B :: C :: Bp :: bc :: nil) >= 3).
{
	assert(HBCBpeq : rk(B :: C :: Bp :: nil) = 3) by (apply LBCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 3) by (solve_hyps_min HBCBpeq HBCBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Bp :: nil) (Oo :: B :: C :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Bp :: nil) (Oo :: B :: C :: Bp :: bc :: nil) 3 3 HBCBpmtmp Hcomp Hincl);apply HT.
}

assert(HOoBCBpbcM : rk(Oo :: B :: C :: Bp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoBCBpbcm : rk(Oo :: B :: C :: Bp :: bc ::  nil) >= 1) by (solve_hyps_min HOoBCBpbceq HOoBCBpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoCBpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: C :: Bp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoCBpbc requis par la preuve de (?)OoCBpbc pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 2 pour Cbc requis par la preuve de (?)OoCBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour CBpCpbc requis par la preuve de (?)Cbc pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCBpCpbcM3 : rk(C :: Bp :: Cp :: bc :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBpCpbcMtmp : rk(Bp :: Cp :: bc :: nil) <= 2) by (solve_hyps_max HBpCpbceq HBpCpbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Bp :: Cp :: bc :: nil) (C :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Bp :: Cp :: bc :: nil) ((C :: nil) ++ (Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Bp :: Cp :: bc :: nil) (nil) 1 2 0 HCMtmp HBpCpbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCBpCpbcm2 : rk(C :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HCBpeq : rk(C :: Bp :: nil) = 2) by (apply LCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpmtmp : rk(C :: Bp :: nil) >= 2) by (solve_hyps_min HCBpeq HCBpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: nil) (C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: nil) (C :: Bp :: Cp :: bc :: nil) 2 2 HCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCBpCpbcm3 : rk(C :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HCBpCpmtmp : rk(C :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HCBpCpeq HCBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: Cp :: nil) (C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: Cp :: nil) (C :: Bp :: Cp :: bc :: nil) 3 3 HCBpCpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Cbc requis par la preuve de (?)Cbc pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 -2 et -4*)
assert(HCbcm2 : rk(C :: bc :: nil) >= 2).
{
	assert(HBpCpbcMtmp : rk(Bp :: Cp :: bc :: nil) <= 2) by (solve_hyps_max HBpCpbceq HBpCpbcM2).
	assert(HCBpCpbcmtmp : rk(C :: Bp :: Cp :: bc :: nil) >= 3) by (solve_hyps_min HCBpCpbceq HCBpCpbcm3).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (C :: bc :: nil) (Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Bp :: Cp :: bc :: nil) (C :: bc :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: bc :: Bp :: Cp :: bc :: nil) ((C :: bc :: nil) ++ (Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCBpCpbcmtmp;try rewrite HT2 in HCBpCpbcmtmp.
	assert(HT := rule_2 (C :: bc :: nil) (Bp :: Cp :: bc :: nil) (bc :: nil) 3 1 2 HCBpCpbcmtmp Hbcmtmp HBpCpbcMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoCBpbc requis par la preuve de (?)OoCBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoCBpbc requis par la preuve de (?)OoCBpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoCBpbcm2 : rk(Oo :: C :: Bp :: bc :: nil) >= 2).
{
	assert(HCBpeq : rk(C :: Bp :: nil) = 2) by (apply LCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpmtmp : rk(C :: Bp :: nil) >= 2) by (solve_hyps_min HCBpeq HCBpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: nil) (Oo :: C :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: nil) (Oo :: C :: Bp :: bc :: nil) 2 2 HCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 4 5 et -4*)
(* ensembles concernés AUB : Oo :: B :: C :: Bp :: bc ::  de rang :  3 et 3 	 AiB : C :: bc ::  de rang :  2 et 2 	 A : B :: C :: bc ::   de rang : 2 et 2 *)
assert(HOoCBpbcm3 : rk(Oo :: C :: Bp :: bc :: nil) >= 3).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoBCBpbceq : rk(Oo :: B :: C :: Bp :: bc :: nil) = 3) by (apply LOoBCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBCBpbcmtmp : rk(Oo :: B :: C :: Bp :: bc :: nil) >= 3) by (solve_hyps_min HOoBCBpbceq HOoBCBpbcm3).
	assert(HCbcmtmp : rk(C :: bc :: nil) >= 2) by (solve_hyps_min HCbceq HCbcm2).
	assert(Hincl : incl (C :: bc :: nil) (list_inter (B :: C :: bc :: nil) (Oo :: C :: Bp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: Bp :: bc :: nil) (B :: C :: bc :: Oo :: C :: Bp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: bc :: Oo :: C :: Bp :: bc :: nil) ((B :: C :: bc :: nil) ++ (Oo :: C :: Bp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoBCBpbcmtmp;try rewrite HT2 in HOoBCBpbcmtmp.
	assert(HT := rule_4 (B :: C :: bc :: nil) (Oo :: C :: Bp :: bc :: nil) (C :: bc :: nil) 3 2 2 HOoBCBpbcmtmp HCbcmtmp HBCbcMtmp Hincl); apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoCBpbcM3 : rk(Oo :: C :: Bp :: bc :: nil) <= 3).
{
	assert(HOoBCBpbceq : rk(Oo :: B :: C :: Bp :: bc :: nil) = 3) by (apply LOoBCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBCBpbcMtmp : rk(Oo :: B :: C :: Bp :: bc :: nil) <= 3) by (solve_hyps_max HOoBCBpbceq HOoBCBpbcM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: C :: Bp :: bc :: nil) (Oo :: B :: C :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Oo :: C :: Bp :: bc :: nil) (Oo :: B :: C :: Bp :: bc :: nil) 3 3 HOoBCBpbcMtmp Hcomp Hincl);apply HT.
}

assert(HOoCBpbcM : rk(Oo :: C :: Bp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoCBpbcm : rk(Oo :: C :: Bp :: bc ::  nil) >= 1) by (solve_hyps_min HOoCBpbceq HOoCBpbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoBCBpCpbc *)
(* dans la couche 0 *)
Lemma LBCBpCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: C :: Bp :: Cp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BCBpCpbc requis par la preuve de (?)BCBpCpbc pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpCpbc requis par la preuve de (?)BCBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)BCBpCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpCpbc requis par la preuve de (?)BCBpCpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  de rang :  4 et 4 	 AiB : B :: C ::  de rang :  2 et 2 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HBCBpCpbcm2 : rk(B :: C :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpCpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpbceq HOoABCApBpCpbcm4).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: Cp :: bc :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (B :: C :: Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpbcmtmp;try rewrite HT2 in HOoABCApBpCpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: Cp :: bc :: nil) (B :: C :: nil) 4 2 4 HOoABCApBpCpbcmtmp HBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCBpCpbcm3 : rk(B :: C :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HBCBpeq : rk(B :: C :: Bp :: nil) = 3) by (apply LBCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 3) by (solve_hyps_min HBCBpeq HBCBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Bp :: nil) (B :: C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Bp :: nil) (B :: C :: Bp :: Cp :: bc :: nil) 3 3 HBCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HBCBpCpbcM3 : rk(B :: C :: Bp :: Cp :: bc :: nil) <= 3).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HBpCpbcMtmp : rk(Bp :: Cp :: bc :: nil) <= 2) by (solve_hyps_max HBpCpbceq HBpCpbcM2).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (B :: C :: bc :: nil) (Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: Cp :: bc :: nil) (B :: C :: bc :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: bc :: Bp :: Cp :: bc :: nil) ((B :: C :: bc :: nil) ++ (Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: C :: bc :: nil) (Bp :: Cp :: bc :: nil) (bc :: nil) 2 2 1 HBCbcMtmp HBpCpbcMtmp Hbcmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HBCBpCpbcM : rk(B :: C :: Bp :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpCpbcm : rk(B :: C :: Bp :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HBCBpCpbceq HBCBpCpbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoBCBpCpbc *)
(* dans constructLemma(), requis par LCBpbc *)
(* dans la couche 0 *)
Lemma LBCBpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: C :: Bp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour BCBpbc requis par la preuve de (?)BCBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BCBpbc requis par la preuve de (?)BCBpbc pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)BCBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BCBpbc requis par la preuve de (?)BCBpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: bc ::  de rang :  4 et 4 	 AiB : B :: C ::  de rang :  2 et 2 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HBCBpbcm2 : rk(B :: C :: Bp :: bc :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpbceq HOoABCApBpbcm4).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: B :: C :: Bp :: bc :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (B :: C :: Bp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpbcmtmp;try rewrite HT2 in HOoABCApBpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (B :: C :: Bp :: bc :: nil) (B :: C :: nil) 4 2 4 HOoABCApBpbcmtmp HBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HBCBpbcM3 : rk(B :: C :: Bp :: bc :: nil) <= 3).
{
	assert(HBpMtmp : rk(Bp :: nil) <= 1) by (solve_hyps_max HBpeq HBpM1).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Bp :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: bc :: nil) (Bp :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Bp :: B :: C :: bc :: nil) ((Bp :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Bp :: nil) (B :: C :: bc :: nil) (nil) 1 2 0 HBpMtmp HBCbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HBCBpbcm3 : rk(B :: C :: Bp :: bc :: nil) >= 3).
{
	assert(HBCBpeq : rk(B :: C :: Bp :: nil) = 3) by (apply LBCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 3) by (solve_hyps_min HBCBpeq HBCBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Bp :: nil) (B :: C :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Bp :: nil) (B :: C :: Bp :: bc :: nil) 3 3 HBCBpmtmp Hcomp Hincl);apply HT.
}

assert(HBCBpbcM : rk(B :: C :: Bp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBCBpbcm : rk(B :: C :: Bp :: bc ::  nil) >= 1) by (solve_hyps_min HBCBpbceq HBCBpbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LCBpbc *)
(* dans constructLemma(), requis par LCbc *)
(* dans la couche 0 *)
Lemma LCBpCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Bp :: Cp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour CBpCpbc requis par la preuve de (?)CBpCpbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HCBpCpbcM3 : rk(C :: Bp :: Cp :: bc :: nil) <= 3).
{
	assert(HCMtmp : rk(C :: nil) <= 1) by (solve_hyps_max HCeq HCM1).
	assert(HBpCpbcMtmp : rk(Bp :: Cp :: bc :: nil) <= 2) by (solve_hyps_max HBpCpbceq HBpCpbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (C :: nil) (Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Bp :: Cp :: bc :: nil) (C :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Bp :: Cp :: bc :: nil) ((C :: nil) ++ (Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (C :: nil) (Bp :: Cp :: bc :: nil) (nil) 1 2 0 HCMtmp HBpCpbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCBpCpbcm2 : rk(C :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HCBpeq : rk(C :: Bp :: nil) = 2) by (apply LCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpmtmp : rk(C :: Bp :: nil) >= 2) by (solve_hyps_min HCBpeq HCBpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: nil) (C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: nil) (C :: Bp :: Cp :: bc :: nil) 2 2 HCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HCBpCpbcm3 : rk(C :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HCBpCpmtmp : rk(C :: Bp :: Cp :: nil) >= 3) by (solve_hyps_min HCBpCpeq HCBpCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: Cp :: nil) (C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: Cp :: nil) (C :: Bp :: Cp :: bc :: nil) 3 3 HCBpCpmtmp Hcomp Hincl);apply HT.
}

assert(HCBpCpbcM : rk(C :: Bp :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HCBpCpbcm : rk(C :: Bp :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HCBpCpbceq HCBpCpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: bc ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour Cbc requis par la preuve de (?)Cbc pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(HCbcm2 : rk(C :: bc :: nil) >= 2).
{
	assert(HBpCpbcMtmp : rk(Bp :: Cp :: bc :: nil) <= 2) by (solve_hyps_max HBpCpbceq HBpCpbcM2).
	assert(HCBpCpbceq : rk(C :: Bp :: Cp :: bc :: nil) = 3) by (apply LCBpCpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpCpbcmtmp : rk(C :: Bp :: Cp :: bc :: nil) >= 3) by (solve_hyps_min HCBpCpbceq HCBpCpbcm3).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (C :: bc :: nil) (Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (C :: Bp :: Cp :: bc :: nil) (C :: bc :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: bc :: Bp :: Cp :: bc :: nil) ((C :: bc :: nil) ++ (Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HCBpCpbcmtmp;try rewrite HT2 in HCBpCpbcmtmp.
	assert(HT := rule_2 (C :: bc :: nil) (Bp :: Cp :: bc :: nil) (bc :: nil) 3 1 2 HCBpCpbcmtmp Hbcmtmp HBpCpbcMtmp Hincl);apply HT.
}

assert(HCbcM : rk(C :: bc ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HCbceq HCbcM2).
assert(HCbcm : rk(C :: bc ::  nil) >= 1) by (solve_hyps_min HCbceq HCbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LCBpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(C :: Bp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour CBpbc requis par la preuve de (?)CBpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour CBpbc requis par la preuve de (?)CBpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HCBpbcm2 : rk(C :: Bp :: bc :: nil) >= 2).
{
	assert(HCBpeq : rk(C :: Bp :: nil) = 2) by (apply LCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpmtmp : rk(C :: Bp :: nil) >= 2) by (solve_hyps_min HCBpeq HCBpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Bp :: nil) (C :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Bp :: nil) (C :: Bp :: bc :: nil) 2 2 HCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : B :: C :: Bp :: bc ::  de rang :  3 et 3 	 AiB : C :: bc ::  de rang :  2 et 2 	 A : B :: C :: bc ::   de rang : 2 et 2 *)
assert(HCBpbcm3 : rk(C :: Bp :: bc :: nil) >= 3).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HBCBpbceq : rk(B :: C :: Bp :: bc :: nil) = 3) by (apply LBCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpbcmtmp : rk(B :: C :: Bp :: bc :: nil) >= 3) by (solve_hyps_min HBCBpbceq HBCBpbcm3).
	assert(HCbceq : rk(C :: bc :: nil) = 2) by (apply LCbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCbcmtmp : rk(C :: bc :: nil) >= 2) by (solve_hyps_min HCbceq HCbcm2).
	assert(Hincl : incl (C :: bc :: nil) (list_inter (B :: C :: bc :: nil) (C :: Bp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: C :: Bp :: bc :: nil) (B :: C :: bc :: C :: Bp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: bc :: C :: Bp :: bc :: nil) ((B :: C :: bc :: nil) ++ (C :: Bp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HBCBpbcmtmp;try rewrite HT2 in HBCBpbcmtmp.
	assert(HT := rule_4 (B :: C :: bc :: nil) (C :: Bp :: bc :: nil) (C :: bc :: nil) 3 2 2 HBCBpbcmtmp HCbcmtmp HBCbcMtmp Hincl); apply HT.
}

assert(HCBpbcM : rk(C :: Bp :: bc ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HCBpbceq HCBpbcM3).
assert(HCBpbcm : rk(C :: Bp :: bc ::  nil) >= 1) by (solve_hyps_min HCBpbceq HCBpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoBCBpCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: B :: C :: Bp :: Cp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoBCBpCpbc requis par la preuve de (?)OoBCBpCpbc pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoBCBpCpbc requis par la preuve de (?)OoBCBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoBCBpCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBCBpCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoBCbcM3 : rk(Oo :: B :: C :: bc :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: bc :: nil) ((Oo :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (B :: C :: bc :: nil) (nil) 1 2 0 HOoMtmp HBCbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCbcm2 : rk(Oo :: B :: C :: bc :: nil) >= 2).
{
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (Oo :: B :: C :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (Oo :: B :: C :: bc :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoBCm2 : rk(Oo :: B :: C :: nil) >= 2).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoBCbcmtmp : rk(Oo :: B :: C :: bc :: nil) >= 2) by (solve_hyps_min HOoBCbceq HOoBCbcm2).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: B :: C :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: B :: C :: bc :: nil) ((Oo :: B :: C :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoBCbcmtmp;try rewrite HT2 in HOoBCbcmtmp.
	assert(HT := rule_2 (Oo :: B :: C :: nil) (B :: C :: bc :: nil) (B :: C :: nil) 2 2 2 HOoBCbcmtmp HBCmtmp HBCbcMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCBpCpbc requis par la preuve de (?)OoBCBpCpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  de rang :  4 et 4 	 AiB : Oo :: B :: C ::  de rang :  2 et 3 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HOoBCBpCpbcm2 : rk(Oo :: B :: C :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApBpCpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpbceq HOoABCApBpCpbcm4).
	assert(HOoBCmtmp : rk(Oo :: B :: C :: nil) >= 2) by (solve_hyps_min HOoBCeq HOoBCm2).
	assert(Hincl : incl (Oo :: B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Bp :: Cp :: bc :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (Oo :: B :: C :: Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpbcmtmp;try rewrite HT2 in HOoABCApBpCpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil) (Oo :: B :: C :: nil) 4 2 4 HOoABCApBpCpbcmtmp HOoBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCBpCpbcm3 : rk(Oo :: B :: C :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HBCBpeq : rk(B :: C :: Bp :: nil) = 3) by (apply LBCBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpmtmp : rk(B :: C :: Bp :: nil) >= 3) by (solve_hyps_min HBCBpeq HBCBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Bp :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Bp :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil) 3 3 HBCBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 4*)
assert(HOoBCBpCpbcM3 : rk(Oo :: B :: C :: Bp :: Cp :: bc :: nil) <= 3).
{
	assert(HOoCBpbceq : rk(Oo :: C :: Bp :: bc :: nil) = 3) by (apply LOoCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoCBpbcMtmp : rk(Oo :: C :: Bp :: bc :: nil) <= 3) by (solve_hyps_max HOoCBpbceq HOoCBpbcM3).
	assert(HBCBpCpbceq : rk(B :: C :: Bp :: Cp :: bc :: nil) = 3) by (apply LBCBpCpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCBpCpbcMtmp : rk(B :: C :: Bp :: Cp :: bc :: nil) <= 3) by (solve_hyps_max HBCBpCpbceq HBCBpCpbcM3).
	assert(HCBpbceq : rk(C :: Bp :: bc :: nil) = 3) by (apply LCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCBpbcmtmp : rk(C :: Bp :: bc :: nil) >= 3) by (solve_hyps_min HCBpbceq HCBpbcm3).
	assert(Hincl : incl (C :: Bp :: bc :: nil) (list_inter (Oo :: C :: Bp :: bc :: nil) (B :: C :: Bp :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: Bp :: Cp :: bc :: nil) (Oo :: C :: Bp :: bc :: B :: C :: Bp :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: C :: Bp :: bc :: B :: C :: Bp :: Cp :: bc :: nil) ((Oo :: C :: Bp :: bc :: nil) ++ (B :: C :: Bp :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: C :: Bp :: bc :: nil) (B :: C :: Bp :: Cp :: bc :: nil) (C :: Bp :: bc :: nil) 3 3 3 HOoCBpbcMtmp HBCBpCpbcMtmp HCBpbcmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HOoBCBpCpbcM : rk(Oo :: B :: C :: Bp :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoBCBpCpbcm : rk(Oo :: B :: C :: Bp :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HOoBCBpCpbceq HOoBCBpCpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoBCCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: B :: C :: Cp :: bc ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoBCCpbc requis par la preuve de (?)OoBCCpbc pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoBCCpbc requis par la preuve de (?)OoBCCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoBCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBCCpbc pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoBCbcM3 : rk(Oo :: B :: C :: bc :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: bc :: nil) ((Oo :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (B :: C :: bc :: nil) (nil) 1 2 0 HOoMtmp HBCbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCbcm2 : rk(Oo :: B :: C :: bc :: nil) >= 2).
{
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (Oo :: B :: C :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (Oo :: B :: C :: bc :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoBCm2 : rk(Oo :: B :: C :: nil) >= 2).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoBCbcmtmp : rk(Oo :: B :: C :: bc :: nil) >= 2) by (solve_hyps_min HOoBCbceq HOoBCbcm2).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: B :: C :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: B :: C :: bc :: nil) ((Oo :: B :: C :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoBCbcmtmp;try rewrite HT2 in HOoBCbcmtmp.
	assert(HT := rule_2 (Oo :: B :: C :: nil) (B :: C :: bc :: nil) (B :: C :: nil) 2 2 2 HOoBCbcmtmp HBCmtmp HBCbcMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCCpbc requis par la preuve de (?)OoBCCpbc pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp :: bc ::  de rang :  4 et 4 	 AiB : Oo :: B :: C ::  de rang :  2 et 3 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HOoBCCpbcm2 : rk(Oo :: B :: C :: Cp :: bc :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApCpbcmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 4) by (solve_hyps_min HOoABCApCpbceq HOoABCApCpbcm4).
	assert(HOoBCmtmp : rk(Oo :: B :: C :: nil) >= 2) by (solve_hyps_min HOoBCeq HOoBCm2).
	assert(Hincl : incl (Oo :: B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Cp :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Cp :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Cp :: bc :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (Oo :: B :: C :: Cp :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpbcmtmp;try rewrite HT2 in HOoABCApCpbcmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Cp :: bc :: nil) (Oo :: B :: C :: nil) 4 2 4 HOoABCApCpbcmtmp HOoBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoBCCpbcm3 : rk(Oo :: B :: C :: Cp :: bc :: nil) >= 3).
{
	assert(HBCCpmtmp : rk(B :: C :: Cp :: nil) >= 3) by (solve_hyps_min HBCCpeq HBCCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: bc :: nil) 3 3 HBCCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCCpbcM3 : rk(Oo :: B :: C :: Cp :: bc :: nil) <= 3).
{
	assert(HOoBCBpCpbceq : rk(Oo :: B :: C :: Bp :: Cp :: bc :: nil) = 3) by (apply LOoBCBpCpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBCBpCpbcMtmp : rk(Oo :: B :: C :: Bp :: Cp :: bc :: nil) <= 3) by (solve_hyps_max HOoBCBpCpbceq HOoBCBpCpbcM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: B :: C :: Cp :: bc :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Oo :: B :: C :: Cp :: bc :: nil) (Oo :: B :: C :: Bp :: Cp :: bc :: nil) 3 3 HOoBCBpCpbcMtmp Hcomp Hincl);apply HT.
}

assert(HOoBCCpbcM : rk(Oo :: B :: C :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoBCCpbcm : rk(Oo :: B :: C :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HOoBCCpbceq HOoBCCpbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoBCCp *)
(* dans la couche 0 *)
Lemma LOoABCCpD : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Cp :: D ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCCpD requis par la preuve de (?)OoABCCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCCpD pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCCpD requis par la preuve de (?)OoABCCpD pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpD requis par la preuve de (?)OoABCCpD pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpD requis par la preuve de (?)OoABCApCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpD requis par la preuve de (?)OoABCApCpD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpDm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpDm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCCpD pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCCpD requis par la preuve de (?)OoABCCpD pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp :: D ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCCpDm2 : rk(Oo :: A :: B :: C :: Cp :: D :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApCpDmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) >= 3) by (solve_hyps_min HOoABCApCpDeq HOoABCApCpDm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: D :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: D :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Cp :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpDmtmp;try rewrite HT2 in HOoABCApCpDmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApCpDmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D ::  de rang :  4 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoABCCpDm3 : rk(Oo :: A :: B :: C :: Cp :: D :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HOoABCApBpCpDmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpDeq HOoABCApBpCpDm4).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: D :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (Oo :: A :: B :: C :: Cp :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpDmtmp;try rewrite HT2 in HOoABCApBpCpDmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil) (A :: B :: nil) 4 2 3 HOoABCApBpCpDmtmp HABmtmp HABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCCpDm4 : rk(Oo :: A :: B :: C :: Cp :: D :: nil) >= 4).
{
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCCpDM : rk(Oo :: A :: B :: C :: Cp :: D ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCCpDm : rk(Oo :: A :: B :: C :: Cp :: D ::  nil) >= 1) by (solve_hyps_min HOoABCCpDeq HOoABCCpDm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoBCCp *)
(* dans la couche 0 *)
Lemma LOoABCCpbcD : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Cp :: bc :: D ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCCpbcD requis par la preuve de (?)OoABCCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCCpbcD pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCCpbcD requis par la preuve de (?)OoABCCpbcD pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpbcD requis par la preuve de (?)OoABCCpbcD pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpbcD requis par la preuve de (?)OoABCApCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpbcD requis par la preuve de (?)OoABCApCpbcD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcDm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcDm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCCpbcD pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCCpbcD requis par la preuve de (?)OoABCCpbcD pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp :: bc :: D ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCCpbcDm2 : rk(Oo :: A :: B :: C :: Cp :: bc :: D :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApCpbcDmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) >= 3) by (solve_hyps_min HOoABCApCpbcDeq HOoABCApCpbcDm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: bc :: D :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: bc :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: bc :: D :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Cp :: bc :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpbcDmtmp;try rewrite HT2 in HOoABCApCpbcDmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApCpbcDmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D ::  de rang :  4 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoABCCpbcDm3 : rk(Oo :: A :: B :: C :: Cp :: bc :: D :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HOoABCApBpCpbcDmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpbcDeq HOoABCApBpCpbcDm4).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: bc :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: bc :: D :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (Oo :: A :: B :: C :: Cp :: bc :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpbcDmtmp;try rewrite HT2 in HOoABCApBpCpbcDmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil) (A :: B :: nil) 4 2 3 HOoABCApBpCpbcDmtmp HABmtmp HABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCCpbcDm4 : rk(Oo :: A :: B :: C :: Cp :: bc :: D :: nil) >= 4).
{
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: bc :: D :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCCpbcDM : rk(Oo :: A :: B :: C :: Cp :: bc :: D ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCCpbcDm : rk(Oo :: A :: B :: C :: Cp :: bc :: D ::  nil) >= 1) by (solve_hyps_min HOoABCCpbcDeq HOoABCCpbcDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoBCCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: B :: C :: Cp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoBCCp requis par la preuve de (?)OoBCCp pour la règle 3  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoBCCp requis par la preuve de (?)OoBCCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoBCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm4 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCbc requis par la preuve de (?)OoBCbc pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoBCbcM3 : rk(Oo :: B :: C :: bc :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: bc :: nil) ((Oo :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (B :: C :: bc :: nil) (nil) 1 2 0 HOoMtmp HBCbcMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoBCbcm2 : rk(Oo :: B :: C :: bc :: nil) >= 2).
{
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (B :: C :: nil) (Oo :: B :: C :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: nil) (Oo :: B :: C :: bc :: nil) 2 2 HBCmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoBC requis par la preuve de (?)OoBC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoBCm2 : rk(Oo :: B :: C :: nil) >= 2).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoBCbcmtmp : rk(Oo :: B :: C :: bc :: nil) >= 2) by (solve_hyps_min HOoBCbceq HOoBCbcm2).
	assert(HBCeq : rk(B :: C :: nil) = 2) by (apply LBC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBCmtmp : rk(B :: C :: nil) >= 2) by (solve_hyps_min HBCeq HBCm2).
	assert(Hincl : incl (B :: C :: nil) (list_inter (Oo :: B :: C :: nil) (B :: C :: bc :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: C :: bc :: nil) (Oo :: B :: C :: B :: C :: bc :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: B :: C :: bc :: nil) ((Oo :: B :: C :: nil) ++ (B :: C :: bc :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoBCbcmtmp;try rewrite HT2 in HOoBCbcmtmp.
	assert(HT := rule_2 (Oo :: B :: C :: nil) (B :: C :: bc :: nil) (B :: C :: nil) 2 2 2 HOoBCbcmtmp HBCmtmp HBCbcMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBCCp requis par la preuve de (?)OoBCCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp ::  de rang :  4 et 4 	 AiB : Oo :: B :: C ::  de rang :  2 et 3 	 A : Oo :: A :: B :: C :: Ap ::   de rang : 4 et 4 *)
assert(HOoBCCpm2 : rk(Oo :: B :: C :: Cp :: nil) >= 2).
{
	assert(HOoABCApeq : rk(Oo :: A :: B :: C :: Ap :: nil) = 4) by (apply LOoABCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApMtmp : rk(Oo :: A :: B :: C :: Ap :: nil) <= 4) by (solve_hyps_max HOoABCApeq HOoABCApM4).
	assert(HOoABCApCpmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 4) by (solve_hyps_min HOoABCApCpeq HOoABCApCpm4).
	assert(HOoBCmtmp : rk(Oo :: B :: C :: nil) >= 2) by (solve_hyps_min HOoBCeq HOoBCm2).
	assert(Hincl : incl (Oo :: B :: C :: nil) (list_inter (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: nil) (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: C :: Ap :: Oo :: B :: C :: Cp :: nil) ((Oo :: A :: B :: C :: Ap :: nil) ++ (Oo :: B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpmtmp;try rewrite HT2 in HOoABCApCpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: C :: Ap :: nil) (Oo :: B :: C :: Cp :: nil) (Oo :: B :: C :: nil) 4 2 4 HOoABCApCpmtmp HOoBCmtmp HOoABCApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoBCCpm3 : rk(Oo :: B :: C :: Cp :: nil) >= 3).
{
	assert(HBCCpmtmp : rk(B :: C :: Cp :: nil) >= 3) by (solve_hyps_min HBCCpeq HBCCpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: nil) 3 3 HBCCpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HOoBCCpM3 : rk(Oo :: B :: C :: Cp :: nil) <= 3).
{
	assert(HOoBCCpbceq : rk(Oo :: B :: C :: Cp :: bc :: nil) = 3) by (apply LOoBCCpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBCCpbcMtmp : rk(Oo :: B :: C :: Cp :: bc :: nil) <= 3) by (solve_hyps_max HOoBCCpbceq HOoBCCpbcM3).
	assert(HOoABCCpDeq : rk(Oo :: A :: B :: C :: Cp :: D :: nil) = 4) by (apply LOoABCCpD with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCCpDMtmp : rk(Oo :: A :: B :: C :: Cp :: D :: nil) <= 4) by (solve_hyps_max HOoABCCpDeq HOoABCCpDM4).
	assert(HOoABCCpbcDeq : rk(Oo :: A :: B :: C :: Cp :: bc :: D :: nil) = 4) by (apply LOoABCCpbcD with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCCpbcDmtmp : rk(Oo :: A :: B :: C :: Cp :: bc :: D :: nil) >= 4) by (solve_hyps_min HOoABCCpbcDeq HOoABCCpbcDm4).
	assert(Hincl : incl (Oo :: B :: C :: Cp :: nil) (list_inter (Oo :: B :: C :: Cp :: bc :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Cp :: bc :: D :: nil) (Oo :: B :: C :: Cp :: bc :: Oo :: A :: B :: C :: Cp :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: C :: Cp :: bc :: Oo :: A :: B :: C :: Cp :: D :: nil) ((Oo :: B :: C :: Cp :: bc :: nil) ++ (Oo :: A :: B :: C :: Cp :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCCpbcDmtmp;try rewrite HT2 in HOoABCCpbcDmtmp.
	assert(HT := rule_3 (Oo :: B :: C :: Cp :: bc :: nil) (Oo :: A :: B :: C :: Cp :: D :: nil) (Oo :: B :: C :: Cp :: nil) 3 4 4 HOoBCCpbcMtmp HOoABCCpDMtmp HOoABCCpbcDmtmp Hincl);apply HT.
}


assert(HOoBCCpM : rk(Oo :: B :: C :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoBCCpm : rk(Oo :: B :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HOoBCCpeq HOoBCCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Cp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCCp requis par la preuve de (?)OoABCCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCCp requis par la preuve de (?)OoABCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCCp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCCp requis par la preuve de (?)OoABCCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Cp ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCCpm2 : rk(Oo :: A :: B :: C :: Cp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApCpmtmp : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 3) by (solve_hyps_min HOoABCApCpeq HOoABCApCpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Cp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Cp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApCpmtmp;try rewrite HT2 in HOoABCApCpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Cp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApCpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoABCCpm3 : rk(Oo :: A :: B :: C :: Cp :: nil) >= 3).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HOoABCApBpCpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpeq HOoABCApBpCpm4).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: Oo :: A :: B :: C :: Cp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (Oo :: A :: B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpmtmp;try rewrite HT2 in HOoABCApBpCpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (Oo :: A :: B :: C :: Cp :: nil) (A :: B :: nil) 4 2 3 HOoABCApBpCpmtmp HABmtmp HABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCCpm4 : rk(Oo :: A :: B :: C :: Cp :: nil) >= 4).
{
	assert(HABCCpmtmp : rk(A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HABCCpeq HABCCpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Cp :: nil) (Oo :: A :: B :: C :: Cp :: nil) 4 4 HABCCpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCCpM : rk(Oo :: A :: B :: C :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCCpm : rk(Oo :: A :: B :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HOoABCCpeq HOoABCCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Cp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCp requis par la preuve de (?)OoABCApCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpm4 : rk(Oo :: A :: B :: C :: Ap :: Cp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApCpM : rk(Oo :: A :: B :: C :: Ap :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApCpm : rk(Oo :: A :: B :: C :: Ap :: Cp ::  nil) >= 1) by (solve_hyps_min HOoABCApCpeq HOoABCApCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCp requis par la preuve de (?)OoABCApBpCp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpCpM : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpCpm : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp ::  nil) >= 1) by (solve_hyps_min HOoABCApBpCpeq HOoABCApBpCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpbc requis par la preuve de (?)OoABCApBpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpbcM : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpbcm : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCApBpbceq HOoABCApBpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Cp :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApCpbc requis par la preuve de (?)OoABCApCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApCpbcM : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApCpbcm : rk(Oo :: A :: B :: C :: Ap :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCApCpbceq HOoABCApCpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpCpbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbc requis par la preuve de (?)OoABCApBpCpbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpCpbcM : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpCpbcm : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCApBpCpbceq HOoABCApBpCpbcm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpCpacbc : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpacbc requis par la preuve de (?)OoABCApBpCpacbc pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpacbcm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpCpacbcM : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpCpacbcm : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: ac :: bc ::  nil) >= 1) by (solve_hyps_min HOoABCApBpCpacbceq HOoABCApBpCpacbcm1).
intuition.
Qed.

(* dans constructLemma(), requis par LABD *)
(* dans la couche 0 *)
Lemma LABD : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: D ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour CD requis par la preuve de (?)ABD pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour ABD requis par la preuve de (?)ABD pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApD requis par la preuve de (?)ABD pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApD requis par la preuve de (?)OoABApD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApD requis par la preuve de (?)OoABApD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApDm2 : rk(Oo :: A :: B :: Ap :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApDm3 : rk(Oo :: A :: B :: Ap :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour ABD requis par la preuve de (?)ABD pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: D ::  de rang :  3 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HABDm2 : rk(A :: B :: D :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApDmtmp : rk(Oo :: A :: B :: Ap :: D :: nil) >= 3) by (solve_hyps_min HOoABApDeq HOoABApDm3).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (A :: B :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: D :: nil) (Oo :: A :: B :: Ap :: A :: B :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: A :: B :: D :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (A :: B :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApDmtmp;try rewrite HT2 in HOoABApDmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (A :: B :: D :: nil) (A :: B :: nil) 3 2 3 HOoABApDmtmp HABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: -4 -2 et 5*)
assert(HABDm3 : rk(A :: B :: D :: nil) >= 3).
{
	assert(HCDMtmp : rk(C :: D :: nil) <= 2) by (solve_hyps_max HCDeq HCDM2).
	assert(HABCDmtmp : rk(A :: B :: C :: D :: nil) >= 4) by (solve_hyps_min HABCDeq HABCDm4).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (A :: B :: D :: nil) (C :: D :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: D :: nil) (A :: B :: D :: C :: D :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: D :: C :: D :: nil) ((A :: B :: D :: nil) ++ (C :: D :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCDmtmp;try rewrite HT2 in HABCDmtmp.
	assert(HT := rule_2 (A :: B :: D :: nil) (C :: D :: nil) (D :: nil) 4 1 2 HABCDmtmp HDmtmp HCDMtmp Hincl);apply HT.
}

assert(HABDM : rk(A :: B :: D ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HABDeq HABDM3).
assert(HABDm : rk(A :: B :: D ::  nil) >= 1) by (solve_hyps_min HABDeq HABDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpCpD : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpD requis par la preuve de (?)OoABCApBpCpD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpDm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpCpDM : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpCpDm : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: D ::  nil) >= 1) by (solve_hyps_min HOoABCApBpCpDeq HOoABCApBpCpDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoABCApBpCpbcD : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpCpbcD requis par la preuve de (?)OoABCApBpCpbcD pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpCpbcDm4 : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCApBpCpbcDM : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCApBpCpbcDm : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: bc :: D ::  nil) >= 1) by (solve_hyps_min HOoABCApBpCpbcDeq HOoABCApBpCpbcDm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(D :: Dp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour DDp requis par la preuve de (?)DDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : A :: B :: D :: Dp ::  de rang :  4 et 4 	 AiB : D ::  de rang :  1 et 1 	 A : A :: B :: D ::   de rang : 3 et 3 *)
assert(HDDpm2 : rk(D :: Dp :: nil) >= 2).
{
	assert(HABDeq : rk(A :: B :: D :: nil) = 3) by (apply LABD with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABDMtmp : rk(A :: B :: D :: nil) <= 3) by (solve_hyps_max HABDeq HABDM3).
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(HDmtmp : rk(D :: nil) >= 1) by (solve_hyps_min HDeq HDm1).
	assert(Hincl : incl (D :: nil) (list_inter (A :: B :: D :: nil) (D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: D :: Dp :: nil) (A :: B :: D :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: D :: D :: Dp :: nil) ((A :: B :: D :: nil) ++ (D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABDDpmtmp;try rewrite HT2 in HABDDpmtmp.
	assert(HT := rule_4 (A :: B :: D :: nil) (D :: Dp :: nil) (D :: nil) 4 1 3 HABDDpmtmp HDmtmp HABDMtmp Hincl); apply HT.
}

assert(HDDpM : rk(D :: Dp ::  nil) <= 2) (* dim : 3 *) by (solve_hyps_max HDDpeq HDDpM2).
assert(HDDpm : rk(D :: Dp ::  nil) >= 1) by (solve_hyps_min HDDpeq HDDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoDDp *)
(* dans constructLemma(), requis par LOoADDp *)
(* dans constructLemma(), requis par LOoAApDDp *)
(* dans constructLemma(), requis par LAApDDp *)
(* dans la couche 0 *)
Lemma LAApDDpad : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: Ap :: D :: Dp :: ad ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour AApDDpad requis par la preuve de (?)AApDDpad pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour AApDDpad requis par la preuve de (?)AApDDpad pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)AApDDpad pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpDDpad requis par la preuve de (?)ABCApBpDDpad pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpDDpad requis par la preuve de (?)ABCApBpDDpad pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpadm3 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpadm4 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpadm2 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpadm3 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: D :: Dp :: ad ::  de rang :  4 et 4 	 AiB : A :: Ap :: Bp ::  de rang :  3 et 3 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACApBpDDpadm4 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpDDpadmtmp : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4) by (solve_hyps_min HABCApBpDDpadeq HABCApBpDDpadm4).
	assert(HAApBpmtmp : rk(A :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HAApBpeq HAApBpm3).
	assert(Hincl : incl (A :: Ap :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpDDpadmtmp;try rewrite HT2 in HABCApBpDDpadmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) (A :: Ap :: Bp :: nil) 4 3 3 HABCApBpDDpadmtmp HAApBpmtmp HABApBpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour AApDDpad requis par la preuve de (?)AApDDpad pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: Ap :: Bp :: D :: Dp :: ad ::  de rang :  4 et 4 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HAApDDpadm2 : rk(A :: Ap :: D :: Dp :: ad :: nil) >= 2).
{
	assert(HCApBpeq : rk(C :: Ap :: Bp :: nil) = 3) by (apply LCApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApBpMtmp : rk(C :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HCApBpeq HCApBpM3).
	assert(HACApBpDDpadmtmp : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4) by (solve_hyps_min HACApBpDDpadeq HACApBpDDpadm4).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: Bp :: nil) (A :: Ap :: D :: Dp :: ad :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) (C :: Ap :: Bp :: A :: Ap :: D :: Dp :: ad :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: A :: Ap :: D :: Dp :: ad :: nil) ((C :: Ap :: Bp :: nil) ++ (A :: Ap :: D :: Dp :: ad :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACApBpDDpadmtmp;try rewrite HT2 in HACApBpDDpadmtmp.
	assert(HT := rule_4 (C :: Ap :: Bp :: nil) (A :: Ap :: D :: Dp :: ad :: nil) (Ap :: nil) 4 1 3 HACApBpDDpadmtmp HApmtmp HCApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAApDDpadm3 : rk(A :: Ap :: D :: Dp :: ad :: nil) >= 3).
{
	assert(HADDpmtmp : rk(A :: D :: Dp :: nil) >= 3) by (solve_hyps_min HADDpeq HADDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: Dp :: nil) (A :: Ap :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: Dp :: nil) (A :: Ap :: D :: Dp :: ad :: nil) 3 3 HADDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HAApDDpadM3 : rk(A :: Ap :: D :: Dp :: ad :: nil) <= 3).
{
	assert(HADadMtmp : rk(A :: D :: ad :: nil) <= 2) by (solve_hyps_max HADadeq HADadM2).
	assert(HApDpadMtmp : rk(Ap :: Dp :: ad :: nil) <= 2) by (solve_hyps_max HApDpadeq HApDpadM2).
	assert(Hadmtmp : rk(ad :: nil) >= 1) by (solve_hyps_min Hadeq Hadm1).
	assert(Hincl : incl (ad :: nil) (list_inter (A :: D :: ad :: nil) (Ap :: Dp :: ad :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: Ap :: D :: Dp :: ad :: nil) (A :: D :: ad :: Ap :: Dp :: ad :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: D :: ad :: Ap :: Dp :: ad :: nil) ((A :: D :: ad :: nil) ++ (Ap :: Dp :: ad :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (A :: D :: ad :: nil) (Ap :: Dp :: ad :: nil) (ad :: nil) 2 2 1 HADadMtmp HApDpadMtmp Hadmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HAApDDpadM : rk(A :: Ap :: D :: Dp :: ad ::  nil) <= 4) by (apply rk_upper_dim).
assert(HAApDDpadm : rk(A :: Ap :: D :: Dp :: ad ::  nil) >= 1) by (solve_hyps_min HAApDDpadeq HAApDDpadm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAApDDp *)
(* dans la couche 0 *)
Lemma LABApDDpbd : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: Ap :: D :: Dp :: bd ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABApDDpbd requis par la preuve de (?)ABApDDpbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApDDpbd requis par la preuve de (?)ABApDDpbd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABApDDpbdm3 : rk(A :: B :: Ap :: D :: Dp :: bd :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABApDDpbdm4 : rk(A :: B :: Ap :: D :: Dp :: bd :: nil) >= 4).
{
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: Dp :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: Dp :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil) 4 4 HABDDpmtmp Hcomp Hincl);apply HT.
}

assert(HABApDDpbdM : rk(A :: B :: Ap :: D :: Dp :: bd ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABApDDpbdm : rk(A :: B :: Ap :: D :: Dp :: bd ::  nil) >= 1) by (solve_hyps_min HABApDDpbdeq HABApDDpbdm1).
intuition.
Qed.

(* dans constructLemma(), requis par LAApDDp *)
(* dans la couche 0 *)
Lemma LABApDDpadbd : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: Ap :: D :: Dp :: ad :: bd ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABApDDpadbd requis par la preuve de (?)ABApDDpadbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABApDDpadbd requis par la preuve de (?)ABApDDpadbd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABApDDpadbdm3 : rk(A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: Ap :: D :: Dp :: ad :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABApDDpadbdm4 : rk(A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) >= 4).
{
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: Dp :: nil) (A :: B :: Ap :: D :: Dp :: ad :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: Dp :: nil) (A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) 4 4 HABDDpmtmp Hcomp Hincl);apply HT.
}

assert(HABApDDpadbdM : rk(A :: B :: Ap :: D :: Dp :: ad :: bd ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABApDDpadbdm : rk(A :: B :: Ap :: D :: Dp :: ad :: bd ::  nil) >= 1) by (solve_hyps_min HABApDDpadbdeq HABApDDpadbdm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LAApDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: Ap :: D :: Dp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour AApDDp requis par la preuve de (?)AApDDp pour la règle 3  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour AApDDp requis par la preuve de (?)AApDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)AApDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour ABCApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpDDp requis par la preuve de (?)ABCApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpDDp requis par la preuve de (?)ABCApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpm3 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpm4 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpm2 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpm3 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: D :: Dp ::  de rang :  4 et 4 	 AiB : A :: Ap :: Bp ::  de rang :  3 et 3 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACApBpDDpm4 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpDDpmtmp : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABCApBpDDpeq HABCApBpDDpm4).
	assert(HAApBpmtmp : rk(A :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HAApBpeq HAApBpm3).
	assert(Hincl : incl (A :: Ap :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Ap :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpDDpmtmp;try rewrite HT2 in HABCApBpDDpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) (A :: Ap :: Bp :: nil) 4 3 3 HABCApBpDDpmtmp HAApBpmtmp HABApBpMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour AApDDp requis par la preuve de (?)AApDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : A :: C :: Ap :: Bp :: D :: Dp ::  de rang :  4 et 4 	 AiB : Ap ::  de rang :  1 et 1 	 A : C :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HAApDDpm2 : rk(A :: Ap :: D :: Dp :: nil) >= 2).
{
	assert(HCApBpeq : rk(C :: Ap :: Bp :: nil) = 3) by (apply LCApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApBpMtmp : rk(C :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HCApBpeq HCApBpM3).
	assert(HACApBpDDpmtmp : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4) by (solve_hyps_min HACApBpDDpeq HACApBpDDpm4).
	assert(HApmtmp : rk(Ap :: nil) >= 1) by (solve_hyps_min HApeq HApm1).
	assert(Hincl : incl (Ap :: nil) (list_inter (C :: Ap :: Bp :: nil) (A :: Ap :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: C :: Ap :: Bp :: D :: Dp :: nil) (C :: Ap :: Bp :: A :: Ap :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (C :: Ap :: Bp :: A :: Ap :: D :: Dp :: nil) ((C :: Ap :: Bp :: nil) ++ (A :: Ap :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HACApBpDDpmtmp;try rewrite HT2 in HACApBpDDpmtmp.
	assert(HT := rule_4 (C :: Ap :: Bp :: nil) (A :: Ap :: D :: Dp :: nil) (Ap :: nil) 4 1 3 HACApBpDDpmtmp HApmtmp HCApBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HAApDDpm3 : rk(A :: Ap :: D :: Dp :: nil) >= 3).
{
	assert(HADDpmtmp : rk(A :: D :: Dp :: nil) >= 3) by (solve_hyps_min HADDpeq HADDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: Dp :: nil) (A :: Ap :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: Dp :: nil) (A :: Ap :: D :: Dp :: nil) 3 3 HADDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HAApDDpM3 : rk(A :: Ap :: D :: Dp :: nil) <= 3).
{
	assert(HAApDDpadeq : rk(A :: Ap :: D :: Dp :: ad :: nil) = 3) by (apply LAApDDpad with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HAApDDpadMtmp : rk(A :: Ap :: D :: Dp :: ad :: nil) <= 3) by (solve_hyps_max HAApDDpadeq HAApDDpadM3).
	assert(HABApDDpbdeq : rk(A :: B :: Ap :: D :: Dp :: bd :: nil) = 4) by (apply LABApDDpbd with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApDDpbdMtmp : rk(A :: B :: Ap :: D :: Dp :: bd :: nil) <= 4) by (solve_hyps_max HABApDDpbdeq HABApDDpbdM4).
	assert(HABApDDpadbdeq : rk(A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) = 4) by (apply LABApDDpadbd with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApDDpadbdmtmp : rk(A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) >= 4) by (solve_hyps_min HABApDDpadbdeq HABApDDpadbdm4).
	assert(Hincl : incl (A :: Ap :: D :: Dp :: nil) (list_inter (A :: Ap :: D :: Dp :: ad :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: Ap :: D :: Dp :: ad :: bd :: nil) (A :: Ap :: D :: Dp :: ad :: A :: B :: Ap :: D :: Dp :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: Ap :: D :: Dp :: ad :: A :: B :: Ap :: D :: Dp :: bd :: nil) ((A :: Ap :: D :: Dp :: ad :: nil) ++ (A :: B :: Ap :: D :: Dp :: bd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABApDDpadbdmtmp;try rewrite HT2 in HABApDDpadbdmtmp.
	assert(HT := rule_3 (A :: Ap :: D :: Dp :: ad :: nil) (A :: B :: Ap :: D :: Dp :: bd :: nil) (A :: Ap :: D :: Dp :: nil) 3 4 4 HAApDDpadMtmp HABApDDpbdMtmp HABApDDpadbdmtmp Hincl);apply HT.
}


assert(HAApDDpM : rk(A :: Ap :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HAApDDpm : rk(A :: Ap :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HAApDDpeq HAApDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoAApDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: Ap :: D :: Dp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoAApDDp requis par la preuve de (?)OoAApDDp pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoAApDDp requis par la preuve de (?)OoAApDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoAApDDp requis par la preuve de (?)OoAApDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoAApDDpm2 : rk(Oo :: A :: Ap :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: Ap :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: Ap :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoAApDDpm3 : rk(Oo :: A :: Ap :: D :: Dp :: nil) >= 3).
{
	assert(HADDpmtmp : rk(A :: D :: Dp :: nil) >= 3) by (solve_hyps_min HADDpeq HADDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: Dp :: nil) (Oo :: A :: Ap :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: Dp :: nil) (Oo :: A :: Ap :: D :: Dp :: nil) 3 3 HADDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et 4*)
assert(HOoAApDDpM3 : rk(Oo :: A :: Ap :: D :: Dp :: nil) <= 3).
{
	assert(HOoAApMtmp : rk(Oo :: A :: Ap :: nil) <= 2) by (solve_hyps_max HOoAApeq HOoAApM2).
	assert(HAApDDpeq : rk(A :: Ap :: D :: Dp :: nil) = 3) by (apply LAApDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HAApDDpMtmp : rk(A :: Ap :: D :: Dp :: nil) <= 3) by (solve_hyps_max HAApDDpeq HAApDDpM3).
	assert(HAApeq : rk(A :: Ap :: nil) = 2) by (apply LAAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HAApmtmp : rk(A :: Ap :: nil) >= 2) by (solve_hyps_min HAApeq HAApm2).
	assert(Hincl : incl (A :: Ap :: nil) (list_inter (Oo :: A :: Ap :: nil) (A :: Ap :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: Ap :: D :: Dp :: nil) (Oo :: A :: Ap :: A :: Ap :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: Ap :: A :: Ap :: D :: Dp :: nil) ((Oo :: A :: Ap :: nil) ++ (A :: Ap :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: A :: Ap :: nil) (A :: Ap :: D :: Dp :: nil) (A :: Ap :: nil) 2 3 2 HOoAApMtmp HAApDDpMtmp HAApmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HOoAApDDpM : rk(Oo :: A :: Ap :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoAApDDpm : rk(Oo :: A :: Ap :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoAApDDpeq HOoAApDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoADDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: D :: Dp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoADDp requis par la preuve de (?)OoADDp pour la règle 6  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoADDp requis par la preuve de (?)OoADDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoADDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCApBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCApBpbcDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcDDpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcDDpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCBpbcDDpm2 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApBpbcDDpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoABCApBpbcDDpeq HOoABCApBpbcDDpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpbcDDpmtmp;try rewrite HT2 in HOoABCApBpbcDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApBpbcDDpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCBpbcDDpm3 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCBpbcDDpm4 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 4).
{
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACApBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACApBpbcDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApBpbcDDpm2 : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApBpbcDDpm3 : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAC requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACac requis par la preuve de (?)OoAC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACac requis par la preuve de (?)OoACac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACac requis par la preuve de (?)OoACac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACacM3 : rk(Oo :: A :: C :: ac :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: ac :: nil) ((Oo :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: C :: ac :: nil) (nil) 1 2 0 HOoMtmp HACacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACacm2 : rk(Oo :: A :: C :: ac :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: ac :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAC requis par la preuve de (?)OoAC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoACm2 : rk(Oo :: A :: C :: nil) >= 2).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACacmtmp : rk(Oo :: A :: C :: ac :: nil) >= 2) by (solve_hyps_min HOoACaceq HOoACacm2).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: A :: C :: ac :: nil) ((Oo :: A :: C :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACacmtmp;try rewrite HT2 in HOoACacmtmp.
	assert(HT := rule_2 (Oo :: A :: C :: nil) (A :: C :: ac :: nil) (A :: C :: nil) 2 2 2 HOoACacmtmp HACmtmp HACacMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: C ::  de rang :  2 et 3 	 A : Oo :: A :: C :: Ap ::   de rang : 3 et 3 *)
assert(HOoACBpbcDDpm2 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoACApeq : rk(Oo :: A :: C :: Ap :: nil) = 3) by (apply LOoACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApBpbcDDpmtmp : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoACApBpbcDDpeq HOoACApBpbcDDpm3).
	assert(HOoACmtmp : rk(Oo :: A :: C :: nil) >= 2) by (solve_hyps_min HOoACeq HOoACm2).
	assert(Hincl : incl (Oo :: A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: C :: Ap :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApBpbcDDpmtmp;try rewrite HT2 in HOoACApBpbcDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: C :: nil) 3 2 3 HOoACApBpbcDDpmtmp HOoACmtmp HOoACApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACBpbcDDpm3 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HACBpeq : rk(A :: C :: Bp :: nil) = 3) by (apply LACBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACBpmtmp : rk(A :: C :: Bp :: nil) >= 3) by (solve_hyps_min HACBpeq HACBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Bp :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Bp :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) 3 3 HACBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et -4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Bp :: bc :: D :: Dp ::  de rang :  4 et 4 	 AiB : C :: bc ::  de rang :  2 et 2 	 A : B :: C :: bc ::   de rang : 2 et 2 *)
assert(HOoACBpbcDDpm4 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 4).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoABCBpbcDDpmtmp : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 4) by (solve_hyps_min HOoABCBpbcDDpeq HOoABCBpbcDDpm4).
	assert(HCbceq : rk(C :: bc :: nil) = 2) by (apply LCbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCbcmtmp : rk(C :: bc :: nil) >= 2) by (solve_hyps_min HCbceq HCbcm2).
	assert(Hincl : incl (C :: bc :: nil) (list_inter (B :: C :: bc :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) (B :: C :: bc :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: bc :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) ((B :: C :: bc :: nil) ++ (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCBpbcDDpmtmp;try rewrite HT2 in HOoABCBpbcDDpmtmp.
	assert(HT := rule_4 (B :: C :: bc :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) (C :: bc :: nil) 4 2 2 HOoABCBpbcDDpmtmp HCbcmtmp HBCbcMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoADDp requis par la preuve de (?)OoADDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 -2 et 4*)
(* ensembles concernés AUB : Oo :: A :: C :: Bp :: bc :: D :: Dp ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : Oo :: C :: Bp :: bc ::   de rang : 3 et 3 *)
assert(HOoADDpm2 : rk(Oo :: A :: D :: Dp :: nil) >= 2).
{
	assert(HOoCBpbceq : rk(Oo :: C :: Bp :: bc :: nil) = 3) by (apply LOoCBpbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoCBpbcMtmp : rk(Oo :: C :: Bp :: bc :: nil) <= 3) by (solve_hyps_max HOoCBpbceq HOoCBpbcM3).
	assert(HOoACBpbcDDpmtmp : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 4) by (solve_hyps_min HOoACBpbcDDpeq HOoACBpbcDDpm4).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Oo :: C :: Bp :: bc :: nil) (Oo :: A :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) (Oo :: C :: Bp :: bc :: Oo :: A :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: C :: Bp :: bc :: Oo :: A :: D :: Dp :: nil) ((Oo :: C :: Bp :: bc :: nil) ++ (Oo :: A :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACBpbcDDpmtmp;try rewrite HT2 in HOoACBpbcDDpmtmp.
	assert(HT := rule_4 (Oo :: C :: Bp :: bc :: nil) (Oo :: A :: D :: Dp :: nil) (Oo :: nil) 4 1 3 HOoACBpbcDDpmtmp HOomtmp HOoCBpbcMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoADDpm3 : rk(Oo :: A :: D :: Dp :: nil) >= 3).
{
	assert(HADDpmtmp : rk(A :: D :: Dp :: nil) >= 3) by (solve_hyps_min HADDpeq HADDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: D :: Dp :: nil) (Oo :: A :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: D :: Dp :: nil) (Oo :: A :: D :: Dp :: nil) 3 3 HADDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoADDpM3 : rk(Oo :: A :: D :: Dp :: nil) <= 3).
{
	assert(HOoAApDDpeq : rk(Oo :: A :: Ap :: D :: Dp :: nil) = 3) by (apply LOoAApDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoAApDDpMtmp : rk(Oo :: A :: Ap :: D :: Dp :: nil) <= 3) by (solve_hyps_max HOoAApDDpeq HOoAApDDpM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: D :: Dp :: nil) (Oo :: A :: Ap :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (Oo :: A :: D :: Dp :: nil) (Oo :: A :: Ap :: D :: Dp :: nil) 3 3 HOoAApDDpMtmp Hcomp Hincl);apply HT.
}

assert(HOoADDpM : rk(Oo :: A :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoADDpm : rk(Oo :: A :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoADDpeq HOoADDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoDDp *)
(* dans constructLemma(), requis par LOoBBpDDp *)
(* dans constructLemma(), requis par LBBpDDp *)
(* dans la couche 0 *)
Lemma LBBpDDpbd : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: Bp :: D :: Dp :: bd ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BBpDDpbd requis par la preuve de (?)BBpDDpbd pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BBpDDpbd requis par la preuve de (?)BBpDDpbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABBpDDpbd requis par la preuve de (?)BBpDDpbd pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABBpDDpbd requis par la preuve de (?)OoABBpDDpbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApBpDDpbd requis par la preuve de (?)OoABBpDDpbd pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApBpDDpbd requis par la preuve de (?)OoABApBpDDpbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBpDDpbd requis par la preuve de (?)OoABApBpDDpbd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpbdm2 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpbdm3 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABBpDDpbd pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABBpDDpbd requis par la preuve de (?)OoABBpDDpbd pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABBpDDpbdm2 : rk(Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpDDpbdmtmp : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) >= 3) by (solve_hyps_min HOoABApBpDDpbdeq HOoABApBpDDpbdm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpDDpbdmtmp;try rewrite HT2 in HOoABApBpDDpbdmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABApBpDDpbdmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABBpDDpbdm3 : rk(Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BBpDDpbd requis par la preuve de (?)BBpDDpbd pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Bp :: D :: Dp :: bd ::  de rang :  3 et 4 	 AiB : B :: Bp ::  de rang :  2 et 2 	 A : Oo :: A :: B :: Bp ::   de rang : 3 et 3 *)
assert(HBBpDDpbdm2 : rk(B :: Bp :: D :: Dp :: bd :: nil) >= 2).
{
	assert(HOoABBpeq : rk(Oo :: A :: B :: Bp :: nil) = 3) by (apply LOoABBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABBpMtmp : rk(Oo :: A :: B :: Bp :: nil) <= 3) by (solve_hyps_max HOoABBpeq HOoABBpM3).
	assert(HOoABBpDDpbdmtmp : rk(Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) >= 3) by (solve_hyps_min HOoABBpDDpbdeq HOoABBpDDpbdm3).
	assert(HBBpeq : rk(B :: Bp :: nil) = 2) by (apply LBBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpmtmp : rk(B :: Bp :: nil) >= 2) by (solve_hyps_min HBBpeq HBBpm2).
	assert(Hincl : incl (B :: Bp :: nil) (list_inter (Oo :: A :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Bp :: D :: Dp :: bd :: nil) (Oo :: A :: B :: Bp :: B :: Bp :: D :: Dp :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Bp :: B :: Bp :: D :: Dp :: bd :: nil) ((Oo :: A :: B :: Bp :: nil) ++ (B :: Bp :: D :: Dp :: bd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABBpDDpbdmtmp;try rewrite HT2 in HOoABBpDDpbdmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: bd :: nil) (B :: Bp :: nil) 3 2 3 HOoABBpDDpbdmtmp HBBpmtmp HOoABBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HBBpDDpbdm3 : rk(B :: Bp :: D :: Dp :: bd :: nil) >= 3).
{
	assert(HBDDpmtmp : rk(B :: D :: Dp :: nil) >= 3) by (solve_hyps_min HBDDpeq HBDDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: D :: Dp :: nil) (B :: Bp :: D :: Dp :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: D :: Dp :: nil) (B :: Bp :: D :: Dp :: bd :: nil) 3 3 HBDDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HBBpDDpbdM3 : rk(B :: Bp :: D :: Dp :: bd :: nil) <= 3).
{
	assert(HBDbdMtmp : rk(B :: D :: bd :: nil) <= 2) by (solve_hyps_max HBDbdeq HBDbdM2).
	assert(HBpDpbdMtmp : rk(Bp :: Dp :: bd :: nil) <= 2) by (solve_hyps_max HBpDpbdeq HBpDpbdM2).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (B :: D :: bd :: nil) (Bp :: Dp :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (B :: Bp :: D :: Dp :: bd :: nil) (B :: D :: bd :: Bp :: Dp :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: D :: bd :: Bp :: Dp :: bd :: nil) ((B :: D :: bd :: nil) ++ (Bp :: Dp :: bd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (B :: D :: bd :: nil) (Bp :: Dp :: bd :: nil) (bd :: nil) 2 2 1 HBDbdMtmp HBpDpbdMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HBBpDDpbdM : rk(B :: Bp :: D :: Dp :: bd ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBBpDDpbdm : rk(B :: Bp :: D :: Dp :: bd ::  nil) >= 1) by (solve_hyps_min HBBpDDpbdeq HBBpDDpbdm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBBpDDp *)
(* dans la couche 0 *)
Lemma LABBpDDpcd : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: Bp :: D :: Dp :: cd ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABBpDDpcd requis par la preuve de (?)ABBpDDpcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABBpDDpcd requis par la preuve de (?)ABBpDDpcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApBpDDpcd requis par la preuve de (?)ABBpDDpcd pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApBpDDpcd requis par la preuve de (?)OoABApBpDDpcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBpDDpcd requis par la preuve de (?)OoABApBpDDpcd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpcdm2 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpcdm3 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABBpDDpcd requis par la preuve de (?)ABBpDDpcd pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd ::  de rang :  3 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HABBpDDpcdm2 : rk(A :: B :: Bp :: D :: Dp :: cd :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpDDpcdmtmp : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) >= 3) by (solve_hyps_min HOoABApBpDDpcdeq HOoABApBpDDpcdm3).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: cd :: nil) (Oo :: A :: B :: Ap :: A :: B :: Bp :: D :: Dp :: cd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: A :: B :: Bp :: D :: Dp :: cd :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (A :: B :: Bp :: D :: Dp :: cd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpDDpcdmtmp;try rewrite HT2 in HOoABApBpDDpcdmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil) (A :: B :: nil) 3 2 3 HOoABApBpDDpcdmtmp HABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABBpDDpcdm3 : rk(A :: B :: Bp :: D :: Dp :: cd :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABBpDDpcdm4 : rk(A :: B :: Bp :: D :: Dp :: cd :: nil) >= 4).
{
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: Dp :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: Dp :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil) 4 4 HABDDpmtmp Hcomp Hincl);apply HT.
}

assert(HABBpDDpcdM : rk(A :: B :: Bp :: D :: Dp :: cd ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABBpDDpcdm : rk(A :: B :: Bp :: D :: Dp :: cd ::  nil) >= 1) by (solve_hyps_min HABBpDDpcdeq HABBpDDpcdm1).
intuition.
Qed.

(* dans constructLemma(), requis par LBBpDDp *)
(* dans la couche 0 *)
Lemma LABBpDDpbdcd : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: Bp :: D :: Dp :: bd :: cd ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABBpDDpbdcd requis par la preuve de (?)ABBpDDpbdcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ABBpDDpbdcd requis par la preuve de (?)ABBpDDpbdcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApBpDDpbdcd requis par la preuve de (?)ABBpDDpbdcd pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApBpDDpbdcd requis par la preuve de (?)OoABApBpDDpbdcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBpDDpbdcd requis par la preuve de (?)OoABApBpDDpbdcd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpbdcdm2 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpbdcdm3 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABBpDDpbdcd requis par la preuve de (?)ABBpDDpbdcd pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd ::  de rang :  3 et 4 	 AiB : A :: B ::  de rang :  2 et 2 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HABBpDDpbdcdm2 : rk(A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpDDpbdcdmtmp : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) >= 3) by (solve_hyps_min HOoABApBpDDpbdcdeq HOoABApBpDDpbdcdm3).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: bd :: cd :: nil) (Oo :: A :: B :: Ap :: A :: B :: Bp :: D :: Dp :: bd :: cd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpDDpbdcdmtmp;try rewrite HT2 in HOoABApBpDDpbdcdmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) (A :: B :: nil) 3 2 3 HOoABApBpDDpbdcdmtmp HABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABBpDDpbdcdm3 : rk(A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABBpDDpbdcdm4 : rk(A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) >= 4).
{
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: Dp :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: Dp :: nil) (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) 4 4 HABDDpmtmp Hcomp Hincl);apply HT.
}

assert(HABBpDDpbdcdM : rk(A :: B :: Bp :: D :: Dp :: bd :: cd ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABBpDDpbdcdm : rk(A :: B :: Bp :: D :: Dp :: bd :: cd ::  nil) >= 1) by (solve_hyps_min HABBpDDpbdcdeq HABBpDDpbdcdm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LBBpDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(B :: Bp :: D :: Dp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour BBpDDp requis par la preuve de (?)BBpDDp pour la règle 3  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour BBpDDp requis par la preuve de (?)BBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)BBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpm2 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpm3 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABBpDDpm2 : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpDDpmtmp : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoABApBpDDpeq HOoABApBpDDpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpDDpmtmp;try rewrite HT2 in HOoABApBpDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABApBpDDpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABBpDDpm3 : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour BBpDDp requis par la preuve de (?)BBpDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 4 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Bp :: D :: Dp ::  de rang :  3 et 4 	 AiB : B :: Bp ::  de rang :  2 et 2 	 A : Oo :: A :: B :: Bp ::   de rang : 3 et 3 *)
assert(HBBpDDpm2 : rk(B :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoABBpeq : rk(Oo :: A :: B :: Bp :: nil) = 3) by (apply LOoABBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABBpMtmp : rk(Oo :: A :: B :: Bp :: nil) <= 3) by (solve_hyps_max HOoABBpeq HOoABBpM3).
	assert(HOoABBpDDpmtmp : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoABBpDDpeq HOoABBpDDpm3).
	assert(HBBpeq : rk(B :: Bp :: nil) = 2) by (apply LBBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpmtmp : rk(B :: Bp :: nil) >= 2) by (solve_hyps_min HBBpeq HBBpm2).
	assert(Hincl : incl (B :: Bp :: nil) (list_inter (Oo :: A :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Bp :: D :: Dp :: nil) (Oo :: A :: B :: Bp :: B :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Bp :: B :: Bp :: D :: Dp :: nil) ((Oo :: A :: B :: Bp :: nil) ++ (B :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABBpDDpmtmp;try rewrite HT2 in HOoABBpDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: nil) (B :: Bp :: nil) 3 2 3 HOoABBpDDpmtmp HBBpmtmp HOoABBpMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HBBpDDpm3 : rk(B :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HBDDpmtmp : rk(B :: D :: Dp :: nil) >= 3) by (solve_hyps_min HBDDpeq HBDDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: D :: Dp :: nil) (B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: D :: Dp :: nil) (B :: Bp :: D :: Dp :: nil) 3 3 HBDDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HBBpDDpM3 : rk(B :: Bp :: D :: Dp :: nil) <= 3).
{
	assert(HBBpDDpbdeq : rk(B :: Bp :: D :: Dp :: bd :: nil) = 3) by (apply LBBpDDpbd with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpDDpbdMtmp : rk(B :: Bp :: D :: Dp :: bd :: nil) <= 3) by (solve_hyps_max HBBpDDpbdeq HBBpDDpbdM3).
	assert(HABBpDDpcdeq : rk(A :: B :: Bp :: D :: Dp :: cd :: nil) = 4) by (apply LABBpDDpcd with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABBpDDpcdMtmp : rk(A :: B :: Bp :: D :: Dp :: cd :: nil) <= 4) by (solve_hyps_max HABBpDDpcdeq HABBpDDpcdM4).
	assert(HABBpDDpbdcdeq : rk(A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) = 4) by (apply LABBpDDpbdcd with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABBpDDpbdcdmtmp : rk(A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) >= 4) by (solve_hyps_min HABBpDDpbdcdeq HABBpDDpbdcdm4).
	assert(Hincl : incl (B :: Bp :: D :: Dp :: nil) (list_inter (B :: Bp :: D :: Dp :: bd :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: Bp :: D :: Dp :: bd :: cd :: nil) (B :: Bp :: D :: Dp :: bd :: A :: B :: Bp :: D :: Dp :: cd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: Bp :: D :: Dp :: bd :: A :: B :: Bp :: D :: Dp :: cd :: nil) ((B :: Bp :: D :: Dp :: bd :: nil) ++ (A :: B :: Bp :: D :: Dp :: cd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABBpDDpbdcdmtmp;try rewrite HT2 in HABBpDDpbdcdmtmp.
	assert(HT := rule_3 (B :: Bp :: D :: Dp :: bd :: nil) (A :: B :: Bp :: D :: Dp :: cd :: nil) (B :: Bp :: D :: Dp :: nil) 3 4 4 HBBpDDpbdMtmp HABBpDDpcdMtmp HABBpDDpbdcdmtmp Hincl);apply HT.
}


assert(HBBpDDpM : rk(B :: Bp :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HBBpDDpm : rk(B :: Bp :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HBBpDDpeq HBBpDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoBBpDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: B :: Bp :: D :: Dp ::  nil) = 3.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoBBpDDp requis par la preuve de (?)OoBBpDDp pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoBBpDDp requis par la preuve de (?)OoBBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoBBpDDp requis par la preuve de (?)OoBBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoBBpDDpm2 : rk(Oo :: B :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoBBpmtmp : rk(Oo :: B :: Bp :: nil) >= 2) by (solve_hyps_min HOoBBpeq HOoBBpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: B :: Bp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: B :: Bp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil) 2 2 HOoBBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoBBpDDpm3 : rk(Oo :: B :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HBDDpmtmp : rk(B :: D :: Dp :: nil) >= 3) by (solve_hyps_min HBDDpeq HBDDpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (B :: D :: Dp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (B :: D :: Dp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil) 3 3 HBDDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 4 et 4*)
assert(HOoBBpDDpM3 : rk(Oo :: B :: Bp :: D :: Dp :: nil) <= 3).
{
	assert(HOoBBpMtmp : rk(Oo :: B :: Bp :: nil) <= 2) by (solve_hyps_max HOoBBpeq HOoBBpM2).
	assert(HBBpDDpeq : rk(B :: Bp :: D :: Dp :: nil) = 3) by (apply LBBpDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpDDpMtmp : rk(B :: Bp :: D :: Dp :: nil) <= 3) by (solve_hyps_max HBBpDDpeq HBBpDDpM3).
	assert(HBBpeq : rk(B :: Bp :: nil) = 2) by (apply LBBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HBBpmtmp : rk(B :: Bp :: nil) >= 2) by (solve_hyps_min HBBpeq HBBpm2).
	assert(Hincl : incl (B :: Bp :: nil) (list_inter (Oo :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: B :: Bp :: D :: Dp :: nil) (Oo :: B :: Bp :: B :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: B :: Bp :: B :: Bp :: D :: Dp :: nil) ((Oo :: B :: Bp :: nil) ++ (B :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: B :: Bp :: nil) (B :: Bp :: D :: Dp :: nil) (B :: Bp :: nil) 2 3 2 HOoBBpMtmp HBBpDDpMtmp HBBpmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HOoBBpDDpM : rk(Oo :: B :: Bp :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoBBpDDpm : rk(Oo :: B :: Bp :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoBBpDDpeq HOoBBpDDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoDDp *)
(* dans la couche 0 *)
Lemma LOoABBpDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: Bp :: D :: Dp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABApBpDDp requis par la preuve de (?)OoABApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpm2 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABApBpDDpm3 : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABBpDDp requis par la preuve de (?)OoABBpDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: Ap :: Bp :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABBpDDpm2 : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABApBpDDpmtmp : rk(Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoABApBpDDpeq HOoABApBpDDpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Ap :: Bp :: D :: Dp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: Bp :: D :: Dp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABApBpDDpmtmp;try rewrite HT2 in HOoABApBpDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABApBpDDpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABBpDDpm3 : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABBpDDpm4 : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 4).
{
	assert(HABDDpmtmp : rk(A :: B :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABDDpeq HABDDpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: D :: Dp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: D :: Dp :: nil) (Oo :: A :: B :: Bp :: D :: Dp :: nil) 4 4 HABDDpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABBpDDpM : rk(Oo :: A :: B :: Bp :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABBpDDpm : rk(Oo :: A :: B :: Bp :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoABBpDDpeq HOoABBpDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: D :: Dp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoDDp requis par la preuve de (?)OoDDp pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoDDp requis par la preuve de (?)OoDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoDDpm2 : rk(Oo :: D :: Dp :: nil) >= 2).
{
	assert(HDDpeq : rk(D :: Dp :: nil) = 2) by (apply LDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HDDpmtmp : rk(D :: Dp :: nil) >= 2) by (solve_hyps_min HDDpeq HDDpm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (D :: Dp :: nil) (Oo :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (D :: Dp :: nil) (Oo :: D :: Dp :: nil) 2 2 HDDpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HOoDDpM2 : rk(Oo :: D :: Dp :: nil) <= 2).
{
	assert(HOoADDpeq : rk(Oo :: A :: D :: Dp :: nil) = 3) by (apply LOoADDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoADDpMtmp : rk(Oo :: A :: D :: Dp :: nil) <= 3) by (solve_hyps_max HOoADDpeq HOoADDpM3).
	assert(HOoBBpDDpeq : rk(Oo :: B :: Bp :: D :: Dp :: nil) = 3) by (apply LOoBBpDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBBpDDpMtmp : rk(Oo :: B :: Bp :: D :: Dp :: nil) <= 3) by (solve_hyps_max HOoBBpDDpeq HOoBBpDDpM3).
	assert(HOoABBpDDpeq : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) = 4) by (apply LOoABBpDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABBpDDpmtmp : rk(Oo :: A :: B :: Bp :: D :: Dp :: nil) >= 4) by (solve_hyps_min HOoABBpDDpeq HOoABBpDDpm4).
	assert(Hincl : incl (Oo :: D :: Dp :: nil) (list_inter (Oo :: A :: D :: Dp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: Bp :: D :: Dp :: nil) (Oo :: A :: D :: Dp :: Oo :: B :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: D :: Dp :: Oo :: B :: Bp :: D :: Dp :: nil) ((Oo :: A :: D :: Dp :: nil) ++ (Oo :: B :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABBpDDpmtmp;try rewrite HT2 in HOoABBpDDpmtmp.
	assert(HT := rule_3 (Oo :: A :: D :: Dp :: nil) (Oo :: B :: Bp :: D :: Dp :: nil) (Oo :: D :: Dp :: nil) 3 3 4 HOoADDpMtmp HOoBBpDDpMtmp HOoABBpDDpmtmp Hincl);apply HT.
}


assert(HOoDDpM : rk(Oo :: D :: Dp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HOoDDpeq HOoDDpM3).
assert(HOoDDpm : rk(Oo :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoDDpeq HOoDDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACApBpDDp *)
(* dans la couche 0 *)
Lemma LABCApBpDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: C :: Ap :: Bp :: D :: Dp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpDDp requis par la preuve de (?)ABCApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpDDp requis par la preuve de (?)ABCApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpm3 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpm4 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HABCApBpDDpM : rk(A :: B :: C :: Ap :: Bp :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpDDpm : rk(A :: B :: C :: Ap :: Bp :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HABCApBpDDpeq HABCApBpDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApBpDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Ap :: Bp :: D :: Dp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApBpDDp requis par la preuve de (?)ACApBpDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpm2 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpm3 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: D :: Dp ::  de rang :  4 et 4 	 AiB : A :: Ap :: Bp ::  de rang :  3 et 3 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACApBpDDpm4 : rk(A :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpDDpeq : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) = 4) by (apply LABCApBpDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABCApBpDDpmtmp : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) >= 4) by (solve_hyps_min HABCApBpDDpeq HABCApBpDDpm4).
	assert(HAApBpmtmp : rk(A :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HAApBpeq HAApBpm3).
	assert(Hincl : incl (A :: Ap :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: D :: Dp :: nil) (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Ap :: Bp :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpDDpmtmp;try rewrite HT2 in HABCApBpDDpmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: nil) (A :: Ap :: Bp :: nil) 4 3 3 HABCApBpDDpmtmp HAApBpmtmp HABApBpMtmp Hincl); apply HT.
}

assert(HACApBpDDpM : rk(A :: C :: Ap :: Bp :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApBpDDpm : rk(A :: C :: Ap :: Bp :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HACApBpDDpeq HACApBpDDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LOoACBpbcDDp *)
(* dans la couche 0 *)
Lemma LOoABCBpbcDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCApBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCApBpbcDDp requis par la preuve de (?)OoABCApBpbcDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcDDpm2 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCApBpbcDDpm3 : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAB requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoABab requis par la preuve de (?)OoAB pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoABab requis par la preuve de (?)OoABab pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABab requis par la preuve de (?)OoABab pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoABabM3 : rk(Oo :: A :: B :: ab :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: ab :: nil) ((Oo :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: B :: ab :: nil) (nil) 1 2 0 HOoMtmp HABabMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoABabm2 : rk(Oo :: A :: B :: ab :: nil) >= 2).
{
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: B :: nil) (Oo :: A :: B :: ab :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: nil) (Oo :: A :: B :: ab :: nil) 2 2 HABmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAB requis par la preuve de (?)OoAB pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoABm2 : rk(Oo :: A :: B :: nil) >= 2).
{
	assert(HABabMtmp : rk(A :: B :: ab :: nil) <= 2) by (solve_hyps_max HABabeq HABabM2).
	assert(HOoABabmtmp : rk(Oo :: A :: B :: ab :: nil) >= 2) by (solve_hyps_min HOoABabeq HOoABabm2).
	assert(HABeq : rk(A :: B :: nil) = 2) by (apply LAB with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABmtmp : rk(A :: B :: nil) >= 2) by (solve_hyps_min HABeq HABm2).
	assert(Hincl : incl (A :: B :: nil) (list_inter (Oo :: A :: B :: nil) (A :: B :: ab :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: ab :: nil) (Oo :: A :: B :: A :: B :: ab :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: A :: B :: ab :: nil) ((Oo :: A :: B :: nil) ++ (A :: B :: ab :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABabmtmp;try rewrite HT2 in HOoABabmtmp.
	assert(HT := rule_2 (Oo :: A :: B :: nil) (A :: B :: ab :: nil) (A :: B :: nil) 2 2 2 HOoABabmtmp HABmtmp HABabMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoABCBpbcDDp requis par la preuve de (?)OoABCBpbcDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: B ::  de rang :  2 et 3 	 A : Oo :: A :: B :: Ap ::   de rang : 3 et 3 *)
assert(HOoABCBpbcDDpm2 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoABApeq : rk(Oo :: A :: B :: Ap :: nil) = 3) by (apply LOoABAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApMtmp : rk(Oo :: A :: B :: Ap :: nil) <= 3) by (solve_hyps_max HOoABApeq HOoABApM3).
	assert(HOoABCApBpbcDDpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoABCApBpbcDDpeq HOoABCApBpbcDDpm3).
	assert(HOoABmtmp : rk(Oo :: A :: B :: nil) >= 2) by (solve_hyps_min HOoABeq HOoABm2).
	assert(Hincl : incl (Oo :: A :: B :: nil) (list_inter (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) ((Oo :: A :: B :: Ap :: nil) ++ (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpbcDDpmtmp;try rewrite HT2 in HOoABCApBpbcDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: B :: nil) 3 2 3 HOoABCApBpbcDDpmtmp HOoABmtmp HOoABApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCBpbcDDpm3 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HABBpmtmp : rk(A :: B :: Bp :: nil) >= 3) by (solve_hyps_min HABBpeq HABBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) 3 3 HABBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoABCBpbcDDpm4 : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 4).
{
	assert(HABCBpmtmp : rk(A :: B :: C :: Bp :: nil) >= 4) by (solve_hyps_min HABCBpeq HABCBpm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Bp :: nil) (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) 4 4 HABCBpmtmp Hcomp Hincl);apply HT.
}

assert(HOoABCBpbcDDpM : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoABCBpbcDDpm : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoABCBpbcDDpeq HOoABCBpbcDDpm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoACBpbcDDp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: A :: C :: Bp :: bc :: D :: Dp ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACApBpbcDDp pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACApBpbcDDp requis par la preuve de (?)OoACApBpbcDDp pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HOoACApBpbcDDpm2 : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoAApmtmp : rk(Oo :: A :: Ap :: nil) >= 2) by (solve_hyps_min HOoAApeq HOoAApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (Oo :: A :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 2 2 HOoAApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACApBpbcDDpm3 : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoAC requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoACac requis par la preuve de (?)OoAC pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoACac requis par la preuve de (?)OoACac pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACac requis par la preuve de (?)OoACac pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HOoACacM3 : rk(Oo :: A :: C :: ac :: nil) <= 3).
{
	assert(HOoMtmp : rk(Oo :: nil) <= 1) by (solve_hyps_max HOoeq HOoM1).
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (Oo :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: ac :: nil) ((Oo :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (Oo :: nil) (A :: C :: ac :: nil) (nil) 1 2 0 HOoMtmp HACacMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACacm2 : rk(Oo :: A :: C :: ac :: nil) >= 2).
{
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (A :: C :: nil) (Oo :: A :: C :: ac :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: nil) (Oo :: A :: C :: ac :: nil) 2 2 HACmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoAC requis par la preuve de (?)OoAC pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 5 4 et -4*)
assert(HOoACm2 : rk(Oo :: A :: C :: nil) >= 2).
{
	assert(HACacMtmp : rk(A :: C :: ac :: nil) <= 2) by (solve_hyps_max HACaceq HACacM2).
	assert(HOoACacmtmp : rk(Oo :: A :: C :: ac :: nil) >= 2) by (solve_hyps_min HOoACaceq HOoACacm2).
	assert(HACeq : rk(A :: C :: nil) = 2) by (apply LAC with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACmtmp : rk(A :: C :: nil) >= 2) by (solve_hyps_min HACeq HACm2).
	assert(Hincl : incl (A :: C :: nil) (list_inter (Oo :: A :: C :: nil) (A :: C :: ac :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: ac :: nil) (Oo :: A :: C :: A :: C :: ac :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: A :: C :: ac :: nil) ((Oo :: A :: C :: nil) ++ (A :: C :: ac :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACacmtmp;try rewrite HT2 in HOoACacmtmp.
	assert(HT := rule_2 (Oo :: A :: C :: nil) (A :: C :: ac :: nil) (A :: C :: nil) 2 2 2 HOoACacmtmp HACmtmp HACacMtmp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour OoACBpbcDDp requis par la preuve de (?)OoACBpbcDDp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 4) *)
(* marque des antécédents AUB AiB A: 5 5 et 4*)
(* ensembles concernés AUB : Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp ::  de rang :  3 et 4 	 AiB : Oo :: A :: C ::  de rang :  2 et 3 	 A : Oo :: A :: C :: Ap ::   de rang : 3 et 3 *)
assert(HOoACBpbcDDpm2 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 2).
{
	assert(HOoACApeq : rk(Oo :: A :: C :: Ap :: nil) = 3) by (apply LOoACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACApMtmp : rk(Oo :: A :: C :: Ap :: nil) <= 3) by (solve_hyps_max HOoACApeq HOoACApM3).
	assert(HOoACApBpbcDDpmtmp : rk(Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) >= 3) by (solve_hyps_min HOoACApBpbcDDpeq HOoACApBpbcDDpm3).
	assert(HOoACmtmp : rk(Oo :: A :: C :: nil) >= 2) by (solve_hyps_min HOoACeq HOoACm2).
	assert(Hincl : incl (Oo :: A :: C :: nil) (list_inter (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: C :: Ap :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: C :: Ap :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Ap :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) ((Oo :: A :: C :: Ap :: nil) ++ (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoACApBpbcDDpmtmp;try rewrite HT2 in HOoACApBpbcDDpmtmp.
	assert(HT := rule_4 (Oo :: A :: C :: Ap :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) (Oo :: A :: C :: nil) 3 2 3 HOoACApBpbcDDpmtmp HOoACmtmp HOoACApMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HOoACBpbcDDpm3 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 3).
{
	assert(HACBpeq : rk(A :: C :: Bp :: nil) = 3) by (apply LACBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACBpmtmp : rk(A :: C :: Bp :: nil) >= 3) by (solve_hyps_min HACBpeq HACBpm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Bp :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Bp :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) 3 3 HACBpmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Bp :: bc :: D :: Dp ::  de rang :  4 et 4 	 AiB : C :: bc ::  de rang :  2 et 2 	 A : B :: C :: bc ::   de rang : 2 et 2 *)
assert(HOoACBpbcDDpm4 : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) >= 4).
{
	assert(HBCbcMtmp : rk(B :: C :: bc :: nil) <= 2) by (solve_hyps_max HBCbceq HBCbcM2).
	assert(HOoABCBpbcDDpeq : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) = 4) by (apply LOoABCBpbcDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCBpbcDDpmtmp : rk(Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) >= 4) by (solve_hyps_min HOoABCBpbcDDpeq HOoABCBpbcDDpm4).
	assert(HCbceq : rk(C :: bc :: nil) = 2) by (apply LCbc with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCbcmtmp : rk(C :: bc :: nil) >= 2) by (solve_hyps_min HCbceq HCbcm2).
	assert(Hincl : incl (C :: bc :: nil) (list_inter (B :: C :: bc :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Bp :: bc :: D :: Dp :: nil) (B :: C :: bc :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (B :: C :: bc :: Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) ((B :: C :: bc :: nil) ++ (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCBpbcDDpmtmp;try rewrite HT2 in HOoABCBpbcDDpmtmp.
	assert(HT := rule_4 (B :: C :: bc :: nil) (Oo :: A :: C :: Bp :: bc :: D :: Dp :: nil) (C :: bc :: nil) 4 2 2 HOoABCBpbcDDpmtmp HCbcmtmp HBCbcMtmp Hincl); apply HT.
}

assert(HOoACBpbcDDpM : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp ::  nil) <= 4) by (apply rk_upper_dim).
assert(HOoACBpbcDDpm : rk(Oo :: A :: C :: Bp :: bc :: D :: Dp ::  nil) >= 1) by (solve_hyps_min HOoACBpbcDDpeq HOoACBpbcDDpm1).
intuition.
Qed.

(* dans constructLemma(), requis par LACApBpDDpad *)
(* dans la couche 0 *)
Lemma LABCApBpDDpad : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ABCApBpDDpad requis par la preuve de (?)ABCApBpDDpad pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ABCApBpDDpad requis par la preuve de (?)ABCApBpDDpad pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpadm3 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 3).
{
	assert(HABApmtmp : rk(A :: B :: Ap :: nil) >= 3) by (solve_hyps_min HABApeq HABApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 3 3 HABApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(HABCApBpDDpadm4 : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4).
{
	assert(HABCApmtmp : rk(A :: B :: C :: Ap :: nil) >= 4) by (solve_hyps_min HABCApeq HABCApm4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: B :: C :: Ap :: nil) (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 4 4 HABCApmtmp Hcomp Hincl);apply HT.
}

assert(HABCApBpDDpadM : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) <= 4) by (apply rk_upper_dim).
assert(HABCApBpDDpadm : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) >= 1) by (solve_hyps_min HABCApBpDDpadeq HABCApBpDDpadm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LACApBpDDpad : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(A :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) = 4.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour ACApBpDDpad requis par la preuve de (?)ACApBpDDpad pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpadm2 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 2).
{
	assert(HCApeq : rk(C :: Ap :: nil) = 2) by (apply LCAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HCApmtmp : rk(C :: Ap :: nil) >= 2) by (solve_hyps_min HCApeq HCApm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 2 2 HCApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HACApBpDDpadm3 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 3).
{
	assert(HACApeq : rk(A :: C :: Ap :: nil) = 3) by (apply LACAp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HACApmtmp : rk(A :: C :: Ap :: nil) >= 3) by (solve_hyps_min HACApeq HACApm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (A :: C :: Ap :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) 3 3 HACApmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : A :: B :: C :: Ap :: Bp :: D :: Dp :: ad ::  de rang :  4 et 4 	 AiB : A :: Ap :: Bp ::  de rang :  3 et 3 	 A : A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HACApBpDDpadm4 : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4).
{
	assert(HABApBpeq : rk(A :: B :: Ap :: Bp :: nil) = 3) by (apply LABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABApBpMtmp : rk(A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HABApBpeq HABApBpM3).
	assert(HABCApBpDDpadeq : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) = 4) by (apply LABCApBpDDpad with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HABCApBpDDpadmtmp : rk(A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) >= 4) by (solve_hyps_min HABCApBpDDpadeq HABCApBpDDpadm4).
	assert(HAApBpmtmp : rk(A :: Ap :: Bp :: nil) >= 3) by (solve_hyps_min HAApBpeq HAApBpm3).
	assert(Hincl : incl (A :: Ap :: Bp :: nil) (list_inter (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (A :: B :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (A :: B :: Ap :: Bp :: A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) ((A :: B :: Ap :: Bp :: nil) ++ (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HABCApBpDDpadmtmp;try rewrite HT2 in HABCApBpDDpadmtmp.
	assert(HT := rule_4 (A :: B :: Ap :: Bp :: nil) (A :: C :: Ap :: Bp :: D :: Dp :: ad :: nil) (A :: Ap :: Bp :: nil) 4 3 3 HABCApBpDDpadmtmp HAApBpmtmp HABApBpMtmp Hincl); apply HT.
}

assert(HACApBpDDpadM : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) <= 4) by (apply rk_upper_dim).
assert(HACApBpDDpadm : rk(A :: C :: Ap :: Bp :: D :: Dp :: ad ::  nil) >= 1) by (solve_hyps_min HACApBpDDpadeq HACApBpDDpadm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LOoCCp : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->
rk(Oo :: C :: Cp ::  nil) = 2.
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour OoCCp requis par la preuve de (?)OoCCp pour la règle 3  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour OoCCp requis par la preuve de (?)OoCCp pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 4 -2 et 4*)
(* ensembles concernés AUB : Oo :: A :: B :: C :: Ap :: Bp :: Cp ::  de rang :  4 et 4 	 AiB : Oo ::  de rang :  1 et 1 	 A : Oo :: A :: B :: Ap :: Bp ::   de rang : 3 et 3 *)
assert(HOoCCpm2 : rk(Oo :: C :: Cp :: nil) >= 2).
{
	assert(HOoABApBpeq : rk(Oo :: A :: B :: Ap :: Bp :: nil) = 3) by (apply LOoABApBp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABApBpMtmp : rk(Oo :: A :: B :: Ap :: Bp :: nil) <= 3) by (solve_hyps_max HOoABApBpeq HOoABApBpM3).
	assert(HOoABCApBpCpeq : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) = 4) by (apply LOoABCApBpCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCApBpCpmtmp : rk(Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) >= 4) by (solve_hyps_min HOoABCApBpCpeq HOoABCApBpCpm4).
	assert(HOomtmp : rk(Oo :: nil) >= 1) by (solve_hyps_min HOoeq HOom1).
	assert(Hincl : incl (Oo :: nil) (list_inter (Oo :: A :: B :: Ap :: Bp :: nil) (Oo :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Ap :: Bp :: Cp :: nil) (Oo :: A :: B :: Ap :: Bp :: Oo :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: B :: Ap :: Bp :: Oo :: C :: Cp :: nil) ((Oo :: A :: B :: Ap :: Bp :: nil) ++ (Oo :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCApBpCpmtmp;try rewrite HT2 in HOoABCApBpCpmtmp.
	assert(HT := rule_4 (Oo :: A :: B :: Ap :: Bp :: nil) (Oo :: C :: Cp :: nil) (Oo :: nil) 4 1 3 HOoABCApBpCpmtmp HOomtmp HOoABApBpMtmp Hincl); apply HT.
}

(* Application de la règle 3 code (6 dans la thèse) *)
(* marque des antécédents A B AUB: 4 4 et 4*)
assert(HOoCCpM2 : rk(Oo :: C :: Cp :: nil) <= 2).
{
	assert(HOoACCpeq : rk(Oo :: A :: C :: Cp :: nil) = 3) by (apply LOoACCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoACCpMtmp : rk(Oo :: A :: C :: Cp :: nil) <= 3) by (solve_hyps_max HOoACCpeq HOoACCpM3).
	assert(HOoBCCpeq : rk(Oo :: B :: C :: Cp :: nil) = 3) by (apply LOoBCCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoBCCpMtmp : rk(Oo :: B :: C :: Cp :: nil) <= 3) by (solve_hyps_max HOoBCCpeq HOoBCCpM3).
	assert(HOoABCCpeq : rk(Oo :: A :: B :: C :: Cp :: nil) = 4) by (apply LOoABCCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption).
	assert(HOoABCCpmtmp : rk(Oo :: A :: B :: C :: Cp :: nil) >= 4) by (solve_hyps_min HOoABCCpeq HOoABCCpm4).
	assert(Hincl : incl (Oo :: C :: Cp :: nil) (list_inter (Oo :: A :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (Oo :: A :: B :: C :: Cp :: nil) (Oo :: A :: C :: Cp :: Oo :: B :: C :: Cp :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (Oo :: A :: C :: Cp :: Oo :: B :: C :: Cp :: nil) ((Oo :: A :: C :: Cp :: nil) ++ (Oo :: B :: C :: Cp :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HOoABCCpmtmp;try rewrite HT2 in HOoABCCpmtmp.
	assert(HT := rule_3 (Oo :: A :: C :: Cp :: nil) (Oo :: B :: C :: Cp :: nil) (Oo :: C :: Cp :: nil) 3 3 4 HOoACCpMtmp HOoBCCpMtmp HOoABCCpmtmp Hincl);apply HT.
}


assert(HOoCCpM : rk(Oo :: C :: Cp ::  nil) <= 3) (* dim : 3 *) by (solve_hyps_max HOoCCpeq HOoCCpM3).
assert(HOoCCpm : rk(Oo :: C :: Cp ::  nil) >= 1) by (solve_hyps_min HOoCCpeq HOoCCpm1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd ,
rk(Oo :: A :: Ap ::  nil) = 2 -> rk(A :: B :: Ap ::  nil) = 3 -> rk(A :: B :: C :: Ap ::  nil) = 4 ->
rk(Oo :: B :: Bp ::  nil) = 2 -> rk(A :: B :: Bp ::  nil) = 3 -> rk(A :: B :: C :: Bp ::  nil) = 4 ->
rk(A :: Ap :: Bp ::  nil) = 3 -> rk(B :: Ap :: Bp ::  nil) = 3 -> rk(A :: C :: Cp ::  nil) = 3 ->
rk(B :: C :: Cp ::  nil) = 3 -> rk(A :: B :: C :: Cp ::  nil) = 4 -> rk(C :: Ap :: Cp ::  nil) = 3 ->
rk(C :: Bp :: Cp ::  nil) = 3 -> rk(A :: B :: ab ::  nil) = 2 -> rk(Ap :: Bp :: ab ::  nil) = 2 ->
rk(A :: C :: ac ::  nil) = 2 -> rk(Ap :: Cp :: ac ::  nil) = 2 -> rk(B :: C :: bc ::  nil) = 2 ->
rk(Bp :: Cp :: bc ::  nil) = 2 -> rk(ab :: ac :: bc ::  nil) = 2 -> rk(A :: B :: C :: D ::  nil) = 4 ->
rk(Ap :: Bp :: Dp ::  nil) = 3 -> rk(Ap :: Cp :: Dp ::  nil) = 3 -> rk(Bp :: Cp :: Dp ::  nil) = 3 ->
rk(Ap :: Bp :: Cp :: Dp ::  nil) = 4 -> rk(A :: D :: Dp ::  nil) = 3 -> rk(B :: D :: Dp ::  nil) = 3 ->
rk(A :: B :: D :: Dp ::  nil) = 4 -> rk(A :: C :: D :: Dp ::  nil) = 4 -> rk(B :: C :: D :: Dp ::  nil) = 4 ->
rk(Ap :: D :: Dp ::  nil) = 3 -> rk(Bp :: D :: Dp ::  nil) = 3 -> rk(A :: D :: ad ::  nil) = 2 ->
rk(Ap :: Dp :: ad ::  nil) = 2 -> rk(B :: D :: bd ::  nil) = 2 -> rk(Bp :: Dp :: bd ::  nil) = 2 ->
rk(ab :: ad :: bd ::  nil) = 2 -> rk(C :: D :: cd ::  nil) = 2 -> rk(Cp :: Dp :: cd ::  nil) = 2 ->
rk(ac :: ad :: cd ::  nil) = 2 -> rk(bc :: bd :: cd ::  nil) = 2 -> rk(ab :: ac :: bc :: ad :: bd :: cd ::  nil) = 3 ->

	 rk(Oo :: C :: Cp ::  nil) = 2  /\ 
	 rk(Oo :: D :: Dp ::  nil) = 2  .
Proof.

intros Oo A B C Ap Bp Cp ab ac bc D Dp ad bd cd 
HOoAApeq HABApeq HABCApeq HOoBBpeq HABBpeq HABCBpeq HAApBpeq HBApBpeq HACCpeq HBCCpeq
HABCCpeq HCApCpeq HCBpCpeq HABabeq HApBpabeq HACaceq HApCpaceq HBCbceq HBpCpbceq Habacbceq
HABCDeq HApBpDpeq HApCpDpeq HBpCpDpeq HApBpCpDpeq HADDpeq HBDDpeq HABDDpeq HACDDpeq HBCDDpeq
HApDDpeq HBpDDpeq HADadeq HApDpadeq HBDbdeq HBpDpbdeq Habadbdeq HCDcdeq HCpDpcdeq Hacadcdeq
Hbcbdcdeq Habacbcadbdcdeq .
repeat split.

	apply LOoCCp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption.

	apply LOoDDp with (Oo := Oo) (A := A) (B := B) (C := C) (Ap := Ap) (Bp := Bp) (Cp := Cp) (ab := ab) (ac := ac) (bc := bc) (D := D) (Dp := Dp) (ad := ad) (bd := bd) (cd := cd) ; assumption.
Qed .
