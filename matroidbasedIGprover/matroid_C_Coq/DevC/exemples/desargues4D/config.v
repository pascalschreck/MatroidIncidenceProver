Load "preamble4D.v".


(* dans constructLemma(), requis par Labbd *)
(* dans la couche 0 *)
Lemma Labbcbdcd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: bc :: bd :: cd ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbcbdcd requis par la preuve de (?)abbcbdcd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdcd requis par la preuve de (?)abbcbdcd pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbcbdcdM3 : rk(ab :: bc :: bd :: cd :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bc :: bd :: cd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: cd :: nil) (ab :: bc :: bd :: cd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: bd :: cd :: nil) ((ab :: nil) ++ (bc :: bd :: cd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bc :: bd :: cd :: nil) (nil) 1 2 0 HabMtmp HbcbdcdMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdcdm3 : rk(ab :: bc :: bd :: cd :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: cd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: cd :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

assert(HabbcbdcdM : rk(ab :: bc :: bd :: cd ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Habbcbdcdeq HabbcbdcdM4).
assert(Habbcbdcdm : rk(ab :: bc :: bd :: cd ::  nil) >= 1) by (solve_hyps_min Habbcbdcdeq Habbcbdcdm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labbd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: bd ::  nil) = 2.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbd requis par la preuve de (?)abbd pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(Habbdm2 : rk(ab :: bd :: nil) >= 2).
{
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(Habbcbdcdeq : rk(ab :: bc :: bd :: cd :: nil) = 3) by (apply Labbcbdcd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habbcbdcdmtmp : rk(ab :: bc :: bd :: cd :: nil) >= 3) by (solve_hyps_min Habbcbdcdeq Habbcbdcdm3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: bd :: nil) (bc :: bd :: cd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: cd :: nil) (ab :: bd :: bc :: bd :: cd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: bc :: bd :: cd :: nil) ((ab :: bd :: nil) ++ (bc :: bd :: cd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdcdmtmp;try rewrite HT2 in Habbcbdcdmtmp.
	assert(HT := rule_2 (ab :: bd :: nil) (bc :: bd :: cd :: nil) (bd :: nil) 3 1 2 Habbcbdcdmtmp Hbdmtmp HbcbdcdMtmp Hincl);apply HT.
}

assert(HabbdM : rk(ab :: bd ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max Habbdeq HabbdM2).
assert(Habbdm : rk(ab :: bd ::  nil) >= 1) by (solve_hyps_min Habbdeq Habbdm1).
intuition.
Qed.

(* dans constructLemma(), requis par Lbcbd *)
(* dans la couche 0 *)
Lemma Labadbcbd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ad :: bc :: bd ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abadbcbd requis par la preuve de (?)abadbcbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abadbcbd requis par la preuve de (?)abadbcbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadbcbd requis par la preuve de (?)abadbcbd pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabadbcbdM3 : rk(ab :: ad :: bc :: bd :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: ad :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bc :: bd :: nil) (bc :: ab :: ad :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: ad :: bd :: nil) ((bc :: nil) ++ (ab :: ad :: bd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: ad :: bd :: nil) (nil) 1 2 0 HbcMtmp HabadbdMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbcbdm2 : rk(ab :: ad :: bc :: bd :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: bc :: bd :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbcbdm3 : rk(ab :: ad :: bc :: bd :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

assert(HabadbcbdM : rk(ab :: ad :: bc :: bd ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Habadbcbdeq HabadbcbdM4).
assert(Habadbcbdm : rk(ab :: ad :: bc :: bd ::  nil) >= 1) by (solve_hyps_min Habadbcbdeq Habadbcbdm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbcbd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: bd ::  nil) = 2.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour bcbd requis par la preuve de (?)bcbd pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: 4 -2 et -4*)
(* ensembles concernés AUB : ab :: ad :: bc :: bd ::  de rang :  3 et 3 	 AiB : bd ::  de rang :  1 et 1 	 A : ab :: ad :: bd ::   de rang : 2 et 2 *)
assert(Hbcbdm2 : rk(bc :: bd :: nil) >= 2).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(Habadbcbdeq : rk(ab :: ad :: bc :: bd :: nil) = 3) by (apply Labadbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habadbcbdmtmp : rk(ab :: ad :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habadbcbdeq Habadbcbdm3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: ad :: bd :: nil) (bc :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bc :: bd :: nil) (ab :: ad :: bd :: bc :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: bc :: bd :: nil) ((ab :: ad :: bd :: nil) ++ (bc :: bd :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habadbcbdmtmp;try rewrite HT2 in Habadbcbdmtmp.
	assert(HT := rule_4 (ab :: ad :: bd :: nil) (bc :: bd :: nil) (bd :: nil) 3 1 2 Habadbcbdmtmp Hbdmtmp HabadbdMtmp Hincl); apply HT.
}

assert(HbcbdM : rk(bc :: bd ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max Hbcbdeq HbcbdM2).
assert(Hbcbdm : rk(bc :: bd ::  nil) >= 1) by (solve_hyps_min Hbcbdeq Hbcbdm1).
intuition.
Qed.

(* dans constructLemma(), requis par Labacbcbd *)
(* dans la couche 0 *)
Lemma Labacadbcbd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: ad :: bc :: bd ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abacadbcbd requis par la preuve de (?)abacadbcbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abacadbcbd requis par la preuve de (?)abacadbcbd pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abacadbcbd requis par la preuve de (?)abacadbcbd pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abacadbd requis par la preuve de (?)abacadbcbd pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abacadbd requis par la preuve de (?)abacadbd pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabacadbdM3 : rk(ab :: ac :: ad :: bd :: nil) <= 3).
{
	assert(HacMtmp : rk(ac :: nil) <= 1) by (solve_hyps_max Haceq HacM1).
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: nil) (ab :: ad :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bd :: nil) (ac :: ab :: ad :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ab :: ad :: bd :: nil) ((ac :: nil) ++ (ab :: ad :: bd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: nil) (ab :: ad :: bd :: nil) (nil) 1 2 0 HacMtmp HabadbdMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadbcbd requis par la preuve de (?)abacadbcbd pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabacadbcbdM4 : rk(ab :: ac :: ad :: bc :: bd :: nil) <= 4).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabacadbdMtmp : rk(ab :: ac :: ad :: bd :: nil) <= 3) by (solve_hyps_max Habacadbdeq HabacadbdM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: ac :: ad :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bc :: bd :: nil) (bc :: ab :: ac :: ad :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: ac :: ad :: bd :: nil) ((bc :: nil) ++ (ab :: ac :: ad :: bd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: ac :: ad :: bd :: nil) (nil) 1 3 0 HbcMtmp HabacadbdMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HabacadbcbdM3 : rk(ab :: ac :: ad :: bc :: bd :: nil) <= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(Hadmtmp : rk(ad :: nil) >= 1) by (solve_hyps_min Hadeq Hadm1).
	assert(Hincl : incl (ad :: nil) (list_inter (ac :: ad :: bc :: nil) (ab :: ad :: bd :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bc :: bd :: nil) (ac :: ad :: bc :: ab :: ad :: bd :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: ab :: ad :: bd :: nil) ((ac :: ad :: bc :: nil) ++ (ab :: ad :: bd :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: ad :: bc :: nil) (ab :: ad :: bd :: nil) (ad :: nil) 2 2 1 HacadbcMtmp HabadbdMtmp Hadmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbcbdm2 : rk(ab :: ac :: ad :: bc :: bd :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: bc :: bd :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbcbdm3 : rk(ab :: ac :: ad :: bc :: bd :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

assert(HabacadbcbdM : rk(ab :: ac :: ad :: bc :: bd ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habacadbcbdm : rk(ab :: ac :: ad :: bc :: bd ::  nil) >= 1) by (solve_hyps_min Habacadbcbdeq Habacadbcbdm1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labacbcbd : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: bc :: bd ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacbcbd requis par la preuve de (?)abacbcbd pour la règle 6  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abacbcbd requis par la preuve de (?)abacbcbd pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacbcbdm3 : rk(ab :: ac :: bc :: bd :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: bc :: bd :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 6 (code, 3 ou 4 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HabacbcbdM3 : rk(ab :: ac :: bc :: bd :: nil) <= 3).
{
	assert(Habacadbcbdeq : rk(ab :: ac :: ad :: bc :: bd :: nil) = 3) by (apply Labacadbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacadbcbdMtmp : rk(ab :: ac :: ad :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacadbcbdeq HabacadbcbdM3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: ac :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (ab :: ac :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: nil) 3 3 HabacadbcbdMtmp Hcomp Hincl);apply HT.
}

assert(HabacbcbdM : rk(ab :: ac :: bc :: bd ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Habacbcbdeq HabacbcbdM4).
assert(Habacbcbdm : rk(ab :: ac :: bc :: bd ::  nil) >= 1) by (solve_hyps_min Habacbcbdeq Habacbcbdm1).
intuition.
Qed.

(* dans constructLemma(), requis par Labbe *)
(* dans constructLemma(), requis par Labbdbede *)
(* dans constructLemma(), requis par Labadbdbede *)
(* dans constructLemma(), requis par Labacadbdbede *)
(* dans constructLemma(), requis par Labacadbcbdbede *)
(* dans constructLemma(), requis par Labacadaebcbdbede *)
(* dans constructLemma(), requis par Labacadaebcbdbecede *)
(* dans la couche 0 *)
Lemma Lbcbdbece : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: bd :: be :: ce ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour bcbdbece requis par la preuve de (?)bcbdbece pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbcbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbece requis par la preuve de (?)abbcbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbcbeceM3 : rk(ab :: bc :: be :: ce :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: be :: ce :: nil) (ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: be :: ce :: nil) ((ab :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bc :: be :: ce :: nil) (nil) 1 2 0 HabMtmp HbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbeceM4 : rk(ab :: bc :: bd :: be :: ce :: nil) <= 4).
{
	assert(HbdMtmp : rk(bd :: nil) <= 1) by (solve_hyps_max Hbdeq HbdM1).
	assert(HabbcbeceMtmp : rk(ab :: bc :: be :: ce :: nil) <= 3) by (solve_hyps_max Habbcbeceeq HabbcbeceM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bd :: nil) (ab :: bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (bd :: ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bd :: ab :: bc :: be :: ce :: nil) ((bd :: nil) ++ (ab :: bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bd :: nil) (ab :: bc :: be :: ce :: nil) (nil) 1 3 0 HbdMtmp HabbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbecem3 : rk(ab :: bc :: bd :: be :: ce :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbece requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbece requis par la preuve de (?)bcbdbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbeceM3 : rk(bc :: bd :: be :: ce :: nil) <= 3).
{
	assert(HbdMtmp : rk(bd :: nil) <= 1) by (solve_hyps_max Hbdeq HbdM1).
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bd :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: ce :: nil) (bd :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bd :: bc :: be :: ce :: nil) ((bd :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bd :: nil) (bc :: be :: ce :: nil) (nil) 1 2 0 HbdMtmp HbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: ce ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: be ::   de rang : 1 et 2 *)
assert(Hbcbdbecem2 : rk(bc :: bd :: be :: ce :: nil) >= 2).
{
	assert(HabbeMtmp : rk(ab :: be :: nil) <= 2) by (solve_hyps_max Habbeeq HabbeM2).
	assert(Habbcbdbecemtmp : rk(ab :: bc :: bd :: be :: ce :: nil) >= 3) by (solve_hyps_min Habbcbdbeceeq Habbcbdbecem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bc :: bd :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (ab :: be :: bc :: bd :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bc :: bd :: be :: ce :: nil) ((ab :: be :: nil) ++ (bc :: bd :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbecemtmp;try rewrite HT2 in Habbcbdbecemtmp.
	assert(HT := rule_4 (ab :: be :: nil) (bc :: bd :: be :: ce :: nil) (be :: nil) 3 1 2 Habbcbdbecemtmp Hbemtmp HabbeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hbcbdbecem3 : rk(bc :: bd :: be :: ce :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (bc :: bd :: be :: ce :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (bc :: bd :: be :: ce :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

assert(HbcbdbeceM : rk(bc :: bd :: be :: ce ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Hbcbdbeceeq HbcbdbeceM4).
assert(Hbcbdbecem : rk(bc :: bd :: be :: ce ::  nil) >= 1) by (solve_hyps_min Hbcbdbeceeq Hbcbdbecem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labacadaebcbdbecede *)
(* dans la couche 0 *)
Lemma Labacadaebcbdbecede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbecede pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abaebcbe requis par la preuve de (?)abadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abaebcbe requis par la preuve de (?)abaebcbe pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabaebcbeM3 : rk(ab :: ae :: bc :: be :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: ae :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: be :: nil) (bc :: ab :: ae :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: ae :: be :: nil) ((bc :: nil) ++ (ab :: ae :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: ae :: be :: nil) (nil) 1 2 0 HbcMtmp HabaebeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabadaebcbdbeM4 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) <= 4).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HabaebcbeMtmp : rk(ab :: ae :: bc :: be :: nil) <= 3) by (solve_hyps_max Habaebcbeeq HabaebcbeM3).
	assert(Habmtmp : rk(ab :: nil) >= 1) by (solve_hyps_min Habeq Habm1).
	assert(Hincl : incl (ab :: nil) (list_inter (ab :: ad :: bd :: nil) (ab :: ae :: bc :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: ae :: bc :: bd :: be :: nil) (ab :: ad :: bd :: ab :: ae :: bc :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: ab :: ae :: bc :: be :: nil) ((ab :: ad :: bd :: nil) ++ (ab :: ae :: bc :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (ab :: ae :: bc :: be :: nil) (ab :: nil) 2 3 1 HabadbdMtmp HabaebcbeMtmp Habmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadaebcbdbem2 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadaebcbdbem3 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbem2 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbem3 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et -4*)
assert(HabacadaebcbdbeM4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) <= 4).
{
	assert(Habacbcbdeq : rk(ab :: ac :: bc :: bd :: nil) = 3) by (apply Labacbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacbcbdMtmp : rk(ab :: ac :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacbcbdeq HabacbcbdM3).
	assert(HabadaebcbdbeMtmp : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) <= 4) by (solve_hyps_max Habadaebcbdbeeq HabadaebcbdbeM4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: nil) ((ab :: ac :: bc :: bd :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) (ab :: bc :: bd :: nil) 3 4 3 HabacbcbdMtmp HabadaebcbdbeMtmp Habbcbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour bcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbedeM4 : rk(ab :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (bc :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: bd :: be :: de :: nil) ((bc :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HbcMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbedem3 : rk(ab :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbedeM3 : rk(bc :: bd :: be :: de :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: de :: nil) ((bc :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HbcMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: de ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: be ::   de rang : 1 et 2 *)
assert(Hbcbdbedem2 : rk(bc :: bd :: be :: de :: nil) >= 2).
{
	assert(HabbeMtmp : rk(ab :: be :: nil) <= 2) by (solve_hyps_max Habbeeq HabbeM2).
	assert(Habbcbdbedemtmp : rk(ab :: bc :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habbcbdbedeeq Habbcbdbedem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (ab :: be :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bc :: bd :: be :: de :: nil) ((ab :: be :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbedemtmp;try rewrite HT2 in Habbcbdbedemtmp.
	assert(HT := rule_4 (ab :: be :: nil) (bc :: bd :: be :: de :: nil) (be :: nil) 3 1 2 Habbcbdbedemtmp Hbemtmp HabbeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hbcbdbedem3 : rk(bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbedem2 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbedem3 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 5 5 et -4*)
assert(HabacadaebcbdbedeM4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HabacadaebcbdbeMtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) <= 4) by (solve_hyps_max Habacadaebcbdbeeq HabacadaebcbdbeM4).
	assert(HbcbdbedeMtmp : rk(bc :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM3).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: bc :: bd :: be :: de :: nil) ((ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: nil) 4 3 3 HabacadaebcbdbeMtmp HbcbdbedeMtmp Hbcbdbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abacadaebcbdbecede requis par la preuve de (?)abacadaebcbdbecede pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadaebcbdbecede requis par la preuve de (?)abacadaebcbdbecede pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadaebcbdbecede requis par la preuve de (?)abacadaebcbdbecede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadaebcbdbecede requis par la preuve de (?)abacadaebcbdbecede pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbecedem2 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbecedem3 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: -4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: bc :: bd :: cd ::   de rang : 3 et 3 *)
assert(Habacadaebcbdbecedem4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 4).
{
	assert(Habbcbdcdeq : rk(ab :: bc :: bd :: cd :: nil) = 3) by (apply Labbcbdcd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabbcbdcdMtmp : rk(ab :: bc :: bd :: cd :: nil) <= 3) by (solve_hyps_max Habbcbdcdeq HabbcbdcdM3).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: bc :: bd :: cd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: cd :: ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: bd :: cd :: ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) ((ab :: bc :: bd :: cd :: nil) ++ (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: bc :: bd :: cd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habacadaebcbdbecdcedemtmp Habbcbdmtmp HabbcbdcdMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et -4*)
assert(HabacadaebcbdbecedeM4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) <= 4).
{
	assert(Hbcbdbeceeq : rk(bc :: bd :: be :: ce :: nil) = 3) by (apply Lbcbdbece with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbeceMtmp : rk(bc :: bd :: be :: ce :: nil) <= 3) by (solve_hyps_max Hbcbdbeceeq HbcbdbeceM3).
	assert(HabacadaebcbdbedeMtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) <= 4) by (solve_hyps_max Habacadaebcbdbedeeq HabacadaebcbdbedeM4).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (bc :: bd :: be :: ce :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) (bc :: bd :: be :: ce :: ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: ce :: ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) ((bc :: bd :: be :: ce :: nil) ++ (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: bd :: be :: ce :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) (bc :: bd :: be :: nil) 3 4 3 HbcbdbeceMtmp HabacadaebcbdbedeMtmp Hbcbdbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HabacadaebcbdbecedeM : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habacadaebcbdbecedem : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de ::  nil) >= 1) by (solve_hyps_min Habacadaebcbdbecedeeq Habacadaebcbdbecedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labacadaebcbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abaebcbe requis par la preuve de (?)abadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abaebcbe requis par la preuve de (?)abaebcbe pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabaebcbeM3 : rk(ab :: ae :: bc :: be :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: ae :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: be :: nil) (bc :: ab :: ae :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: ae :: be :: nil) ((bc :: nil) ++ (ab :: ae :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: ae :: be :: nil) (nil) 1 2 0 HbcMtmp HabaebeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadaebcbdbe requis par la preuve de (?)abadaebcbdbe pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabadaebcbdbeM4 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) <= 4).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HabaebcbeMtmp : rk(ab :: ae :: bc :: be :: nil) <= 3) by (solve_hyps_max Habaebcbeeq HabaebcbeM3).
	assert(Habmtmp : rk(ab :: nil) >= 1) by (solve_hyps_min Habeq Habm1).
	assert(Hincl : incl (ab :: nil) (list_inter (ab :: ad :: bd :: nil) (ab :: ae :: bc :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: ae :: bc :: bd :: be :: nil) (ab :: ad :: bd :: ab :: ae :: bc :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: ab :: ae :: bc :: be :: nil) ((ab :: ad :: bd :: nil) ++ (ab :: ae :: bc :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (ab :: ae :: bc :: be :: nil) (ab :: nil) 2 3 1 HabadbdMtmp HabaebcbeMtmp Habmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadaebcbdbem2 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadaebcbdbem3 : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadaebcbdbe requis par la preuve de (?)abacadaebcbdbe pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbem2 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbem3 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et -4*)
assert(HabacadaebcbdbeM4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) <= 4).
{
	assert(Habacbcbdeq : rk(ab :: ac :: bc :: bd :: nil) = 3) by (apply Labacbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacbcbdMtmp : rk(ab :: ac :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacbcbdeq HabacbcbdM3).
	assert(HabadaebcbdbeMtmp : rk(ab :: ad :: ae :: bc :: bd :: be :: nil) <= 4) by (solve_hyps_max Habadaebcbdbeeq HabadaebcbdbeM4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: nil) ((ab :: ac :: bc :: bd :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: nil) (ab :: bc :: bd :: nil) 3 4 3 HabacbcbdMtmp HabadaebcbdbeMtmp Habbcbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 3 pour bcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbedeM4 : rk(ab :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (bc :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: bd :: be :: de :: nil) ((bc :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HbcMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbedem3 : rk(ab :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbedeM3 : rk(bc :: bd :: be :: de :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: de :: nil) ((bc :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HbcMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: de ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: be ::   de rang : 1 et 2 *)
assert(Hbcbdbedem2 : rk(bc :: bd :: be :: de :: nil) >= 2).
{
	assert(HabbeMtmp : rk(ab :: be :: nil) <= 2) by (solve_hyps_max Habbeeq HabbeM2).
	assert(Habbcbdbedemtmp : rk(ab :: bc :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habbcbdbedeeq Habbcbdbedem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (ab :: be :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bc :: bd :: be :: de :: nil) ((ab :: be :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbedemtmp;try rewrite HT2 in Habbcbdbedemtmp.
	assert(HT := rule_4 (ab :: be :: nil) (bc :: bd :: be :: de :: nil) (be :: nil) 3 1 2 Habbcbdbedemtmp Hbemtmp HabbeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hbcbdbedem3 : rk(bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadaebcbdbede requis par la preuve de (?)abacadaebcbdbede pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbedem2 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadaebcbdbedem3 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 5 5 et -4*)
assert(HabacadaebcbdbedeM4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HabacadaebcbdbeMtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) <= 4) by (solve_hyps_max Habacadaebcbdbeeq HabacadaebcbdbeM4).
	assert(HbcbdbedeMtmp : rk(bc :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM3).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: bc :: bd :: be :: de :: nil) ((ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ac :: ad :: ae :: bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: nil) 4 3 3 HabacadaebcbdbeMtmp HbcbdbedeMtmp Hbcbdbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de ::  de rang :  4 et 4 	 AiB : bc :: bd :: be ::  de rang :  3 et 3 	 A : bc :: bd :: be :: ce ::   de rang : 3 et 3 *)
assert(Habacadaebcbdbedem4 : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 4).
{
	assert(Hbcbdbeceeq : rk(bc :: bd :: be :: ce :: nil) = 3) by (apply Lbcbdbece with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbeceMtmp : rk(bc :: bd :: be :: ce :: nil) <= 3) by (solve_hyps_max Hbcbdbeceeq HbcbdbeceM3).
	assert(Habacadaebcbdbecedeeq : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) = 4) by (apply Labacadaebcbdbecede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habacadaebcbdbecedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecedeeq Habacadaebcbdbecedem4).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (bc :: bd :: be :: ce :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: ce :: de :: nil) (bc :: bd :: be :: ce :: ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: ce :: ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) ((bc :: bd :: be :: ce :: nil) ++ (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecedemtmp;try rewrite HT2 in Habacadaebcbdbecedemtmp.
	assert(HT := rule_4 (bc :: bd :: be :: ce :: nil) (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) (bc :: bd :: be :: nil) 4 3 3 Habacadaebcbdbecedemtmp Hbcbdbemtmp HbcbdbeceMtmp Hincl); apply HT.
}

assert(HabacadaebcbdbedeM : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habacadaebcbdbedem : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Habacadaebcbdbedeeq Habacadaebcbdbedem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labacadbcbdbede *)
(* dans la couche 0 *)
Lemma Lacadaede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ac :: ad :: ae :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour acadaede requis par la preuve de (?)acadaede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acadaede requis par la preuve de (?)acadaede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HacadaedeM3 : rk(ac :: ad :: ae :: de :: nil) <= 3).
{
	assert(HacMtmp : rk(ac :: nil) <= 1) by (solve_hyps_max Haceq HacM1).
	assert(HadaedeMtmp : rk(ad :: ae :: de :: nil) <= 2) by (solve_hyps_max Hadaedeeq HadaedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: nil) (ad :: ae :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: ae :: de :: nil) (ac :: ad :: ae :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: ae :: de :: nil) ((ac :: nil) ++ (ad :: ae :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: nil) (ad :: ae :: de :: nil) (nil) 1 2 0 HacMtmp HadaedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadaedem3 : rk(ac :: ad :: ae :: de :: nil) >= 3).
{
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: de :: nil) (ac :: ad :: ae :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: de :: nil) (ac :: ad :: ae :: de :: nil) 3 3 Hacaddemtmp Hcomp Hincl);apply HT.
}

assert(HacadaedeM : rk(ac :: ad :: ae :: de ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Hacadaedeeq HacadaedeM4).
assert(Hacadaedem : rk(ac :: ad :: ae :: de ::  nil) >= 1) by (solve_hyps_min Hacadaedeeq Hacadaedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labacadbcbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: ad :: bc :: bd :: be :: de ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadbcbdbede requis par la preuve de (?)abacadbcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abadbcbdbede requis par la preuve de (?)abacadbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour abadbcbdbede requis par la preuve de (?)abadbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadbcbdbede requis par la preuve de (?)abadbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbede requis par la preuve de (?)abadbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbedeM3 : rk(bc :: bd :: be :: de :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: de :: nil) ((bc :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HbcMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadbcbdbede requis par la preuve de (?)abadbcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabadbcbdbedeM4 : rk(ab :: ad :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HbcbdbedeMtmp : rk(bc :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: ad :: bd :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bc :: bd :: be :: de :: nil) (ab :: ad :: bd :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: bc :: bd :: be :: de :: nil) ((ab :: ad :: bd :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (bc :: bd :: be :: de :: nil) (bd :: nil) 2 3 1 HabadbdMtmp HbcbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbcbdbedem2 : rk(ab :: ad :: bc :: bd :: be :: de :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbcbdbedem3 : rk(ab :: ad :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacadbcbdbede requis par la preuve de (?)abacadbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour abacadbcbdbede requis par la preuve de (?)abacadbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadbcbdbede requis par la preuve de (?)abacadbcbdbede pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbcbdbedem2 : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbcbdbedem3 : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 5 et -4*)
assert(HabacadbcbdbedeM4 : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(Habacbcbdeq : rk(ab :: ac :: bc :: bd :: nil) = 3) by (apply Labacbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacbcbdMtmp : rk(ab :: ac :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacbcbdeq HabacbcbdM3).
	assert(HabadbcbdbedeMtmp : rk(ab :: ad :: bc :: bd :: be :: de :: nil) <= 4) by (solve_hyps_max Habadbcbdbedeeq HabadbcbdbedeM4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ac :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bc :: bd :: be :: de :: nil) (ab :: ac :: bc :: bd :: ab :: ad :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: bc :: bd :: ab :: ad :: bc :: bd :: be :: de :: nil) ((ab :: ac :: bc :: bd :: nil) ++ (ab :: ad :: bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ac :: bc :: bd :: nil) (ab :: ad :: bc :: bd :: be :: de :: nil) (ab :: bc :: bd :: nil) 3 4 3 HabacbcbdMtmp HabadbcbdbedeMtmp Habbcbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: de ::  de rang :  4 et 4 	 AiB : ac :: ad :: de ::  de rang :  3 et 3 	 A : ac :: ad :: ae :: de ::   de rang : 3 et 3 *)
assert(Habacadbcbdbedem4 : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) >= 4).
{
	assert(Hacadaedeeq : rk(ac :: ad :: ae :: de :: nil) = 3) by (apply Lacadaede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HacadaedeMtmp : rk(ac :: ad :: ae :: de :: nil) <= 3) by (solve_hyps_max Hacadaedeeq HacadaedeM3).
	assert(Habacadaebcbdbedeeq : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) = 4) by (apply Labacadaebcbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habacadaebcbdbedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbedeeq Habacadaebcbdbedem4).
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hincl : incl (ac :: ad :: de :: nil) (list_inter (ac :: ad :: ae :: de :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: de :: nil) (ac :: ad :: ae :: de :: ab :: ac :: ad :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: ae :: de :: ab :: ac :: ad :: bc :: bd :: be :: de :: nil) ((ac :: ad :: ae :: de :: nil) ++ (ab :: ac :: ad :: bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbedemtmp;try rewrite HT2 in Habacadaebcbdbedemtmp.
	assert(HT := rule_4 (ac :: ad :: ae :: de :: nil) (ab :: ac :: ad :: bc :: bd :: be :: de :: nil) (ac :: ad :: de :: nil) 4 3 3 Habacadaebcbdbedemtmp Hacaddemtmp HacadaedeMtmp Hincl); apply HT.
}

assert(HabacadbcbdbedeM : rk(ab :: ac :: ad :: bc :: bd :: be :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habacadbcbdbedem : rk(ab :: ac :: ad :: bc :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Habacadbcbdbedeeq Habacadbcbdbedem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labacadbdbede *)
(* dans la couche 0 *)
Lemma Lacadbcde : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ac :: ad :: bc :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour acadbcde requis par la preuve de (?)acadbcde pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour acadbcde requis par la preuve de (?)acadbcde pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acadbcde requis par la preuve de (?)acadbcde pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -2 et 5*)
assert(HacadbcdeM3 : rk(ac :: ad :: bc :: de :: nil) <= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(HdeMtmp : rk(de :: nil) <= 1) by (solve_hyps_max Hdeeq HdeM1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: ad :: bc :: nil) (de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: bc :: de :: nil) (ac :: ad :: bc :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: de :: nil) ((ac :: ad :: bc :: nil) ++ (de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: ad :: bc :: nil) (de :: nil) (nil) 2 1 0 HacadbcMtmp HdeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadbcdem2 : rk(ac :: ad :: bc :: de :: nil) >= 2).
{
	assert(Hacadbcmtmp : rk(ac :: ad :: bc :: nil) >= 2) by (solve_hyps_min Hacadbceq Hacadbcm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: bc :: nil) (ac :: ad :: bc :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: bc :: nil) (ac :: ad :: bc :: de :: nil) 2 2 Hacadbcmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadbcdem3 : rk(ac :: ad :: bc :: de :: nil) >= 3).
{
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: de :: nil) (ac :: ad :: bc :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: de :: nil) (ac :: ad :: bc :: de :: nil) 3 3 Hacaddemtmp Hcomp Hincl);apply HT.
}

assert(HacadbcdeM : rk(ac :: ad :: bc :: de ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Hacadbcdeeq HacadbcdeM4).
assert(Hacadbcdem : rk(ac :: ad :: bc :: de ::  nil) >= 1) by (solve_hyps_min Hacadbcdeeq Hacadbcdem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labacadbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ac :: ad :: bd :: be :: de ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abacadbdbede requis par la preuve de (?)abacadbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour abacadbdbede requis par la preuve de (?)abacadbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abacadbdbede requis par la preuve de (?)abacadbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour acbdbede requis par la preuve de (?)abacadbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acbdbede requis par la preuve de (?)acbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HacbdbedeM3 : rk(ac :: bd :: be :: de :: nil) <= 3).
{
	assert(HacMtmp : rk(ac :: nil) <= 1) by (solve_hyps_max Haceq HacM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: bd :: be :: de :: nil) (ac :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: bd :: be :: de :: nil) ((ac :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HacMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacadbdbede requis par la preuve de (?)abacadbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabacadbdbedeM4 : rk(ab :: ac :: ad :: bd :: be :: de :: nil) <= 4).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HacbdbedeMtmp : rk(ac :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hacbdbedeeq HacbdbedeM3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: ad :: bd :: nil) (ac :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bd :: be :: de :: nil) (ab :: ad :: bd :: ac :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: ac :: bd :: be :: de :: nil) ((ab :: ad :: bd :: nil) ++ (ac :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (ac :: bd :: be :: de :: nil) (bd :: nil) 2 3 1 HabadbdMtmp HacbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbdbedem2 : rk(ab :: ac :: ad :: bd :: be :: de :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacadbdbedem3 : rk(ab :: ac :: ad :: bd :: be :: de :: nil) >= 3).
{
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: de :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: de :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil) 3 3 Hacaddemtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: bc :: bd :: be :: de ::  de rang :  4 et 4 	 AiB : ac :: ad :: de ::  de rang :  3 et 3 	 A : ac :: ad :: bc :: de ::   de rang : 3 et 3 *)
assert(Habacadbdbedem4 : rk(ab :: ac :: ad :: bd :: be :: de :: nil) >= 4).
{
	assert(Hacadbcdeeq : rk(ac :: ad :: bc :: de :: nil) = 3) by (apply Lacadbcde with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HacadbcdeMtmp : rk(ac :: ad :: bc :: de :: nil) <= 3) by (solve_hyps_max Hacadbcdeeq HacadbcdeM3).
	assert(Habacadbcbdbedeeq : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) = 4) by (apply Labacadbcbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habacadbcbdbedemtmp : rk(ab :: ac :: ad :: bc :: bd :: be :: de :: nil) >= 4) by (solve_hyps_min Habacadbcbdbedeeq Habacadbcbdbedem4).
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hincl : incl (ac :: ad :: de :: nil) (list_inter (ac :: ad :: bc :: de :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bc :: bd :: be :: de :: nil) (ac :: ad :: bc :: de :: ab :: ac :: ad :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: de :: ab :: ac :: ad :: bd :: be :: de :: nil) ((ac :: ad :: bc :: de :: nil) ++ (ab :: ac :: ad :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadbcbdbedemtmp;try rewrite HT2 in Habacadbcbdbedemtmp.
	assert(HT := rule_4 (ac :: ad :: bc :: de :: nil) (ab :: ac :: ad :: bd :: be :: de :: nil) (ac :: ad :: de :: nil) 4 3 3 Habacadbcbdbedemtmp Hacaddemtmp HacadbcdeMtmp Hincl); apply HT.
}

assert(HabacadbdbedeM : rk(ab :: ac :: ad :: bd :: be :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habacadbdbedem : rk(ab :: ac :: ad :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Habacadbdbedeeq Habacadbdbedem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labadbdbede *)
(* dans constructLemma(), requis par Lacbdbede *)
(* dans la couche 0 *)
Lemma Lacbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ac :: bd :: be :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abadbdbede requis par la preuve de (?)acbdbede pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabadbdbedeM4 : rk(ab :: ad :: bd :: be :: de :: nil) <= 4).
{
	assert(HadMtmp : rk(ad :: nil) <= 1) by (solve_hyps_max Hadeq HadM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ad :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bd :: be :: de :: nil) (ad :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ad :: ab :: bd :: be :: de :: nil) ((ad :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ad :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HadMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HabadbdbedeM3 : rk(ab :: ad :: bd :: be :: de :: nil) <= 3).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: ad :: bd :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bd :: be :: de :: nil) (ab :: ad :: bd :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: bd :: be :: de :: nil) ((ab :: ad :: bd :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (bd :: be :: de :: nil) (bd :: nil) 2 2 1 HabadbdMtmp HbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbdbedem2 : rk(ab :: ad :: bd :: be :: de :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: bd :: be :: de :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour acbdbede requis par la preuve de (?)acbdbede pour la règle 2  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour acbcbdbecdde requis par la preuve de (?)acbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour acbdbede requis par la preuve de (?)acbcbdbecdde pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acbdbede requis par la preuve de (?)acbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HacbdbedeM3 : rk(ac :: bd :: be :: de :: nil) <= 3).
{
	assert(HacMtmp : rk(ac :: nil) <= 1) by (solve_hyps_max Haceq HacM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: bd :: be :: de :: nil) (ac :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: bd :: be :: de :: nil) ((ac :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HacMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour acbcbdbecdde requis par la preuve de (?)acbcbdbecdde pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour acbcbdbecdde requis par la preuve de (?)acbcbdbecdde pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abacaebcbdbecdde requis par la preuve de (?)acbcbdbecdde pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abacaebcbdbecdde requis par la preuve de (?)abacaebcbdbecdde pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habacaebcbdbecddem3 : rk(ab :: ac :: ae :: bc :: bd :: be :: cd :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ac :: ae :: bc :: bd :: be :: cd :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ac :: ae :: bc :: bd :: be :: cd :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour acbcbdbecdde requis par la preuve de (?)acbcbdbecdde pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : ab :: ac :: ae :: bc :: bd :: be :: cd :: de ::  de rang :  3 et 5 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: ae :: be ::   de rang : 2 et 2 *)
assert(Hacbcbdbecddem2 : rk(ac :: bc :: bd :: be :: cd :: de :: nil) >= 2).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Habacaebcbdbecddemtmp : rk(ab :: ac :: ae :: bc :: bd :: be :: cd :: de :: nil) >= 3) by (solve_hyps_min Habacaebcbdbecddeeq Habacaebcbdbecddem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: ae :: be :: nil) (ac :: bc :: bd :: be :: cd :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ae :: bc :: bd :: be :: cd :: de :: nil) (ab :: ae :: be :: ac :: bc :: bd :: be :: cd :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: ac :: bc :: bd :: be :: cd :: de :: nil) ((ab :: ae :: be :: nil) ++ (ac :: bc :: bd :: be :: cd :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacaebcbdbecddemtmp;try rewrite HT2 in Habacaebcbdbecddemtmp.
	assert(HT := rule_4 (ab :: ae :: be :: nil) (ac :: bc :: bd :: be :: cd :: de :: nil) (be :: nil) 3 1 2 Habacaebcbdbecddemtmp Hbemtmp HabaebeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacbcbdbecddem3 : rk(ac :: bc :: bd :: be :: cd :: de :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (ac :: bc :: bd :: be :: cd :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (ac :: bc :: bd :: be :: cd :: de :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HacbcbdbecddeM4 : rk(ac :: bc :: bd :: be :: cd :: de :: nil) <= 4).
{
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(HacbdbedeMtmp : rk(ac :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hacbdbedeeq HacbdbedeM3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (bc :: bd :: cd :: nil) (ac :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: bc :: bd :: be :: cd :: de :: nil) (bc :: bd :: cd :: ac :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: cd :: ac :: bd :: be :: de :: nil) ((bc :: bd :: cd :: nil) ++ (ac :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: bd :: cd :: nil) (ac :: bd :: be :: de :: nil) (bd :: nil) 2 3 1 HbcbdcdMtmp HacbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : ac :: bc :: bd :: be :: cd :: de ::  de rang :  3 et 4 	 AiB : bd ::  de rang :  1 et 1 	 A : bc :: bd :: cd ::   de rang : 2 et 2 *)
assert(Hacbdbedem2 : rk(ac :: bd :: be :: de :: nil) >= 2).
{
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(Hacbcbdbecddemtmp : rk(ac :: bc :: bd :: be :: cd :: de :: nil) >= 3) by (solve_hyps_min Hacbcbdbecddeeq Hacbcbdbecddem3).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (bc :: bd :: cd :: nil) (ac :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: bc :: bd :: be :: cd :: de :: nil) (bc :: bd :: cd :: ac :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: cd :: ac :: bd :: be :: de :: nil) ((bc :: bd :: cd :: nil) ++ (ac :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Hacbcbdbecddemtmp;try rewrite HT2 in Hacbcbdbecddemtmp.
	assert(HT := rule_4 (bc :: bd :: cd :: nil) (ac :: bd :: be :: de :: nil) (bd :: nil) 3 1 2 Hacbcbdbecddemtmp Hbdmtmp HbcbdcdMtmp Hincl); apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 5*)
assert(Hacbdbedem3 : rk(ac :: bd :: be :: de :: nil) >= 3).
{
	assert(HabadbdbedeMtmp : rk(ab :: ad :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habadbdbedeeq HabadbdbedeM3).
	assert(Habacadbdbedeeq : rk(ab :: ac :: ad :: bd :: be :: de :: nil) = 4) by (apply Labacadbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habacadbdbedemtmp : rk(ab :: ac :: ad :: bd :: be :: de :: nil) >= 4) by (solve_hyps_min Habacadbdbedeeq Habacadbdbedem4).
	assert(Hbdbedemtmp : rk(bd :: be :: de :: nil) >= 2) by (solve_hyps_min Hbdbedeeq Hbdbedem2).
	assert(Hincl : incl (bd :: be :: de :: nil) (list_inter (ac :: bd :: be :: de :: nil) (ab :: ad :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bd :: be :: de :: nil) (ac :: bd :: be :: de :: ab :: ad :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: bd :: be :: de :: ab :: ad :: bd :: be :: de :: nil) ((ac :: bd :: be :: de :: nil) ++ (ab :: ad :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadbdbedemtmp;try rewrite HT2 in Habacadbdbedemtmp.
	assert(HT := rule_2 (ac :: bd :: be :: de :: nil) (ab :: ad :: bd :: be :: de :: nil) (bd :: be :: de :: nil) 4 2 3 Habacadbdbedemtmp Hbdbedemtmp HabadbdbedeMtmp Hincl);apply HT.
}

assert(HacbdbedeM : rk(ac :: bd :: be :: de ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Hacbdbedeeq HacbdbedeM4).
assert(Hacbdbedem : rk(ac :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Hacbdbedeeq Hacbdbedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labadbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ad :: bd :: be :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadbdbede requis par la preuve de (?)abadbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabadbdbedeM4 : rk(ab :: ad :: bd :: be :: de :: nil) <= 4).
{
	assert(HadMtmp : rk(ad :: nil) <= 1) by (solve_hyps_max Hadeq HadM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ad :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bd :: be :: de :: nil) (ad :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ad :: ab :: bd :: be :: de :: nil) ((ad :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ad :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HadMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HabadbdbedeM3 : rk(ab :: ad :: bd :: be :: de :: nil) <= 3).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (ab :: ad :: bd :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bd :: be :: de :: nil) (ab :: ad :: bd :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: bd :: be :: de :: nil) ((ab :: ad :: bd :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ad :: bd :: nil) (bd :: be :: de :: nil) (bd :: nil) 2 2 1 HabadbdMtmp HbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habadbdbedem2 : rk(ab :: ad :: bd :: be :: de :: nil) >= 2).
{
	assert(Habadbdmtmp : rk(ab :: ad :: bd :: nil) >= 2) by (solve_hyps_min Habadbdeq Habadbdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ad :: bd :: nil) (ab :: ad :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ad :: bd :: nil) (ab :: ad :: bd :: be :: de :: nil) 2 2 Habadbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: bd :: be :: de ::  de rang :  4 et 4 	 AiB : bd :: be :: de ::  de rang :  2 et 2 	 A : ac :: bd :: be :: de ::   de rang : 3 et 3 *)
assert(Habadbdbedem3 : rk(ab :: ad :: bd :: be :: de :: nil) >= 3).
{
	assert(Hacbdbedeeq : rk(ac :: bd :: be :: de :: nil) = 3) by (apply Lacbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HacbdbedeMtmp : rk(ac :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hacbdbedeeq HacbdbedeM3).
	assert(Habacadbdbedeeq : rk(ab :: ac :: ad :: bd :: be :: de :: nil) = 4) by (apply Labacadbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habacadbdbedemtmp : rk(ab :: ac :: ad :: bd :: be :: de :: nil) >= 4) by (solve_hyps_min Habacadbdbedeeq Habacadbdbedem4).
	assert(Hbdbedemtmp : rk(bd :: be :: de :: nil) >= 2) by (solve_hyps_min Hbdbedeeq Hbdbedem2).
	assert(Hincl : incl (bd :: be :: de :: nil) (list_inter (ac :: bd :: be :: de :: nil) (ab :: ad :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: bd :: be :: de :: nil) (ac :: bd :: be :: de :: ab :: ad :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: bd :: be :: de :: ab :: ad :: bd :: be :: de :: nil) ((ac :: bd :: be :: de :: nil) ++ (ab :: ad :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadbdbedemtmp;try rewrite HT2 in Habacadbdbedemtmp.
	assert(HT := rule_4 (ac :: bd :: be :: de :: nil) (ab :: ad :: bd :: be :: de :: nil) (bd :: be :: de :: nil) 4 2 3 Habacadbdbedemtmp Hbdbedemtmp HacbdbedeMtmp Hincl); apply HT.
}

assert(HabadbdbedeM : rk(ab :: ad :: bd :: be :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habadbdbedem : rk(ab :: ad :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Habadbdbedeeq Habadbdbedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: bd :: be :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)abbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbedeM4 : rk(ab :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (bc :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: bd :: be :: de :: nil) ((bc :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HbcMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbedem3 : rk(ab :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour bcbe requis par la preuve de (?)abbdbede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: de ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : bc :: be ::   de rang : 1 et 2 *)
assert(Habbdbedem2 : rk(ab :: bd :: be :: de :: nil) >= 2).
{
	assert(HbcbeMtmp : rk(bc :: be :: nil) <= 2) by (solve_hyps_max Hbcbeeq HbcbeM2).
	assert(Habbcbdbedemtmp : rk(ab :: bc :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habbcbdbedeeq Habbcbdbedem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (bc :: be :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (bc :: be :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: be :: ab :: bd :: be :: de :: nil) ((bc :: be :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbedemtmp;try rewrite HT2 in Habbcbdbedemtmp.
	assert(HT := rule_4 (bc :: be :: nil) (ab :: bd :: be :: de :: nil) (be :: nil) 3 1 2 Habbcbdbedemtmp Hbemtmp HbcbeMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 3) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : ab :: ad :: bd :: be :: de ::  de rang :  3 et 3 	 AiB : ab :: bd ::  de rang :  2 et 2 	 A : ab :: ad :: bd ::   de rang : 2 et 2 *)
assert(Habbdbedem3 : rk(ab :: bd :: be :: de :: nil) >= 3).
{
	assert(HabadbdMtmp : rk(ab :: ad :: bd :: nil) <= 2) by (solve_hyps_max Habadbdeq HabadbdM2).
	assert(Habadbdbedeeq : rk(ab :: ad :: bd :: be :: de :: nil) = 3) by (apply Labadbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habadbdbedemtmp : rk(ab :: ad :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habadbdbedeeq Habadbdbedem3).
	assert(Habbdeq : rk(ab :: bd :: nil) = 2) by (apply Labbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habbdmtmp : rk(ab :: bd :: nil) >= 2) by (solve_hyps_min Habbdeq Habbdm2).
	assert(Hincl : incl (ab :: bd :: nil) (list_inter (ab :: ad :: bd :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: bd :: be :: de :: nil) (ab :: ad :: bd :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bd :: ab :: bd :: be :: de :: nil) ((ab :: ad :: bd :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habadbdbedemtmp;try rewrite HT2 in Habadbdbedemtmp.
	assert(HT := rule_4 (ab :: ad :: bd :: nil) (ab :: bd :: be :: de :: nil) (ab :: bd :: nil) 3 2 2 Habadbdbedemtmp Habbdmtmp HabadbdMtmp Hincl); apply HT.
}

assert(HabbdbedeM : rk(ab :: bd :: be :: de ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Habbdbedeeq HabbdbedeM4).
assert(Habbdbedem : rk(ab :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Habbdbedeeq Habbdbedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labbe : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: be ::  nil) = 2.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)abbe pour la règle 2  *)
(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -2 et -4*)
assert(Habbem2 : rk(ab :: be :: nil) >= 2).
{
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Habbdbedeeq : rk(ab :: bd :: be :: de :: nil) = 3) by (apply Labbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habbdbedemtmp : rk(ab :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habbdbedeeq Habbdbedem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: be :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bd :: be :: de :: nil) ((ab :: be :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbdbedemtmp;try rewrite HT2 in Habbdbedemtmp.
	assert(HT := rule_2 (ab :: be :: nil) (bd :: be :: de :: nil) (be :: nil) 3 1 2 Habbdbedemtmp Hbemtmp HbdbedeMtmp Hincl);apply HT.
}

assert(HabbeM : rk(ab :: be ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max Habbeeq HabbeM2).
assert(Habbem : rk(ab :: be ::  nil) >= 1) by (solve_hyps_min Habbeeq Habbem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbcbe : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: be ::  nil) = 2.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour bcbe requis par la preuve de (?)bcbe pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 2) *)
(* marque des antécédents AUB AiB A: -4 -2 et 4*)
(* ensembles concernés AUB : bc :: bd :: be ::  de rang :  3 et 3 	 AiB : bc ::  de rang :  1 et 1 	 A : bc :: bd ::   de rang : 2 et 2 *)
assert(Hbcbem2 : rk(bc :: be :: nil) >= 2).
{
	assert(Hbcbdeq : rk(bc :: bd :: nil) = 2) by (apply Lbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdMtmp : rk(bc :: bd :: nil) <= 2) by (solve_hyps_max Hbcbdeq HbcbdM2).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (bc :: bd :: nil) (bc :: be :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: nil) (bc :: bd :: bc :: be :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: bc :: be :: nil) ((bc :: bd :: nil) ++ (bc :: be :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Hbcbdbemtmp;try rewrite HT2 in Hbcbdbemtmp.
	assert(HT := rule_4 (bc :: bd :: nil) (bc :: be :: nil) (bc :: nil) 3 1 2 Hbcbdbemtmp Hbcmtmp HbcbdMtmp Hincl); apply HT.
}

assert(HbcbeM : rk(bc :: be ::  nil) <= 2) (* dim : 4 *) by (solve_hyps_max Hbcbeeq HbcbeM2).
assert(Hbcbem : rk(bc :: be ::  nil) >= 1) by (solve_hyps_min Hbcbeeq Hbcbem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labbcbdbece *)
(* dans constructLemma(), requis par Labaebcbdbece *)
(* dans constructLemma(), requis par Labaebcbdbecede *)
(* dans la couche 0 *)
Lemma Labaebcbdbecede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ae :: bc :: bd :: be :: ce :: de ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour abaebdbede requis par la preuve de (?)abaebcbdbecede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abaebdbede requis par la preuve de (?)abaebdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abaebdbede requis par la preuve de (?)abaebdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abaebdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebdbede requis par la preuve de (?)abaebdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabaebdbedeM4 : rk(ab :: ae :: bd :: be :: de :: nil) <= 4).
{
	assert(HaeMtmp : rk(ae :: nil) <= 1) by (solve_hyps_max Haeeq HaeM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ae :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bd :: be :: de :: nil) (ae :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ae :: ab :: bd :: be :: de :: nil) ((ae :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ae :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HaeMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HabaebdbedeM3 : rk(ab :: ae :: bd :: be :: de :: nil) <= 3).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: ae :: be :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bd :: be :: de :: nil) (ab :: ae :: be :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: bd :: be :: de :: nil) ((ab :: ae :: be :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ae :: be :: nil) (bd :: be :: de :: nil) (be :: nil) 2 2 1 HabaebeMtmp HbdbedeMtmp Hbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habaebdbedem2 : rk(ab :: ae :: bd :: be :: de :: nil) >= 2).
{
	assert(Habaebemtmp : rk(ab :: ae :: be :: nil) >= 2) by (solve_hyps_min Habaebeeq Habaebem2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ab :: ae :: be :: nil) (ab :: ae :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: ae :: be :: nil) (ab :: ae :: bd :: be :: de :: nil) 2 2 Habaebemtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abaebcbdbecede requis par la preuve de (?)abaebcbdbecede pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)abaebcbdbecede pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour adbc requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : ad :: bc ::  de rang :  1 et 2 	 A : ac :: ad :: bc ::   de rang : 2 et 2 *)
assert(Habadaebcbdbecdcedem3 : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Hadbcmtmp : rk(ad :: bc :: nil) >= 1) by (solve_hyps_min Hadbceq Hadbcm1).
	assert(Hincl : incl (ad :: bc :: nil) (list_inter (ac :: ad :: bc :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ac :: ad :: bc :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ac :: ad :: bc :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ac :: ad :: bc :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ad :: bc :: nil) 4 1 2 Habacadaebcbdbecdcedemtmp Hadbcmtmp HacadbcMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: -4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: ac :: bc :: bd ::   de rang : 3 et 3 *)
assert(Habadaebcbdbecdcedem4 : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4).
{
	assert(Habacbcbdeq : rk(ab :: ac :: bc :: bd :: nil) = 3) by (apply Labacbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacbcbdMtmp : rk(ab :: ac :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacbcbdeq HabacbcbdM3).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ab :: ac :: bc :: bd :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habacadaebcbdbecdcedemtmp Habbcbdmtmp HabacbcbdMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : bc ::  de rang :  1 et 1 	 A : ac :: ad :: bc ::   de rang : 2 et 2 *)
assert(Habaebcbdbecdcedem3 : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (ac :: ad :: bc :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ac :: ad :: bc :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ac :: ad :: bc :: nil) ++ (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ac :: ad :: bc :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (bc :: nil) 4 1 2 Habacadaebcbdbecdcedemtmp Hbcmtmp HacadbcMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 5 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: ad :: bc :: bd ::   de rang : 3 et 3 *)
assert(Habaebcbdbecdcedem4 : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4).
{
	assert(Habadbcbdeq : rk(ab :: ad :: bc :: bd :: nil) = 3) by (apply Labadbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabadbcbdMtmp : rk(ab :: ad :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habadbcbdeq HabadbcbdM3).
	assert(Habadaebcbdbecdcedemtmp : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habadaebcbdbecdcedeeq Habadaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ad :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: ad :: bc :: bd :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bc :: bd :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ab :: ad :: bc :: bd :: nil) ++ (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habadaebcbdbecdcedemtmp;try rewrite HT2 in Habadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: ad :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habadaebcbdbecdcedemtmp Habbcbdmtmp HabadbcbdMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abaebcbdbecede requis par la preuve de (?)abaebcbdbecede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebcbdbecede requis par la preuve de (?)abaebcbdbecede pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habaebcbdbecedem3 : rk(ab :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : ab :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 5 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: bc :: bd :: cd ::   de rang : 3 et 3 *)
assert(Habaebcbdbecedem4 : rk(ab :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 4).
{
	assert(Habbcbdcdeq : rk(ab :: bc :: bd :: cd :: nil) = 3) by (apply Labbcbdcd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabbcbdcdMtmp : rk(ab :: bc :: bd :: cd :: nil) <= 3) by (solve_hyps_max Habbcbdcdeq HabbcbdcdM3).
	assert(Habaebcbdbecdcedemtmp : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habaebcbdbecdcedeeq Habaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: bc :: bd :: cd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: cd :: ab :: ae :: bc :: bd :: be :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: bd :: cd :: ab :: ae :: bc :: bd :: be :: ce :: de :: nil) ((ab :: bc :: bd :: cd :: nil) ++ (ab :: ae :: bc :: bd :: be :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habaebcbdbecdcedemtmp;try rewrite HT2 in Habaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: bc :: bd :: cd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habaebcbdbecdcedemtmp Habbcbdmtmp HabbcbdcdMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabaebcbdbecedeM4 : rk(ab :: ae :: bc :: bd :: be :: ce :: de :: nil) <= 4).
{
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(HabaebdbedeMtmp : rk(ab :: ae :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habaebdbedeeq HabaebdbedeM3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (bc :: be :: ce :: nil) (ab :: ae :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: ce :: de :: nil) (bc :: be :: ce :: ab :: ae :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: be :: ce :: ab :: ae :: bd :: be :: de :: nil) ((bc :: be :: ce :: nil) ++ (ab :: ae :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: be :: ce :: nil) (ab :: ae :: bd :: be :: de :: nil) (be :: nil) 2 3 1 HbcbeceMtmp HabaebdbedeMtmp Hbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HabaebcbdbecedeM : rk(ab :: ae :: bc :: bd :: be :: ce :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habaebcbdbecedem : rk(ab :: ae :: bc :: bd :: be :: ce :: de ::  nil) >= 1) by (solve_hyps_min Habaebcbdbecedeeq Habaebcbdbecedem1).
intuition.
Qed.

(* dans constructLemma(), requis par Labaebcbdbece *)
(* dans la couche 0 *)
Lemma Lbcbdbede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: bd :: be :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbdbede requis par la preuve de (?)abbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbdbedeM3 : rk(ab :: bd :: be :: de :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bd :: be :: de :: nil) (ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bd :: be :: de :: nil) ((ab :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HabMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbede requis par la preuve de (?)abbcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbedeM4 : rk(ab :: bc :: bd :: be :: de :: nil) <= 4).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HabbdbedeMtmp : rk(ab :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Habbdbedeeq HabbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (ab :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (bc :: ab :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: ab :: bd :: be :: de :: nil) ((bc :: nil) ++ (ab :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (ab :: bd :: be :: de :: nil) (nil) 1 3 0 HbcMtmp HabbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbedem3 : rk(ab :: bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbede requis par la preuve de (?)bcbdbede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbedeM3 : rk(bc :: bd :: be :: de :: nil) <= 3).
{
	assert(HbcMtmp : rk(bc :: nil) <= 1) by (solve_hyps_max Hbceq HbcM1).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bc :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: de :: nil) ((bc :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: nil) (bd :: be :: de :: nil) (nil) 1 2 0 HbcMtmp HbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: de ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: be ::   de rang : 1 et 2 *)
assert(Hbcbdbedem2 : rk(bc :: bd :: be :: de :: nil) >= 2).
{
	assert(HabbeMtmp : rk(ab :: be :: nil) <= 2) by (solve_hyps_max Habbeeq HabbeM2).
	assert(Habbcbdbedemtmp : rk(ab :: bc :: bd :: be :: de :: nil) >= 3) by (solve_hyps_min Habbcbdbedeeq Habbcbdbedem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: de :: nil) (ab :: be :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bc :: bd :: be :: de :: nil) ((ab :: be :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbedemtmp;try rewrite HT2 in Habbcbdbedemtmp.
	assert(HT := rule_4 (ab :: be :: nil) (bc :: bd :: be :: de :: nil) (be :: nil) 3 1 2 Habbcbdbedemtmp Hbemtmp HabbeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hbcbdbedem3 : rk(bc :: bd :: be :: de :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (bc :: bd :: be :: de :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

assert(HbcbdbedeM : rk(bc :: bd :: be :: de ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM4).
assert(Hbcbdbedem : rk(bc :: bd :: be :: de ::  nil) >= 1) by (solve_hyps_min Hbcbdbedeeq Hbcbdbedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labaebcbdbece : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: ae :: bc :: bd :: be :: ce ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abaebcbdbece requis par la preuve de (?)abaebcbdbece pour la règle 2  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour bcbdbece requis par la preuve de (?)abaebcbdbece pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbcbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbece requis par la preuve de (?)abbcbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbcbeceM3 : rk(ab :: bc :: be :: ce :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: be :: ce :: nil) (ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: be :: ce :: nil) ((ab :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bc :: be :: ce :: nil) (nil) 1 2 0 HabMtmp HbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbeceM4 : rk(ab :: bc :: bd :: be :: ce :: nil) <= 4).
{
	assert(HbdMtmp : rk(bd :: nil) <= 1) by (solve_hyps_max Hbdeq HbdM1).
	assert(HabbcbeceMtmp : rk(ab :: bc :: be :: ce :: nil) <= 3) by (solve_hyps_max Habbcbeceeq HabbcbeceM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bd :: nil) (ab :: bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (bd :: ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bd :: ab :: bc :: be :: ce :: nil) ((bd :: nil) ++ (ab :: bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bd :: nil) (ab :: bc :: be :: ce :: nil) (nil) 1 3 0 HbdMtmp HabbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbecem3 : rk(ab :: bc :: bd :: be :: ce :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour abbe requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour bcbdbece requis par la preuve de (?)bcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour bcbdbece requis par la preuve de (?)bcbdbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbcbdbeceM3 : rk(bc :: bd :: be :: ce :: nil) <= 3).
{
	assert(HbdMtmp : rk(bd :: nil) <= 1) by (solve_hyps_max Hbdeq HbdM1).
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bd :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: ce :: nil) (bd :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bd :: bc :: be :: ce :: nil) ((bd :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bd :: nil) (bc :: be :: ce :: nil) (nil) 1 2 0 HbdMtmp HbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 3) *)
(* marque des antécédents AUB AiB A: 5 -2 et 5*)
(* ensembles concernés AUB : ab :: bc :: bd :: be :: ce ::  de rang :  3 et 4 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: be ::   de rang : 1 et 2 *)
assert(Hbcbdbecem2 : rk(bc :: bd :: be :: ce :: nil) >= 2).
{
	assert(HabbeMtmp : rk(ab :: be :: nil) <= 2) by (solve_hyps_max Habbeeq HabbeM2).
	assert(Habbcbdbecemtmp : rk(ab :: bc :: bd :: be :: ce :: nil) >= 3) by (solve_hyps_min Habbcbdbeceeq Habbcbdbecem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: be :: nil) (bc :: bd :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (ab :: be :: bc :: bd :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: be :: bc :: bd :: be :: ce :: nil) ((ab :: be :: nil) ++ (bc :: bd :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbecemtmp;try rewrite HT2 in Habbcbdbecemtmp.
	assert(HT := rule_4 (ab :: be :: nil) (bc :: bd :: be :: ce :: nil) (be :: nil) 3 1 2 Habbcbdbecemtmp Hbemtmp HabbeMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abaebcbdbece requis par la preuve de (?)abaebcbdbece pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebcbdbece requis par la preuve de (?)abaebcbdbece pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habaebcbdbecem3 : rk(ab :: ae :: bc :: bd :: be :: ce :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: ce :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HabaebcbdbeceM4 : rk(ab :: ae :: bc :: bd :: be :: ce :: nil) <= 4).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(HbcbdbeceMtmp : rk(bc :: bd :: be :: ce :: nil) <= 3) by (solve_hyps_max Hbcbdbeceeq HbcbdbeceM3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: ae :: be :: nil) (bc :: bd :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: ce :: nil) (ab :: ae :: be :: bc :: bd :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: bc :: bd :: be :: ce :: nil) ((ab :: ae :: be :: nil) ++ (bc :: bd :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: ae :: be :: nil) (bc :: bd :: be :: ce :: nil) (be :: nil) 2 3 1 HabaebeMtmp HbcbdbeceMtmp Hbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 -4 et 4*)
assert(Habaebcbdbecem4 : rk(ab :: ae :: bc :: bd :: be :: ce :: nil) >= 4).
{
	assert(Hbcbdbedeeq : rk(bc :: bd :: be :: de :: nil) = 3) by (apply Lbcbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbedeMtmp : rk(bc :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM3).
	assert(Habaebcbdbecedeeq : rk(ab :: ae :: bc :: bd :: be :: ce :: de :: nil) = 4) by (apply Labaebcbdbecede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habaebcbdbecedemtmp : rk(ab :: ae :: bc :: bd :: be :: ce :: de :: nil) >= 4) by (solve_hyps_min Habaebcbdbecedeeq Habaebcbdbecedem4).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (ab :: ae :: bc :: bd :: be :: ce :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: ce :: de :: nil) (ab :: ae :: bc :: bd :: be :: ce :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: bc :: bd :: be :: ce :: bc :: bd :: be :: de :: nil) ((ab :: ae :: bc :: bd :: be :: ce :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habaebcbdbecedemtmp;try rewrite HT2 in Habaebcbdbecedemtmp.
	assert(HT := rule_2 (ab :: ae :: bc :: bd :: be :: ce :: nil) (bc :: bd :: be :: de :: nil) (bc :: bd :: be :: nil) 4 3 3 Habaebcbdbecedemtmp Hbcbdbemtmp HbcbdbedeMtmp Hincl);apply HT.
}

assert(HabaebcbdbeceM : rk(ab :: ae :: bc :: bd :: be :: ce ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habaebcbdbecem : rk(ab :: ae :: bc :: bd :: be :: ce ::  nil) >= 1) by (solve_hyps_min Habaebcbdbeceeq Habaebcbdbecem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labbcbdbece : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: bc :: bd :: be :: ce ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour abbcbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbece requis par la preuve de (?)abbcbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HabbcbeceM3 : rk(ab :: bc :: be :: ce :: nil) <= 3).
{
	assert(HabMtmp : rk(ab :: nil) <= 1) by (solve_hyps_max Habeq HabM1).
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ab :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: be :: ce :: nil) (ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: be :: ce :: nil) ((ab :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ab :: nil) (bc :: be :: ce :: nil) (nil) 1 2 0 HabMtmp HbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abbcbdbece requis par la preuve de (?)abbcbdbece pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HabbcbdbeceM4 : rk(ab :: bc :: bd :: be :: ce :: nil) <= 4).
{
	assert(HbdMtmp : rk(bd :: nil) <= 1) by (solve_hyps_max Hbdeq HbdM1).
	assert(HabbcbeceMtmp : rk(ab :: bc :: be :: ce :: nil) <= 3) by (solve_hyps_max Habbcbeceeq HabbcbeceM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (bd :: nil) (ab :: bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (bd :: ab :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bd :: ab :: bc :: be :: ce :: nil) ((bd :: nil) ++ (ab :: bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bd :: nil) (ab :: bc :: be :: ce :: nil) (nil) 1 3 0 HbdMtmp HabbcbeceMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbecem3 : rk(ab :: bc :: bd :: be :: ce :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: ce :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 4) *)
(* marque des antécédents AUB AiB A: 4 4 et -4*)
(* ensembles concernés AUB : ab :: ae :: bc :: bd :: be :: ce ::  de rang :  4 et 4 	 AiB : ab :: be ::  de rang :  2 et 2 	 A : ab :: ae :: be ::   de rang : 2 et 2 *)
assert(Habbcbdbecem4 : rk(ab :: bc :: bd :: be :: ce :: nil) >= 4).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Habaebcbdbeceeq : rk(ab :: ae :: bc :: bd :: be :: ce :: nil) = 4) by (apply Labaebcbdbece with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habaebcbdbecemtmp : rk(ab :: ae :: bc :: bd :: be :: ce :: nil) >= 4) by (solve_hyps_min Habaebcbdbeceeq Habaebcbdbecem4).
	assert(Habbeeq : rk(ab :: be :: nil) = 2) by (apply Labbe with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habbemtmp : rk(ab :: be :: nil) >= 2) by (solve_hyps_min Habbeeq Habbem2).
	assert(Hincl : incl (ab :: be :: nil) (list_inter (ab :: ae :: be :: nil) (ab :: bc :: bd :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: ce :: nil) (ab :: ae :: be :: ab :: bc :: bd :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: ab :: bc :: bd :: be :: ce :: nil) ((ab :: ae :: be :: nil) ++ (ab :: bc :: bd :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habaebcbdbecemtmp;try rewrite HT2 in Habaebcbdbecemtmp.
	assert(HT := rule_4 (ab :: ae :: be :: nil) (ab :: bc :: bd :: be :: ce :: nil) (ab :: be :: nil) 4 2 2 Habaebcbdbecemtmp Habbemtmp HabaebeMtmp Hincl); apply HT.
}

assert(HabbcbdbeceM : rk(ab :: bc :: bd :: be :: ce ::  nil) <= 5) by (apply rk_upper_dim).
assert(Habbcbdbecem : rk(ab :: bc :: bd :: be :: ce ::  nil) >= 1) by (solve_hyps_min Habbcbdbeceeq Habbcbdbecem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbcbdbecdde : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: bd :: be :: cd :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour bcbdbecdde requis par la preuve de (?)bcbdbecdde pour la règle 1  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour bcbdbecdde requis par la preuve de (?)bcbdbecdde pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 5 pour bcbdbecdde requis par la preuve de (?)bcbdbecdde pour la règle 5  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abaebcbdbecdde requis par la preuve de (?)bcbdbecdde pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebcbdbecdde requis par la preuve de (?)abaebcbdbecdde pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habaebcbdbecddem3 : rk(ab :: ae :: bc :: bd :: be :: cd :: de :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: de :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour bcbdbecdde requis par la preuve de (?)bcbdbecdde pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 2 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : ab :: ae :: bc :: bd :: be :: cd :: de ::  de rang :  3 et 5 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: ae :: be ::   de rang : 2 et 2 *)
assert(Hbcbdbecddem2 : rk(bc :: bd :: be :: cd :: de :: nil) >= 2).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Habaebcbdbecddemtmp : rk(ab :: ae :: bc :: bd :: be :: cd :: de :: nil) >= 3) by (solve_hyps_min Habaebcbdbecddeeq Habaebcbdbecddem3).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: ae :: be :: nil) (bc :: bd :: be :: cd :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: cd :: de :: nil) (ab :: ae :: be :: bc :: bd :: be :: cd :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: bc :: bd :: be :: cd :: de :: nil) ((ab :: ae :: be :: nil) ++ (bc :: bd :: be :: cd :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habaebcbdbecddemtmp;try rewrite HT2 in Habaebcbdbecddemtmp.
	assert(HT := rule_4 (ab :: ae :: be :: nil) (bc :: bd :: be :: cd :: de :: nil) (be :: nil) 3 1 2 Habaebcbdbecddemtmp Hbemtmp HabaebeMtmp Hincl); apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hbcbdbecddem3 : rk(bc :: bd :: be :: cd :: de :: nil) >= 3).
{
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (bc :: bd :: be :: nil) (bc :: bd :: be :: cd :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (bc :: bd :: be :: nil) (bc :: bd :: be :: cd :: de :: nil) 3 3 Hbcbdbemtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 4 et 5*)
assert(HbcbdbecddeM4 : rk(bc :: bd :: be :: cd :: de :: nil) <= 4).
{
	assert(HcdMtmp : rk(cd :: nil) <= 1) by (solve_hyps_max Hcdeq HcdM1).
	assert(Hbcbdbedeeq : rk(bc :: bd :: be :: de :: nil) = 3) by (apply Lbcbdbede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbedeMtmp : rk(bc :: bd :: be :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbedeeq HbcbdbedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (cd :: nil) (bc :: bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: cd :: de :: nil) (cd :: bc :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (cd :: bc :: bd :: be :: de :: nil) ((cd :: nil) ++ (bc :: bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (cd :: nil) (bc :: bd :: be :: de :: nil) (nil) 1 3 0 HcdMtmp HbcbdbedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HbcbdbecddeM3 : rk(bc :: bd :: be :: cd :: de :: nil) <= 3).
{
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(HbdbedeMtmp : rk(bd :: be :: de :: nil) <= 2) by (solve_hyps_max Hbdbedeeq HbdbedeM2).
	assert(Hbdmtmp : rk(bd :: nil) >= 1) by (solve_hyps_min Hbdeq Hbdm1).
	assert(Hincl : incl (bd :: nil) (list_inter (bc :: bd :: cd :: nil) (bd :: be :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: cd :: de :: nil) (bc :: bd :: cd :: bd :: be :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: cd :: bd :: be :: de :: nil) ((bc :: bd :: cd :: nil) ++ (bd :: be :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: bd :: cd :: nil) (bd :: be :: de :: nil) (bd :: nil) 2 2 1 HbcbdcdMtmp HbdbedeMtmp Hbdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HbcbdbecddeM : rk(bc :: bd :: be :: cd :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Hbcbdbecddem : rk(bc :: bd :: be :: cd :: de ::  nil) >= 1) by (solve_hyps_min Hbcbdbecddeeq Hbcbdbecddem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lacadcdcede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ac :: ad :: cd :: ce :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour acadcdcede requis par la preuve de (?)acadcdcede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour acadcdcede requis par la preuve de (?)acadcdcede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acadcdcede requis par la preuve de (?)acadcdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour accdcede requis par la preuve de (?)acadcdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour accdcede requis par la preuve de (?)accdcede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HaccdcedeM3 : rk(ac :: cd :: ce :: de :: nil) <= 3).
{
	assert(HacMtmp : rk(ac :: nil) <= 1) by (solve_hyps_max Haceq HacM1).
	assert(HcdcedeMtmp : rk(cd :: ce :: de :: nil) <= 2) by (solve_hyps_max Hcdcedeeq HcdcedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ac :: nil) (cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: cd :: ce :: de :: nil) (ac :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: cd :: ce :: de :: nil) ((ac :: nil) ++ (cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: nil) (cd :: ce :: de :: nil) (nil) 1 2 0 HacMtmp HcdcedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour acadcdcede requis par la preuve de (?)acadcdcede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 5 et 5*)
assert(HacadcdcedeM4 : rk(ac :: ad :: cd :: ce :: de :: nil) <= 4).
{
	assert(HadMtmp : rk(ad :: nil) <= 1) by (solve_hyps_max Hadeq HadM1).
	assert(HaccdcedeMtmp : rk(ac :: cd :: ce :: de :: nil) <= 3) by (solve_hyps_max Haccdcedeeq HaccdcedeM3).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ad :: nil) (ac :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: cd :: ce :: de :: nil) (ad :: ac :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ad :: ac :: cd :: ce :: de :: nil) ((ad :: nil) ++ (ac :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ad :: nil) (ac :: cd :: ce :: de :: nil) (nil) 1 3 0 HadMtmp HaccdcedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 -4 et -2*)
assert(HacadcdcedeM3 : rk(ac :: ad :: cd :: ce :: de :: nil) <= 3).
{
	assert(HacadcdMtmp : rk(ac :: ad :: cd :: nil) <= 2) by (solve_hyps_max Hacadcdeq HacadcdM2).
	assert(HcdcedeMtmp : rk(cd :: ce :: de :: nil) <= 2) by (solve_hyps_max Hcdcedeeq HcdcedeM2).
	assert(Hcdmtmp : rk(cd :: nil) >= 1) by (solve_hyps_min Hcdeq Hcdm1).
	assert(Hincl : incl (cd :: nil) (list_inter (ac :: ad :: cd :: nil) (cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: cd :: ce :: de :: nil) (ac :: ad :: cd :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: cd :: cd :: ce :: de :: nil) ((ac :: ad :: cd :: nil) ++ (cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: ad :: cd :: nil) (cd :: ce :: de :: nil) (cd :: nil) 2 2 1 HacadcdMtmp HcdcedeMtmp Hcdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadcdcedem2 : rk(ac :: ad :: cd :: ce :: de :: nil) >= 2).
{
	assert(Hacadcdmtmp : rk(ac :: ad :: cd :: nil) >= 2) by (solve_hyps_min Hacadcdeq Hacadcdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: cd :: nil) (ac :: ad :: cd :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: cd :: nil) (ac :: ad :: cd :: ce :: de :: nil) 2 2 Hacadcdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadcdcedem3 : rk(ac :: ad :: cd :: ce :: de :: nil) >= 3).
{
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: de :: nil) (ac :: ad :: cd :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: de :: nil) (ac :: ad :: cd :: ce :: de :: nil) 3 3 Hacaddemtmp Hcomp Hincl);apply HT.
}

assert(HacadcdcedeM : rk(ac :: ad :: cd :: ce :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Hacadcdcedem : rk(ac :: ad :: cd :: ce :: de ::  nil) >= 1) by (solve_hyps_min Hacadcdcedeeq Hacadcdcedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lacadaecdcede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ac :: ad :: ae :: cd :: ce :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour acadaecdcede requis par la preuve de (?)acadaecdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 2 <= rg <= 4 pour acadaecdcede requis par la preuve de (?)acadaecdcede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour acadaecdcede requis par la preuve de (?)acadaecdcede pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour aecdcede requis par la preuve de (?)acadaecdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour aecdcede requis par la preuve de (?)aecdcede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HaecdcedeM3 : rk(ae :: cd :: ce :: de :: nil) <= 3).
{
	assert(HaeMtmp : rk(ae :: nil) <= 1) by (solve_hyps_max Haeeq HaeM1).
	assert(HcdcedeMtmp : rk(cd :: ce :: de :: nil) <= 2) by (solve_hyps_max Hcdcedeeq HcdcedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (ae :: nil) (cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ae :: cd :: ce :: de :: nil) (ae :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ae :: cd :: ce :: de :: nil) ((ae :: nil) ++ (cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ae :: nil) (cd :: ce :: de :: nil) (nil) 1 2 0 HaeMtmp HcdcedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour acadaecdcede requis par la preuve de (?)acadaecdcede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HacadaecdcedeM4 : rk(ac :: ad :: ae :: cd :: ce :: de :: nil) <= 4).
{
	assert(HacadcdMtmp : rk(ac :: ad :: cd :: nil) <= 2) by (solve_hyps_max Hacadcdeq HacadcdM2).
	assert(HaecdcedeMtmp : rk(ae :: cd :: ce :: de :: nil) <= 3) by (solve_hyps_max Haecdcedeeq HaecdcedeM3).
	assert(Hcdmtmp : rk(cd :: nil) >= 1) by (solve_hyps_min Hcdeq Hcdm1).
	assert(Hincl : incl (cd :: nil) (list_inter (ac :: ad :: cd :: nil) (ae :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: ae :: cd :: ce :: de :: nil) (ac :: ad :: cd :: ae :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: cd :: ae :: cd :: ce :: de :: nil) ((ac :: ad :: cd :: nil) ++ (ae :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: ad :: cd :: nil) (ae :: cd :: ce :: de :: nil) (cd :: nil) 2 3 1 HacadcdMtmp HaecdcedeMtmp Hcdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadaecdcedem2 : rk(ac :: ad :: ae :: cd :: ce :: de :: nil) >= 2).
{
	assert(Hacadcdmtmp : rk(ac :: ad :: cd :: nil) >= 2) by (solve_hyps_min Hacadcdeq Hacadcdm2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: cd :: nil) (ac :: ad :: ae :: cd :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: cd :: nil) (ac :: ad :: ae :: cd :: ce :: de :: nil) 2 2 Hacadcdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Hacadaecdcedem3 : rk(ac :: ad :: ae :: cd :: ce :: de :: nil) >= 3).
{
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ac :: ad :: de :: nil) (ac :: ad :: ae :: cd :: ce :: de :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ac :: ad :: de :: nil) (ac :: ad :: ae :: cd :: ce :: de :: nil) 3 3 Hacaddemtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et -4*)
assert(HacadaecdcedeM3 : rk(ac :: ad :: ae :: cd :: ce :: de :: nil) <= 3).
{
	assert(Hacadaedeeq : rk(ac :: ad :: ae :: de :: nil) = 3) by (apply Lacadaede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HacadaedeMtmp : rk(ac :: ad :: ae :: de :: nil) <= 3) by (solve_hyps_max Hacadaedeeq HacadaedeM3).
	assert(Hacadcdcedeeq : rk(ac :: ad :: cd :: ce :: de :: nil) = 3) by (apply Lacadcdcede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HacadcdcedeMtmp : rk(ac :: ad :: cd :: ce :: de :: nil) <= 3) by (solve_hyps_max Hacadcdcedeeq HacadcdcedeM3).
	assert(Hacaddemtmp : rk(ac :: ad :: de :: nil) >= 3) by (solve_hyps_min Hacaddeeq Hacaddem3).
	assert(Hincl : incl (ac :: ad :: de :: nil) (list_inter (ac :: ad :: ae :: de :: nil) (ac :: ad :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ac :: ad :: ae :: cd :: ce :: de :: nil) (ac :: ad :: ae :: de :: ac :: ad :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: ae :: de :: ac :: ad :: cd :: ce :: de :: nil) ((ac :: ad :: ae :: de :: nil) ++ (ac :: ad :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (ac :: ad :: ae :: de :: nil) (ac :: ad :: cd :: ce :: de :: nil) (ac :: ad :: de :: nil) 3 3 3 HacadaedeMtmp HacadcdcedeMtmp Hacaddemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HacadaecdcedeM : rk(ac :: ad :: ae :: cd :: ce :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Hacadaecdcedem : rk(ac :: ad :: ae :: cd :: ce :: de ::  nil) >= 1) by (solve_hyps_min Hacadaecdcedeeq Hacadaecdcedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Lbcbdbecdcede : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(bc :: bd :: be :: cd :: ce :: de ::  nil) = 3.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour bcbdbecdcede requis par la preuve de (?)bcbdbecdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour becdcede requis par la preuve de (?)bcbdbecdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour becdcede requis par la preuve de (?)becdcede pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -2 -4 et 5*)
assert(HbecdcedeM3 : rk(be :: cd :: ce :: de :: nil) <= 3).
{
	assert(HbeMtmp : rk(be :: nil) <= 1) by (solve_hyps_max Hbeeq HbeM1).
	assert(HcdcedeMtmp : rk(cd :: ce :: de :: nil) <= 2) by (solve_hyps_max Hcdcedeeq HcdcedeM2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (be :: nil) (cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (be :: cd :: ce :: de :: nil) (be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (be :: cd :: ce :: de :: nil) ((be :: nil) ++ (cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (be :: nil) (cd :: ce :: de :: nil) (nil) 1 2 0 HbeMtmp HcdcedeMtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour bcbdbecdcede requis par la preuve de (?)bcbdbecdcede pour la règle 1  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)bcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 4 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 2 pour adbc requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abadaebcbdbecdcede requis par la preuve de (?)abadaebcbdbecdcede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: -4 5 et -4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : ad :: bc ::  de rang :  1 et 2 	 A : ac :: ad :: bc ::   de rang : 2 et 2 *)
assert(Habadaebcbdbecdcedem3 : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Hadbcmtmp : rk(ad :: bc :: nil) >= 1) by (solve_hyps_min Hadbceq Hadbcm1).
	assert(Hincl : incl (ad :: bc :: nil) (list_inter (ac :: ad :: bc :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ac :: ad :: bc :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ac :: ad :: bc :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ac :: ad :: bc :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ad :: bc :: nil) 4 1 2 Habacadaebcbdbecdcedemtmp Hadbcmtmp HacadbcMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: -4 -4 et 4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: ac :: bc :: bd ::   de rang : 3 et 3 *)
assert(Habadaebcbdbecdcedem4 : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4).
{
	assert(Habacbcbdeq : rk(ab :: ac :: bc :: bd :: nil) = 3) by (apply Labacbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabacbcbdMtmp : rk(ab :: ac :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habacbcbdeq HabacbcbdM3).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ac :: bc :: bd :: ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ab :: ac :: bc :: bd :: nil) ++ (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: ac :: bc :: bd :: nil) (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habacadaebcbdbecdcedemtmp Habbcbdmtmp HabacbcbdMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 3 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour abaebcbdbecdcede requis par la preuve de (?)abaebcbdbecdcede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: -4 -2 et -4*)
(* ensembles concernés AUB : ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 4 	 AiB : bc ::  de rang :  1 et 1 	 A : ac :: ad :: bc ::   de rang : 2 et 2 *)
assert(Habaebcbdbecdcedem3 : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 3).
{
	assert(HacadbcMtmp : rk(ac :: ad :: bc :: nil) <= 2) by (solve_hyps_max Hacadbceq HacadbcM2).
	assert(Habacadaebcbdbecdcedemtmp : rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habacadaebcbdbecdcedeeq Habacadaebcbdbecdcedem4).
	assert(Hbcmtmp : rk(bc :: nil) >= 1) by (solve_hyps_min Hbceq Hbcm1).
	assert(Hincl : incl (bc :: nil) (list_inter (ac :: ad :: bc :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ac :: ad :: bc :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ac :: ad :: bc :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ac :: ad :: bc :: nil) ++ (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habacadaebcbdbecdcedemtmp;try rewrite HT2 in Habacadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ac :: ad :: bc :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (bc :: nil) 4 1 2 Habacadaebcbdbecdcedemtmp Hbcmtmp HacadbcMtmp Hincl); apply HT.
}

(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 4 et 5) *)
(* marque des antécédents AUB AiB A: 5 -4 et 4*)
(* ensembles concernés AUB : ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 5 	 AiB : ab :: bc :: bd ::  de rang :  3 et 3 	 A : ab :: ad :: bc :: bd ::   de rang : 3 et 3 *)
assert(Habaebcbdbecdcedem4 : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4).
{
	assert(Habadbcbdeq : rk(ab :: ad :: bc :: bd :: nil) = 3) by (apply Labadbcbd with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HabadbcbdMtmp : rk(ab :: ad :: bc :: bd :: nil) <= 3) by (solve_hyps_max Habadbcbdeq HabadbcbdM3).
	assert(Habadaebcbdbecdcedemtmp : rk(ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habadaebcbdbecdcedeeq Habadaebcbdbecdcedem4).
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (list_inter (ab :: ad :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: ad :: bc :: bd :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ad :: bc :: bd :: ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ab :: ad :: bc :: bd :: nil) ++ (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habadaebcbdbecdcedemtmp;try rewrite HT2 in Habadaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: ad :: bc :: bd :: nil) (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: bc :: bd :: nil) 4 3 3 Habadaebcbdbecdcedemtmp Habbcbdmtmp HabadbcbdMtmp Hincl); apply HT.
}

(* dans constructProofaux(), preuve de 1 <= rg <= 5 pour bcbdbecdcede requis par la preuve de (?)bcbdbecdcede pour la règle 4  *)
(* Application de la règle 4 code (7 ou 8 dans la thèse) concerne B (rang 3 et 5) *)
(* marque des antécédents AUB AiB A: 5 -2 et -4*)
(* ensembles concernés AUB : ab :: ae :: bc :: bd :: be :: cd :: ce :: de ::  de rang :  4 et 5 	 AiB : be ::  de rang :  1 et 1 	 A : ab :: ae :: be ::   de rang : 2 et 2 *)
assert(Hbcbdbecdcedem3 : rk(bc :: bd :: be :: cd :: ce :: de :: nil) >= 3).
{
	assert(HabaebeMtmp : rk(ab :: ae :: be :: nil) <= 2) by (solve_hyps_max Habaebeeq HabaebeM2).
	assert(Habaebcbdbecdcedemtmp : rk(ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) >= 4) by (solve_hyps_min Habaebcbdbecdcedeeq Habaebcbdbecdcedem4).
	assert(Hbemtmp : rk(be :: nil) >= 1) by (solve_hyps_min Hbeeq Hbem1).
	assert(Hincl : incl (be :: nil) (list_inter (ab :: ae :: be :: nil) (bc :: bd :: be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: ae :: bc :: bd :: be :: cd :: ce :: de :: nil) (ab :: ae :: be :: bc :: bd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: ae :: be :: bc :: bd :: be :: cd :: ce :: de :: nil) ((ab :: ae :: be :: nil) ++ (bc :: bd :: be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habaebcbdbecdcedemtmp;try rewrite HT2 in Habaebcbdbecdcedemtmp.
	assert(HT := rule_4 (ab :: ae :: be :: nil) (bc :: bd :: be :: cd :: ce :: de :: nil) (be :: nil) 4 1 2 Habaebcbdbecdcedemtmp Hbemtmp HabaebeMtmp Hincl); apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : -4 5 et -2*)
assert(HbcbdbecdcedeM4 : rk(bc :: bd :: be :: cd :: ce :: de :: nil) <= 4).
{
	assert(HbcbdcdMtmp : rk(bc :: bd :: cd :: nil) <= 2) by (solve_hyps_max Hbcbdcdeq HbcbdcdM2).
	assert(HbecdcedeMtmp : rk(be :: cd :: ce :: de :: nil) <= 3) by (solve_hyps_max Hbecdcedeeq HbecdcedeM3).
	assert(Hcdmtmp : rk(cd :: nil) >= 1) by (solve_hyps_min Hcdeq Hcdm1).
	assert(Hincl : incl (cd :: nil) (list_inter (bc :: bd :: cd :: nil) (be :: cd :: ce :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: cd :: ce :: de :: nil) (bc :: bd :: cd :: be :: cd :: ce :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: cd :: be :: cd :: ce :: de :: nil) ((bc :: bd :: cd :: nil) ++ (be :: cd :: ce :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: bd :: cd :: nil) (be :: cd :: ce :: de :: nil) (cd :: nil) 2 3 1 HbcbdcdMtmp HbecdcedeMtmp Hcdmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et -4*)
assert(HbcbdbecdcedeM3 : rk(bc :: bd :: be :: cd :: ce :: de :: nil) <= 3).
{
	assert(Hbcbdbeceeq : rk(bc :: bd :: be :: ce :: nil) = 3) by (apply Lbcbdbece with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbeceMtmp : rk(bc :: bd :: be :: ce :: nil) <= 3) by (solve_hyps_max Hbcbdbeceeq HbcbdbeceM3).
	assert(Hbcbdbecddeeq : rk(bc :: bd :: be :: cd :: de :: nil) = 3) by (apply Lbcbdbecdde with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(HbcbdbecddeMtmp : rk(bc :: bd :: be :: cd :: de :: nil) <= 3) by (solve_hyps_max Hbcbdbecddeeq HbcbdbecddeM3).
	assert(Hbcbdbemtmp : rk(bc :: bd :: be :: nil) >= 3) by (solve_hyps_min Hbcbdbeeq Hbcbdbem3).
	assert(Hincl : incl (bc :: bd :: be :: nil) (list_inter (bc :: bd :: be :: ce :: nil) (bc :: bd :: be :: cd :: de :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (bc :: bd :: be :: cd :: ce :: de :: nil) (bc :: bd :: be :: ce :: bc :: bd :: be :: cd :: de :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (bc :: bd :: be :: ce :: bc :: bd :: be :: cd :: de :: nil) ((bc :: bd :: be :: ce :: nil) ++ (bc :: bd :: be :: cd :: de :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (bc :: bd :: be :: ce :: nil) (bc :: bd :: be :: cd :: de :: nil) (bc :: bd :: be :: nil) 3 3 3 HbcbdbeceMtmp HbcbdbecddeMtmp Hbcbdbemtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}

assert(HbcbdbecdcedeM : rk(bc :: bd :: be :: cd :: ce :: de ::  nil) <= 5) by (apply rk_upper_dim).
assert(Hbcbdbecdcedem : rk(bc :: bd :: be :: cd :: ce :: de ::  nil) >= 1) by (solve_hyps_min Hbcbdbecdcedeeq Hbcbdbecdcedem1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma Labbcbdbe : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> rk(ab :: bc :: bd :: be ::  nil) = 4.
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .

(* dans constructProofaux(), preuve de 3 <= rg <= 4 pour abbcbdbe requis par la preuve de (?)abbcbdbe pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour abbcbdbe requis par la preuve de (?)abbcbdbe pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : -4 *)
assert(Habbcbdbem3 : rk(ab :: bc :: bd :: be :: nil) >= 3).
{
	assert(Habbcbdmtmp : rk(ab :: bc :: bd :: nil) >= 3) by (solve_hyps_min Habbcbdeq Habbcbdm3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (ab :: bc :: bd :: nil) (ab :: bc :: bd :: be :: nil) 3 3 Habbcbdmtmp Hcomp Hincl);apply HT.
}

(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et -4*)
assert(Habbcbdbem4 : rk(ab :: bc :: bd :: be :: nil) >= 4).
{
	assert(HbcbeceMtmp : rk(bc :: be :: ce :: nil) <= 2) by (solve_hyps_max Hbcbeceeq HbcbeceM2).
	assert(Habbcbdbeceeq : rk(ab :: bc :: bd :: be :: ce :: nil) = 4) by (apply Labbcbdbece with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Habbcbdbecemtmp : rk(ab :: bc :: bd :: be :: ce :: nil) >= 4) by (solve_hyps_min Habbcbdbeceeq Habbcbdbecem4).
	assert(Hbcbeeq : rk(bc :: be :: nil) = 2) by (apply Lbcbe with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption).
	assert(Hbcbemtmp : rk(bc :: be :: nil) >= 2) by (solve_hyps_min Hbcbeeq Hbcbem2).
	assert(Hincl : incl (bc :: be :: nil) (list_inter (ab :: bc :: bd :: be :: nil) (bc :: be :: ce :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (ab :: bc :: bd :: be :: ce :: nil) (ab :: bc :: bd :: be :: bc :: be :: ce :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (ab :: bc :: bd :: be :: bc :: be :: ce :: nil) ((ab :: bc :: bd :: be :: nil) ++ (bc :: be :: ce :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in Habbcbdbecemtmp;try rewrite HT2 in Habbcbdbecemtmp.
	assert(HT := rule_2 (ab :: bc :: bd :: be :: nil) (bc :: be :: ce :: nil) (bc :: be :: nil) 4 2 2 Habbcbdbecemtmp Hbcbemtmp HbcbeceMtmp Hincl);apply HT.
}

assert(HabbcbdbeM : rk(ab :: bc :: bd :: be ::  nil) <= 4) (* dim : 4 *) by (solve_hyps_max Habbcbdbeeq HabbcbdbeM4).
assert(Habbcbdbem : rk(ab :: bc :: bd :: be ::  nil) >= 1) by (solve_hyps_min Habbcbdbeeq Habbcbdbem1).
intuition.
Qed.

(* dans la couche 0 *)
Theorem def_Conclusion : forall ab ac ad ae bc bd be cd ce de ,
rk(ac :: ad :: bc ::  nil) = 2 -> rk(ab :: ad :: bd ::  nil) = 2 -> rk(ab :: bc :: bd ::  nil) = 3 ->
rk(ab :: ae :: be ::  nil) = 2 -> rk(bc :: bd :: be ::  nil) = 3 -> rk(ac :: ad :: cd ::  nil) = 2 ->
rk(bc :: bd :: cd ::  nil) = 2 -> rk(ac :: ae :: ce ::  nil) = 2 -> rk(bc :: be :: ce ::  nil) = 2 ->
rk(ac :: ad :: de ::  nil) = 3 -> rk(ad :: ae :: de ::  nil) = 2 -> rk(bd :: be :: de ::  nil) = 2 ->
rk(cd :: ce :: de ::  nil) = 2 -> rk(ab :: ac :: ad :: ae :: bc :: bd :: be :: cd :: ce :: de ::  nil) = 4 -> 
	 rk(ab :: bc :: bd :: be ::  nil) = 4  /\ 
	 rk(ac :: ad :: ae :: cd :: ce :: de ::  nil) = 3  /\ 
	 rk(bc :: bd :: be :: cd :: ce :: de ::  nil) = 3  .
Proof.

intros ab ac ad ae bc bd be cd ce de 
Hacadbceq Habadbdeq Habbcbdeq Habaebeeq Hbcbdbeeq Hacadcdeq Hbcbdcdeq Hacaeceeq Hbcbeceeq Hacaddeeq
Hadaedeeq Hbdbedeeq Hcdcedeeq Habacadaebcbdbecdcedeeq .
repeat split.

	apply Labbcbdbe with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption.

	apply Lacadaecdcede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption.

	apply Lbcbdbecdcede with (ab := ab) (ac := ac) (ad := ad) (ae := ae) (bc := bc) (bd := bd) (be := be) (cd := cd) (ce := ce) (de := de) ; assumption.
Qed .
