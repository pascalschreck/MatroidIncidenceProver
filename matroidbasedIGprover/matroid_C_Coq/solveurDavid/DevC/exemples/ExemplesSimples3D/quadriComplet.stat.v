Lemma LP1P2P3P4P5P6 : forall P1 P2 P3 P4 P5 P6 ,
rk(P1 :: P2 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 ::  nil) = 3 -> rk(P3 :: P4 :: P5 ::  nil) = 2 ->
rk(P1 :: P4 :: P6 ::  nil) = 2 -> rk(P2 :: P5 :: P6 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 3.
Proof.

intros P1 P2 P3 P4 P5 P6 
HP1P2P3eq HP1P2P3P4eq HP3P4P5eq HP1P4P6eq HP2P5P6eq .

assert(HP1P2P3P4P6M3 : rk(P1 :: P2 :: P3 :: P4 :: P6 :: nil) <= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 2) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	try assert(HP1P4P6eq : rk(P1 :: P4 :: P6 :: nil) = 2) by (apply LP1P4P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P4P6Mtmp : rk(P1 :: P4 :: P6 :: nil) <= 2) by (solve_hyps_max HP1P4P6eq HP1P4P6M2).
	try assert(HP1eq : rk(P1 :: nil) = 1) by (apply LP1 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1mtmp : rk(P1 :: nil) >= 1) by (solve_hyps_min HP1eq HP1m1).
	assert(Hincl : incl (P1 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P1 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P6 :: nil) (P1 :: P2 :: P3 :: P1 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P1 :: P4 :: P6 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P1 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: nil) (P1 :: P4 :: P6 :: nil) (P1 :: nil) 2 2 1 HP1P2P3Mtmp HP1P4P6Mtmp HP1mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P4P6M1. try clear HP1P4P6M2. try clear HP1P4P6M3. try clear HP1P4P6m4. try clear HP1P4P6m3. try clear HP1P4P6m2. try clear HP1P4P6m1. try clear HP1M1. try clear HP1M2. try clear HP1M3. try clear HP1m4. try clear HP1m3. try clear HP1m2. try clear HP1m1. 

assert(HP1P2P3P4P6m2 : rk(P1 :: P2 :: P3 :: P4 :: P6 :: nil) >= 2).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 2) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P2P3eq HP1P2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil) 2 2 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P6m3 : rk(P1 :: P2 :: P3 :: P4 :: P6 :: nil) >= 3).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 3) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil) 3 3 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP3P4m2 : rk(P3 :: P4 :: nil) >= 2).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 2) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3Mtmp : rk(P1 :: P2 :: P3 :: nil) <= 2) by (solve_hyps_max HP1P2P3eq HP1P2P3M2).
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 3) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m3).
	try assert(HP3eq : rk(P3 :: nil) = 1) by (apply LP3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP3mtmp : rk(P3 :: nil) >= 1) by (solve_hyps_min HP3eq HP3m1).
	assert(Hincl : incl (P3 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P3 :: P4 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: nil) (P3 :: P4 :: nil) (P3 :: nil) 3 1 2 HP1P2P3P4mtmp HP3mtmp HP1P2P3Mtmp Hincl); apply HT.
}
try clear HP3M1. try clear HP3M2. try clear HP3M3. try clear HP3m4. try clear HP3m3. try clear HP3m2. try clear HP3m1. 

assert(HP1P2P3P4P5P6m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 2).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 2) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P2P3eq HP1P2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) 2 2 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3M1. try clear HP1P2P3M2. try clear HP1P2P3M3. try clear HP1P2P3m4. try clear HP1P2P3m3. try clear HP1P2P3m2. try clear HP1P2P3m1. 

assert(HP1P2P3P4P5P6m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 3).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 3) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) 3 3 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4M1. try clear HP1P2P3P4M2. try clear HP1P2P3P4M3. try clear HP1P2P3P4m4. try clear HP1P2P3P4m3. try clear HP1P2P3P4m2. try clear HP1P2P3P4m1. 

assert(HP1P2P3P4P5P6M3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) <= 3).
{
	try assert(HP3P4P5eq : rk(P3 :: P4 :: P5 :: nil) = 2) by (apply LP3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP3P4P5Mtmp : rk(P3 :: P4 :: P5 :: nil) <= 2) by (solve_hyps_max HP3P4P5eq HP3P4P5M2).
	try assert(HP1P2P3P4P6eq : rk(P1 :: P2 :: P3 :: P4 :: P6 :: nil) = 3) by (apply LP1P2P3P4P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP1P2P3P4P6Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P6 :: nil) <= 3) by (solve_hyps_max HP1P2P3P4P6eq HP1P2P3P4P6M3).
	try assert(HP3P4eq : rk(P3 :: P4 :: nil) = 2) by (apply LP3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) ;try assumption).
	assert(HP3P4mtmp : rk(P3 :: P4 :: nil) >= 2) by (solve_hyps_min HP3P4eq HP3P4m2).
	assert(Hincl : incl (P3 :: P4 :: nil) (list_inter (P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P3 :: P4 :: P5 :: P1 :: P2 :: P3 :: P4 :: P6 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P3 :: P4 :: P5 :: P1 :: P2 :: P3 :: P4 :: P6 :: nil) ((P3 :: P4 :: P5 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P6 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P6 :: nil) (P3 :: P4 :: nil) 2 3 2 HP3P4P5Mtmp HP1P2P3P4P6Mtmp HP3P4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP3P4P5M1. try clear HP3P4P5M2. try clear HP3P4P5M3. try clear HP3P4P5m4. try clear HP3P4P5m3. try clear HP3P4P5m2. try clear HP3P4P5m1. try clear HP1P2P3P4P6M1. try clear HP1P2P3P4P6M2. try clear HP1P2P3P4P6M3. try clear HP1P2P3P4P6m4. try clear HP1P2P3P4P6m3. try clear HP1P2P3P4P6m2. try clear HP1P2P3P4P6m1. try clear HP3P4M1. try clear HP3P4M2. try clear HP3P4M3. try clear HP3P4m4. try clear HP3P4m3. try clear HP3P4m2. try clear HP3P4m1. 

assert(HP1P2P3P4P5P6M : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) <= 4) by (apply rk_upper_dim).
assert(HP1P2P3P4P5P6m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) >= 1) by (solve_hyps_min HP1P2P3P4P5P6eq HP1P2P3P4P5P6m1).
intuition.
Qed.

