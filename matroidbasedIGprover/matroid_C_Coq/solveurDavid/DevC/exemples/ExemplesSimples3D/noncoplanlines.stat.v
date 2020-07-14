Lemma LP1P2P3P4P5P6 : forall P1 P2 P3 P4 P5 P6 P7 P8 ,
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 2 -> rk(P5 :: P6 ::  nil) = 2 -> rk(P5 :: P6 :: P7 :: P8 ::  nil) = 2 ->
rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 4.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 
HP1P2P3P4eq HP5P6eq HP5P6P7P8eq HP1P2P3P4P5P6P7P8eq .

assert(HP1P2P3P4P5M3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) <= 3).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 2) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M2).
	try assert(HP5eq : rk(P5 :: nil) = 1) by (apply LP5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP5Mtmp : rk(P5 :: nil) <= 1) by (solve_hyps_max HP5eq HP5M1).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P1 :: P2 :: P3 :: P4 :: nil) (P5 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: nil) ((P1 :: P2 :: P3 :: P4 :: nil) ++ (P5 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: nil) (P5 :: nil) (nil) 2 1 0 HP1P2P3P4Mtmp HP5Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HP1P2P3P4P5m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 2).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 2) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 2 2 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3).
{
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 2) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP5P6P7P8Mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P7P8eq HP5P6P7P8M2).
	try assert(HP1P2P3P4P5P6P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP1P2P3P4P5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P7P8eq HP1P2P3P4P5P6P7P8m4).
	try assert(HP5eq : rk(P5 :: nil) = 1) by (apply LP5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP5mtmp : rk(P5 :: nil) >= 1) by (solve_hyps_min HP5eq HP5m1).
	assert(Hincl : incl (P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P5 :: P6 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P5 :: P6 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P5 :: P6 :: P7 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: nil) 4 1 2 HP1P2P3P4P5P6P7P8mtmp HP5mtmp HP5P6P7P8Mtmp Hincl);apply HT.
}
try clear HP5M1. try clear HP5M2. try clear HP5M3. try clear HP5m4. try clear HP5m3. try clear HP5m2. try clear HP5m1. 

assert(HP1P2P3P4P5P7P8m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) >= 2).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 2) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) 2 2 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5P7P8m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) >= 3).
{
	try assert(HP6eq : rk(P6 :: nil) = 1) by (apply LP6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP6Mtmp : rk(P6 :: nil) <= 1) by (solve_hyps_max HP6eq HP6M1).
	try assert(HP1P2P3P4P5P6P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP1P2P3P4P5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P7P8eq HP1P2P3P4P5P6P7P8m4).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P6 :: P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) ((P6 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8mtmp.
	assert(HT := rule_4 (P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) (nil) 4 0 1 HP1P2P3P4P5P6P7P8mtmp Hmtmp HP6Mtmp Hincl); apply HT.
}
try clear HP6M1. try clear HP6M2. try clear HP6M3. try clear HP6m4. try clear HP6m3. try clear HP6m2. try clear HP6m1. 

assert(HP1P2P3P4P5P6m2 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 2).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 2) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 2) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) 2 2 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4M1. try clear HP1P2P3P4M2. try clear HP1P2P3P4M3. try clear HP1P2P3P4m4. try clear HP1P2P3P4m3. try clear HP1P2P3P4m2. try clear HP1P2P3P4m1. 

assert(HP1P2P3P4P5P6m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 3).
{
	try assert(HP1P2P3P4P5P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) = 4) by (apply LP1P2P3P4P5P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5P7P8Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P5P7P8eq HP1P2P3P4P5P7P8M4).
	try assert(HP1P2P3P4P5P6P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP1P2P3P4P5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P7P8eq HP1P2P3P4P5P6P7P8m4).
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 3) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 4 3 4 HP1P2P3P4P5P6P7P8mtmp HP1P2P3P4P5mtmp HP1P2P3P4P5P7P8Mtmp Hincl);apply HT.
}
try clear HP1P2P3P4P5P7P8M1. try clear HP1P2P3P4P5P7P8M2. try clear HP1P2P3P4P5P7P8M3. try clear HP1P2P3P4P5P7P8m4. try clear HP1P2P3P4P5P7P8m3. try clear HP1P2P3P4P5P7P8m2. try clear HP1P2P3P4P5P7P8m1. try clear HP1P2P3P4P5M1. try clear HP1P2P3P4P5M2. try clear HP1P2P3P4P5M3. try clear HP1P2P3P4P5m4. try clear HP1P2P3P4P5m3. try clear HP1P2P3P4P5m2. try clear HP1P2P3P4P5m1. 

assert(HP1P2P3P4P5P6m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 4).
{
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 2) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP5P6P7P8Mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) <= 2) by (solve_hyps_max HP5P6P7P8eq HP5P6P7P8M2).
	try assert(HP1P2P3P4P5P6P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP1P2P3P4P5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P7P8eq HP1P2P3P4P5P6P7P8m4).
	try assert(HP5P6eq : rk(P5 :: P6 :: nil) = 2) by (apply LP5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP5P6mtmp : rk(P5 :: P6 :: nil) >= 2) by (solve_hyps_min HP5P6eq HP5P6m2).
	assert(Hincl : incl (P5 :: P6 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P5 :: P6 :: P7 :: P8 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P5 :: P6 :: P7 :: P8 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P5 :: P6 :: P7 :: P8 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: nil) 4 2 2 HP1P2P3P4P5P6P7P8mtmp HP5P6mtmp HP5P6P7P8Mtmp Hincl);apply HT.
}
try clear HP5P6P7P8M1. try clear HP5P6P7P8M2. try clear HP5P6P7P8M3. try clear HP5P6P7P8m4. try clear HP5P6P7P8m3. try clear HP5P6P7P8m2. try clear HP5P6P7P8m1. try clear HP5P6M1. try clear HP5P6M2. try clear HP5P6M3. try clear HP5P6m4. try clear HP5P6m3. try clear HP5P6m2. try clear HP5P6m1. try clear HP1P2P3P4P5P6P7P8M1. try clear HP1P2P3P4P5P6P7P8M2. try clear HP1P2P3P4P5P6P7P8M3. try clear HP1P2P3P4P5P6P7P8m4. try clear HP1P2P3P4P5P6P7P8m3. try clear HP1P2P3P4P5P6P7P8m2. try clear HP1P2P3P4P5P6P7P8m1. 

assert(HP1P2P3P4P5P6M : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) <= 4) by (apply rk_upper_dim).
assert(HP1P2P3P4P5P6m : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) >= 1) by (solve_hyps_min HP1P2P3P4P5P6eq HP1P2P3P4P5P6m1).
intuition.
Qed.

