Lemma LP7P8P9 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 ,
rk(P1 :: P2 :: P3 ::  nil) = 3 -> rk(P4 :: P5 :: P6 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P7 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P7 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P8 ::  nil) = 3 ->
rk(P4 :: P5 :: P6 :: P8 ::  nil) = 3 -> rk(P7 :: P8 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P9 ::  nil) = 3 ->
rk(P4 :: P5 :: P6 :: P9 ::  nil) = 3 -> rk(P7 :: P9 ::  nil) = 2 -> rk(P8 :: P9 ::  nil) = 2 ->
rk(P7 :: P8 :: P9 ::  nil) = 2.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 
HP1P2P3eq HP4P5P6eq HP1P2P3P4P5P6eq HP1P2P3P7eq HP4P5P6P7eq HP1P2P3P8eq HP4P5P6P8eq HP7P8eq HP1P2P3P9eq HP4P5P6P9eq
HP7P9eq HP8P9eq .

assert(HP1P2P3P7P9m3 : rk(P1 :: P2 :: P3 :: P7 :: P9 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: P9 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P7P9M3 : rk(P1 :: P2 :: P3 :: P7 :: P9 :: nil) <= 3).
{
	try assert(HP1P2P3P7eq : rk(P1 :: P2 :: P3 :: P7 :: nil) = 3) by (apply LP1P2P3P7 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P7Mtmp : rk(P1 :: P2 :: P3 :: P7 :: nil) <= 3) by (solve_hyps_max HP1P2P3P7eq HP1P2P3P7M3).
	try assert(HP1P2P3P9eq : rk(P1 :: P2 :: P3 :: P9 :: nil) = 3) by (apply LP1P2P3P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P9Mtmp : rk(P1 :: P2 :: P3 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P9eq HP1P2P3P9M3).
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P7 :: P9 :: nil) (P1 :: P2 :: P3 :: P7 :: P1 :: P2 :: P3 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P7 :: P1 :: P2 :: P3 :: P9 :: nil) ((P1 :: P2 :: P3 :: P7 :: nil) ++ (P1 :: P2 :: P3 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P7 :: nil) (P1 :: P2 :: P3 :: P9 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P7Mtmp HP1P2P3P9Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P7M1. try clear HP1P2P3P7M2. try clear HP1P2P3P7M3. try clear HP1P2P3P7m4. try clear HP1P2P3P7m3. try clear HP1P2P3P7m2. try clear HP1P2P3P7m1. try clear HP1P2P3P9M1. try clear HP1P2P3P9M2. try clear HP1P2P3P9M3. try clear HP1P2P3P9m4. try clear HP1P2P3P9m3. try clear HP1P2P3P9m2. try clear HP1P2P3P9m1. 

assert(HP1P2P3P7P8P9m3 : rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P7P8P9M3 : rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP1P2P3P8eq : rk(P1 :: P2 :: P3 :: P8 :: nil) = 3) by (apply LP1P2P3P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P8Mtmp : rk(P1 :: P2 :: P3 :: P8 :: nil) <= 3) by (solve_hyps_max HP1P2P3P8eq HP1P2P3P8M3).
	try assert(HP1P2P3P7P9eq : rk(P1 :: P2 :: P3 :: P7 :: P9 :: nil) = 3) by (apply LP1P2P3P7P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P7P9Mtmp : rk(P1 :: P2 :: P3 :: P7 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P7P9eq HP1P2P3P7P9M3).
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P7 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) (P1 :: P2 :: P3 :: P8 :: P1 :: P2 :: P3 :: P7 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P8 :: P1 :: P2 :: P3 :: P7 :: P9 :: nil) ((P1 :: P2 :: P3 :: P8 :: nil) ++ (P1 :: P2 :: P3 :: P7 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P8 :: nil) (P1 :: P2 :: P3 :: P7 :: P9 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P8Mtmp HP1P2P3P7P9Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P8M1. try clear HP1P2P3P8M2. try clear HP1P2P3P8M3. try clear HP1P2P3P8m4. try clear HP1P2P3P8m3. try clear HP1P2P3P8m2. try clear HP1P2P3P8m1. try clear HP1P2P3P7P9M1. try clear HP1P2P3P7P9M2. try clear HP1P2P3P7P9M3. try clear HP1P2P3P7P9m4. try clear HP1P2P3P7P9m3. try clear HP1P2P3P7P9m2. try clear HP1P2P3P7P9m1. 

assert(HP4P5P6P7P9m3 : rk(P4 :: P5 :: P6 :: P7 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P9 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P7P9M3 : rk(P4 :: P5 :: P6 :: P7 :: P9 :: nil) <= 3).
{
	try assert(HP4P5P6P7eq : rk(P4 :: P5 :: P6 :: P7 :: nil) = 3) by (apply LP4P5P6P7 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6P7Mtmp : rk(P4 :: P5 :: P6 :: P7 :: nil) <= 3) by (solve_hyps_max HP4P5P6P7eq HP4P5P6P7M3).
	try assert(HP4P5P6P9eq : rk(P4 :: P5 :: P6 :: P9 :: nil) = 3) by (apply LP4P5P6P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6P9Mtmp : rk(P4 :: P5 :: P6 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P6P9eq HP4P5P6P9M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P7 :: nil) (P4 :: P5 :: P6 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P7 :: P9 :: nil) (P4 :: P5 :: P6 :: P7 :: P4 :: P5 :: P6 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P7 :: P4 :: P5 :: P6 :: P9 :: nil) ((P4 :: P5 :: P6 :: P7 :: nil) ++ (P4 :: P5 :: P6 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P7 :: nil) (P4 :: P5 :: P6 :: P9 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P7Mtmp HP4P5P6P9Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P7M1. try clear HP4P5P6P7M2. try clear HP4P5P6P7M3. try clear HP4P5P6P7m4. try clear HP4P5P6P7m3. try clear HP4P5P6P7m2. try clear HP4P5P6P7m1. try clear HP4P5P6P9M1. try clear HP4P5P6P9M2. try clear HP4P5P6P9M3. try clear HP4P5P6P9m4. try clear HP4P5P6P9m3. try clear HP4P5P6P9m2. try clear HP4P5P6P9m1. 

assert(HP4P5P6P7P8P9m3 : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P7P8P9M3 : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) <= 3).
{
	try assert(HP4P5P6P8eq : rk(P4 :: P5 :: P6 :: P8 :: nil) = 3) by (apply LP4P5P6P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6P8Mtmp : rk(P4 :: P5 :: P6 :: P8 :: nil) <= 3) by (solve_hyps_max HP4P5P6P8eq HP4P5P6P8M3).
	try assert(HP4P5P6P7P9eq : rk(P4 :: P5 :: P6 :: P7 :: P9 :: nil) = 3) by (apply LP4P5P6P7P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6P7P9Mtmp : rk(P4 :: P5 :: P6 :: P7 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P6P7P9eq HP4P5P6P7P9M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P6 :: P7 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P8 :: P4 :: P5 :: P6 :: P7 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P8 :: P4 :: P5 :: P6 :: P7 :: P9 :: nil) ((P4 :: P5 :: P6 :: P8 :: nil) ++ (P4 :: P5 :: P6 :: P7 :: P9 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P8 :: nil) (P4 :: P5 :: P6 :: P7 :: P9 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P8Mtmp HP4P5P6P7P9Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P8M1. try clear HP4P5P6P8M2. try clear HP4P5P6P8M3. try clear HP4P5P6P8m4. try clear HP4P5P6P8m3. try clear HP4P5P6P8m2. try clear HP4P5P6P8m1. try clear HP4P5P6P7P9M1. try clear HP4P5P6P7P9M2. try clear HP4P5P6P7P9M3. try clear HP4P5P6P7P9m4. try clear HP4P5P6P7P9m3. try clear HP4P5P6P7P9m2. try clear HP4P5P6P7P9m1. try clear HP4P5P6M1. try clear HP4P5P6M2. try clear HP4P5P6M3. try clear HP4P5P6m4. try clear HP4P5P6m3. try clear HP4P5P6m2. try clear HP4P5P6m1. 

assert(HP1P2P3P4P5P6P7P8P9m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3M1. try clear HP1P2P3M2. try clear HP1P2P3M3. try clear HP1P2P3m4. try clear HP1P2P3m3. try clear HP1P2P3m2. try clear HP1P2P3m1. 

assert(HP1P2P3P4P5P6P7P8P9m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) >= 4).
{
	try assert(HP1P2P3P4P5P6eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) = 4) by (apply LP1P2P3P4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P4P5P6mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6eq HP1P2P3P4P5P6m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) 4 4 HP1P2P3P4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6M1. try clear HP1P2P3P4P5P6M2. try clear HP1P2P3P4P5P6M3. try clear HP1P2P3P4P5P6m4. try clear HP1P2P3P4P5P6m3. try clear HP1P2P3P4P5P6m2. try clear HP1P2P3P4P5P6m1. 

assert(HP7P8P9m2 : rk(P7 :: P8 :: P9 :: nil) >= 2).
{
	try assert(HP7P8eq : rk(P7 :: P8 :: nil) = 2) by (apply LP7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP7P8mtmp : rk(P7 :: P8 :: nil) >= 2) by (solve_hyps_min HP7P8eq HP7P8m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: nil) (P7 :: P8 :: P9 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: nil) (P7 :: P8 :: P9 :: nil) 2 2 HP7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8M1. try clear HP7P8M2. try clear HP7P8M3. try clear HP7P8m4. try clear HP7P8m3. try clear HP7P8m2. try clear HP7P8m1. 

assert(HP7P8P9M2 : rk(P7 :: P8 :: P9 :: nil) <= 2).
{
	try assert(HP1P2P3P7P8P9eq : rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) = 3) by (apply LP1P2P3P7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P7P8P9Mtmp : rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP1P2P3P7P8P9eq HP1P2P3P7P8P9M3).
	try assert(HP4P5P6P7P8P9eq : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) = 3) by (apply LP4P5P6P7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP4P5P6P7P8P9Mtmp : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) <= 3) by (solve_hyps_max HP4P5P6P7P8P9eq HP4P5P6P7P8P9M3).
	try assert(HP1P2P3P4P5P6P7P8P9eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) = 4) by (apply LP1P2P3P4P5P6P7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8P9mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P7P8P9eq HP1P2P3P4P5P6P7P8P9m4).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (list_inter (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) ((P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) ++ (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8P9mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8P9mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P7 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: nil) 3 3 4 HP1P2P3P7P8P9Mtmp HP4P5P6P7P8P9Mtmp HP1P2P3P4P5P6P7P8P9mtmp Hincl);apply HT.
}
try clear HP1P2P3P7P8P9M1. try clear HP1P2P3P7P8P9M2. try clear HP1P2P3P7P8P9M3. try clear HP1P2P3P7P8P9m4. try clear HP1P2P3P7P8P9m3. try clear HP1P2P3P7P8P9m2. try clear HP1P2P3P7P8P9m1. try clear HP4P5P6P7P8P9M1. try clear HP4P5P6P7P8P9M2. try clear HP4P5P6P7P8P9M3. try clear HP4P5P6P7P8P9m4. try clear HP4P5P6P7P8P9m3. try clear HP4P5P6P7P8P9m2. try clear HP4P5P6P7P8P9m1. try clear HP1P2P3P4P5P6P7P8P9M1. try clear HP1P2P3P4P5P6P7P8P9M2. try clear HP1P2P3P4P5P6P7P8P9M3. try clear HP1P2P3P4P5P6P7P8P9m4. try clear HP1P2P3P4P5P6P7P8P9m3. try clear HP1P2P3P4P5P6P7P8P9m2. try clear HP1P2P3P4P5P6P7P8P9m1. 

assert(HP7P8P9M : rk(P7 :: P8 :: P9 ::  nil) <= 3) by (solve_hyps_max HP7P8P9eq HP7P8P9M3).
assert(HP7P8P9m : rk(P7 :: P8 :: P9 ::  nil) >= 1) by (solve_hyps_min HP7P8P9eq HP7P8P9m1).
intuition.
Qed.

