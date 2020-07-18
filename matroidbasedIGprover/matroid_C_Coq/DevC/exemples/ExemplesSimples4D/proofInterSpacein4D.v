Lemma LP9P10P11P12 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 ,
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 4 -> rk(P5 :: P6 :: P7 :: P8 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 ::  nil) = 5 ->
rk(P1 :: P2 :: P3 :: P4 :: P9 ::  nil) = 4 -> rk(P5 :: P6 :: P7 :: P8 :: P9 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P4 :: P10 ::  nil) = 4 ->
rk(P5 :: P6 :: P7 :: P8 :: P10 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P4 :: P11 ::  nil) = 4 -> rk(P5 :: P6 :: P7 :: P8 :: P11 ::  nil) = 4 ->
rk(P9 :: P10 :: P11 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P4 :: P12 ::  nil) = 4 -> rk(P5 :: P6 :: P7 :: P8 :: P12 ::  nil) = 4 ->
rk(P9 :: P10 :: P12 ::  nil) = 3 -> rk(P9 :: P11 :: P12 ::  nil) = 3 -> rk(P10 :: P11 :: P12 ::  nil) = 3 ->
rk(P9 :: P10 :: P11 :: P12 ::  nil) = 3.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 
HP1P2P3P4eq HP5P6P7P8eq HP1P2P3P4P5P6P7P8eq HP1P2P3P4P9eq HP5P6P7P8P9eq HP1P2P3P4P10eq HP5P6P7P8P10eq HP1P2P3P4P11eq HP5P6P7P8P11eq HP9P10P11eq
HP1P2P3P4P12eq HP5P6P7P8P12eq HP9P10P12eq HP9P11P12eq HP10P11P12eq .

assert(HP1P2P3P4P9P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) >= 4).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P9P12M4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) <= 4).
{
	try assert(HP1P2P3P4P9eq : rk(P1 :: P2 :: P3 :: P4 :: P9 :: nil) = 4) by (apply LP1P2P3P4P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P9Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P9 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P9eq HP1P2P3P4P9M4).
	try assert(HP1P2P3P4P12eq : rk(P1 :: P2 :: P3 :: P4 :: P12 :: nil) = 4) by (apply LP1P2P3P4P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P12Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P12 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P12eq HP1P2P3P4P12M4).
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P9 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P1 :: P2 :: P3 :: P4 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P9 :: P1 :: P2 :: P3 :: P4 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P9 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P9 :: nil) (P1 :: P2 :: P3 :: P4 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 4 4 4 HP1P2P3P4P9Mtmp HP1P2P3P4P12Mtmp HP1P2P3P4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P9M1. try clear HP1P2P3P4P9M2. try clear HP1P2P3P4P9M3. try clear HP1P2P3P4P9M4. try clear HP1P2P3P4P9M5. try clear HP1P2P3P4P9M6. try clear HP1P2P3P4P9M7. try clear HP1P2P3P4P9m7. try clear HP1P2P3P4P9m6. try clear HP1P2P3P4P9m5. try clear HP1P2P3P4P9m4. try clear HP1P2P3P4P9m3. try clear HP1P2P3P4P9m2. try clear HP1P2P3P4P9m1. try clear HP1P2P3P4P12M1. try clear HP1P2P3P4P12M2. try clear HP1P2P3P4P12M3. try clear HP1P2P3P4P12M4. try clear HP1P2P3P4P12M5. try clear HP1P2P3P4P12M6. try clear HP1P2P3P4P12M7. try clear HP1P2P3P4P12m7. try clear HP1P2P3P4P12m6. try clear HP1P2P3P4P12m5. try clear HP1P2P3P4P12m4. try clear HP1P2P3P4P12m3. try clear HP1P2P3P4P12m2. try clear HP1P2P3P4P12m1. 

assert(HP1P2P3P4P9P10P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) >= 4).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P9P10P12M4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) <= 4).
{
	try assert(HP1P2P3P4P10eq : rk(P1 :: P2 :: P3 :: P4 :: P10 :: nil) = 4) by (apply LP1P2P3P4P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P10Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P10 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P10eq HP1P2P3P4P10M4).
	try assert(HP1P2P3P4P9P12eq : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) = 4) by (apply LP1P2P3P4P9P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P9P12Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P9P12eq HP1P2P3P4P9P12M4).
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P10 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P10 :: P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P10 :: P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P10 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P10 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 4 4 4 HP1P2P3P4P10Mtmp HP1P2P3P4P9P12Mtmp HP1P2P3P4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P10M1. try clear HP1P2P3P4P10M2. try clear HP1P2P3P4P10M3. try clear HP1P2P3P4P10M4. try clear HP1P2P3P4P10M5. try clear HP1P2P3P4P10M6. try clear HP1P2P3P4P10M7. try clear HP1P2P3P4P10m7. try clear HP1P2P3P4P10m6. try clear HP1P2P3P4P10m5. try clear HP1P2P3P4P10m4. try clear HP1P2P3P4P10m3. try clear HP1P2P3P4P10m2. try clear HP1P2P3P4P10m1. try clear HP1P2P3P4P9P12M1. try clear HP1P2P3P4P9P12M2. try clear HP1P2P3P4P9P12M3. try clear HP1P2P3P4P9P12M4. try clear HP1P2P3P4P9P12M5. try clear HP1P2P3P4P9P12M6. try clear HP1P2P3P4P9P12M7. try clear HP1P2P3P4P9P12m7. try clear HP1P2P3P4P9P12m6. try clear HP1P2P3P4P9P12m5. try clear HP1P2P3P4P9P12m4. try clear HP1P2P3P4P9P12m3. try clear HP1P2P3P4P9P12m2. try clear HP1P2P3P4P9P12m1. 

assert(HP1P2P3P4P9P10P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) >= 4).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P9P10P11P12M4 : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) <= 4).
{
	try assert(HP1P2P3P4P11eq : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) = 4) by (apply LP1P2P3P4P11 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P11 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P11eq HP1P2P3P4P11M4).
	try assert(HP1P2P3P4P9P10P12eq : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) = 4) by (apply LP1P2P3P4P9P10P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P9P10P12Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P9P10P12eq HP1P2P3P4P9P10P12M4).
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P11 :: P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 4 4 4 HP1P2P3P4P11Mtmp HP1P2P3P4P9P10P12Mtmp HP1P2P3P4mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P11M1. try clear HP1P2P3P4P11M2. try clear HP1P2P3P4P11M3. try clear HP1P2P3P4P11M4. try clear HP1P2P3P4P11M5. try clear HP1P2P3P4P11M6. try clear HP1P2P3P4P11M7. try clear HP1P2P3P4P11m7. try clear HP1P2P3P4P11m6. try clear HP1P2P3P4P11m5. try clear HP1P2P3P4P11m4. try clear HP1P2P3P4P11m3. try clear HP1P2P3P4P11m2. try clear HP1P2P3P4P11m1. try clear HP1P2P3P4P9P10P12M1. try clear HP1P2P3P4P9P10P12M2. try clear HP1P2P3P4P9P10P12M3. try clear HP1P2P3P4P9P10P12M4. try clear HP1P2P3P4P9P10P12M5. try clear HP1P2P3P4P9P10P12M6. try clear HP1P2P3P4P9P10P12M7. try clear HP1P2P3P4P9P10P12m7. try clear HP1P2P3P4P9P10P12m6. try clear HP1P2P3P4P9P10P12m5. try clear HP1P2P3P4P9P10P12m4. try clear HP1P2P3P4P9P10P12m3. try clear HP1P2P3P4P9P10P12m2. try clear HP1P2P3P4P9P10P12m1. 

assert(HP5P6P7P8P9P12m4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) >= 4).
{
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) 4 4 HP5P6P7P8mtmp Hcomp Hincl);apply HT.
}


assert(HP5P6P7P8P9P12M4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) <= 4).
{
	try assert(HP5P6P7P8P9eq : rk(P5 :: P6 :: P7 :: P8 :: P9 :: nil) = 4) by (apply LP5P6P7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P9Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P9 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P9eq HP5P6P7P8P9M4).
	try assert(HP5P6P7P8P12eq : rk(P5 :: P6 :: P7 :: P8 :: P12 :: nil) = 4) by (apply LP5P6P7P8P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P12Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P12 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P12eq HP5P6P7P8P12M4).
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (list_inter (P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P5 :: P6 :: P7 :: P8 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P5 :: P6 :: P7 :: P8 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P7 :: P8 :: P9 :: P5 :: P6 :: P7 :: P8 :: P12 :: nil) ((P5 :: P6 :: P7 :: P8 :: P9 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P5 :: P6 :: P7 :: P8 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: nil) 4 4 4 HP5P6P7P8P9Mtmp HP5P6P7P8P12Mtmp HP5P6P7P8mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P6P7P8P9M1. try clear HP5P6P7P8P9M2. try clear HP5P6P7P8P9M3. try clear HP5P6P7P8P9M4. try clear HP5P6P7P8P9M5. try clear HP5P6P7P8P9M6. try clear HP5P6P7P8P9M7. try clear HP5P6P7P8P9m7. try clear HP5P6P7P8P9m6. try clear HP5P6P7P8P9m5. try clear HP5P6P7P8P9m4. try clear HP5P6P7P8P9m3. try clear HP5P6P7P8P9m2. try clear HP5P6P7P8P9m1. try clear HP5P6P7P8P12M1. try clear HP5P6P7P8P12M2. try clear HP5P6P7P8P12M3. try clear HP5P6P7P8P12M4. try clear HP5P6P7P8P12M5. try clear HP5P6P7P8P12M6. try clear HP5P6P7P8P12M7. try clear HP5P6P7P8P12m7. try clear HP5P6P7P8P12m6. try clear HP5P6P7P8P12m5. try clear HP5P6P7P8P12m4. try clear HP5P6P7P8P12m3. try clear HP5P6P7P8P12m2. try clear HP5P6P7P8P12m1. 

assert(HP5P6P7P8P9P10P12m4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) >= 4).
{
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) 4 4 HP5P6P7P8mtmp Hcomp Hincl);apply HT.
}


assert(HP5P6P7P8P9P10P12M4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) <= 4).
{
	try assert(HP5P6P7P8P10eq : rk(P5 :: P6 :: P7 :: P8 :: P10 :: nil) = 4) by (apply LP5P6P7P8P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P10Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P10 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P10eq HP5P6P7P8P10M4).
	try assert(HP5P6P7P8P9P12eq : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) = 4) by (apply LP5P6P7P8P9P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P9P12Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P9P12eq HP5P6P7P8P9P12M4).
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (list_inter (P5 :: P6 :: P7 :: P8 :: P10 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: P10 :: P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P7 :: P8 :: P10 :: P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) ((P5 :: P6 :: P7 :: P8 :: P10 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P7 :: P8 :: P10 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: nil) 4 4 4 HP5P6P7P8P10Mtmp HP5P6P7P8P9P12Mtmp HP5P6P7P8mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P6P7P8P10M1. try clear HP5P6P7P8P10M2. try clear HP5P6P7P8P10M3. try clear HP5P6P7P8P10M4. try clear HP5P6P7P8P10M5. try clear HP5P6P7P8P10M6. try clear HP5P6P7P8P10M7. try clear HP5P6P7P8P10m7. try clear HP5P6P7P8P10m6. try clear HP5P6P7P8P10m5. try clear HP5P6P7P8P10m4. try clear HP5P6P7P8P10m3. try clear HP5P6P7P8P10m2. try clear HP5P6P7P8P10m1. try clear HP5P6P7P8P9P12M1. try clear HP5P6P7P8P9P12M2. try clear HP5P6P7P8P9P12M3. try clear HP5P6P7P8P9P12M4. try clear HP5P6P7P8P9P12M5. try clear HP5P6P7P8P9P12M6. try clear HP5P6P7P8P9P12M7. try clear HP5P6P7P8P9P12m7. try clear HP5P6P7P8P9P12m6. try clear HP5P6P7P8P9P12m5. try clear HP5P6P7P8P9P12m4. try clear HP5P6P7P8P9P12m3. try clear HP5P6P7P8P9P12m2. try clear HP5P6P7P8P9P12m1. 

assert(HP5P6P7P8P9P10P11P12m4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) >= 4).
{
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P5 :: P6 :: P7 :: P8 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) 4 4 HP5P6P7P8mtmp Hcomp Hincl);apply HT.
}


assert(HP5P6P7P8P9P10P11P12M4 : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) <= 4).
{
	try assert(HP5P6P7P8P11eq : rk(P5 :: P6 :: P7 :: P8 :: P11 :: nil) = 4) by (apply LP5P6P7P8P11 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P11Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P11 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P11eq HP5P6P7P8P11M4).
	try assert(HP5P6P7P8P9P10P12eq : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) = 4) by (apply LP5P6P7P8P9P10P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P9P10P12Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P9P10P12eq HP5P6P7P8P9P10P12M4).
	try assert(HP5P6P7P8eq : rk(P5 :: P6 :: P7 :: P8 :: nil) = 4) by (apply LP5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8mtmp : rk(P5 :: P6 :: P7 :: P8 :: nil) >= 4) by (solve_hyps_min HP5P6P7P8eq HP5P6P7P8m4).
	assert(Hincl : incl (P5 :: P6 :: P7 :: P8 :: nil) (list_inter (P5 :: P6 :: P7 :: P8 :: P11 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: P11 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P5 :: P6 :: P7 :: P8 :: P11 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) ((P5 :: P6 :: P7 :: P8 :: P11 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P5 :: P6 :: P7 :: P8 :: P11 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: nil) 4 4 4 HP5P6P7P8P11Mtmp HP5P6P7P8P9P10P12Mtmp HP5P6P7P8mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP5P6P7P8P11M1. try clear HP5P6P7P8P11M2. try clear HP5P6P7P8P11M3. try clear HP5P6P7P8P11M4. try clear HP5P6P7P8P11M5. try clear HP5P6P7P8P11M6. try clear HP5P6P7P8P11M7. try clear HP5P6P7P8P11m7. try clear HP5P6P7P8P11m6. try clear HP5P6P7P8P11m5. try clear HP5P6P7P8P11m4. try clear HP5P6P7P8P11m3. try clear HP5P6P7P8P11m2. try clear HP5P6P7P8P11m1. try clear HP5P6P7P8P9P10P12M1. try clear HP5P6P7P8P9P10P12M2. try clear HP5P6P7P8P9P10P12M3. try clear HP5P6P7P8P9P10P12M4. try clear HP5P6P7P8P9P10P12M5. try clear HP5P6P7P8P9P10P12M6. try clear HP5P6P7P8P9P10P12M7. try clear HP5P6P7P8P9P10P12m7. try clear HP5P6P7P8P9P10P12m6. try clear HP5P6P7P8P9P10P12m5. try clear HP5P6P7P8P9P10P12m4. try clear HP5P6P7P8P9P10P12m3. try clear HP5P6P7P8P9P10P12m2. try clear HP5P6P7P8P9P10P12m1. try clear HP5P6P7P8M1. try clear HP5P6P7P8M2. try clear HP5P6P7P8M3. try clear HP5P6P7P8M4. try clear HP5P6P7P8M5. try clear HP5P6P7P8M6. try clear HP5P6P7P8M7. try clear HP5P6P7P8m7. try clear HP5P6P7P8m6. try clear HP5P6P7P8m5. try clear HP5P6P7P8m4. try clear HP5P6P7P8m3. try clear HP5P6P7P8m2. try clear HP5P6P7P8m1. 

assert(HP1P2P3P4P5P6P7P8P9P10P11P12m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) >= 4).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 4) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) 4 4 HP1P2P3P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4M1. try clear HP1P2P3P4M2. try clear HP1P2P3P4M3. try clear HP1P2P3P4M4. try clear HP1P2P3P4M5. try clear HP1P2P3P4M6. try clear HP1P2P3P4M7. try clear HP1P2P3P4m7. try clear HP1P2P3P4m6. try clear HP1P2P3P4m5. try clear HP1P2P3P4m4. try clear HP1P2P3P4m3. try clear HP1P2P3P4m2. try clear HP1P2P3P4m1. 

assert(HP1P2P3P4P5P6P7P8P9P10P11P12m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5P6P7P8eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) = 5) by (apply LP1P2P3P4P5P6P7P8 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5P6P7P8eq HP1P2P3P4P5P6P7P8m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) 5 5 HP1P2P3P4P5P6P7P8mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P7P8M1. try clear HP1P2P3P4P5P6P7P8M2. try clear HP1P2P3P4P5P6P7P8M3. try clear HP1P2P3P4P5P6P7P8M4. try clear HP1P2P3P4P5P6P7P8M5. try clear HP1P2P3P4P5P6P7P8M6. try clear HP1P2P3P4P5P6P7P8M7. try clear HP1P2P3P4P5P6P7P8m7. try clear HP1P2P3P4P5P6P7P8m6. try clear HP1P2P3P4P5P6P7P8m5. try clear HP1P2P3P4P5P6P7P8m4. try clear HP1P2P3P4P5P6P7P8m3. try clear HP1P2P3P4P5P6P7P8m2. try clear HP1P2P3P4P5P6P7P8m1. 

assert(HP9P10P11P12m3 : rk(P9 :: P10 :: P11 :: P12 :: nil) >= 3).
{
	try assert(HP9P10P11eq : rk(P9 :: P10 :: P11 :: nil) = 3) by (apply LP9P10P11 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP9P10P11mtmp : rk(P9 :: P10 :: P11 :: nil) >= 3) by (solve_hyps_min HP9P10P11eq HP9P10P11m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P9 :: P10 :: P11 :: nil) (P9 :: P10 :: P11 :: P12 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P9 :: P10 :: P11 :: nil) (P9 :: P10 :: P11 :: P12 :: nil) 3 3 HP9P10P11mtmp Hcomp Hincl);apply HT.
}
try clear HP9P10P11M1. try clear HP9P10P11M2. try clear HP9P10P11M3. try clear HP9P10P11M4. try clear HP9P10P11M5. try clear HP9P10P11M6. try clear HP9P10P11M7. try clear HP9P10P11m7. try clear HP9P10P11m6. try clear HP9P10P11m5. try clear HP9P10P11m4. try clear HP9P10P11m3. try clear HP9P10P11m2. try clear HP9P10P11m1. 

assert(HP9P10P11P12M3 : rk(P9 :: P10 :: P11 :: P12 :: nil) <= 3).
{
	try assert(HP1P2P3P4P9P10P11P12eq : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) = 4) by (apply LP1P2P3P4P9P10P11P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P9P10P11P12Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) <= 4) by (solve_hyps_max HP1P2P3P4P9P10P11P12eq HP1P2P3P4P9P10P11P12M4).
	try assert(HP5P6P7P8P9P10P11P12eq : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) = 4) by (apply LP5P6P7P8P9P10P11P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP5P6P7P8P9P10P11P12Mtmp : rk(P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) <= 4) by (solve_hyps_max HP5P6P7P8P9P10P11P12eq HP5P6P7P8P9P10P11P12M4).
	try assert(HP1P2P3P4P5P6P7P8P9P10P11P12eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) = 5) by (apply LP1P2P3P4P5P6P7P8P9P10P11P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8P9P10P11P12mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5P6P7P8P9P10P11P12eq HP1P2P3P4P5P6P7P8P9P10P11P12m5).
	assert(Hincl : incl (P9 :: P10 :: P11 :: P12 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) ((P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) ++ (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8P9P10P11P12mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8P9P10P11P12mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P4 :: P9 :: P10 :: P11 :: P12 :: nil) (P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: nil) (P9 :: P10 :: P11 :: P12 :: nil) 4 4 5 HP1P2P3P4P9P10P11P12Mtmp HP5P6P7P8P9P10P11P12Mtmp HP1P2P3P4P5P6P7P8P9P10P11P12mtmp Hincl);apply HT.
}
try clear HP1P2P3P4P9P10P11P12M1. try clear HP1P2P3P4P9P10P11P12M2. try clear HP1P2P3P4P9P10P11P12M3. try clear HP1P2P3P4P9P10P11P12M4. try clear HP1P2P3P4P9P10P11P12M5. try clear HP1P2P3P4P9P10P11P12M6. try clear HP1P2P3P4P9P10P11P12M7. try clear HP1P2P3P4P9P10P11P12m7. try clear HP1P2P3P4P9P10P11P12m6. try clear HP1P2P3P4P9P10P11P12m5. try clear HP1P2P3P4P9P10P11P12m4. try clear HP1P2P3P4P9P10P11P12m3. try clear HP1P2P3P4P9P10P11P12m2. try clear HP1P2P3P4P9P10P11P12m1. try clear HP5P6P7P8P9P10P11P12M1. try clear HP5P6P7P8P9P10P11P12M2. try clear HP5P6P7P8P9P10P11P12M3. try clear HP5P6P7P8P9P10P11P12M4. try clear HP5P6P7P8P9P10P11P12M5. try clear HP5P6P7P8P9P10P11P12M6. try clear HP5P6P7P8P9P10P11P12M7. try clear HP5P6P7P8P9P10P11P12m7. try clear HP5P6P7P8P9P10P11P12m6. try clear HP5P6P7P8P9P10P11P12m5. try clear HP5P6P7P8P9P10P11P12m4. try clear HP5P6P7P8P9P10P11P12m3. try clear HP5P6P7P8P9P10P11P12m2. try clear HP5P6P7P8P9P10P11P12m1. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M1. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M2. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M3. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M4. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M5. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M6. try clear HP1P2P3P4P5P6P7P8P9P10P11P12M7. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m7. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m6. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m5. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m4. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m3. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m2. try clear HP1P2P3P4P5P6P7P8P9P10P11P12m1. 

assert(HP9P10P11P12M : rk(P9 :: P10 :: P11 :: P12 ::  nil) <= 4) by (solve_hyps_max HP9P10P11P12eq HP9P10P11P12M4).
assert(HP9P10P11P12m : rk(P9 :: P10 :: P11 :: P12 ::  nil) >= 1) by (solve_hyps_min HP9P10P11P12eq HP9P10P11P12m1).
intuition.
Qed.

