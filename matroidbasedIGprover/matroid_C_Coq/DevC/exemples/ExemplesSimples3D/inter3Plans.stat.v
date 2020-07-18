Lemma LP12P13 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 ,
rk(P1 :: P2 :: P3 ::  nil) = 3 -> rk(P4 :: P5 :: P6 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 4 ->
rk(P7 :: P8 :: P9 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 ::  nil) = 4 -> rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P10 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P10 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P10 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P11 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P11 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P11 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P12 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P12 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P12 ::  nil) = 3 ->
rk(P1 :: P2 :: P3 :: P13 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P13 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P13 ::  nil) = 3 ->
rk(P12 :: P13 ::  nil) = 1.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 
HP1P2P3eq HP4P5P6eq HP1P2P3P4P5P6eq HP7P8P9eq HP1P2P3P7P8P9eq HP4P5P6P7P8P9eq HP1P2P3P10eq HP4P5P6P10eq HP7P8P9P10eq HP1P2P3P11eq
HP4P5P6P11eq HP7P8P9P11eq HP1P2P3P12eq HP4P5P6P12eq HP7P8P9P12eq HP1P2P3P13eq HP4P5P6P13eq HP7P8P9P13eq .

assert(HP7P8P9P12P13m3 : rk(P7 :: P8 :: P9 :: P12 :: P13 :: nil) >= 3).
{
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P12 :: P13 :: nil) 3 3 HP7P8P9mtmp Hcomp Hincl);apply HT.
}


assert(HP7P8P9P12P13M3 : rk(P7 :: P8 :: P9 :: P12 :: P13 :: nil) <= 3).
{
	try assert(HP7P8P9P12eq : rk(P7 :: P8 :: P9 :: P12 :: nil) = 3) by (apply LP7P8P9P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P12Mtmp : rk(P7 :: P8 :: P9 :: P12 :: nil) <= 3) by (solve_hyps_max HP7P8P9P12eq HP7P8P9P12M3).
	try assert(HP7P8P9P13eq : rk(P7 :: P8 :: P9 :: P13 :: nil) = 3) by (apply LP7P8P9P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P13Mtmp : rk(P7 :: P8 :: P9 :: P13 :: nil) <= 3) by (solve_hyps_max HP7P8P9P13eq HP7P8P9P13M3).
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (list_inter (P7 :: P8 :: P9 :: P12 :: nil) (P7 :: P8 :: P9 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P9 :: P12 :: P13 :: nil) (P7 :: P8 :: P9 :: P12 :: P7 :: P8 :: P9 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P9 :: P12 :: P7 :: P8 :: P9 :: P13 :: nil) ((P7 :: P8 :: P9 :: P12 :: nil) ++ (P7 :: P8 :: P9 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: P8 :: P9 :: P12 :: nil) (P7 :: P8 :: P9 :: P13 :: nil) (P7 :: P8 :: P9 :: nil) 3 3 3 HP7P8P9P12Mtmp HP7P8P9P13Mtmp HP7P8P9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7P8P9P13M1. try clear HP7P8P9P13M2. try clear HP7P8P9P13M3. try clear HP7P8P9P13m4. try clear HP7P8P9P13m3. try clear HP7P8P9P13m2. try clear HP7P8P9P13m1. 

assert(HP1P2P3P10P13m3 : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P10P13M3 : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) <= 3).
{
	try assert(HP1P2P3P10eq : rk(P1 :: P2 :: P3 :: P10 :: nil) = 3) by (apply LP1P2P3P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P10Mtmp : rk(P1 :: P2 :: P3 :: P10 :: nil) <= 3) by (solve_hyps_max HP1P2P3P10eq HP1P2P3P10M3).
	try assert(HP1P2P3P13eq : rk(P1 :: P2 :: P3 :: P13 :: nil) = 3) by (apply LP1P2P3P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M3).
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P10 :: nil) (P1 :: P2 :: P3 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P10 :: P13 :: nil) (P1 :: P2 :: P3 :: P10 :: P1 :: P2 :: P3 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P10 :: P1 :: P2 :: P3 :: P13 :: nil) ((P1 :: P2 :: P3 :: P10 :: nil) ++ (P1 :: P2 :: P3 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P10 :: nil) (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P10Mtmp HP1P2P3P13Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P10M1. try clear HP1P2P3P10M2. try clear HP1P2P3P10M3. try clear HP1P2P3P10m4. try clear HP1P2P3P10m3. try clear HP1P2P3P10m2. try clear HP1P2P3P10m1. try clear HP1P2P3P13M1. try clear HP1P2P3P13M2. try clear HP1P2P3P13M3. try clear HP1P2P3P13m4. try clear HP1P2P3P13m3. try clear HP1P2P3P13m2. try clear HP1P2P3P13m1. 

assert(HP1P2P3P10P12P13m3 : rk(P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P10P12P13M3 : rk(P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) <= 3).
{
	try assert(HP1P2P3P12eq : rk(P1 :: P2 :: P3 :: P12 :: nil) = 3) by (apply LP1P2P3P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P12Mtmp : rk(P1 :: P2 :: P3 :: P12 :: nil) <= 3) by (solve_hyps_max HP1P2P3P12eq HP1P2P3P12M3).
	try assert(HP1P2P3P10P13eq : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) = 3) by (apply LP1P2P3P10P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P10P13Mtmp : rk(P1 :: P2 :: P3 :: P10 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P10P13eq HP1P2P3P10P13M3).
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) (P1 :: P2 :: P3 :: P12 :: P1 :: P2 :: P3 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P12 :: P1 :: P2 :: P3 :: P10 :: P13 :: nil) ((P1 :: P2 :: P3 :: P12 :: nil) ++ (P1 :: P2 :: P3 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P12 :: nil) (P1 :: P2 :: P3 :: P10 :: P13 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P12Mtmp HP1P2P3P10P13Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P12M1. try clear HP1P2P3P12M2. try clear HP1P2P3P12M3. try clear HP1P2P3P12m4. try clear HP1P2P3P12m3. try clear HP1P2P3P12m2. try clear HP1P2P3P12m1. try clear HP1P2P3P10P13M1. try clear HP1P2P3P10P13M2. try clear HP1P2P3P10P13M3. try clear HP1P2P3P10P13m4. try clear HP1P2P3P10P13m3. try clear HP1P2P3P10P13m2. try clear HP1P2P3P10P13m1. 

assert(HP4P5P6P10P13m3 : rk(P4 :: P5 :: P6 :: P10 :: P13 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P10 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P10 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P10P13M3 : rk(P4 :: P5 :: P6 :: P10 :: P13 :: nil) <= 3).
{
	try assert(HP4P5P6P10eq : rk(P4 :: P5 :: P6 :: P10 :: nil) = 3) by (apply LP4P5P6P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6P10Mtmp : rk(P4 :: P5 :: P6 :: P10 :: nil) <= 3) by (solve_hyps_max HP4P5P6P10eq HP4P5P6P10M3).
	try assert(HP4P5P6P13eq : rk(P4 :: P5 :: P6 :: P13 :: nil) = 3) by (apply LP4P5P6P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6P13Mtmp : rk(P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP4P5P6P13eq HP4P5P6P13M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P10 :: nil) (P4 :: P5 :: P6 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P10 :: P13 :: nil) (P4 :: P5 :: P6 :: P10 :: P4 :: P5 :: P6 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P10 :: P4 :: P5 :: P6 :: P13 :: nil) ((P4 :: P5 :: P6 :: P10 :: nil) ++ (P4 :: P5 :: P6 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P10 :: nil) (P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P10Mtmp HP4P5P6P13Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P10M1. try clear HP4P5P6P10M2. try clear HP4P5P6P10M3. try clear HP4P5P6P10m4. try clear HP4P5P6P10m3. try clear HP4P5P6P10m2. try clear HP4P5P6P10m1. try clear HP4P5P6P13M1. try clear HP4P5P6P13M2. try clear HP4P5P6P13M3. try clear HP4P5P6P13m4. try clear HP4P5P6P13m3. try clear HP4P5P6P13m2. try clear HP4P5P6P13m1. 

assert(HP4P5P6P10P12P13m3 : rk(P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P10P12P13M3 : rk(P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) <= 3).
{
	try assert(HP4P5P6P12eq : rk(P4 :: P5 :: P6 :: P12 :: nil) = 3) by (apply LP4P5P6P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6P12Mtmp : rk(P4 :: P5 :: P6 :: P12 :: nil) <= 3) by (solve_hyps_max HP4P5P6P12eq HP4P5P6P12M3).
	try assert(HP4P5P6P10P13eq : rk(P4 :: P5 :: P6 :: P10 :: P13 :: nil) = 3) by (apply LP4P5P6P10P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6P10P13Mtmp : rk(P4 :: P5 :: P6 :: P10 :: P13 :: nil) <= 3) by (solve_hyps_max HP4P5P6P10P13eq HP4P5P6P10P13M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P12 :: nil) (P4 :: P5 :: P6 :: P10 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) (P4 :: P5 :: P6 :: P12 :: P4 :: P5 :: P6 :: P10 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P12 :: P4 :: P5 :: P6 :: P10 :: P13 :: nil) ((P4 :: P5 :: P6 :: P12 :: nil) ++ (P4 :: P5 :: P6 :: P10 :: P13 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P12 :: nil) (P4 :: P5 :: P6 :: P10 :: P13 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P12Mtmp HP4P5P6P10P13Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P12M1. try clear HP4P5P6P12M2. try clear HP4P5P6P12M3. try clear HP4P5P6P12m4. try clear HP4P5P6P12m3. try clear HP4P5P6P12m2. try clear HP4P5P6P12m1. try clear HP4P5P6P10P13M1. try clear HP4P5P6P10P13M2. try clear HP4P5P6P10P13M3. try clear HP4P5P6P10P13m4. try clear HP4P5P6P10P13m3. try clear HP4P5P6P10P13m2. try clear HP4P5P6P10P13m1. try clear HP4P5P6M1. try clear HP4P5P6M2. try clear HP4P5P6M3. try clear HP4P5P6m4. try clear HP4P5P6m3. try clear HP4P5P6m2. try clear HP4P5P6m1. 

assert(HP1P2P3P4P5P6P10P12P13m3 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3M1. try clear HP1P2P3M2. try clear HP1P2P3M3. try clear HP1P2P3m4. try clear HP1P2P3m3. try clear HP1P2P3m2. try clear HP1P2P3m1. 

assert(HP1P2P3P4P5P6P10P12P13m4 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	try assert(HP1P2P3P4P5P6eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) = 4) by (apply LP1P2P3P4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P4P5P6mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6eq HP1P2P3P4P5P6m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) 4 4 HP1P2P3P4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6M1. try clear HP1P2P3P4P5P6M2. try clear HP1P2P3P4P5P6M3. try clear HP1P2P3P4P5P6m4. try clear HP1P2P3P4P5P6m3. try clear HP1P2P3P4P5P6m2. try clear HP1P2P3P4P5P6m1. 

assert(HP7P8P9P10P12P13m3 : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 3).
{
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 3 3 HP7P8P9mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8P9M1. try clear HP7P8P9M2. try clear HP7P8P9M3. try clear HP7P8P9m4. try clear HP7P8P9m3. try clear HP7P8P9m2. try clear HP7P8P9m1. 

assert(HP7P8P9P10P12P13m4 : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4).
{
	try assert(HP7P8P9P10eq : rk(P7 :: P8 :: P9 :: P10 :: nil) = 4) by (apply LP7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P10mtmp : rk(P7 :: P8 :: P9 :: P10 :: nil) >= 4) by (solve_hyps_min HP7P8P9P10eq HP7P8P9P10m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P9 :: P10 :: nil) (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: P9 :: P10 :: nil) (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) 4 4 HP7P8P9P10mtmp Hcomp Hincl);apply HT.
}
try clear HP7P8P9P10M1. try clear HP7P8P9P10M2. try clear HP7P8P9P10M3. try clear HP7P8P9P10m4. try clear HP7P8P9P10m3. try clear HP7P8P9P10m2. try clear HP7P8P9P10m1. 

assert(HP10P12P13m2 : rk(P10 :: P12 :: P13 :: nil) >= 2).
{
	try assert(HP7P8P9P12eq : rk(P7 :: P8 :: P9 :: P12 :: nil) = 3) by (apply LP7P8P9P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P12Mtmp : rk(P7 :: P8 :: P9 :: P12 :: nil) <= 3) by (solve_hyps_max HP7P8P9P12eq HP7P8P9P12M3).
	try assert(HP7P8P9P10P12P13eq : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) = 4) by (apply LP7P8P9P10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P10P12P13mtmp : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP7P8P9P10P12P13eq HP7P8P9P10P12P13m4).
	try assert(HP12eq : rk(P12 :: nil) = 1) by (apply LP12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP12mtmp : rk(P12 :: nil) >= 1) by (solve_hyps_min HP12eq HP12m1).
	assert(Hincl : incl (P12 :: nil) (list_inter (P7 :: P8 :: P9 :: P12 :: nil) (P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P7 :: P8 :: P9 :: P12 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P9 :: P12 :: P10 :: P12 :: P13 :: nil) ((P7 :: P8 :: P9 :: P12 :: nil) ++ (P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP7P8P9P10P12P13mtmp;try rewrite HT2 in HP7P8P9P10P12P13mtmp.
	assert(HT := rule_4 (P7 :: P8 :: P9 :: P12 :: nil) (P10 :: P12 :: P13 :: nil) (P12 :: nil) 4 1 3 HP7P8P9P10P12P13mtmp HP12mtmp HP7P8P9P12Mtmp Hincl); apply HT.
}
try clear HP7P8P9P12M1. try clear HP7P8P9P12M2. try clear HP7P8P9P12M3. try clear HP7P8P9P12m4. try clear HP7P8P9P12m3. try clear HP7P8P9P12m2. try clear HP7P8P9P12m1. try clear HP12M1. try clear HP12M2. try clear HP12M3. try clear HP12m4. try clear HP12m3. try clear HP12m2. try clear HP12m1. 

assert(HP10P12P13M2 : rk(P10 :: P12 :: P13 :: nil) <= 2).
{
	try assert(HP1P2P3P10P12P13eq : rk(P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) = 3) by (apply LP1P2P3P10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P10P12P13Mtmp : rk(P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP1P2P3P10P12P13eq HP1P2P3P10P12P13M3).
	try assert(HP4P5P6P10P12P13eq : rk(P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) = 3) by (apply LP4P5P6P10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP4P5P6P10P12P13Mtmp : rk(P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP4P5P6P10P12P13eq HP4P5P6P10P12P13M3).
	try assert(HP1P2P3P4P5P6P10P12P13eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) = 4) by (apply LP1P2P3P4P5P6P10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP1P2P3P4P5P6P10P12P13mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P5P6P10P12P13eq HP1P2P3P4P5P6P10P12P13m4).
	assert(Hincl : incl (P10 :: P12 :: P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) ((P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) ++ (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P10P12P13mtmp;try rewrite HT2 in HP1P2P3P4P5P6P10P12P13mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P10 :: P12 :: P13 :: nil) (P4 :: P5 :: P6 :: P10 :: P12 :: P13 :: nil) (P10 :: P12 :: P13 :: nil) 3 3 4 HP1P2P3P10P12P13Mtmp HP4P5P6P10P12P13Mtmp HP1P2P3P4P5P6P10P12P13mtmp Hincl);apply HT.
}
try clear HP1P2P3P10P12P13M1. try clear HP1P2P3P10P12P13M2. try clear HP1P2P3P10P12P13M3. try clear HP1P2P3P10P12P13m4. try clear HP1P2P3P10P12P13m3. try clear HP1P2P3P10P12P13m2. try clear HP1P2P3P10P12P13m1. try clear HP4P5P6P10P12P13M1. try clear HP4P5P6P10P12P13M2. try clear HP4P5P6P10P12P13M3. try clear HP4P5P6P10P12P13m4. try clear HP4P5P6P10P12P13m3. try clear HP4P5P6P10P12P13m2. try clear HP4P5P6P10P12P13m1. try clear HP1P2P3P4P5P6P10P12P13M1. try clear HP1P2P3P4P5P6P10P12P13M2. try clear HP1P2P3P4P5P6P10P12P13M3. try clear HP1P2P3P4P5P6P10P12P13m4. try clear HP1P2P3P4P5P6P10P12P13m3. try clear HP1P2P3P4P5P6P10P12P13m2. try clear HP1P2P3P4P5P6P10P12P13m1. 

assert(HP12P13M1 : rk(P12 :: P13 :: nil) <= 1).
{
	try assert(HP7P8P9P12P13eq : rk(P7 :: P8 :: P9 :: P12 :: P13 :: nil) = 3) by (apply LP7P8P9P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P12P13Mtmp : rk(P7 :: P8 :: P9 :: P12 :: P13 :: nil) <= 3) by (solve_hyps_max HP7P8P9P12P13eq HP7P8P9P12P13M3).
	try assert(HP10P12P13eq : rk(P10 :: P12 :: P13 :: nil) = 2) by (apply LP10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP10P12P13Mtmp : rk(P10 :: P12 :: P13 :: nil) <= 2) by (solve_hyps_max HP10P12P13eq HP10P12P13M2).
	try assert(HP7P8P9P10P12P13eq : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) = 4) by (apply LP7P8P9P10P12P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) ;try assumption).
	assert(HP7P8P9P10P12P13mtmp : rk(P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) >= 4) by (solve_hyps_min HP7P8P9P10P12P13eq HP7P8P9P10P12P13m4).
	assert(Hincl : incl (P12 :: P13 :: nil) (list_inter (P7 :: P8 :: P9 :: P12 :: P13 :: nil) (P10 :: P12 :: P13 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P9 :: P10 :: P12 :: P13 :: nil) (P7 :: P8 :: P9 :: P12 :: P13 :: P10 :: P12 :: P13 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P9 :: P12 :: P13 :: P10 :: P12 :: P13 :: nil) ((P7 :: P8 :: P9 :: P12 :: P13 :: nil) ++ (P10 :: P12 :: P13 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP7P8P9P10P12P13mtmp;try rewrite HT2 in HP7P8P9P10P12P13mtmp.
	assert(HT := rule_3 (P7 :: P8 :: P9 :: P12 :: P13 :: nil) (P10 :: P12 :: P13 :: nil) (P12 :: P13 :: nil) 3 2 4 HP7P8P9P12P13Mtmp HP10P12P13Mtmp HP7P8P9P10P12P13mtmp Hincl);apply HT.
}
try clear HP7P8P9P12P13M1. try clear HP7P8P9P12P13M2. try clear HP7P8P9P12P13M3. try clear HP7P8P9P12P13m4. try clear HP7P8P9P12P13m3. try clear HP7P8P9P12P13m2. try clear HP7P8P9P12P13m1. try clear HP10P12P13M1. try clear HP10P12P13M2. try clear HP10P12P13M3. try clear HP10P12P13m4. try clear HP10P12P13m3. try clear HP10P12P13m2. try clear HP10P12P13m1. try clear HP7P8P9P10P12P13M1. try clear HP7P8P9P10P12P13M2. try clear HP7P8P9P10P12P13M3. try clear HP7P8P9P10P12P13m4. try clear HP7P8P9P10P12P13m3. try clear HP7P8P9P10P12P13m2. try clear HP7P8P9P10P12P13m1. 

assert(HP12P13M : rk(P12 :: P13 ::  nil) <= 2) by (solve_hyps_max HP12P13eq HP12P13M2).
assert(HP12P13m : rk(P12 :: P13 ::  nil) >= 1) by (solve_hyps_min HP12P13eq HP12P13m1).
intuition.
Qed.

