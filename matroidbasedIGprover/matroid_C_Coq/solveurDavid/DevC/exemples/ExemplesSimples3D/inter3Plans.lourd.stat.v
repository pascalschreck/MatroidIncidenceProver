Lemma LP16P17 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 ,
rk(P1 :: P2 :: P3 ::  nil) = 3 -> rk(P4 :: P5 :: P6 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 4 ->
rk(P7 :: P8 :: P9 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P7 :: P8 :: P9 ::  nil) = 4 -> rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P10 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P10 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P11 ::  nil) = 3 ->
rk(P4 :: P5 :: P6 :: P11 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P11 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P12 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P13 ::  nil) = 4 -> rk(P4 :: P5 :: P6 :: P13 ::  nil) = 3 -> rk(P7 :: P8 :: P9 :: P13 ::  nil) = 3 ->
rk(P4 :: P5 :: P6 :: P14 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P15 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P15 ::  nil) = 4 ->
rk(P7 :: P8 :: P9 :: P15 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P16 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P16 ::  nil) = 3 ->
rk(P7 :: P8 :: P9 :: P16 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P17 ::  nil) = 3 -> rk(P4 :: P5 :: P6 :: P17 ::  nil) = 3 ->
rk(P7 :: P8 :: P9 :: P17 ::  nil) = 3 -> rk(P16 :: P17 ::  nil) = 1.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 
HP1P2P3eq HP4P5P6eq HP1P2P3P4P5P6eq HP7P8P9eq HP1P2P3P7P8P9eq HP4P5P6P7P8P9eq HP1P2P3P10eq HP7P8P9P10eq HP1P2P3P11eq HP4P5P6P11eq
HP7P8P9P11eq HP1P2P3P12eq HP1P2P3P13eq HP4P5P6P13eq HP7P8P9P13eq HP4P5P6P14eq HP1P2P3P15eq HP4P5P6P15eq HP7P8P9P15eq HP1P2P3P16eq
HP4P5P6P16eq HP7P8P9P16eq HP1P2P3P17eq HP4P5P6P17eq HP7P8P9P17eq .

assert(HP1P2P3P16P17m3 : rk(P1 :: P2 :: P3 :: P16 :: P17 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P16 :: P17 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P16P17M3 : rk(P1 :: P2 :: P3 :: P16 :: P17 :: nil) <= 3).
{
	try assert(HP1P2P3P16eq : rk(P1 :: P2 :: P3 :: P16 :: nil) = 3) by (apply LP1P2P3P16 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P16Mtmp : rk(P1 :: P2 :: P3 :: P16 :: nil) <= 3) by (solve_hyps_max HP1P2P3P16eq HP1P2P3P16M3).
	try assert(HP1P2P3P17eq : rk(P1 :: P2 :: P3 :: P17 :: nil) = 3) by (apply LP1P2P3P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P17Mtmp : rk(P1 :: P2 :: P3 :: P17 :: nil) <= 3) by (solve_hyps_max HP1P2P3P17eq HP1P2P3P17M3).
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: P16 :: nil) (P1 :: P2 :: P3 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P16 :: P17 :: nil) (P1 :: P2 :: P3 :: P16 :: P1 :: P2 :: P3 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P16 :: P1 :: P2 :: P3 :: P17 :: nil) ((P1 :: P2 :: P3 :: P16 :: nil) ++ (P1 :: P2 :: P3 :: P17 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P16 :: nil) (P1 :: P2 :: P3 :: P17 :: nil) (P1 :: P2 :: P3 :: nil) 3 3 3 HP1P2P3P16Mtmp HP1P2P3P17Mtmp HP1P2P3mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P17M1. try clear HP1P2P3P17M2. try clear HP1P2P3P17M3. try clear HP1P2P3P17m4. try clear HP1P2P3P17m3. try clear HP1P2P3P17m2. try clear HP1P2P3P17m1. 

assert(HP4P5P6P13P17m3 : rk(P4 :: P5 :: P6 :: P13 :: P17 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P13 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P13 :: P17 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P13P17M3 : rk(P4 :: P5 :: P6 :: P13 :: P17 :: nil) <= 3).
{
	try assert(HP4P5P6P13eq : rk(P4 :: P5 :: P6 :: P13 :: nil) = 3) by (apply LP4P5P6P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P13Mtmp : rk(P4 :: P5 :: P6 :: P13 :: nil) <= 3) by (solve_hyps_max HP4P5P6P13eq HP4P5P6P13M3).
	try assert(HP4P5P6P17eq : rk(P4 :: P5 :: P6 :: P17 :: nil) = 3) by (apply LP4P5P6P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P17Mtmp : rk(P4 :: P5 :: P6 :: P17 :: nil) <= 3) by (solve_hyps_max HP4P5P6P17eq HP4P5P6P17M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P13 :: P17 :: nil) (P4 :: P5 :: P6 :: P13 :: P4 :: P5 :: P6 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P13 :: P4 :: P5 :: P6 :: P17 :: nil) ((P4 :: P5 :: P6 :: P13 :: nil) ++ (P4 :: P5 :: P6 :: P17 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P13 :: nil) (P4 :: P5 :: P6 :: P17 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P13Mtmp HP4P5P6P17Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P13M1. try clear HP4P5P6P13M2. try clear HP4P5P6P13M3. try clear HP4P5P6P13m4. try clear HP4P5P6P13m3. try clear HP4P5P6P13m2. try clear HP4P5P6P13m1. try clear HP4P5P6P17M1. try clear HP4P5P6P17M2. try clear HP4P5P6P17M3. try clear HP4P5P6P17m4. try clear HP4P5P6P17m3. try clear HP4P5P6P17m2. try clear HP4P5P6P17m1. 

assert(HP4P5P6P13P16P17m3 : rk(P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}


assert(HP4P5P6P13P16P17M3 : rk(P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) <= 3).
{
	try assert(HP4P5P6P16eq : rk(P4 :: P5 :: P6 :: P16 :: nil) = 3) by (apply LP4P5P6P16 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P16Mtmp : rk(P4 :: P5 :: P6 :: P16 :: nil) <= 3) by (solve_hyps_max HP4P5P6P16eq HP4P5P6P16M3).
	try assert(HP4P5P6P13P17eq : rk(P4 :: P5 :: P6 :: P13 :: P17 :: nil) = 3) by (apply LP4P5P6P13P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P13P17Mtmp : rk(P4 :: P5 :: P6 :: P13 :: P17 :: nil) <= 3) by (solve_hyps_max HP4P5P6P13P17eq HP4P5P6P13P17M3).
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (list_inter (P4 :: P5 :: P6 :: P16 :: nil) (P4 :: P5 :: P6 :: P13 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) (P4 :: P5 :: P6 :: P16 :: P4 :: P5 :: P6 :: P13 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P16 :: P4 :: P5 :: P6 :: P13 :: P17 :: nil) ((P4 :: P5 :: P6 :: P16 :: nil) ++ (P4 :: P5 :: P6 :: P13 :: P17 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P4 :: P5 :: P6 :: P16 :: nil) (P4 :: P5 :: P6 :: P13 :: P17 :: nil) (P4 :: P5 :: P6 :: nil) 3 3 3 HP4P5P6P16Mtmp HP4P5P6P13P17Mtmp HP4P5P6mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP4P5P6P16M1. try clear HP4P5P6P16M2. try clear HP4P5P6P16M3. try clear HP4P5P6P16m4. try clear HP4P5P6P16m3. try clear HP4P5P6P16m2. try clear HP4P5P6P16m1. try clear HP4P5P6P13P17M1. try clear HP4P5P6P13P17M2. try clear HP4P5P6P13P17M3. try clear HP4P5P6P13P17m4. try clear HP4P5P6P13P17m3. try clear HP4P5P6P13P17m2. try clear HP4P5P6P13P17m1. 

assert(HP7P8P9P13P17m3 : rk(P7 :: P8 :: P9 :: P13 :: P17 :: nil) >= 3).
{
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P13 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P13 :: P17 :: nil) 3 3 HP7P8P9mtmp Hcomp Hincl);apply HT.
}


assert(HP7P8P9P13P17M3 : rk(P7 :: P8 :: P9 :: P13 :: P17 :: nil) <= 3).
{
	try assert(HP7P8P9P13eq : rk(P7 :: P8 :: P9 :: P13 :: nil) = 3) by (apply LP7P8P9P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9P13Mtmp : rk(P7 :: P8 :: P9 :: P13 :: nil) <= 3) by (solve_hyps_max HP7P8P9P13eq HP7P8P9P13M3).
	try assert(HP7P8P9P17eq : rk(P7 :: P8 :: P9 :: P17 :: nil) = 3) by (apply LP7P8P9P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9P17Mtmp : rk(P7 :: P8 :: P9 :: P17 :: nil) <= 3) by (solve_hyps_max HP7P8P9P17eq HP7P8P9P17M3).
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (list_inter (P7 :: P8 :: P9 :: P13 :: nil) (P7 :: P8 :: P9 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P9 :: P13 :: P17 :: nil) (P7 :: P8 :: P9 :: P13 :: P7 :: P8 :: P9 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P9 :: P13 :: P7 :: P8 :: P9 :: P17 :: nil) ((P7 :: P8 :: P9 :: P13 :: nil) ++ (P7 :: P8 :: P9 :: P17 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: P8 :: P9 :: P13 :: nil) (P7 :: P8 :: P9 :: P17 :: nil) (P7 :: P8 :: P9 :: nil) 3 3 3 HP7P8P9P13Mtmp HP7P8P9P17Mtmp HP7P8P9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7P8P9P13M1. try clear HP7P8P9P13M2. try clear HP7P8P9P13M3. try clear HP7P8P9P13m4. try clear HP7P8P9P13m3. try clear HP7P8P9P13m2. try clear HP7P8P9P13m1. try clear HP7P8P9P17M1. try clear HP7P8P9P17M2. try clear HP7P8P9P17M3. try clear HP7P8P9P17m4. try clear HP7P8P9P17m3. try clear HP7P8P9P17m2. try clear HP7P8P9P17m1. 

assert(HP7P8P9P13P16P17m3 : rk(P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) >= 3).
{
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P7 :: P8 :: P9 :: nil) (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) 3 3 HP7P8P9mtmp Hcomp Hincl);apply HT.
}


assert(HP7P8P9P13P16P17M3 : rk(P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) <= 3).
{
	try assert(HP7P8P9P16eq : rk(P7 :: P8 :: P9 :: P16 :: nil) = 3) by (apply LP7P8P9P16 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9P16Mtmp : rk(P7 :: P8 :: P9 :: P16 :: nil) <= 3) by (solve_hyps_max HP7P8P9P16eq HP7P8P9P16M3).
	try assert(HP7P8P9P13P17eq : rk(P7 :: P8 :: P9 :: P13 :: P17 :: nil) = 3) by (apply LP7P8P9P13P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9P13P17Mtmp : rk(P7 :: P8 :: P9 :: P13 :: P17 :: nil) <= 3) by (solve_hyps_max HP7P8P9P13P17eq HP7P8P9P13P17M3).
	try assert(HP7P8P9eq : rk(P7 :: P8 :: P9 :: nil) = 3) by (apply LP7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9mtmp : rk(P7 :: P8 :: P9 :: nil) >= 3) by (solve_hyps_min HP7P8P9eq HP7P8P9m3).
	assert(Hincl : incl (P7 :: P8 :: P9 :: nil) (list_inter (P7 :: P8 :: P9 :: P16 :: nil) (P7 :: P8 :: P9 :: P13 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) (P7 :: P8 :: P9 :: P16 :: P7 :: P8 :: P9 :: P13 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P7 :: P8 :: P9 :: P16 :: P7 :: P8 :: P9 :: P13 :: P17 :: nil) ((P7 :: P8 :: P9 :: P16 :: nil) ++ (P7 :: P8 :: P9 :: P13 :: P17 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P7 :: P8 :: P9 :: P16 :: nil) (P7 :: P8 :: P9 :: P13 :: P17 :: nil) (P7 :: P8 :: P9 :: nil) 3 3 3 HP7P8P9P16Mtmp HP7P8P9P13P17Mtmp HP7P8P9mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP7P8P9P16M1. try clear HP7P8P9P16M2. try clear HP7P8P9P16M3. try clear HP7P8P9P16m4. try clear HP7P8P9P16m3. try clear HP7P8P9P16m2. try clear HP7P8P9P16m1. try clear HP7P8P9P13P17M1. try clear HP7P8P9P13P17M2. try clear HP7P8P9P13P17M3. try clear HP7P8P9P13P17m4. try clear HP7P8P9P13P17m3. try clear HP7P8P9P13P17m2. try clear HP7P8P9P13P17m1. try clear HP7P8P9M1. try clear HP7P8P9M2. try clear HP7P8P9M3. try clear HP7P8P9m4. try clear HP7P8P9m3. try clear HP7P8P9m2. try clear HP7P8P9m1. 

assert(HP4P5P6P7P8P9P13P16P17m3 : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) >= 3).
{
	try assert(HP4P5P6eq : rk(P4 :: P5 :: P6 :: nil) = 3) by (apply LP4P5P6 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6mtmp : rk(P4 :: P5 :: P6 :: nil) >= 3) by (solve_hyps_min HP4P5P6eq HP4P5P6m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) 3 3 HP4P5P6mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6M1. try clear HP4P5P6M2. try clear HP4P5P6M3. try clear HP4P5P6m4. try clear HP4P5P6m3. try clear HP4P5P6m2. try clear HP4P5P6m1. 

assert(HP4P5P6P7P8P9P13P16P17m4 : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) >= 4).
{
	try assert(HP4P5P6P7P8P9eq : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) = 4) by (apply LP4P5P6P7P8P9 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P7P8P9mtmp : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) >= 4) by (solve_hyps_min HP4P5P6P7P8P9eq HP4P5P6P7P8P9m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: nil) (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) 4 4 HP4P5P6P7P8P9mtmp Hcomp Hincl);apply HT.
}
try clear HP4P5P6P7P8P9M1. try clear HP4P5P6P7P8P9M2. try clear HP4P5P6P7P8P9M3. try clear HP4P5P6P7P8P9m4. try clear HP4P5P6P7P8P9m3. try clear HP4P5P6P7P8P9m2. try clear HP4P5P6P7P8P9m1. 

assert(HP1P2P3P13P16P17m3 : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) >= 3).
{
	try assert(HP1P2P3eq : rk(P1 :: P2 :: P3 :: nil) = 3) by (apply LP1P2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3mtmp : rk(P1 :: P2 :: P3 :: nil) >= 3) by (solve_hyps_min HP1P2P3eq HP1P2P3m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) 3 3 HP1P2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3M1. try clear HP1P2P3M2. try clear HP1P2P3M3. try clear HP1P2P3m4. try clear HP1P2P3m3. try clear HP1P2P3m2. try clear HP1P2P3m1. 

assert(HP1P2P3P13P16P17m4 : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) >= 4).
{
	try assert(HP1P2P3P13eq : rk(P1 :: P2 :: P3 :: P13 :: nil) = 4) by (apply LP1P2P3P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P13mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) >= 4) by (solve_hyps_min HP1P2P3P13eq HP1P2P3P13m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P13 :: nil) (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) 4 4 HP1P2P3P13mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P13M1. try clear HP1P2P3P13M2. try clear HP1P2P3P13M3. try clear HP1P2P3P13m4. try clear HP1P2P3P13m3. try clear HP1P2P3P13m2. try clear HP1P2P3P13m1. 

assert(HP13P16P17m2 : rk(P13 :: P16 :: P17 :: nil) >= 2).
{
	try assert(HP1P2P3P16eq : rk(P1 :: P2 :: P3 :: P16 :: nil) = 3) by (apply LP1P2P3P16 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P16Mtmp : rk(P1 :: P2 :: P3 :: P16 :: nil) <= 3) by (solve_hyps_max HP1P2P3P16eq HP1P2P3P16M3).
	try assert(HP1P2P3P13P16P17eq : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) = 4) by (apply LP1P2P3P13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P13P16P17mtmp : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) >= 4) by (solve_hyps_min HP1P2P3P13P16P17eq HP1P2P3P13P16P17m4).
	try assert(HP16eq : rk(P16 :: nil) = 1) by (apply LP16 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP16mtmp : rk(P16 :: nil) >= 1) by (solve_hyps_min HP16eq HP16m1).
	assert(Hincl : incl (P16 :: nil) (list_inter (P1 :: P2 :: P3 :: P16 :: nil) (P13 :: P16 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) (P1 :: P2 :: P3 :: P16 :: P13 :: P16 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P16 :: P13 :: P16 :: P17 :: nil) ((P1 :: P2 :: P3 :: P16 :: nil) ++ (P13 :: P16 :: P17 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P13P16P17mtmp;try rewrite HT2 in HP1P2P3P13P16P17mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P16 :: nil) (P13 :: P16 :: P17 :: nil) (P16 :: nil) 4 1 3 HP1P2P3P13P16P17mtmp HP16mtmp HP1P2P3P16Mtmp Hincl); apply HT.
}
try clear HP1P2P3P16M1. try clear HP1P2P3P16M2. try clear HP1P2P3P16M3. try clear HP1P2P3P16m4. try clear HP1P2P3P16m3. try clear HP1P2P3P16m2. try clear HP1P2P3P16m1. try clear HP16M1. try clear HP16M2. try clear HP16M3. try clear HP16m4. try clear HP16m3. try clear HP16m2. try clear HP16m1. 

assert(HP13P16P17M2 : rk(P13 :: P16 :: P17 :: nil) <= 2).
{
	try assert(HP4P5P6P13P16P17eq : rk(P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) = 3) by (apply LP4P5P6P13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P13P16P17Mtmp : rk(P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) <= 3) by (solve_hyps_max HP4P5P6P13P16P17eq HP4P5P6P13P16P17M3).
	try assert(HP7P8P9P13P16P17eq : rk(P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) = 3) by (apply LP7P8P9P13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP7P8P9P13P16P17Mtmp : rk(P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) <= 3) by (solve_hyps_max HP7P8P9P13P16P17eq HP7P8P9P13P16P17M3).
	try assert(HP4P5P6P7P8P9P13P16P17eq : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) = 4) by (apply LP4P5P6P7P8P9P13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP4P5P6P7P8P9P13P16P17mtmp : rk(P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) >= 4) by (solve_hyps_min HP4P5P6P7P8P9P13P16P17eq HP4P5P6P7P8P9P13P16P17m4).
	assert(Hincl : incl (P13 :: P16 :: P17 :: nil) (list_inter (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) ((P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) ++ (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P5P6P7P8P9P13P16P17mtmp;try rewrite HT2 in HP4P5P6P7P8P9P13P16P17mtmp.
	assert(HT := rule_3 (P4 :: P5 :: P6 :: P13 :: P16 :: P17 :: nil) (P7 :: P8 :: P9 :: P13 :: P16 :: P17 :: nil) (P13 :: P16 :: P17 :: nil) 3 3 4 HP4P5P6P13P16P17Mtmp HP7P8P9P13P16P17Mtmp HP4P5P6P7P8P9P13P16P17mtmp Hincl);apply HT.
}
try clear HP4P5P6P13P16P17M1. try clear HP4P5P6P13P16P17M2. try clear HP4P5P6P13P16P17M3. try clear HP4P5P6P13P16P17m4. try clear HP4P5P6P13P16P17m3. try clear HP4P5P6P13P16P17m2. try clear HP4P5P6P13P16P17m1. try clear HP7P8P9P13P16P17M1. try clear HP7P8P9P13P16P17M2. try clear HP7P8P9P13P16P17M3. try clear HP7P8P9P13P16P17m4. try clear HP7P8P9P13P16P17m3. try clear HP7P8P9P13P16P17m2. try clear HP7P8P9P13P16P17m1. try clear HP4P5P6P7P8P9P13P16P17M1. try clear HP4P5P6P7P8P9P13P16P17M2. try clear HP4P5P6P7P8P9P13P16P17M3. try clear HP4P5P6P7P8P9P13P16P17m4. try clear HP4P5P6P7P8P9P13P16P17m3. try clear HP4P5P6P7P8P9P13P16P17m2. try clear HP4P5P6P7P8P9P13P16P17m1. 

assert(HP16P17M1 : rk(P16 :: P17 :: nil) <= 1).
{
	try assert(HP1P2P3P16P17eq : rk(P1 :: P2 :: P3 :: P16 :: P17 :: nil) = 3) by (apply LP1P2P3P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P16P17Mtmp : rk(P1 :: P2 :: P3 :: P16 :: P17 :: nil) <= 3) by (solve_hyps_max HP1P2P3P16P17eq HP1P2P3P16P17M3).
	try assert(HP13P16P17eq : rk(P13 :: P16 :: P17 :: nil) = 2) by (apply LP13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP13P16P17Mtmp : rk(P13 :: P16 :: P17 :: nil) <= 2) by (solve_hyps_max HP13P16P17eq HP13P16P17M2).
	try assert(HP1P2P3P13P16P17eq : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) = 4) by (apply LP1P2P3P13P16P17 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) (P16 := P16) (P17 := P17) ;try assumption).
	assert(HP1P2P3P13P16P17mtmp : rk(P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) >= 4) by (solve_hyps_min HP1P2P3P13P16P17eq HP1P2P3P13P16P17m4).
	assert(Hincl : incl (P16 :: P17 :: nil) (list_inter (P1 :: P2 :: P3 :: P16 :: P17 :: nil) (P13 :: P16 :: P17 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P13 :: P16 :: P17 :: nil) (P1 :: P2 :: P3 :: P16 :: P17 :: P13 :: P16 :: P17 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P16 :: P17 :: P13 :: P16 :: P17 :: nil) ((P1 :: P2 :: P3 :: P16 :: P17 :: nil) ++ (P13 :: P16 :: P17 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P13P16P17mtmp;try rewrite HT2 in HP1P2P3P13P16P17mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P16 :: P17 :: nil) (P13 :: P16 :: P17 :: nil) (P16 :: P17 :: nil) 3 2 4 HP1P2P3P16P17Mtmp HP13P16P17Mtmp HP1P2P3P13P16P17mtmp Hincl);apply HT.
}
try clear HP1P2P3P16P17M1. try clear HP1P2P3P16P17M2. try clear HP1P2P3P16P17M3. try clear HP1P2P3P16P17m4. try clear HP1P2P3P16P17m3. try clear HP1P2P3P16P17m2. try clear HP1P2P3P16P17m1. try clear HP13P16P17M1. try clear HP13P16P17M2. try clear HP13P16P17M3. try clear HP13P16P17m4. try clear HP13P16P17m3. try clear HP13P16P17m2. try clear HP13P16P17m1. try clear HP1P2P3P13P16P17M1. try clear HP1P2P3P13P16P17M2. try clear HP1P2P3P13P16P17M3. try clear HP1P2P3P13P16P17m4. try clear HP1P2P3P13P16P17m3. try clear HP1P2P3P13P16P17m2. try clear HP1P2P3P13P16P17m1. 

assert(HP16P17M : rk(P16 :: P17 ::  nil) <= 2) by (solve_hyps_max HP16P17eq HP16P17M2).
assert(HP16P17m : rk(P16 :: P17 ::  nil) >= 1) by (solve_hyps_min HP16P17eq HP16P17m1).
intuition.
Qed.

