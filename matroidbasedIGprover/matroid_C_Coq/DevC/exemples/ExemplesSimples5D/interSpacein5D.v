Lemma LP11P12P13P14P15 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 ,
rk(P1 :: P2 :: P3 :: P4 :: P5 ::  nil) = 5 -> rk(P6 :: P7 :: P8 :: P9 :: P10 ::  nil) = 5 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 ::  nil) = 6 ->
rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 ::  nil) = 5 -> rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 ::  nil) = 5 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P12 ::  nil) = 5 ->
rk(P6 :: P7 :: P8 :: P9 :: P10 :: P12 ::  nil) = 5 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P13 ::  nil) = 5 -> rk(P6 :: P7 :: P8 :: P9 :: P10 :: P13 ::  nil) = 5 ->
rk(P1 :: P2 :: P3 :: P4 :: P5 :: P14 ::  nil) = 5 -> rk(P6 :: P7 :: P8 :: P9 :: P10 :: P14 ::  nil) = 5 -> rk(P11 :: P12 :: P13 :: P14 ::  nil) = 4 ->
rk(P1 :: P2 :: P3 :: P4 :: P5 :: P15 ::  nil) = 5 -> rk(P6 :: P7 :: P8 :: P9 :: P10 :: P15 ::  nil) = 5 -> rk(P11 :: P12 :: P13 :: P15 ::  nil) = 4 ->
rk(P11 :: P12 :: P14 :: P15 ::  nil) = 4 -> rk(P11 :: P13 :: P14 :: P15 ::  nil) = 4 -> rk(P12 :: P13 :: P14 :: P15 ::  nil) = 4 ->
rk(P11 :: P12 :: P13 :: P14 :: P15 ::  nil) = 4.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 
HP1P2P3P4P5eq HP6P7P8P9P10eq HP1P2P3P4P5P6P7P8P9P10eq HP1P2P3P4P5P11eq HP6P7P8P9P10P11eq HP1P2P3P4P5P12eq HP6P7P8P9P10P12eq HP1P2P3P4P5P13eq HP6P7P8P9P10P13eq HP1P2P3P4P5P14eq
HP6P7P8P9P10P14eq HP11P12P13P14eq HP1P2P3P4P5P15eq HP6P7P8P9P10P15eq HP11P12P13P15eq HP11P12P14P15eq HP11P13P14P15eq HP12P13P14P15eq .

assert(HP1P2P3P4P5P11P15m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) 5 5 HP1P2P3P4P5mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5P11P15M5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) <= 5).
{
	try assert(HP1P2P3P4P5P11eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: nil) = 5) by (apply LP1P2P3P4P5P11 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P11Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P11eq HP1P2P3P4P5P11M5).
	try assert(HP1P2P3P4P5P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil) = 5) by (apply LP1P2P3P4P5P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P15Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P15eq HP1P2P3P4P5P15M5).
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 5 5 5 HP1P2P3P4P5P11Mtmp HP1P2P3P4P5P15Mtmp HP1P2P3P4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P5P11M1. try clear HP1P2P3P4P5P11M2. try clear HP1P2P3P4P5P11M3. try clear HP1P2P3P4P5P11M4. try clear HP1P2P3P4P5P11M5. try clear HP1P2P3P4P5P11M6. try clear HP1P2P3P4P5P11M7. try clear HP1P2P3P4P5P11m7. try clear HP1P2P3P4P5P11m6. try clear HP1P2P3P4P5P11m5. try clear HP1P2P3P4P5P11m4. try clear HP1P2P3P4P5P11m3. try clear HP1P2P3P4P5P11m2. try clear HP1P2P3P4P5P11m1. try clear HP1P2P3P4P5P15M1. try clear HP1P2P3P4P5P15M2. try clear HP1P2P3P4P5P15M3. try clear HP1P2P3P4P5P15M4. try clear HP1P2P3P4P5P15M5. try clear HP1P2P3P4P5P15M6. try clear HP1P2P3P4P5P15M7. try clear HP1P2P3P4P5P15m7. try clear HP1P2P3P4P5P15m6. try clear HP1P2P3P4P5P15m5. try clear HP1P2P3P4P5P15m4. try clear HP1P2P3P4P5P15m3. try clear HP1P2P3P4P5P15m2. try clear HP1P2P3P4P5P15m1. 

assert(HP1P2P3P4P5P11P12P15m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) 5 5 HP1P2P3P4P5mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5P11P12P15M5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) <= 5).
{
	try assert(HP1P2P3P4P5P12eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: nil) = 5) by (apply LP1P2P3P4P5P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P12Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P12eq HP1P2P3P4P5P12M5).
	try assert(HP1P2P3P4P5P11P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) = 5) by (apply LP1P2P3P4P5P11P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P11P15Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P11P15eq HP1P2P3P4P5P11P15M5).
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P5 :: P12 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 5 5 5 HP1P2P3P4P5P12Mtmp HP1P2P3P4P5P11P15Mtmp HP1P2P3P4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P5P12M1. try clear HP1P2P3P4P5P12M2. try clear HP1P2P3P4P5P12M3. try clear HP1P2P3P4P5P12M4. try clear HP1P2P3P4P5P12M5. try clear HP1P2P3P4P5P12M6. try clear HP1P2P3P4P5P12M7. try clear HP1P2P3P4P5P12m7. try clear HP1P2P3P4P5P12m6. try clear HP1P2P3P4P5P12m5. try clear HP1P2P3P4P5P12m4. try clear HP1P2P3P4P5P12m3. try clear HP1P2P3P4P5P12m2. try clear HP1P2P3P4P5P12m1. try clear HP1P2P3P4P5P11P15M1. try clear HP1P2P3P4P5P11P15M2. try clear HP1P2P3P4P5P11P15M3. try clear HP1P2P3P4P5P11P15M4. try clear HP1P2P3P4P5P11P15M5. try clear HP1P2P3P4P5P11P15M6. try clear HP1P2P3P4P5P11P15M7. try clear HP1P2P3P4P5P11P15m7. try clear HP1P2P3P4P5P11P15m6. try clear HP1P2P3P4P5P11P15m5. try clear HP1P2P3P4P5P11P15m4. try clear HP1P2P3P4P5P11P15m3. try clear HP1P2P3P4P5P11P15m2. try clear HP1P2P3P4P5P11P15m1. 

assert(HP1P2P3P4P5P11P12P13P15m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) 5 5 HP1P2P3P4P5mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5P11P12P13P15M5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) <= 5).
{
	try assert(HP1P2P3P4P5P13eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: nil) = 5) by (apply LP1P2P3P4P5P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P13Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P13eq HP1P2P3P4P5P13M5).
	try assert(HP1P2P3P4P5P11P12P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) = 5) by (apply LP1P2P3P4P5P11P12P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P11P12P15Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P11P12P15eq HP1P2P3P4P5P11P12P15M5).
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P5 :: P13 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 5 5 5 HP1P2P3P4P5P13Mtmp HP1P2P3P4P5P11P12P15Mtmp HP1P2P3P4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P5P13M1. try clear HP1P2P3P4P5P13M2. try clear HP1P2P3P4P5P13M3. try clear HP1P2P3P4P5P13M4. try clear HP1P2P3P4P5P13M5. try clear HP1P2P3P4P5P13M6. try clear HP1P2P3P4P5P13M7. try clear HP1P2P3P4P5P13m7. try clear HP1P2P3P4P5P13m6. try clear HP1P2P3P4P5P13m5. try clear HP1P2P3P4P5P13m4. try clear HP1P2P3P4P5P13m3. try clear HP1P2P3P4P5P13m2. try clear HP1P2P3P4P5P13m1. try clear HP1P2P3P4P5P11P12P15M1. try clear HP1P2P3P4P5P11P12P15M2. try clear HP1P2P3P4P5P11P12P15M3. try clear HP1P2P3P4P5P11P12P15M4. try clear HP1P2P3P4P5P11P12P15M5. try clear HP1P2P3P4P5P11P12P15M6. try clear HP1P2P3P4P5P11P12P15M7. try clear HP1P2P3P4P5P11P12P15m7. try clear HP1P2P3P4P5P11P12P15m6. try clear HP1P2P3P4P5P11P12P15m5. try clear HP1P2P3P4P5P11P12P15m4. try clear HP1P2P3P4P5P11P12P15m3. try clear HP1P2P3P4P5P11P12P15m2. try clear HP1P2P3P4P5P11P12P15m1. 

assert(HP1P2P3P4P5P11P12P13P14P15m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 5 5 HP1P2P3P4P5mtmp Hcomp Hincl);apply HT.
}


assert(HP1P2P3P4P5P11P12P13P14P15M5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) <= 5).
{
	try assert(HP1P2P3P4P5P14eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: nil) = 5) by (apply LP1P2P3P4P5P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P14Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P14eq HP1P2P3P4P5P14M5).
	try assert(HP1P2P3P4P5P11P12P13P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) = 5) by (apply LP1P2P3P4P5P11P12P13P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P11P12P13P15Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P11P12P13P15eq HP1P2P3P4P5P11P12P13P15M5).
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: nil) ++ (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P1 :: P2 :: P3 :: P4 :: P5 :: P14 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: nil) 5 5 5 HP1P2P3P4P5P14Mtmp HP1P2P3P4P5P11P12P13P15Mtmp HP1P2P3P4P5mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP1P2P3P4P5P14M1. try clear HP1P2P3P4P5P14M2. try clear HP1P2P3P4P5P14M3. try clear HP1P2P3P4P5P14M4. try clear HP1P2P3P4P5P14M5. try clear HP1P2P3P4P5P14M6. try clear HP1P2P3P4P5P14M7. try clear HP1P2P3P4P5P14m7. try clear HP1P2P3P4P5P14m6. try clear HP1P2P3P4P5P14m5. try clear HP1P2P3P4P5P14m4. try clear HP1P2P3P4P5P14m3. try clear HP1P2P3P4P5P14m2. try clear HP1P2P3P4P5P14m1. try clear HP1P2P3P4P5P11P12P13P15M1. try clear HP1P2P3P4P5P11P12P13P15M2. try clear HP1P2P3P4P5P11P12P13P15M3. try clear HP1P2P3P4P5P11P12P13P15M4. try clear HP1P2P3P4P5P11P12P13P15M5. try clear HP1P2P3P4P5P11P12P13P15M6. try clear HP1P2P3P4P5P11P12P13P15M7. try clear HP1P2P3P4P5P11P12P13P15m7. try clear HP1P2P3P4P5P11P12P13P15m6. try clear HP1P2P3P4P5P11P12P13P15m5. try clear HP1P2P3P4P5P11P12P13P15m4. try clear HP1P2P3P4P5P11P12P13P15m3. try clear HP1P2P3P4P5P11P12P13P15m2. try clear HP1P2P3P4P5P11P12P13P15m1. 

assert(HP6P7P8P9P10P11P15m5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) >= 5).
{
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) 5 5 HP6P7P8P9P10mtmp Hcomp Hincl);apply HT.
}


assert(HP6P7P8P9P10P11P15M5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) <= 5).
{
	try assert(HP6P7P8P9P10P11eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: nil) = 5) by (apply LP6P7P8P9P10P11 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P11Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P11eq HP6P7P8P9P10P11M5).
	try assert(HP6P7P8P9P10P15eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil) = 5) by (apply LP6P7P8P9P10P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P15Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P15eq HP6P7P8P9P10P15M5).
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (list_inter (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil) ((P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: nil) ++ (P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: nil) 5 5 5 HP6P7P8P9P10P11Mtmp HP6P7P8P9P10P15Mtmp HP6P7P8P9P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P7P8P9P10P11M1. try clear HP6P7P8P9P10P11M2. try clear HP6P7P8P9P10P11M3. try clear HP6P7P8P9P10P11M4. try clear HP6P7P8P9P10P11M5. try clear HP6P7P8P9P10P11M6. try clear HP6P7P8P9P10P11M7. try clear HP6P7P8P9P10P11m7. try clear HP6P7P8P9P10P11m6. try clear HP6P7P8P9P10P11m5. try clear HP6P7P8P9P10P11m4. try clear HP6P7P8P9P10P11m3. try clear HP6P7P8P9P10P11m2. try clear HP6P7P8P9P10P11m1. try clear HP6P7P8P9P10P15M1. try clear HP6P7P8P9P10P15M2. try clear HP6P7P8P9P10P15M3. try clear HP6P7P8P9P10P15M4. try clear HP6P7P8P9P10P15M5. try clear HP6P7P8P9P10P15M6. try clear HP6P7P8P9P10P15M7. try clear HP6P7P8P9P10P15m7. try clear HP6P7P8P9P10P15m6. try clear HP6P7P8P9P10P15m5. try clear HP6P7P8P9P10P15m4. try clear HP6P7P8P9P10P15m3. try clear HP6P7P8P9P10P15m2. try clear HP6P7P8P9P10P15m1. 

assert(HP6P7P8P9P10P11P12P15m5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) >= 5).
{
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) 5 5 HP6P7P8P9P10mtmp Hcomp Hincl);apply HT.
}


assert(HP6P7P8P9P10P11P12P15M5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) <= 5).
{
	try assert(HP6P7P8P9P10P12eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) = 5) by (apply LP6P7P8P9P10P12 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P12Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P12eq HP6P7P8P9P10P12M5).
	try assert(HP6P7P8P9P10P11P15eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) = 5) by (apply LP6P7P8P9P10P11P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P11P15Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P11P15eq HP6P7P8P9P10P11P15M5).
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (list_inter (P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) ((P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) ++ (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P7 :: P8 :: P9 :: P10 :: P12 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: nil) 5 5 5 HP6P7P8P9P10P12Mtmp HP6P7P8P9P10P11P15Mtmp HP6P7P8P9P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P7P8P9P10P12M1. try clear HP6P7P8P9P10P12M2. try clear HP6P7P8P9P10P12M3. try clear HP6P7P8P9P10P12M4. try clear HP6P7P8P9P10P12M5. try clear HP6P7P8P9P10P12M6. try clear HP6P7P8P9P10P12M7. try clear HP6P7P8P9P10P12m7. try clear HP6P7P8P9P10P12m6. try clear HP6P7P8P9P10P12m5. try clear HP6P7P8P9P10P12m4. try clear HP6P7P8P9P10P12m3. try clear HP6P7P8P9P10P12m2. try clear HP6P7P8P9P10P12m1. try clear HP6P7P8P9P10P11P15M1. try clear HP6P7P8P9P10P11P15M2. try clear HP6P7P8P9P10P11P15M3. try clear HP6P7P8P9P10P11P15M4. try clear HP6P7P8P9P10P11P15M5. try clear HP6P7P8P9P10P11P15M6. try clear HP6P7P8P9P10P11P15M7. try clear HP6P7P8P9P10P11P15m7. try clear HP6P7P8P9P10P11P15m6. try clear HP6P7P8P9P10P11P15m5. try clear HP6P7P8P9P10P11P15m4. try clear HP6P7P8P9P10P11P15m3. try clear HP6P7P8P9P10P11P15m2. try clear HP6P7P8P9P10P11P15m1. 

assert(HP6P7P8P9P10P11P12P13P15m5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) >= 5).
{
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) 5 5 HP6P7P8P9P10mtmp Hcomp Hincl);apply HT.
}


assert(HP6P7P8P9P10P11P12P13P15M5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) <= 5).
{
	try assert(HP6P7P8P9P10P13eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: nil) = 5) by (apply LP6P7P8P9P10P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P13Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P13eq HP6P7P8P9P10P13M5).
	try assert(HP6P7P8P9P10P11P12P15eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) = 5) by (apply LP6P7P8P9P10P11P12P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P11P12P15Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P11P12P15eq HP6P7P8P9P10P11P12P15M5).
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (list_inter (P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) ((P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: nil) ++ (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P7 :: P8 :: P9 :: P10 :: P13 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: nil) 5 5 5 HP6P7P8P9P10P13Mtmp HP6P7P8P9P10P11P12P15Mtmp HP6P7P8P9P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P7P8P9P10P13M1. try clear HP6P7P8P9P10P13M2. try clear HP6P7P8P9P10P13M3. try clear HP6P7P8P9P10P13M4. try clear HP6P7P8P9P10P13M5. try clear HP6P7P8P9P10P13M6. try clear HP6P7P8P9P10P13M7. try clear HP6P7P8P9P10P13m7. try clear HP6P7P8P9P10P13m6. try clear HP6P7P8P9P10P13m5. try clear HP6P7P8P9P10P13m4. try clear HP6P7P8P9P10P13m3. try clear HP6P7P8P9P10P13m2. try clear HP6P7P8P9P10P13m1. try clear HP6P7P8P9P10P11P12P15M1. try clear HP6P7P8P9P10P11P12P15M2. try clear HP6P7P8P9P10P11P12P15M3. try clear HP6P7P8P9P10P11P12P15M4. try clear HP6P7P8P9P10P11P12P15M5. try clear HP6P7P8P9P10P11P12P15M6. try clear HP6P7P8P9P10P11P12P15M7. try clear HP6P7P8P9P10P11P12P15m7. try clear HP6P7P8P9P10P11P12P15m6. try clear HP6P7P8P9P10P11P12P15m5. try clear HP6P7P8P9P10P11P12P15m4. try clear HP6P7P8P9P10P11P12P15m3. try clear HP6P7P8P9P10P11P12P15m2. try clear HP6P7P8P9P10P11P12P15m1. 

assert(HP6P7P8P9P10P11P12P13P14P15m5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 5).
{
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 5 5 HP6P7P8P9P10mtmp Hcomp Hincl);apply HT.
}


assert(HP6P7P8P9P10P11P12P13P14P15M5 : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) <= 5).
{
	try assert(HP6P7P8P9P10P14eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: nil) = 5) by (apply LP6P7P8P9P10P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P14Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P14eq HP6P7P8P9P10P14M5).
	try assert(HP6P7P8P9P10P11P12P13P15eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) = 5) by (apply LP6P7P8P9P10P11P12P13P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P11P12P13P15Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P11P12P13P15eq HP6P7P8P9P10P11P12P13P15M5).
	try assert(HP6P7P8P9P10eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 5) by (apply LP6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 5) by (solve_hyps_min HP6P7P8P9P10eq HP6P7P8P9P10m5).
	assert(Hincl : incl (P6 :: P7 :: P8 :: P9 :: P10 :: nil) (list_inter (P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) ((P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: nil) ++ (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P6 :: P7 :: P8 :: P9 :: P10 :: P14 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: nil) 5 5 5 HP6P7P8P9P10P14Mtmp HP6P7P8P9P10P11P12P13P15Mtmp HP6P7P8P9P10mtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP6P7P8P9P10P14M1. try clear HP6P7P8P9P10P14M2. try clear HP6P7P8P9P10P14M3. try clear HP6P7P8P9P10P14M4. try clear HP6P7P8P9P10P14M5. try clear HP6P7P8P9P10P14M6. try clear HP6P7P8P9P10P14M7. try clear HP6P7P8P9P10P14m7. try clear HP6P7P8P9P10P14m6. try clear HP6P7P8P9P10P14m5. try clear HP6P7P8P9P10P14m4. try clear HP6P7P8P9P10P14m3. try clear HP6P7P8P9P10P14m2. try clear HP6P7P8P9P10P14m1. try clear HP6P7P8P9P10P11P12P13P15M1. try clear HP6P7P8P9P10P11P12P13P15M2. try clear HP6P7P8P9P10P11P12P13P15M3. try clear HP6P7P8P9P10P11P12P13P15M4. try clear HP6P7P8P9P10P11P12P13P15M5. try clear HP6P7P8P9P10P11P12P13P15M6. try clear HP6P7P8P9P10P11P12P13P15M7. try clear HP6P7P8P9P10P11P12P13P15m7. try clear HP6P7P8P9P10P11P12P13P15m6. try clear HP6P7P8P9P10P11P12P13P15m5. try clear HP6P7P8P9P10P11P12P13P15m4. try clear HP6P7P8P9P10P11P12P13P15m3. try clear HP6P7P8P9P10P11P12P13P15m2. try clear HP6P7P8P9P10P11P12P13P15m1. try clear HP6P7P8P9P10M1. try clear HP6P7P8P9P10M2. try clear HP6P7P8P9P10M3. try clear HP6P7P8P9P10M4. try clear HP6P7P8P9P10M5. try clear HP6P7P8P9P10M6. try clear HP6P7P8P9P10M7. try clear HP6P7P8P9P10m7. try clear HP6P7P8P9P10m6. try clear HP6P7P8P9P10m5. try clear HP6P7P8P9P10m4. try clear HP6P7P8P9P10m3. try clear HP6P7P8P9P10m2. try clear HP6P7P8P9P10m1. 

assert(HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m5 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 5).
{
	try assert(HP1P2P3P4P5eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) = 5) by (apply LP1P2P3P4P5 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: nil) >= 5) by (solve_hyps_min HP1P2P3P4P5eq HP1P2P3P4P5m5).
	assert(Hcomp : 5 <= 5) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 5 5 HP1P2P3P4P5mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5M1. try clear HP1P2P3P4P5M2. try clear HP1P2P3P4P5M3. try clear HP1P2P3P4P5M4. try clear HP1P2P3P4P5M5. try clear HP1P2P3P4P5M6. try clear HP1P2P3P4P5M7. try clear HP1P2P3P4P5m7. try clear HP1P2P3P4P5m6. try clear HP1P2P3P4P5m5. try clear HP1P2P3P4P5m4. try clear HP1P2P3P4P5m3. try clear HP1P2P3P4P5m2. try clear HP1P2P3P4P5m1. 

assert(HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m6 : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 6).
{
	try assert(HP1P2P3P4P5P6P7P8P9P10eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: nil) = 6) by (apply LP1P2P3P4P5P6P7P8P9P10 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8P9P10mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: nil) >= 6) by (solve_hyps_min HP1P2P3P4P5P6P7P8P9P10eq HP1P2P3P4P5P6P7P8P9P10m6).
	assert(Hcomp : 6 <= 6) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) 6 6 HP1P2P3P4P5P6P7P8P9P10mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4P5P6P7P8P9P10M1. try clear HP1P2P3P4P5P6P7P8P9P10M2. try clear HP1P2P3P4P5P6P7P8P9P10M3. try clear HP1P2P3P4P5P6P7P8P9P10M4. try clear HP1P2P3P4P5P6P7P8P9P10M5. try clear HP1P2P3P4P5P6P7P8P9P10M6. try clear HP1P2P3P4P5P6P7P8P9P10M7. try clear HP1P2P3P4P5P6P7P8P9P10m7. try clear HP1P2P3P4P5P6P7P8P9P10m6. try clear HP1P2P3P4P5P6P7P8P9P10m5. try clear HP1P2P3P4P5P6P7P8P9P10m4. try clear HP1P2P3P4P5P6P7P8P9P10m3. try clear HP1P2P3P4P5P6P7P8P9P10m2. try clear HP1P2P3P4P5P6P7P8P9P10m1. 

assert(HP11P12P13P14P15m4 : rk(P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 4).
{
	try assert(HP11P12P13P14eq : rk(P11 :: P12 :: P13 :: P14 :: nil) = 4) by (apply LP11P12P13P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP11P12P13P14mtmp : rk(P11 :: P12 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP11P12P13P14eq HP11P12P13P14m4).
	assert(Hcomp : 4 <= 4) by (repeat constructor).
	assert(Hincl : incl (P11 :: P12 :: P13 :: P14 :: nil) (P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P11 :: P12 :: P13 :: P14 :: nil) (P11 :: P12 :: P13 :: P14 :: P15 :: nil) 4 4 HP11P12P13P14mtmp Hcomp Hincl);apply HT.
}
try clear HP11P12P13P14M1. try clear HP11P12P13P14M2. try clear HP11P12P13P14M3. try clear HP11P12P13P14M4. try clear HP11P12P13P14M5. try clear HP11P12P13P14M6. try clear HP11P12P13P14M7. try clear HP11P12P13P14m7. try clear HP11P12P13P14m6. try clear HP11P12P13P14m5. try clear HP11P12P13P14m4. try clear HP11P12P13P14m3. try clear HP11P12P13P14m2. try clear HP11P12P13P14m1. 

assert(HP11P12P13P14P15M4 : rk(P11 :: P12 :: P13 :: P14 :: P15 :: nil) <= 4).
{
	try assert(HP1P2P3P4P5P11P12P13P14P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) = 5) by (apply LP1P2P3P4P5P11P12P13P14P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P11P12P13P14P15Mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) <= 5) by (solve_hyps_max HP1P2P3P4P5P11P12P13P14P15eq HP1P2P3P4P5P11P12P13P14P15M5).
	try assert(HP6P7P8P9P10P11P12P13P14P15eq : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) = 5) by (apply LP6P7P8P9P10P11P12P13P14P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP6P7P8P9P10P11P12P13P14P15Mtmp : rk(P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) <= 5) by (solve_hyps_max HP6P7P8P9P10P11P12P13P14P15eq HP6P7P8P9P10P11P12P13P14P15M5).
	try assert(HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15eq : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) = 6) by (apply LP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15mtmp : rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) >= 6) by (solve_hyps_min HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15eq HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m6).
	assert(Hincl : incl (P11 :: P12 :: P13 :: P14 :: P15 :: nil) (list_inter (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) ((P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) ++ (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15mtmp;try rewrite HT2 in HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15mtmp.
	assert(HT := rule_3 (P1 :: P2 :: P3 :: P4 :: P5 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P6 :: P7 :: P8 :: P9 :: P10 :: P11 :: P12 :: P13 :: P14 :: P15 :: nil) (P11 :: P12 :: P13 :: P14 :: P15 :: nil) 5 5 6 HP1P2P3P4P5P11P12P13P14P15Mtmp HP6P7P8P9P10P11P12P13P14P15Mtmp HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15mtmp Hincl);apply HT.
}
try clear HP1P2P3P4P5P11P12P13P14P15M1. try clear HP1P2P3P4P5P11P12P13P14P15M2. try clear HP1P2P3P4P5P11P12P13P14P15M3. try clear HP1P2P3P4P5P11P12P13P14P15M4. try clear HP1P2P3P4P5P11P12P13P14P15M5. try clear HP1P2P3P4P5P11P12P13P14P15M6. try clear HP1P2P3P4P5P11P12P13P14P15M7. try clear HP1P2P3P4P5P11P12P13P14P15m7. try clear HP1P2P3P4P5P11P12P13P14P15m6. try clear HP1P2P3P4P5P11P12P13P14P15m5. try clear HP1P2P3P4P5P11P12P13P14P15m4. try clear HP1P2P3P4P5P11P12P13P14P15m3. try clear HP1P2P3P4P5P11P12P13P14P15m2. try clear HP1P2P3P4P5P11P12P13P14P15m1. try clear HP6P7P8P9P10P11P12P13P14P15M1. try clear HP6P7P8P9P10P11P12P13P14P15M2. try clear HP6P7P8P9P10P11P12P13P14P15M3. try clear HP6P7P8P9P10P11P12P13P14P15M4. try clear HP6P7P8P9P10P11P12P13P14P15M5. try clear HP6P7P8P9P10P11P12P13P14P15M6. try clear HP6P7P8P9P10P11P12P13P14P15M7. try clear HP6P7P8P9P10P11P12P13P14P15m7. try clear HP6P7P8P9P10P11P12P13P14P15m6. try clear HP6P7P8P9P10P11P12P13P14P15m5. try clear HP6P7P8P9P10P11P12P13P14P15m4. try clear HP6P7P8P9P10P11P12P13P14P15m3. try clear HP6P7P8P9P10P11P12P13P14P15m2. try clear HP6P7P8P9P10P11P12P13P14P15m1. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M1. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M2. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M3. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M4. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M5. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M6. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15M7. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m7. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m6. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m5. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m4. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m3. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m2. try clear HP1P2P3P4P5P6P7P8P9P10P11P12P13P14P15m1. 

assert(HP11P12P13P14P15M : rk(P11 :: P12 :: P13 :: P14 :: P15 ::  nil) <= 5) by (solve_hyps_max HP11P12P13P14P15eq HP11P12P13P14P15M5).
assert(HP11P12P13P14P15m : rk(P11 :: P12 :: P13 :: P14 :: P15 ::  nil) >= 1) by (solve_hyps_min HP11P12P13P14P15eq HP11P12P13P14P15m1).
intuition.
Qed.

