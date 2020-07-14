Lemma LP4P13 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 ,
rk(P3 :: P8 :: P10 ::  nil) = 2 -> rk(P6 :: P11 :: P12 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P13 ::  nil) = 2 ->
rk(P4 :: P5 :: P6 :: P13 ::  nil) = 2 -> rk(P3 :: P4 :: P5 :: P6 :: P8 :: P10 :: P13 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P6 :: P11 :: P12 :: P13 ::  nil) = 4 ->
rk(P4 :: P7 :: P8 :: P14 ::  nil) = 2 -> rk(P1 :: P9 :: P11 :: P14 ::  nil) = 2 -> rk(P1 :: P3 :: P8 :: P9 :: P10 :: P11 :: P14 ::  nil) = 4 ->
rk(P4 :: P6 :: P7 :: P8 :: P11 :: P12 :: P14 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P4 :: P7 :: P8 :: P13 :: P14 ::  nil) = 4 -> rk(P1 :: P4 :: P5 :: P6 :: P9 :: P11 :: P13 :: P14 ::  nil) = 4 ->
rk(P5 :: P9 :: P10 :: P15 ::  nil) = 2 -> rk(P2 :: P7 :: P12 :: P15 ::  nil) = 2 -> rk(P2 :: P3 :: P7 :: P8 :: P10 :: P12 :: P15 ::  nil) = 4 ->
rk(P5 :: P6 :: P9 :: P10 :: P11 :: P12 :: P15 ::  nil) = 4 -> rk(P1 :: P2 :: P3 :: P5 :: P9 :: P10 :: P13 :: P15 ::  nil) = 4 -> rk(P2 :: P4 :: P5 :: P6 :: P7 :: P12 :: P13 :: P15 ::  nil) = 4 ->
rk(P4 :: P5 :: P7 :: P8 :: P9 :: P10 :: P14 :: P15 ::  nil) = 4 -> rk(P1 :: P2 :: P7 :: P9 :: P11 :: P12 :: P14 :: P15 ::  nil) = 4 -> rk(P4 :: P13 ::  nil) = 2.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 
HP3P8P10eq HP6P11P12eq HP1P2P3P13eq HP4P5P6P13eq HP3P4P5P6P8P10P13eq HP1P2P3P6P11P12P13eq HP4P7P8P14eq HP1P9P11P14eq HP1P3P8P9P10P11P14eq HP4P6P7P8P11P12P14eq
HP1P2P3P4P7P8P13P14eq HP1P4P5P6P9P11P13P14eq HP5P9P10P15eq HP2P7P12P15eq HP2P3P7P8P10P12P15eq HP5P6P9P10P11P12P15eq HP1P2P3P5P9P10P13P15eq HP2P4P5P6P7P12P13P15eq HP4P5P7P8P9P10P14P15eq HP1P2P7P9P11P12P14P15eq
.

assert(HP4P7P8P13P14M3 : rk(P4 :: P7 :: P8 :: P13 :: P14 :: nil) <= 3).
{
	try assert(HP13eq : rk(P13 :: nil) = 1) by (apply LP13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP13Mtmp : rk(P13 :: nil) <= 1) by (solve_hyps_max HP13eq HP13M1).
	try assert(HP4P7P8P14eq : rk(P4 :: P7 :: P8 :: P14 :: nil) = 2) by (apply LP4P7P8P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP4P7P8P14Mtmp : rk(P4 :: P7 :: P8 :: P14 :: nil) <= 2) by (solve_hyps_max HP4P7P8P14eq HP4P7P8P14M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P13 :: nil) (P4 :: P7 :: P8 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P7 :: P8 :: P13 :: P14 :: nil) (P13 :: P4 :: P7 :: P8 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P13 :: P4 :: P7 :: P8 :: P14 :: nil) ((P13 :: nil) ++ (P4 :: P7 :: P8 :: P14 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P13 :: nil) (P4 :: P7 :: P8 :: P14 :: nil) (nil) 1 2 0 HP13Mtmp HP4P7P8P14Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}


assert(HP4P7P8P13P14m3 : rk(P4 :: P7 :: P8 :: P13 :: P14 :: nil) >= 3).
{
	try assert(HP1P2P3P13eq : rk(P1 :: P2 :: P3 :: P13 :: nil) = 2) by (apply LP1P2P3P13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P13Mtmp : rk(P1 :: P2 :: P3 :: P13 :: nil) <= 2) by (solve_hyps_max HP1P2P3P13eq HP1P2P3P13M2).
	try assert(HP1P2P3P4P7P8P13P14eq : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P8 :: P13 :: P14 :: nil) = 4) by (apply LP1P2P3P4P7P8P13P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP1P2P3P4P7P8P13P14mtmp : rk(P1 :: P2 :: P3 :: P4 :: P7 :: P8 :: P13 :: P14 :: nil) >= 4) by (solve_hyps_min HP1P2P3P4P7P8P13P14eq HP1P2P3P4P7P8P13P14m4).
	try assert(HP13eq : rk(P13 :: nil) = 1) by (apply LP13 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP13mtmp : rk(P13 :: nil) >= 1) by (solve_hyps_min HP13eq HP13m1).
	assert(Hincl : incl (P13 :: nil) (list_inter (P1 :: P2 :: P3 :: P13 :: nil) (P4 :: P7 :: P8 :: P13 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: P7 :: P8 :: P13 :: P14 :: nil) (P1 :: P2 :: P3 :: P13 :: P4 :: P7 :: P8 :: P13 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P13 :: P4 :: P7 :: P8 :: P13 :: P14 :: nil) ((P1 :: P2 :: P3 :: P13 :: nil) ++ (P4 :: P7 :: P8 :: P13 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4P7P8P13P14mtmp;try rewrite HT2 in HP1P2P3P4P7P8P13P14mtmp.
	assert(HT := rule_4 (P1 :: P2 :: P3 :: P13 :: nil) (P4 :: P7 :: P8 :: P13 :: P14 :: nil) (P13 :: nil) 4 1 2 HP1P2P3P4P7P8P13P14mtmp HP13mtmp HP1P2P3P13Mtmp Hincl); apply HT.
}
try clear HP1P2P3P13M1. try clear HP1P2P3P13M2. try clear HP1P2P3P13M3. try clear HP1P2P3P13m4. try clear HP1P2P3P13m3. try clear HP1P2P3P13m2. try clear HP1P2P3P13m1. try clear HP13M1. try clear HP13M2. try clear HP13M3. try clear HP13m4. try clear HP13m3. try clear HP13m2. try clear HP13m1. try clear HP1P2P3P4P7P8P13P14M1. try clear HP1P2P3P4P7P8P13P14M2. try clear HP1P2P3P4P7P8P13P14M3. try clear HP1P2P3P4P7P8P13P14m4. try clear HP1P2P3P4P7P8P13P14m3. try clear HP1P2P3P4P7P8P13P14m2. try clear HP1P2P3P4P7P8P13P14m1. 

assert(HP4P13m2 : rk(P4 :: P13 :: nil) >= 2).
{
	try assert(HP4P7P8P14eq : rk(P4 :: P7 :: P8 :: P14 :: nil) = 2) by (apply LP4P7P8P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP4P7P8P14Mtmp : rk(P4 :: P7 :: P8 :: P14 :: nil) <= 2) by (solve_hyps_max HP4P7P8P14eq HP4P7P8P14M2).
	try assert(HP4P7P8P13P14eq : rk(P4 :: P7 :: P8 :: P13 :: P14 :: nil) = 3) by (apply LP4P7P8P13P14 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP4P7P8P13P14mtmp : rk(P4 :: P7 :: P8 :: P13 :: P14 :: nil) >= 3) by (solve_hyps_min HP4P7P8P13P14eq HP4P7P8P13P14m3).
	try assert(HP4eq : rk(P4 :: nil) = 1) by (apply LP4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) (P9 := P9) (P10 := P10) (P11 := P11) (P12 := P12) (P13 := P13) (P14 := P14) (P15 := P15) ;try assumption).
	assert(HP4mtmp : rk(P4 :: nil) >= 1) by (solve_hyps_min HP4eq HP4m1).
	assert(Hincl : incl (P4 :: nil) (list_inter (P4 :: P13 :: nil) (P4 :: P7 :: P8 :: P14 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P4 :: P7 :: P8 :: P13 :: P14 :: nil) (P4 :: P13 :: P4 :: P7 :: P8 :: P14 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P4 :: P13 :: P4 :: P7 :: P8 :: P14 :: nil) ((P4 :: P13 :: nil) ++ (P4 :: P7 :: P8 :: P14 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP4P7P8P13P14mtmp;try rewrite HT2 in HP4P7P8P13P14mtmp.
	assert(HT := rule_2 (P4 :: P13 :: nil) (P4 :: P7 :: P8 :: P14 :: nil) (P4 :: nil) 3 1 2 HP4P7P8P13P14mtmp HP4mtmp HP4P7P8P14Mtmp Hincl);apply HT.
}
try clear HP4P7P8P14M1. try clear HP4P7P8P14M2. try clear HP4P7P8P14M3. try clear HP4P7P8P14m4. try clear HP4P7P8P14m3. try clear HP4P7P8P14m2. try clear HP4P7P8P14m1. try clear HP4M1. try clear HP4M2. try clear HP4M3. try clear HP4m4. try clear HP4m3. try clear HP4m2. try clear HP4m1. try clear HP4P7P8P13P14M1. try clear HP4P7P8P13P14M2. try clear HP4P7P8P13P14M3. try clear HP4P7P8P13P14m4. try clear HP4P7P8P13P14m3. try clear HP4P7P8P13P14m2. try clear HP4P7P8P13P14m1. 

assert(HP4P13M : rk(P4 :: P13 ::  nil) <= 2) by (solve_hyps_max HP4P13eq HP4P13M2).
assert(HP4P13m : rk(P4 :: P13 ::  nil) >= 1) by (solve_hyps_min HP4P13eq HP4P13m1).
intuition.
Qed.

