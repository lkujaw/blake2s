theory quadlets
imports "HOL-SPARK.SPARK"
begin

(* GLOBAL DEFINITIONS & LEMMAS *)

definition quadlet_last :: int
  where "quadlet_last = 2^32 - 1"

definition doublet_last :: int
  where "doublet_last = 2^16 - 1"

lemma product_lte: "0 <= x ==> 0 <= y ==> x <= a ==>
    y <= a ==> x * y <= a^2" for x y :: int
  by (simp add: power2_eq_square Rings.ordered_semiring_class.mult_mono)

lemma quadlet_pow: "4294967296::int == 2^32" by simp
lemma quadlet_pow2: "4294967296::int == 2^(16 * 2)" by simp
lemma doublet_pow: "65536::int == 2^16" by simp

lemma quadlet_last_pow: "4294967295::int == (2^32) - 1" by simp
lemma doublet_last_pow: "65535::int == (2^16) - 1" by simp

lemma mod_shift: "x mod 2^e * 2 = x * 2 mod 2^(Suc e)"
  for x::nat by simp

lemma mod_shift_int: "0 <= (x::int) ==>
    x mod 2^e * 2 = x * 2 mod 2^(Suc e)"
  by (simp add: mod_shift)

(* From the HOL-SPARK reference manual *)
lemma AND_mod: "x AND (2^n - 1) = x mod 2^n"
  for x :: int by (simp flip: mask_eq_exp_minus_1 take_bit_eq_mask
                   take_bit_eq_mod)

lemma AND_mod16: "x AND 65535 = x mod 2^16"
  for x :: int by (presburger add: doublet_last_pow AND_mod)

lemma AND_mod32: "x AND 4294967295 = x mod 2^32"
  for x :: int by (presburger add: quadlet_last_pow AND_mod)

lemma div_mod16: "0 <= x ==> x <= 4294967295 ==>
    x div 65536 <= 65535"
  for x :: int by linarith

definition booleans32 :: "int => int => bool"
  where "booleans32 operand index =
    bit operand (if index < 0 | index > 31 then undefined else nat index)"

definition from_booleans32 :: "(int => bool) => int"
  where "from_booleans32 array = horner_sum of_bool 2 (map array [0..31])"

lemma null_prefix: "0 <= (x::int) ==> x <= 2^bits - 1 ==>
    (n >= bits ==> bit x n = False)"
  by (metis bit_take_bit_iff mod_pos_pos_trivial not_le take_bit_eq_mod
            zle_diff1_eq)

lemma highest_bit_set: "2^n - 1 < (x::int) ==> x <= 2^Suc n - 1 ==>
    bit x n = True"
proof -
  assume a1: "2^n - 1 < x"
  assume a2: "x <= 2^Suc n - 1"
  then have "0 < x" using a1
    by (metis le_less_trans not_exp_less_eq_0_int not_le zle_diff1_eq)
  thus ?thesis using a1 a2
    by (metis add.left_neutral mult_eq_0_iff not_le of_bool_def
              order_le_less take_bit_Suc_from_most take_bit_int_eq_self
              take_bit_int_less_exp zle_diff1_eq)
qed

lemma bit_int32_eqI:
  "0 <= (a::int) ==> a <= 2^32 - 1 ==> 0 <= (b::int) ==> b <= 2^32 - 1 ==>
    (\<forall>(n::nat) \<in> {0..31}. bit a n = bit b n) ==> a = b"
proof -
  assume a0: "0 <= (a::int)"
  assume a1: "a <= 2^32 - (1::int)"
  assume b0: "0 <= (b::int)"
  assume b1: "b <= 2^32 - (1::int)"
  assume "\<forall>(n::nat) \<in> {0..31}. bit a n = bit b n"
  moreover from a0 a1 null_prefix
  have "\<And>n. n >= 32 ==> bit a n = False" by metis
  moreover from b0 b1 null_prefix
  have "\<And>n. n >= 32 ==> bit b n = False" by metis
  ultimately show ?thesis by (auto simp add: bit_eq_iff)
qed

lemma booleans32_reverse_iff:
    "bit (from_booleans32 (booleans32 x)) n = (n < 32 & bit x n)"
  for x :: "int"
  by (cases "n < 32", simp_all add: from_booleans32_def booleans32_def
                      bit_horner_sum_bit_iff)

lemma from_booleans32_max: "from_booleans32 (x) <= 2^32 - 1"
proof -
  have RW: "32 = length (map x [0..31])" by simp
  show ?thesis
    by (subst from_booleans32_def booleans32_def, subst zle_diff1_eq,
        subst RW, subst horner_sum_of_bool_2_less, rule)
qed

lemma from_booleans32_min: "0 <= from_booleans32 (x)"
  by (simp add: sum_nonneg horner_sum_eq_sum from_booleans32_def
                booleans32_def)

lemma booleans32_sym: "0 <= (x::int) ==> x <= 2^32 - 1 ==>
    from_booleans32 (booleans32 x) = x"
  by (subst bit_int32_eqI,
      auto simp add: booleans32_reverse_iff,
      presburger add: from_booleans32_min,
      presburger add: from_booleans32_max quadlet_last_pow)

lemma booleans32_eqI:
  "0 <= (a::int) ==> a <= 2^32 - 1 ==> 0 <= (b::int) ==> b <= 2^32 - 1 ==>
     a = b ==> (booleans32 a) = (booleans32 b)"
  by simp

definition booleans_and :: "(int => bool) => (int => bool) => int => bool"
  where "booleans_and left_array right_array index ==
    left_array (index) & right_array (index)"

definition booleans_not :: "(int => bool) => int => bool"
  where "booleans_not array index == ~ array index"

definition booleans_or :: "(int => bool) => (int => bool) => int => bool"
  where "booleans_or left_array right_array index ==
    left_array (index) | right_array (index)"

definition booleans_xor :: "(int => bool) => (int => bool) => int => bool"
  where "booleans_xor left_array right_array index ==
    left_array (index) ~= right_array (index)"

lemma sum_head: "0 < (n::nat) ==>
    (\<Sum>i \<in> {0..<n}. f i) = f 0 + (\<Sum>i \<in> {1..<n}. f i)"
  by (simp add: sum.atLeast_Suc_lessThan)

lemma sum_tail:
    "(\<Sum>i \<in> {0..<(Suc n)}. f i) = f n + (\<Sum>i \<in> {0..<n}. f i)"
  by (simp add: add.commute)

lemma isolate: "((x::int) + y = z) = (y = z - x)"
  by fastforce

lemma not_sum: "0 <= (x::int) ==>
  (\<Sum>k = 0..<n. if bit x k then 0 else 2^k) = (2^n - 1) - (take_bit n x)"
proof (induction n arbitrary: x)
  case 0
  thus ?case by (simp add: sum_head)
next
  case (Suc n)
  thus ?case
    by (simp add: Suc.prems(1) Suc.IH sum_tail null_prefix
                  take_bit_Suc_from_most)
qed

lemma mod1_nat: "~ n dvd Suc (x::nat) ==>
    (Suc x) mod n = Suc (x mod n)"
  by (auto simp add: Euclidean_Division.mod_Suc dvd_eq_mod_eq_0)

lemma mod1: "0 <= (n::int) ==> ~ n dvd 1 + x ==>
    (1 + x) mod n = 1 + x mod n"
proof (cases "n = 0")
  case True
  thus ?thesis by simp
next
  case False
  assume a2: "0 <= n"
  assume a3: "~ n dvd 1 + x"
  assume a4: "n ~= 0"
  from a2 a4 have c1: "0 < n" by simp
  have c2: "(1 + x) mod n = (1 + (x mod n)) mod n" by (simp add: mod_simps)
  have "1 + x mod n ~= n"
    by (metis a3 dvd_eq_mod_eq_0 mod_add_right_eq mod_self)
  then have c3: "1 + x mod n < n"
    by (metis Euclidean_Division.pos_mod_bound c1 add.commute
              add_less_cancel_left zless_add1_eq)
  have c4: "(1 + (x mod n)) mod n = 1 + (x mod n)"
    by (rule mod_pos_pos_trivial, auto simp add: c1 c3)
  show ?thesis by (subst c2, subst c4, rule)
qed

lemma mod_plus_base: "0 <= (x::int) ==> 0 <= n ==>
  (\<And>i. i \<in> {1..x} ==> ~ n dvd y + i) ==> (x + y) mod n = x + y mod n"
proof (induct x arbitrary: n y rule: int_ge_induct)
  case base
  thus ?case by simp
next
  case (step x)
  have H: "~ n dvd (1::int) + (x + y)"
  proof (safe)
    assume a1: "n dvd 1 + (x + y)"
    have "\<forall>i. (i::int) <= i" by simp
    then show False
      using a1 by (metis add.assoc add.commute atLeastAtMost_iff
                         le_add_same_cancel2 step.hyps(1) step.prems(2))
  qed
  then have RWIH: "(x + 1 + y) mod n = 1 + ((x + y) mod n)"
    by (simp add: algebra_simps mod1 dvd_def step.prems(1) step.prems(2))
  thus ?case using step.prems by (subst RWIH, subst step.hyps(2),
                                  blast, simp, presburger)
qed

lemma mod_plus: "0 <= (x::int) ==> 0 <= n ==> x <= n - (y mod n + 1) ==>
    (x + y) mod n = x + y mod n"
proof -
  assume a1: "0 <= x"
  assume a2: "0 <= n"
  assume a3: "x <= n - (y mod n + 1)"
  then have "(y + x <= y + (n - (y mod n + 1)))" by force
  then have "(y + x <= y - y mod n + n - 1)" by simp
  then have pre: "(y + x <= n * (y div n) + n - 1)"
    by (auto simp add: minus_mod_eq_mult_div)
  then have "\<And>(i::int) k. 1 <= i ==> i <= x ==> y + i = n * k ==> False"
  proof -
    fix i k
    assume ca1: "(1::int) <= i"
    assume ca2: "i <= x"
    assume ca3: "y + i = n * k"
    hence "(y + i) mod n = (n * k) mod n" by simp
    then have f: "(y + i) mod n = 0" by simp
    then have "0 ~= n" using a3 ca2 by force
    then have "y + x <= y + n - 1" using a2 pre
      by (metis Euclidean_Division.pos_mod_sign a3 add.commute
                add_le_cancel_right diff_mono dual_order.antisym
                le_add_same_cancel1 not_le zle_diff1_eq)
    then have "x <= n - 1" by simp
    then have "i <= n - 1" using ca2 by simp
    then have "i = i mod n" using ca1 by auto
    then have "i = 0" using a3 ca2 f
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_add_cancel
                diff_diff_add mod_add_self2 mod_diff_eq not_le zle_diff1_eq
                zmod_zminus1_eq_if)
    then show False using ca1 by linarith
  qed

  thus ?thesis by (subst mod_plus_base, auto simp add: a1 a2 dvd_def)
qed

lemma div_truncate_plus: "0 <= (n::int) ==> 0 <= y ==>
     y <= n - (x mod n + 1) ==> (x + y) div n = x div n"
proof -
  assume a1: "0 <= n"
  assume a2: "0 <= y"
  assume a3: "y <= n - (x mod n + 1)"
  then have s1: "((x + y) div n = x div n) =
      (n * ((x + y) div n) = n * (x div n))" by force
  have s2: "(n * ((x + y) div n) = n * (x div n)) =
      ((x + y) - ((y + x) mod n) = x - (x mod n))"
    by (auto simp add: add.commute minus_mod_eq_mult_div [symmetric])
  then show ?thesis
    by (subst s1, subst s2, insert a1, simp add: mod_simps,
        subst mod_plus, auto simp add: a1 a2 a3)
qed

lemma div_truncate_one: "0 <= (x::int) ==> 1 < n ==> ~ n dvd (1 + x) ==>
    (1 + x) div n = x div n"
proof -
  assume a1: "0 <= x"
  assume a2: "1 < n"
  assume a3: "~ n dvd (1 + x)"
  from a3 have c1: "1 + x mod n > 0"
  proof -
    have "0 <= x mod n"
      using a2 by force
    then show ?thesis
      by linarith
    qed
    from a3 have c2: "1 + x mod n < n"
    proof -
  have "0 ~= (1 + x) mod n"
    by (metis a3 mod_0_imp_dvd)
    then show ?thesis
      by (metis a2 add_diff_cancel_left' int_mod_neg_eq less_le
                   mod_add_right_eq mod_self not_one_le_zero
                   unique_euclidean_semiring_numeral_class.pos_mod_bound
                   verit_comp_simplify1(3) zle_diff1_eq)
  qed
  have RW: "(1 + x) div n = (x + 1) div n" by (simp add: add.commute)
  show ?thesis using a1 a2 c1 c2
    by (subst RW, subst div_truncate_plus, simp_all)
qed

lemma or_plus_nat:
    "2^(n::nat) + ((x::nat) mod 2^n) = (2^n) OR (x mod 2^n)"
  by (subst disjunctive_add [symmetric], auto,
      metis bit_push_bit_iff bit_take_bit_iff
            le_less_trans nat_neq_iff push_bit_of_1 take_bit_nat_def)

lemma or_plus: "0 <= (x::int) ==> 2^(n::nat) + (x mod 2^n) =
    (2^n) OR (x mod 2^n)"
proof -
  have f1: "ALL a b. (a::int) OR b = a + b | (\<exists>n. bit a n & bit b n)"
    by (metis disjunctive_add)
  have "ALL a b i. ~ bit ((i::int) mod push_bit a 1) b | b < a"
    by (metis bit_take_bit_iff push_bit_of_1 take_bit_eq_mod)
  then have "push_bit n 1 OR x mod push_bit n 1 =
               push_bit n 1 + x mod push_bit n 1"
    using f1 by (metis bit_push_bit_iff dual_order.strict_trans2
                       order.strict_iff_order)
  then show ?thesis
    by (simp add: push_bit_of_1)
qed

lemma and_sum: "0 <= (x::int) ==> 0 <= (y::int) ==>
  (\<Sum>k = 0..<n. if bit x k & bit y k then 2^k else 0) =
    (take_bit n x) AND (take_bit n y)"
proof (induction n arbitrary: x y)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have "ALL a b i. ~ bit ((i::int) mod push_bit a 1) b | b < a"
      by (metis bit_take_bit_iff push_bit_of_1 take_bit_eq_mod)
    then have "push_bit n 1 OR x mod push_bit n 1 AND y mod push_bit n 1 =
               push_bit n 1 + (x mod push_bit n 1 AND y mod push_bit n 1)"
      by (metis bit_and_iff bit_push_bit_iff disjunctive_add leD)
    then have l0: "2^n + (x mod 2^n AND y mod 2^n) =
                    (2^n OR x mod 2^n) AND (2^n OR y mod 2^n)"
      by (simp add: bit.disj_conj_distrib push_bit_of_1)
    have f1: "ALL a b. (b::int) + a + - 1 *
                (a OR b) + - 1 * (a AND b) = 0"
      by (metis add_eq_0_iff group_cancel.add1 group_cancel.neg1
                mult_minus1 plus_and_or)
    have "y mod 2^n + 2^n + - 1 * (2^n OR y mod 2^n) + - 1 *
            (2^n AND y mod 2^n) = 2^n + y mod 2^n + - 1 *
              (2^n AND y mod 2^n) + - 1 * (2^n OR y mod 2^n)"
      by presburger
    then have "2^n + y mod 2^n + - 1 * (2^n AND y mod 2^n) + - 1 *
                 (2^n OR y mod 2^n) = 0"
      by (presburger add: f1)
    then have l1: "(2^n OR x mod 2^n) AND y mod 2^n =
                     x mod 2^n AND y mod 2^n"
      by (auto simp add: Suc.prems(2) or_plus algebra_simps plus_and_or
                         bit.conj_disj_distrib2)
    then have "ALL a b n. (b::int) AND take_bit n a =
                 take_bit n b AND a"
      by (metis and.commute bit.conj_ac(1) take_bit_eq_mask)
    then have l2: "x mod 2^n AND (2^n OR y mod 2^n) =
                     x mod 2^n AND y mod 2^n"
      using and.commute bit.disj_zero_right or.commute
      by (metis bit.conj_disj_distrib2 mod_self take_bit_eq_mask
                take_bit_int_def)
    show ?case
      by (simp add: take_bit_Suc_from_most,
          auto simp add: l0 l1 l2 isolate algebra_simps Suc.prems
                         take_bit_eq_mod or_plus Suc.IH)
qed

lemma or_sum: "0 <= (x::int) ==> 0 <= (y::int) ==>
  (\<Sum>k = 0..<n. if bit x k | bit y k then 2^k else 0) =
    (take_bit n x) OR (take_bit n y)"
proof (induction n arbitrary: x y)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have f1: "\<forall>n i. (i::int) AND mask n = i mod push_bit n 1"
    by (metis push_bit_of_1 take_bit_eq_mask take_bit_eq_mod)
  have "push_bit n 1 OR push_bit n 1 OR (x OR y) AND mask n =
          push_bit n 1 + ((x OR y) AND mask n)"
    by (metis bit_push_bit_iff bit_take_bit_iff disjunctive_add leD
              or.left_idem take_bit_eq_mask)
  then have "push_bit n 1 OR y AND mask n OR push_bit n 1 OR x AND mask n =
               push_bit n 1 + ((x OR y) AND mask n)"
    by (metis bit.conj_disj_distrib2 bit.disj_commute bit.disj_left_commute)
  then have "push_bit n 1 OR (push_bit n 1 OR x mod push_bit n 1) OR
               y AND mask n = push_bit n 1 +
                 (x mod push_bit n 1 OR y AND mask n)"
    using f1 by (metis bit.conj_disj_distrib2 bit.disj_commute)
  then have l1: "2^n + (x mod 2^n OR y mod 2^n) =
                   (2^n OR x mod 2^n) OR 2^n OR y mod 2^n"
    using f1 by (simp add: bit.disj_left_commute push_bit_of_1)
  have "push_bit n 1 OR take_bit n x OR take_bit n y =
          push_bit n 1 + (take_bit n x OR take_bit n y)"
    by (metis bit.conj_disj_distrib2 bit_push_bit_iff bit_take_bit_iff
              disjunctive_add leD take_bit_eq_mask)
  then have l2: "2^n + (x mod 2^n OR y mod 2^n) =
                   (2^n OR x mod 2^n) OR y mod 2^n"
    by (simp add: bit.disj_commute bit.disj_left_commute push_bit_of_1
                  take_bit_eq_mod)
  have "push_bit n 1 OR take_bit n x OR take_bit n y =
          push_bit n 1 + (take_bit n x OR take_bit n y)"
    by (metis bit.conj_disj_distrib2 bit_push_bit_iff bit_take_bit_iff
              disjunctive_add leD take_bit_eq_mask)
  then have l3: "2^n + (x mod 2^n OR y mod 2^n) =
                   x mod 2^n OR 2^n OR y mod 2^n"
    by (simp add: bit.disj_left_commute push_bit_of_1 take_bit_eq_mod)
  show ?case
    by (simp add: take_bit_Suc_from_most,
        auto simp add: algebra_simps Suc.prems take_bit_eq_mod
                       or_plus Suc.IH,
        simp add: l1, simp add: l2, simp add: l3)
qed

lemma xor_sum: "0 <= (x::int) ==> 0 <= (y::int) ==>
  (\<Sum>k = 0..<n. if bit x k = (~ bit y k) then 2^k else 0) =
    (take_bit n x) XOR (take_bit n y)"
proof (induction n arbitrary: x y)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have c1: "bit y n ==> bit x n ==> take_bit n x XOR take_bit n y =
      take_bit n x + 2^n XOR take_bit n y + 2^n"
  proof -
    assume a1: "bit y n"
    assume a2: "bit x n"
    then have "take_bit n (x XOR y) = take_bit (Suc n) (x XOR y)"
      by (metis a1 a2 add.left_neutral bit_xor_iff mult_zero_right
                of_bool_def take_bit_Suc_from_most)
    then show ?thesis
      by (simp add: a1 a2 add.commute take_bit_Suc_from_most)
  qed
  have c2: "bit y n ==> ~ bit x n ==> 2^n +
      (take_bit n x XOR take_bit n y) = take_bit n x XOR take_bit n y + 2^n"
  proof -
    assume a1: "bit y n"
    assume a2: "~ bit x n"
    then have "bit (x XOR y) n"
      using a1 bit_xor_iff by blast
    then show ?thesis
      using a1 a2 by (metis add.commute add.left_neutral mult.right_neutral
                            mult_zero_right of_bool_def
                            take_bit_Suc_from_most take_bit_xor)
  qed
  have c3: "~ bit y n ==> bit x n ==>
    2^n + (take_bit n x XOR take_bit n y) =
      take_bit n x + 2^n XOR take_bit n y"
  proof -
    assume a1: "~ bit y n"
    assume a2: "bit x n"
    then have "bit (x XOR y) n" using a1 a2 bit_xor_iff
      by blast
    then show "2^n + (take_bit n x XOR take_bit n y) =
                 take_bit n x + 2^n XOR take_bit n y"
      by (metis a1 a2 add.commute add.left_neutral mult.right_neutral
                mult_zero_right of_bool_def take_bit_Suc_from_most
                take_bit_xor)
  qed
  then show ?case
    by (auto simp add: algebra_simps take_bit_Suc_from_most
                       `0 <= x` `0 <= y` Suc.IH c1 c2 c3)
qed

lemma booleans32_and_eq: "0 <= (x::int) ==> x <= 2^32 - 1 ==>
                          0 <= (y::int) ==> y <= 2^32 - 1 ==>
  from_booleans32 (booleans_and (booleans32 x) (booleans32 y)) = x AND y"
proof -
  assume xmin: "0 <= x"
  assume xmax: "x <= 2^32 - (1::int)"
  assume ymin: "0 <= y"
  assume ymax: "y <= 2^32 - (1::int)"
  have "from_booleans32 (booleans_and (booleans32 x) (booleans32 y)) =
         (\<Sum>k::nat = 0..<32. if bit x k & bit y k then 2^k else 0)"
    by (auto simp add: ac_simps horner_sum_eq_sum of_bool_def
                       from_booleans32_def booleans32_def booleans_and_def)
       (auto cong: if_cong simp: if_distrib)
  moreover have "x AND y AND 4294967295 = (x AND 4294967295) AND y"
    by (simp add: and.left_commute bit.conj_ac(2))
  then have "x AND y AND 4294967295 = x AND y"
    using AND_mod32 xmax xmin by force
  ultimately show ?thesis
    by (simp add: xmin ymin and_sum take_bit_eq_mask mask_eq_exp_minus_1
                  and.left_commute)
qed

lemma booleans32_not_eq: "0 <= (x::int) ==> x <= 2^32 - 1 ==>
  from_booleans32 (booleans_not (booleans32 x)) = (2^32 - 1) - x"
proof -
  assume min: "0 <= x"
  assume max: "x <= 2^32 - (1::int)"
  moreover have "from_booleans32 (booleans_not (booleans32 x)) =
         (\<Sum>k::nat = 0..<32. if bit x k then 0 else 2^k)"
    by (simp add: ac_simps if_conn horner_sum_eq_sum of_bool_def
                  from_booleans32_def booleans32_def booleans_not_def)
       (auto cong: if_cong simp: if_distrib)
  ultimately show ?thesis
    by (simp add: min not_sum take_bit_int_eq_self)
qed

lemma booleans32_or_eq: "0 <= (x::int) ==> x <= 2^32 - 1 ==>
                         0 <= (y::int) ==> y <= 2^32 - 1 ==>
  from_booleans32 (booleans_or (booleans32 x) (booleans32 y)) = x OR y"
proof -
  assume xmin: "0 <= x"
  assume xmax: "x <= 2^32 - (1::int)"
  assume ymin: "0 <= y"
  assume ymax: "y <= 2^32 - (1::int)"
  moreover have
    "from_booleans32 (booleans_or (booleans32 x) (booleans32 y)) =
      (\<Sum>k::nat = 0..<32. if bit x k | bit y k then 2^k else 0)"
    by (simp add: ac_simps horner_sum_eq_sum of_bool_def
                  from_booleans32_def booleans32_def booleans_or_def)
       (auto cong: if_cong simp: if_distrib)
  moreover have "x <= 4294967295"
    using quadlet_pow xmax by presburger
  ultimately show ?thesis
    by (simp add: or_sum xmin ymin take_bit_eq_mask
                  mask_eq_exp_minus_1 AND_mod32)
qed

lemma booleans32_xor_eq: "0 <= (x::int) ==> x <= 2^32 - 1 ==>
                          0 <= (y::int) ==> y <= 2^32 - 1 ==>
  from_booleans32 (booleans_xor (booleans32 x) (booleans32 y)) = x XOR y"
proof -
  assume xmin: "0 <= x"
  assume xmax: "x <= 2^32 - (1::int)"
  assume ymin: "0 <= y"
  assume ymax: "y <= 2^32 - (1::int)"
  moreover have
    "from_booleans32 (booleans_xor (booleans32 x) (booleans32 y)) =
      (\<Sum>k::nat = 0..<32. if bit x k = (~ bit y k) then 2^k else 0)"
    by (simp add: ac_simps horner_sum_eq_sum of_bool_def
                  from_booleans32_def booleans32_def booleans_xor_def)
       (auto cong: if_cong simp: if_distrib)
  moreover have "x <= 4294967295"
    using quadlet_pow xmax by presburger
  ultimately show ?thesis
    by (simp add: xor_sum xmin ymin take_bit_eq_mask
                  mask_eq_exp_minus_1 AND_mod32)
qed

spark_proof_functions
  conjunction (integer, integer) : integer = "(AND)"
  inclusive_disjunction (integer, integer) : integer = "(OR)"
  exclusive_disjunction (integer, integer) : integer = "(XOR)"
  booleans32 (integer, integer) : boolean = booleans32
  from_booleans32 = from_booleans32
  booleans32_t__and = booleans_and
  booleans32_t__not = booleans_not
  booleans32_t__or  = booleans_or
  booleans32_t__xor = booleans_xor


(* QUADLETS/NEGATION *)

spark_open "quadlets/negation"

spark_vc function_negation_2
proof -
  from `0 <= value` `value <= 4294967295`
  show ?C1 by
    (subst quadlet_last_pow) (rule booleans32_not_eq, simp_all)
  show ?C2 by (rule from_booleans32_min)
  show ?C3 by (subst quadlet_last_pow, rule from_booleans32_max)
qed

spark_end


(* QUADLETS/CONJUNCTION *)

spark_open "quadlets/conjunction"

spark_vc function_conjunction_1
proof -
  show ?C1 by
    (rule booleans32_and_eq, auto simp add:
       `0 <= left` `0 <= right` `left <= 4294967295` `right <= 4294967295`)
  show ?C2 by (rule from_booleans32_min)
  show ?C3 by (subst quadlet_last_pow, rule from_booleans32_max)
qed

spark_end


(* QUADLETS/INCLUSIVE_DISJUNCTION *)

spark_open "quadlets/inclusive_disjunction"

spark_vc function_inclusive_disjunction_1
proof -
  show ?C1 by
      (rule booleans32_or_eq, auto simp add: `0 <= left` `0 <= right`
       `left <= 4294967295` `right <= 4294967295`)
  show ?C2 by (rule from_booleans32_min)
  show ?C3 by (subst quadlet_last_pow, rule from_booleans32_max)
qed

spark_end


(* QUADLETS/EXCLUSIVE_DISJUNCTION *)

spark_open "quadlets/exclusive_disjunction"

spark_vc function_exclusive_disjunction_1
proof -
  show ?C1 by
      (rule booleans32_xor_eq, auto simp add: `0 <= left` `0 <= right`
       `left <= 4294967295` `right <= 4294967295`)
  show ?C2 by (rule from_booleans32_min)
  show ?C3 by (subst quadlet_last_pow, rule from_booleans32_max)
qed

spark_end


(* QUADLETS/LEFT_SHIFT *)

spark_open "quadlets/left_shift"

spark_vc function_left_shift_3
  by (simp add: `interfaces__shift_left value amount =
        value * 2 ^ nat amount mod 4294967296 mod 0 mod 4294967296`)

spark_end


(* QUADLETS/OCTET *)

spark_open "quadlets/octet"

spark_vc function_octet_3 by simp

spark_end

(* END OF QUADLET PROOFS *)

end