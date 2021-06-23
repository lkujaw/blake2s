theory blake2s
imports "HOL-SPARK.SPARK" "quadlets"
begin


(* BLAKE2S/INCORPORATE_FLEX *)

spark_open "blake2s/incorporate_flex"

spark_vc procedure_incorporate_flex_7
proof -
  from `message_last - (message_first - 1) <= 64 &
          message_index__1 = message_first - 1
        |
        64 < message_last - (message_first - 1) &
          message_index__1 < message_last`
        `message_last - 64 <= message_index__1`
  show ?thesis by linarith
qed

spark_vc procedure_incorporate_flex_9
proof -
  from `0 <= buffer_index context`
  show ?C1 by (simp add: div_pos_geq sdiv_pos_pos)
  show ?C2 by simp
qed

spark_vc procedure_incorporate_flex_10
proof -
  from `0 <= buffer_index context` `buffer_index context mod 4 = 0`
  show ?C1 using sdiv_pos_pos by auto
  from `buffer_index context mod 4 = 0`
  show ?C2 by auto
qed

spark_vc procedure_incorporate_flex_11
proof -
  from `buffer_index context mod 4 = 1`
  have "(1 + buffer_index context) mod 4 ~= 0"
    using bits_one_mod_two_eq_one dvd_imp_mod_0 mod_mult_self1 mult.commute
    by presburger
  hence "~ 4 dvd (1 + buffer_index context)" by auto
  thus ?C1 using `0 <= buffer_index context`
    by (simp add: algebra_simps sdiv_pos_pos,
        subst div_truncate_one, simp_all)
  thus ?C2 using ` buffer_index context mod 4 = 1` by presburger
qed

spark_vc procedure_incorporate_flex_12
proof -
  from `buffer_index context mod 4 = 2`
  have "(1 + buffer_index context) mod 4 ~= 0"
    using bits_one_mod_two_eq_one dvd_imp_mod_0 mod_mult_self1 mult.commute
    by presburger
  hence "~ 4 dvd (1 + buffer_index context)" by auto
  thus ?C1 using `0 <= buffer_index context`
    by (simp add: algebra_simps sdiv_pos_pos,
        subst div_truncate_one, simp_all)
  thus ?C2 using `buffer_index context mod 4 = 2` by presburger
qed

spark_vc procedure_incorporate_flex_13
proof -
  from `buffer_index context mod 4 = 3`
  have "(1 + (buffer_index context)) mod 4 = 0"
    using bits_one_mod_two_eq_one dvd_imp_mod_0 mod_mult_self1 mult.commute
    by presburger
  hence l1: "4 dvd (1 + buffer_index context)" by auto
  hence "~4 dvd buffer_index context"
    using `buffer_index context mod 4 = 3` by auto
  hence "buffer_index context div 4 =
           (1 + buffer_index context) div 4  - 1"
    using l1 cancel_div_mod_rules(2)
          div_add_self2 nonzero_mult_div_cancel_left by auto
  thus ?C1 using `0 <= buffer_index context` by (simp add: sdiv_pos_pos)
  thus ?C2 using `buffer_index context mod 4 = 3` by presburger
qed

spark_vc procedure_incorporate_flex_21
proof -
  from `message_last - message_index <= 64 &
          message_index__4 = message_index
        | 64 < message_last - message_index &
           message_index__4 < message_last`
       `message_last - 64 <= message_index__4`
       `message_first - 1 <= message_index`
  show ?C1 by auto
  from `message_last - message_index <= 64 &
          message_index__4 = message_index
        | 64 < message_last - message_index &
           message_index__4 < message_last`
     `message_index < message_last`
  show ?C2 by auto
  from `message_last \<le> message__index__subtype__1__last`
       `message_index__4 < message_last`
  show ?C3 by simp
qed

spark_vc procedure_incorporate_flex_23
proof -
  from `buffer_index context = 0`
  show ?thesis by (simp add: sdiv_pos_pos)
qed

spark_vc procedure_incorporate_flex_26
proof -
  from `buffer_index context mod 4 = 0`
  have l1: "4 dvd buffer_index context" by presburger
  hence "buffer_index context ~= 63" by presburger
  moreover from l1 have "buffer_index context ~= 62" by presburger
  moreover from l1 have "buffer_index context ~= 61" by presburger
  ultimately show ?thesis using `buffer_index context < 64` by auto
qed

spark_end


(* BLAKE2S/INITIAL_KEYED_FLEX *)

spark_open "blake2s/initial_keyed_flex"

spark_vc function_initial_keyed_flex_6
proof -
  from `key_length <=
          key__index__subtype__1__last - key__index__subtype__1__first + 1`
       `key__index__subtype__1__last <= 32`
  show "key__index__subtype__1__first - 1 + key_length <= 32" by simp
qed

spark_vc function_initial_keyed_flex_11
proof -
  from `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 0`
  show ?C1 using mod_add_self2 by presburger
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first - 1`
  show ?C2 by (simp_all add: sdiv_pos_pos)
qed

spark_vc function_initial_keyed_flex_28
proof -
  from `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 0`
  show ?C1 using mod_add_self2 by presburger
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first - 1`
  show ?C2 by (simp add: sdiv_pos_pos)
qed

spark_vc function_initial_keyed_flex_30
proof -
  from `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 0`
  show ?C1 using mod_add_self2 by presburger
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first - 1`
  have rw: "(2 + (key_index - key__index__subtype__1__first)) div 4 =
            ((key_index - (key__index__subtype__1__first - 1)) + 1) div 4"
    by (simp add: algebra_simps)
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first - 1`
       `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 0`
  show ?C2
    by (simp add: sdiv_pos_pos, subst rw, subst div_truncate_plus,
        simp_all)
qed

spark_vc function_initial_keyed_flex_33
proof -
  from `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 1`
  show ?C1 using mod_add_self2 by presburger
  from `key__index__subtype__1__first >= 1`
        `key_index >= key__index__subtype__1__first`
  have rw: "(2 + (key_index - key__index__subtype__1__first)) div 4 =
            ((key_index - (key__index__subtype__1__first - 1)) + 1) div 4"
    by (simp add: algebra_simps)
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first`
       `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 1`
  show ?C2 by (simp add: sdiv_pos_pos, subst rw, subst div_truncate_plus,
               simp_all)
qed

spark_vc function_initial_keyed_flex_38
proof-
  from `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 2`
  show ?C1 using mod_add_self2 by presburger
  from `key__index__subtype__1__first >= 1`
        `key_index >= key__index__subtype__1__first + 1`
  have rw: "(2 + (key_index - key__index__subtype__1__first)) div 4 =
            ((key_index - (key__index__subtype__1__first - 1)) + 1) div 4"
    by (simp add: algebra_simps)
  from `key__index__subtype__1__first >= 1`
       `key_index >= key__index__subtype__1__first + 1`
       `(key_index - (key__index__subtype__1__first - 1)) mod 4 = 2`
  show ?C2 by (simp add: sdiv_pos_pos, subst rw, subst div_truncate_plus,
               simp_all)
qed

spark_end


(* BLAKE2S/FINALIZE *)

spark_open "blake2s/finalize"

spark_vc procedure_finalize_27
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `1 < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_28
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_length(context) >= 1`
       `digest__index__subtype__1__first ~=
          digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_29
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_35
proof -
  from `digest_length(context) <= 32`
       `digest_index + 1 ~= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_39
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `2 ~= digest_length(context) `
       `1 < digest_length(context) `
  show ?thesis by simp
qed

spark_vc procedure_finalize_40
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_length(context) >= 1`
       `digest__index__subtype__1__first
          ~= digest_length(context)`
       `digest__index__subtype__1__first + 1
          ~= digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_41
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_index + 1 ~=
          digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_47
proof -
  from `digest_length(context) <= 32`
       `digest_index + 1 ~= digest_length(context)`
       `digest_index + 2 ~= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_51
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `2 ~= digest_length(context)`
       `3 ~= digest_length(context)`
       `1 < digest_length(context)`
  show ?thesis by simp
qed

spark_status

spark_vc procedure_finalize_52
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_length(context) >= 1`
       `digest__index__subtype__1__first ~=
          digest_length(context)`
       `digest__index__subtype__1__first + 1 ~=
          digest_length(context)`
       `digest__index__subtype__1__first + 2 ~=
          digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_53
proof -
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_index + 1 ~= digest_length(context)`
       `digest_index + 2 ~= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_59
proof -
  from `digest_length(context) <= 32`
       `digest_index + 1 ~= digest_length(context)`
       `digest_index + 2 ~= digest_length(context)`
       `digest_index + 3 ~= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?thesis by simp
qed

spark_vc procedure_finalize_66
proof -
  from `2 ~= digest_length(context)`
       `3 ~= digest_length(context)`
       `4 ~= digest_length(context)`
       `1 < digest_length(context)`
  show ?C1 by simp
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `5 <= digest_length(context)`
  show ?C2 by simp
qed

spark_vc procedure_finalize_67
proof -
  from `digest__index__subtype__1__first = 1`
       `digest_length(context) >= 1`
       `digest__index__subtype__1__first ~=
          digest_length(context)`
       `digest__index__subtype__1__first + 1 ~=
          digest_length(context)`
       `digest__index__subtype__1__first + 2 ~=
          digest_length(context)`
       `digest__index__subtype__1__first + 3 ~=
          digest_length(context)`
  show ?C1 by simp
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest__index__subtype__1__first + 4
          <= digest_length(context)`
  show ?C2 by simp
  from `digest__index__subtype__1__first = 1`
  show ?C3 by simp
  from `digest__index__subtype__1__first = 1`
       sdiv_pos_pos
  show ?C4 by simp
qed

spark_vc procedure_finalize_68
proof -
  from `digest_index + 1 ~= digest_length(context)`
       `digest_index + 2 ~= digest_length(context)`
       `digest_index + 3 ~= digest_length(context)`
       `digest_index < digest_length(context)`
  show ?C1 by simp
  from `digest__index__subtype__1__first = 1`
       `digest__index__subtype__1__last -
          digest__index__subtype__1__first + 1
            >= digest_length(context)`
       `digest_index + 4 <= digest_length(context)`
  show ?C2 by simp
  from `(digest_index - 1) mod 4 = 0`
  show ?C3 by presburger
  from `digest__index__subtype__1__first = 1`
       `digest_index > digest__index__subtype__1__first`
       sdiv_pos_pos
  show ?C4 by simp
qed

spark_end

(* END OF BLAKE2S PROOFS *)

end