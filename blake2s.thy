theory blake2s
imports "HOL-SPARK.SPARK"
begin

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

end