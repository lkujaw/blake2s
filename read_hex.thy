theory read_hex
imports "HOL-SPARK.SPARK"
begin

spark_open "b2stest/parse_file/read_hex"

spark_vc procedure_read_hex_6
proof -
  from `source_first <= source_index` sdiv_pos_pos
  have "(source_index - source_first) sdiv 2 =
          (source_index - source_first) div 2"
    by simp
  moreover
  from `source_first <= source_index` sdiv_pos_pos
  have "(source_index + 2 - source_first) sdiv 2 =
          (source_index + 2 - source_first) div 2"
    by simp
  ultimately show ?thesis by (simp add: div_pos_geq)
qed

spark_vc procedure_read_hex_13
proof -
  from `source_index >= source_first`
       `source_index < source_last`
       `target__index__subtype__1__last >=
          (source_last - source_first + 1) sdiv 2`
       sdiv_pos_pos
  have "(source_index - source_first) sdiv 2 <
          target__index__subtype__1__last"
    by simp
  then show ?thesis by simp
qed

spark_vc procedure_read_hex_17
proof -
  from `source_index >= source_first`
       `source_index < source_last`
       `target__index__subtype__1__last >=
          (source_last - source_first + 1) sdiv 2`
  show ?thesis by (simp add: sdiv_pos_pos)
qed

spark_vc procedure_read_hex_18
proof -
  from `source_index >= source_first`
       `source_index < source_last`
       `target__index__subtype__1__last >=
          (source_last - source_first + 1) sdiv 2`
  show ?thesis by (simp add: sdiv_pos_pos)
qed

spark_end

end