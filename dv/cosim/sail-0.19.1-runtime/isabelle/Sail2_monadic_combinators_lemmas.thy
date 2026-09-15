theory Sail2_monadic_combinators_lemmas
  imports Sail2_operators_mwords Sail2_monadic_combinators
begin

lemma untilM_domI:
  fixes V :: "'vars \<Rightarrow> nat"
  assumes "Inv vars"
    and "\<And>vars t vars' t'. \<lbrakk>Inv vars; Run (body vars) t vars'; Run (cond vars') t' False\<rbrakk> \<Longrightarrow> V vars' < V vars \<and> Inv vars'"
  shows "untilM_dom (vars, cond, body)"
  using assms
  by (induction vars rule: measure_induct_rule[where f = V])
     (auto intro: untilM.domintros)

lemma whileM_domI:
  fixes V :: "'vars \<Rightarrow> nat"
  assumes "Inv vars"
    and "\<And>vars t vars' t'. \<lbrakk>Inv vars; Run (cond vars) t True; Run (body vars) t' vars'\<rbrakk> \<Longrightarrow> V vars' < V vars \<and> Inv vars'"
  shows "whileM_dom (vars, cond, body)"
  using assms
  by (induction vars rule: measure_induct_rule[where f = V])
     (auto intro: whileM.domintros)

lemma whileM_dom_step:
  assumes "whileM_dom (vars, cond, body)"
    and "Run (cond vars) t True"
    and "Run (body vars) t' vars'"
  shows "whileM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: whileM.pinduct\<close>)
     (auto intro: whileM.domintros)

lemma untilM_dom_step:
  assumes "untilM_dom (vars, cond, body)"
    and "Run (body vars) t vars'"
    and "Run (cond vars') t' False"
  shows "untilM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: untilM.pinduct\<close>)
     (auto intro: untilM.domintros)

text \<open>Simplification rules for monadic Boolean connectives\<close>

lemma if_return_return[simp]: "(if a then return True else return False) = return a" by auto

lemma and_boolM_simps[simp]:
  "and_boolM (return b) (return c) = return (b \<and> c)"
  "and_boolM x (return True) = x"
  "and_boolM x (return False) = x \<bind> (\<lambda>_. return False)"
  "and_boolM (return True) x = x"
  "and_boolM (return False) x = return False"
  "\<And>x y z. and_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. and_boolM (y r) z))"
  by (auto simp: and_boolM_def)

lemma and_boolM_return_if:
  "and_boolM (return b) y = (if b then y else return False)"
  by (auto simp: and_boolM_def)

lemmas and_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolM x y" for y]

lemma or_boolM_simps[simp]:
  "or_boolM (return b) (return c) = return (b \<or> c)"
  "or_boolM x (return True) = x \<bind> (\<lambda>_. return True)"
  "or_boolM x (return False) = x"
  "\<And>x y z. or_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. or_boolM (y r) z))"
  by (auto simp: or_boolM_def)

lemma or_boolM_return_if:
  "or_boolM (return b) y = (if b then return True else y)"
  by (auto simp: or_boolM_def)

lemmas or_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolM x y" for y]

text \<open>Machine word lemmas\<close>

lemmas uint_simps[simp] = uint_maybe_def (*uint_fail_def uint_nondet_def*)
lemmas sint_simps[simp] = sint_maybe_def (*sint_fail_def sint_nondet_def*)

lemma bools_of_bits_nondet_just_list[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "bools_of_bits_nondet RV bus = return bs"
proof -
  have f: "foreachM bus bools (\<lambda>b bools. bool_of_bitU_nondet RV b \<bind> (\<lambda>b. return (bools @ [b]))) = return (bools @ bs)"
    if "just_list (map bool_of_bitU bus) = Some bs" for bus bs bools
  proof (use that in \<open>induction bus arbitrary: bs bools\<close>)
    case (Cons bu bus bs)
    obtain b bs' where bs: "bs = b # bs'" and bu: "bool_of_bitU bu = Some b"
      using Cons.prems by (cases bu) (auto split: option.splits)
    then show ?case
      using Cons.prems Cons.IH[where bs = bs' and bools = "bools @ [b]"]
      by (cases bu) (auto simp: bool_of_bitU_nondet_def split: option.splits)
  qed auto
  then show ?thesis using f[OF assms, of "[]"] unfolding bools_of_bits_nondet_def
    by auto
qed

lemma of_bits_mword_return_of_bl[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "of_bits_nondet BC_mword RV bus = return (of_bl bs)"
    and "of_bits_fail BC_mword bus = return (of_bl bs)"
  by (auto simp: of_bits_nondet_def of_bits_fail_def maybe_fail_def assms BC_mword_defs)

lemma vec_of_bits_of_bl[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "vec_of_bits_maybe bus = Some (of_bl bs)"
    (*and "vec_of_bits_fail bus = return (of_bl bs)"
    and "vec_of_bits_nondet RV bus = return (of_bl bs)"*)
    and "vec_of_bits_failwith bus = of_bl bs"
    and "vec_of_bits bus = of_bl bs"
  unfolding vec_of_bits_maybe_def (*vec_of_bits_fail_def vec_of_bits_nondet_def*)
            vec_of_bits_failwith_def vec_of_bits_def
  by (auto simp: assms)

lemmas access_vec_dec_test_bit[simp] = access_bv_dec_mword[folded access_vec_dec_def]

lemma access_vec_inc_test_bit[simp]:
  fixes w :: "('a::len) word"
  assumes "n \<ge> 0" and "nat n < LENGTH('a)"
  shows "access_vec_inc w n = bitU_of_bool (bit w (LENGTH('a) - 1 - nat n))"
  using assms
  by (auto simp: access_vec_inc_def access_bv_inc_def access_list_def BC_mword_defs rev_nth test_bit_bl)

lemma bool_of_bitU_monadic_simps[simp]:
  "bool_of_bitU_fail B0 = return False"
  "bool_of_bitU_fail B1 = return True"
  "bool_of_bitU_fail BU = Fail ''bool_of_bitU''"
  "bool_of_bitU_nondet RV B0 = return False"
  "bool_of_bitU_nondet RV B1 = return True"
  "bool_of_bitU_nondet RV BU = choose_bool RV ''bool_of_bitU''"
  unfolding bool_of_bitU_fail_def bool_of_bitU_nondet_def
  by auto

lemma update_vec_dec_simps[simp]:
  "update_vec_dec_maybe w i B0 = Some (set_bit w (nat i) False)"
  "update_vec_dec_maybe w i B1 = Some (set_bit w (nat i) True)"
  "update_vec_dec_maybe w i BU = None"
  (*"update_vec_dec_fail w i B0 = return (set_bit w (nat i) False)"
  "update_vec_dec_fail w i B1 = return (set_bit w (nat i) True)"
  "update_vec_dec_fail w i BU = Fail ''bool_of_bitU''"
  "update_vec_dec_nondet RV w i B0 = return (set_bit w (nat i) False)"
  "update_vec_dec_nondet RV w i B1 = return (set_bit w (nat i) True)"
  "update_vec_dec_nondet RV w i BU = choose_bool RV ''bool_of_bitU'' \<bind> (\<lambda>b. return (set_bit w (nat i) b))"*)
  "update_vec_dec w i B0 = set_bit w (nat i) False"
  "update_vec_dec w i B1 = set_bit w (nat i) True"
  unfolding update_vec_dec_maybe_def (*update_vec_dec_fail_def update_vec_dec_nondet_def*) update_vec_dec_def
  by (auto simp: update_mword_dec_def update_mword_bool_dec_def maybe_failwith_def)

lemma len_of_minus_One_minus_nonneg_lt_len_of[simp]:
  "n \<ge> 0 \<Longrightarrow> nat (int LENGTH('a::len) - 1 - n) < LENGTH('a)"
  by (metis diff_mono diff_zero len_gt_0 nat_eq_iff2 nat_less_iff order_refl zle_diff1_eq)

declare subrange_vec_dec_def[simp]

lemma update_subrange_vec_dec_update_subrange_list_dec:
  assumes "0 \<le> j" and "j \<le> i" and "i < int LENGTH('a)"
  shows "update_subrange_vec_dec (w :: 'a::len word) i j w' =
         of_bl (update_subrange_list_dec (to_bl w) i j (to_bl w'))"
  using assms
  unfolding update_subrange_vec_dec_def update_subrange_list_dec_def update_subrange_list_inc_def
  by (auto simp: word_update_def split_at_def Let_def nat_diff_distrib min_def)

lemma subrange_vec_dec_subrange_list_dec:
  assumes "0 \<le> j" and "j \<le> i" and "i < int LENGTH('a)" and "int LENGTH('b) = i - j + 1"
  shows "subrange_vec_dec (w :: 'a::len word) i j = (of_bl (subrange_list_dec (to_bl w) i j) :: 'b::len word)"
  using assms unfolding subrange_vec_dec_def
  by (auto simp: subrange_list_dec_drop_take slice_take of_bl_drop')

lemma slice_simp[simp]: "slice w lo len = Word.slice (nat lo) w"
  by (auto simp: slice_def)

declare slice_id[simp]

lemma of_bools_of_bl[simp]: "of_bools_method BC_mword = of_bl"
  by (auto simp: BC_mword_defs)

lemma of_bl_bin_word_of_int:
  "len = LENGTH('a) \<Longrightarrow> of_bl (bin_to_bl_aux len n []) = (word_of_int n :: ('a::len) word)"
  by (auto simp: of_bl_def bin_bl_bin')

lemma get_slice_int_0_bin_to_bl[simp]:
  "len > 0 \<Longrightarrow> get_slice_int len n 0 = of_bl (bin_to_bl (nat len) n)"
  unfolding get_slice_int_def get_slice_int_bv_def subrange_list_def
  by (auto simp: subrange_list_dec_drop_take len_bin_to_bl_aux)

lemma to_bl_of_bl[simp]:
  fixes bl :: "bool list"
  defines w: "w \<equiv> of_bl bl :: 'a::len word"
  assumes len: "length bl = LENGTH('a)"
  shows "to_bl w = bl"
  using len unfolding w by (intro word_bl.Abs_inverse) auto

lemma reverse_endianness_byte[simp]:
  "LENGTH('a) = 8 \<Longrightarrow> reverse_endianness (w :: 'a::len word) = w"
  unfolding reverse_endianness_def by (auto simp: reverse_endianness_list_simps)

lemma reverse_reverse_endianness[simp]:
  "8 dvd LENGTH('a) \<Longrightarrow> reverse_endianness (reverse_endianness w) = (w :: 'a::len word)"
  unfolding reverse_endianness_def by (simp)

lemma replicate_bits_zero[simp]: "replicate_bits 0 n = 0"
  by (intro word_eqI) (auto simp: replicate_bits_def test_bit_of_bl rev_nth nth_repeat simp del: repeat.simps)

declare extz_vec_def[simp]
declare exts_vec_def[simp]
declare concat_vec_def[simp]

lemma msb_Bits_msb[simp]:
  "msb w = bitU_of_bool (Most_significant_bit.msb w)"
  by (auto simp: msb_def most_significant_def BC_mword_defs word_msb_alt split: list.splits)

declare and_vec_def[simp]
declare or_vec_def[simp]
declare xor_vec_def[simp]
declare not_vec_def[simp]

lemma arith_vec_simps[simp]:
  "add_vec l r = l + r"
  "sub_vec l r = l - r"
  "mult_vec l r = (ucast l) * (ucast r)"
  unfolding add_vec_def sub_vec_def mult_vec_def
  by auto

declare adds_vec_def[simp]
declare subs_vec_def[simp]
declare mults_vec_def[simp]

lemma arith_vec_int_simps[simp]:
  "add_vec_int l r = l + (word_of_int r)"
  "sub_vec_int l r = l - (word_of_int r)"
  "mult_vec_int l r = (ucast l) * (word_of_int r)"
  unfolding add_vec_int_def sub_vec_int_def mult_vec_int_def
  by (auto simp: arith_op_bv_int_def BC_mword_defs)

lemma shiftl_simp[simp]: "shiftl w l = w << (nat l)"
  by (auto simp: shiftl_def shiftl_mword_def)

lemma shiftr_simp[simp]: "shiftr w l = w >> (nat l)"
  by (auto simp: shiftr_def shiftr_mword_def)

termination shl_int
  apply (rule_tac R="measure (nat o snd)" in shl_int.termination)
   apply simp
  apply simp
  done

declare shl_int.simps[simp del]

lemma shl_int[simp]:
  "shl_int x y = x << (nat y)"
  apply (induct n \<equiv> "nat y" arbitrary: x y)
   apply (simp add: shl_int.simps)
  apply (subst shl_int.simps)
  apply (clarsimp dest!: sym[where s="Suc _"] simp: shiftl_int_def)
  apply (simp add: nat_diff_distrib)
  done

termination shr_int
  apply (rule_tac R="measure (nat o snd)" in shr_int.termination)
   apply simp_all
  done

declare shr_int.simps[simp del]

lemma shr_int[simp]:
  "shr_int x i = x >> (nat i)"
  apply (induct x i rule: shr_int.induct)
  apply (subst shr_int.simps)
  apply (clarsimp simp: shiftr_int_def zdiv_zmult2_eq[symmetric])
  apply (simp add: power_Suc[symmetric] Suc_nat_eq_nat_zadd1 del: power_Suc)
  done

end
