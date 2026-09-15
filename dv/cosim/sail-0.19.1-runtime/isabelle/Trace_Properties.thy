theory Trace_Properties
  imports Sail2_monadic_combinators_lemmas
begin

locale Stateful_Trace_Property =
  fixes pred :: "'state \<Rightarrow> ('abort, 'barrier, 'cache_op, 'fault, 'pa, 'tlb_op, 'translation_summary, 'regval) trace \<Rightarrow> bool"
    and update_state :: "'state \<Rightarrow> ('abort, 'barrier, 'cache_op, 'fault, 'pa, 'tlb_op, 'translation_summary, 'regval) trace \<Rightarrow> 'state"
  assumes pred_append: "\<And>s t1 t2. pred s t1 \<Longrightarrow> pred (update_state s t1) t2 \<Longrightarrow> pred s (t1 @ t2)"
begin

definition traces_satisfy_pred :: "'state \<Rightarrow> ('abort, 'barrier, 'cache_op, 'fault, 'pa, 'tlb_op, 'translation_summary, 'regval, 'a, 'e) monad \<Rightarrow> bool"
  where "traces_satisfy_pred s m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> pred s t)"

lemma traces_satisfy_pred_bind:
  assumes "traces_satisfy_pred s m"
    and "\<And>t a. Run m t a \<Longrightarrow> traces_satisfy_pred (update_state s t) (f a)"
  shows "traces_satisfy_pred s (m \<bind> f)"
  using assms
  unfolding traces_satisfy_pred_def
  by (fastforce elim!: bind_Traces_cases intro: pred_append)

lemma traces_satisfy_pred_return:
  "traces_satisfy_pred s (return a) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_def return_def)

lemma traces_satisfy_pred_throw:
  "traces_satisfy_pred s (throw e) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_def throw_def)

lemma traces_satisfy_pred_try_catch:
  assumes "traces_satisfy_pred s m"
    and "\<And>t e. (m, t, Exception e) \<in> Traces \<Longrightarrow> traces_satisfy_pred (update_state s t) (h e)"
  shows "traces_satisfy_pred s (try_catch m h)"
  using assms
  unfolding traces_satisfy_pred_def
  by (fastforce elim!: try_catch_Traces_cases intro: pred_append)

lemma traces_satisfy_pred_early_return:
  "traces_satisfy_pred s (early_return a) \<longleftrightarrow> pred s []"
  by (auto simp: early_return_def traces_satisfy_pred_throw)

lemma traces_satisfy_pred_catch_early_return:
  assumes "traces_satisfy_pred s m"
  shows "traces_satisfy_pred s (catch_early_return m)"
  using assms
  unfolding traces_satisfy_pred_def catch_early_return_def
  by (auto simp: return_def throw_def split: sum.splits elim!: try_catch_Traces_cases)

lemma traces_satisfy_pred_liftR:
  assumes "traces_satisfy_pred s m"
  shows "traces_satisfy_pred s (liftR m)"
  using assms
  unfolding traces_satisfy_pred_def liftR_def
  by (auto simp: throw_def split: sum.splits elim!: try_catch_Traces_cases)

lemma traces_satisfy_pred_try_catchR:
  assumes "traces_satisfy_pred s m"
    and "\<And>t e. (m, t, Exception (Inr e)) \<in> Traces \<Longrightarrow> traces_satisfy_pred (update_state s t) (h e)"
  shows "traces_satisfy_pred s (try_catchR m h)"
  using assms
  unfolding traces_satisfy_pred_def try_catchR_def
  by (fastforce elim!: try_catch_Traces_cases split: sum.splits simp: throw_def intro: pred_append)

lemma traces_satisfy_pred_maybe_fail:
  "traces_satisfy_pred s (maybe_fail msg x) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_def maybe_fail_def return_def split: option.splits)

lemma traces_satisfy_pred_assert_exp:
  "traces_satisfy_pred s (assert_exp e msg) \<longleftrightarrow> pred s []"
  by (auto simp: traces_satisfy_pred_def assert_exp_def)

(*lemma Read_reg_Traces_iff: "(Read_reg r k, t, m') \<in> Traces \<longleftrightarrow> (\<exists>v t'. t = E_read_reg r v # t' \<and> (k v, t', m') \<in> Traces) \<or> (t = [] \<and> m' = Read_reg r k)"
  by (auto elim: Traces_cases intro: Traces_ConsI)

abbreviation "trace_characterisation m P \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longleftrightarrow> P t m' \<or> (t = [] \<and> m' = m))"

lemma read_reg_trace_characterisation:
  "trace_characterisation (read_reg r) (\<lambda>t m'. \<exists>rv. t = [E_read_reg (name r) rv] \<and> m' = (maybe_fail ''read_reg: unrecognised value'' (of_regval r rv)))"
  unfolding read_reg_def maybe_fail_def return_def
  by (auto split: option.splits; fastforce intro: Traces_ConsI elim: Traces_cases)

lemma traces_satisfy_pred_read_reg:
  "traces_satisfy_pred s (read_reg r) \<longleftrightarrow> (\<forall>rv. pred s [E_read_reg (name r) rv]) \<and> pred s []"
  using read_reg_trace_characterisation[of r]
  by (auto simp: traces_satisfy_pred_def)*)

definition "primitive_exp m \<equiv> (\<forall>t m'. (m, t, m') \<in> Traces \<longrightarrow> t = [] \<or> final m')"

lemma final_bind_iff:
  "final (m \<bind> f) \<longleftrightarrow> final m \<and> (\<forall>a. m = Done a \<longrightarrow> final (f a))"
  by (cases m) (auto simp: final_def)

lemma final_Traces_Nil:
  assumes "final m" and "(m, t, m') \<in> Traces"
  shows "t = []" and "m' = m"
  using assms
  by (auto simp: final_def split: monad.splits)

lemma primitive_exp_bind_left:
  assumes "primitive_exp m" and f: "\<And>a. final (f a)"
  shows "primitive_exp (m \<bind> f)"
  using assms final_Traces_Nil[OF f]
  by (fastforce simp: primitive_exp_def final_bind_iff elim!: bind_Traces_cases)

(*lemma primitive_exp_read_reg: "primitive_exp (read_reg r)"
  by (auto simp: primitive_exp_def read_reg_def final_def elim: Traces_cases split: option.splits)*)

lemmas builtin_primitive_exp_defs =
  return_def throw_def early_return_def maybe_fail_def assert_exp_def headM_def tailM_def
  read_reg_def write_reg_def choose_regval_def choose_convert_def choose_convert_default_def
  choose_bool_def choose_bit_def choose_int_def choose_real_def choose_string_def
  sail_mem_read_request_def sail_mem_write_request_def sail_mem_write_announce_address_def

lemma builtin_primitive_exps:
  "\<And>r. primitive_exp (read_reg r)"
  "\<And>r v. primitive_exp (write_reg r v)"
  "\<And>descr. primitive_exp (choose_regval descr)"
  "\<And>of_rv descr. primitive_exp (choose_convert of_rv descr)"
  "\<And>of_rv x descr. primitive_exp (choose_convert_default of_rv x descr)"
  "\<And>RV descr. primitive_exp (choose_bool RV descr)"
  "\<And>RV descr. primitive_exp (choose_bit RV descr)"
  "\<And>RV descr. primitive_exp (choose_int RV descr)"
  "\<And>RV descr. primitive_exp (choose_real RV descr)"
  "\<And>RV descr. primitive_exp (choose_string RV descr)"
  "\<And>xs. primitive_exp (headM xs)"
  "\<And>xs. primitive_exp (tailM xs)"
  "\<And>BV req. primitive_exp (sail_mem_read_request BV req)"
  "\<And>req. primitive_exp (sail_mem_write_request req)"
  "\<And>req. primitive_exp (sail_mem_write_announce_address req)"
  unfolding builtin_primitive_exp_defs
  by (auto simp: primitive_exp_def final_def elim: Traces_cases
           split: option.splits list.splits result.splits)

lemma runTrace_final_case_simps:
  "runTrace t (Done a) = (case t of [] \<Rightarrow> Some (Done a) | _ \<Rightarrow> None)"
  "runTrace t (Fail msg) = (case t of [] \<Rightarrow> Some (Fail msg) | _ \<Rightarrow> None)"
  "runTrace t (Exception e) = (case t of [] \<Rightarrow> Some (Exception e) | _ \<Rightarrow> None)"
  by (auto split: list.splits Option.bind_splits elim: emitEvent_cases)

lemma builtin_primitive_exps_hasTrace_iffs:
  "\<And>r. hasTrace t (read_reg r) \<longleftrightarrow> (\<exists>rv. t = [E_read_reg (name r) rv])"
  "\<And>BV req. hasTrace t (sail_mem_read_request BV req) \<longleftrightarrow> (\<exists>v. t = [E_mem_read_request req v])"
  "\<And>RV descr. hasTrace t (choose_bool RV descr) \<longleftrightarrow> (\<exists>v. t = [E_choose descr v])"
  unfolding builtin_primitive_exp_defs
  by (auto simp: hasTrace_def emitEvent_intros final_def runTrace_final_case_simps
           split: option.splits Option.bind_splits list.splits result.splits
           elim!: runTrace.elims emitEvent_cases)

lemma primitive_exp_traces_satisfy_pred:
  assumes "primitive_exp m"
  shows "traces_satisfy_pred s m \<longleftrightarrow> (\<forall>t. hasTrace t m \<longrightarrow> pred s t) \<and> pred s []"
  using assms Traces.Nil[of m]
  unfolding primitive_exp_def traces_satisfy_pred_def hasTrace_iff_Traces_final
  by auto

lemmas builtin_primitive_exp_traces_satisfy_pred =
  builtin_primitive_exps[THEN primitive_exp_traces_satisfy_pred,
                         unfolded builtin_primitive_exps_hasTrace_iffs]

(*lemma
  "traces_satisfy_pred s (read_reg r) \<longleftrightarrow> (\<forall>rv. pred s [E_read_reg (name r) rv]) \<and> pred s []"
  using primitive_exp_read_reg[of r, THEN primitive_exp_traces_satisfy_pred, where s = s]
  unfolding hasTrace_read_reg
  by auto*)

end

end
