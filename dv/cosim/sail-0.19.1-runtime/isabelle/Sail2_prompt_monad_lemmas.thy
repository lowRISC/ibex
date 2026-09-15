theory Sail2_prompt_monad_lemmas
  imports
    Sail2_prompt_monad
    Sail2_values_lemmas
begin

notation bind (infixr "\<bind>" 54)
notation either_bind (infixr "\<bind>\<^sub>R" 54)

abbreviation seq :: "('rv,unit,'e)monad \<Rightarrow> ('rv,'b,'e)monad \<Rightarrow>('rv,'b,'e)monad" (infixr "\<then>" 54) where
  "m \<then> n \<equiv> m \<bind> (\<lambda>_. n)"
abbreviation seqR :: "('e,unit)sum \<Rightarrow> ('e,'b)sum \<Rightarrow>('e,'b)sum" (infixr "\<then>\<^sub>R" 54) where
  "m \<then>\<^sub>R n \<equiv> m \<bind>\<^sub>R (\<lambda>_. n)"

lemma All_bind_dom: "bind_dom (m, f)"
  by (induction m) (auto intro: bind.domintros)

termination bind using All_bind_dom by auto
lemmas bind_induct[case_names Done Read_mem Write_memv Read_reg Excl_res Write_ea Barrier Write_reg Fail Exception] = bind.induct

lemma bind_return[simp]: "bind (return a) f = f a"
  by (auto simp: return_def)
lemma bind_return_right[simp]: "bind x return = x" by (induction x) (auto simp: return_def)

lemma bind_assoc[simp]: "bind (bind m f) g = bind m (\<lambda>x. bind (f x) g)"
  by (induction m f arbitrary: g rule: bind.induct) auto

lemma bind_assert_True[simp]: "bind (assert_exp True msg) f = f ()"
  by (auto simp: assert_exp_def)

lemma All_try_catch_dom: "try_catch_dom (m, h)"
  by (induction m) (auto intro: try_catch.domintros)
termination try_catch using All_try_catch_dom by auto
lemmas try_catch_induct[case_names Done Read_mem Write_memv Read_reg Excl_res Write_ea Barrier Write_reg Fail Exception] = try_catch.induct

inductive_set T :: "(('rv, 'a, 'e) monad \<times> 'rv event \<times> ('rv, 'a, 'e) monad) set" where
  Read_mem: "((Read_mem rk addr sz k), E_read_mem rk addr sz v, k v) \<in> T"
| Read_memt: "((Read_memt rk addr sz k), E_read_memt rk addr sz v, k v) \<in> T"
| Write_ea: "((Write_ea wk addr sz k), E_write_ea wk addr sz, k) \<in> T"
| Excl_res: "((Excl_res k), E_excl_res r, k r) \<in> T"
| Write_mem: "((Write_mem wk addr sz v k), E_write_mem wk addr sz v r, k r) \<in> T"
| Write_memt: "((Write_memt wk addr sz v t k), E_write_memt wk addr sz v t r, k r) \<in> T"
| Footprint: "((Footprint k), E_footprint, k) \<in> T"
| Barrier: "((Barrier bk k), E_barrier bk, k) \<in> T"
| Read_reg: "((Read_reg r k), E_read_reg r v, k v) \<in> T"
| Write_reg: "((Write_reg r v k), E_write_reg r v, k) \<in> T"
| Choose: "((Choose descr k), E_choose descr v, k v) \<in> T"
| Print: "((Print msg k), E_print msg, k) \<in> T"

lemma emitEvent_iff_T: "emitEvent m e = Some m' \<longleftrightarrow> (m, e, m') \<in> T"
  by (cases e) (auto simp: emitEvent_def elim: T.cases intro: T.intros split: monad.splits)

inductive_set Traces :: "(('rv, 'a, 'e) monad \<times> 'rv event list \<times> ('rv, 'a, 'e) monad) set" where
  Nil: "(s, [], s) \<in> Traces"
| Step: "\<lbrakk>(s, e, s'') \<in> T; (s'', t, s') \<in> Traces\<rbrakk> \<Longrightarrow> (s, e # t, s') \<in> Traces"

declare Traces.intros[intro]
declare T.intros[intro]

declare prod.splits[split]

lemmas Traces_ConsI = T.intros[THEN Step, rotated]

inductive_cases Traces_NilE[elim]: "(s, [], s') \<in> Traces"
inductive_cases Traces_ConsE[elim]: "(s, e # t, s') \<in> Traces"

lemma runTrace_iff_Traces: "runTrace t m = Some m' \<longleftrightarrow> (m, t, m') \<in> Traces"
  by (induction t m rule: runTrace.induct; fastforce simp: bind_eq_Some_conv emitEvent_iff_T)

lemma hasTrace_iff_Traces_final: "hasTrace t m \<longleftrightarrow> (\<exists>m'. (m, t, m') \<in> Traces \<and> final m')"
  by (auto simp: hasTrace_def runTrace_iff_Traces[symmetric] split: option.splits)

lemma Traces_cases:
  fixes m :: "('rv, 'a, 'e) monad"
  assumes Run: "(m, t, m') \<in> Traces"
  obtains (Nil) a where "m = m'" and "t = []"
  | (Read_mem) rk addr s k t' v where "m = Read_mem rk addr s k" and "t = E_read_mem rk addr s v # t'" and "(k v, t', m') \<in> Traces"
  | (Read_memt) rk addr s k t' v tag where "m = Read_memt rk addr s k" and "t = E_read_memt rk addr s (v, tag) # t'" and "(k (v, tag), t', m') \<in> Traces"
  | (Write_mem) wk addr sz val k v t' where "m = Write_mem wk addr sz val k" and "t = E_write_mem wk addr sz val v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_memt) wk addr sz val tag k t' v where "m = Write_memt wk addr sz val tag k" and "t = E_write_memt wk addr sz val tag v # t'" and "(k v, t', m') \<in> Traces"
  | (Barrier) bk k t' v where "m = Barrier bk k" and "t = E_barrier bk # t'" and "(k, t', m') \<in> Traces"
  | (Read_reg) reg k t' v where "m = Read_reg reg k" and "t = E_read_reg reg v # t'" and "(k v, t', m') \<in> Traces"
  | (Excl_res) k t' v where "m = Excl_res k" and "t = E_excl_res v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_ea) wk addr s k t' where "m = Write_ea wk addr s k" and "t = E_write_ea wk addr s # t'" and "(k, t', m') \<in> Traces"
  | (Footprint) k t' where "m = Footprint k" and "t = E_footprint # t'" and "(k, t', m') \<in> Traces"
  | (Write_reg) reg v k t' where "m = Write_reg reg v k" and "t = E_write_reg reg v # t'" and "(k, t', m') \<in> Traces"
  | (Choose) descr v k t' where "m = Choose descr k" and "t = E_choose descr v # t'" and "(k v, t', m') \<in> Traces"
  | (Print) msg k t' where "m = Print msg k" and "t = E_print msg # t'" and "(k, t', m') \<in> Traces"
proof (use Run in \<open>cases m t m' set: Traces\<close>)
  case Nil
  then show ?thesis by (auto intro: that(1))
next
  case (Step e m'' t')
  note t = \<open>t = e # t'\<close>
  note m' = \<open>(m'', t', m') \<in> Traces\<close>
  from \<open>(m, e, m'') \<in> T\<close> and t and m'
  show ?thesis proof (cases m e m'' rule: T.cases)
    case (Read_memt rk addr sz k v)
    then show ?thesis using t m' by (cases v; elim that; blast)
  qed (elim that; blast)+
qed

abbreviation Run :: "('rv, 'a, 'e) monad \<Rightarrow> 'rv event list \<Rightarrow> 'a \<Rightarrow> bool"
  where "Run s t a \<equiv> (s, t, Done a) \<in> Traces"

lemma final_cases:
  assumes "final m"
  obtains (Done) a where "m = Done a" | (Fail) f where "m = Fail f" | (Ex) e where "m = Exception e"
  using assms by (cases m) (auto simp: final_def)

lemma hasTraces_elim:
  assumes "hasTrace t m"
  obtains m' where "(m, t, m') \<in> Traces" and "final m'"
  using assms
  unfolding hasTrace_iff_Traces_final
  by blast

lemma hasTrace_cases:
  assumes "hasTrace t m"
  obtains (Run) a where "Run m t a"
  | (Fail) f where "(m, t, Fail f) \<in> Traces"
  | (Ex) e where "(m, t, Exception e) \<in> Traces"
  using assms by (elim hasTraces_elim final_cases) auto

lemma Traces_appendI:
  assumes "(s, t1, s') \<in> Traces"
    and "(s', t2, s'') \<in> Traces"
  shows "(s, t1 @ t2, s'') \<in> Traces"
proof (use assms in \<open>induction t1 arbitrary: s\<close>)
  case (Cons e t1)
  then show ?case by (elim Traces_ConsE) auto
qed auto

lemma bind_DoneE:
  assumes "bind m f = Done a"
  obtains a' where "m = Done a'" and "f a' = Done a"
  using assms by (auto elim: bind.elims)

lemma bind_T_cases:
  assumes "(bind m f, e, s') \<in> T"
  obtains (Done) a where "m = Done a" and "(f a, e, s') \<in> T"
  | (Bind) m' where "s' = bind m' f" and "(m, e, m') \<in> T"
  using assms by (cases; fastforce elim: bind.elims)

lemma Traces_bindI:
  fixes m :: "('r, 'a, 'e) monad"
  assumes "Run m t1 a1"
    and "(f a1, t2, m') \<in> Traces"
  shows "(m \<bind> f, t1 @ t2, m') \<in> Traces"
proof (use assms in \<open>induction m t1 "Done a1 :: ('r, 'a, 'e) monad" rule: Traces.induct\<close>)
  case (Step s e s'' t)
  then show ?case by (elim T.cases) auto
qed auto

lemma Run_DoneE:
  assumes "Run (Done a) t a'"
  obtains "t = []" and "a' = a"
  using assms by (auto elim: Traces.cases T.cases)

lemma Run_Done_iff_Nil[simp]: "Run (Done a) t a' \<longleftrightarrow> t = [] \<and> a' = a"
  by (auto elim: Run_DoneE)

lemma Run_Nil_iff_Done: "Run m [] a \<longleftrightarrow> m = Done a"
  by auto

lemma Traces_Nil_iff: "(m, [], m') \<in> Traces \<longleftrightarrow> m' = m"
  by auto

lemma bind_Traces_cases:
  assumes "(m \<bind> f, t, m') \<in> Traces"
  obtains (Left) m'' where "(m, t, m'') \<in> Traces" and "m' = m'' \<bind> f"
  | (Bind) tm am tf where "t = tm @ tf" and "Run m tm am" and "(f am, tf, m') \<in> Traces"
proof (use assms in \<open>induction "bind m f" t m' arbitrary: m rule: Traces.induct\<close>)
  case Nil
  then show ?case by (auto simp: Traces_Nil_iff)
next
  case (Step e s'' t s')
  note IH = Step(3)
  note Left' = Step(4)
  note Bind' = Step(5)
  show thesis
  proof (use \<open>(m \<bind> f, e, s'') \<in> T\<close> in \<open>cases rule: bind_T_cases\<close>)
    case (Done a)
    then show ?thesis using \<open>(s'', t, s') \<in> Traces\<close> Step(5)[of "[]" "e # t" a] by auto
  next
    case (Bind m')
    show ?thesis
    proof (rule IH)
      show "s'' = m' \<bind> f" using Bind by blast
    next
      fix m''
      assume "(m', t, m'') \<in> Traces" and "s' = m'' \<bind> f"
      then show thesis using \<open>(m, e, m') \<in> T\<close> Left'[of m''] by auto
    next
      fix tm tf am
      assume "t = tm @ tf" and "Run m' tm am" and "(f am, tf, s') \<in> Traces"
      then show thesis using \<open>(m, e, m') \<in> T\<close> Bind'[of "e # tm" tf am] by auto
    qed
  qed
qed

lemma final_bind_cases:
  assumes "final (m \<bind> f)"
  obtains (Done) a where "m = Done a" and "final (f a)"
  | (Fail) msg where "m = Fail msg"
  | (Ex) e where "m = Exception e"
  using assms by (cases m) (auto simp: final_def)

lemma hasFailure_iff_Traces_Fail: "hasFailure t m \<longleftrightarrow> (\<exists>msg. (m, t, Fail msg) \<in> Traces)"
  by (auto simp: hasFailure_def runTrace_iff_Traces[symmetric] split: option.splits monad.splits)

lemma hasException_iff_Traces_Exception: "hasException t m \<longleftrightarrow> (\<exists>e. (m, t, Exception e) \<in> Traces)"
  by (auto simp: hasException_def runTrace_iff_Traces[symmetric] split: option.splits monad.splits)

lemma hasTrace_bind_cases:
  assumes "hasTrace t (m \<bind> f)"
  obtains (Bind) tm am tf where "t = tm @ tf" and "Run m tm am" and "hasTrace tf (f am)"
  | (Fail) "hasFailure t m"
  | (Ex) "hasException t m"
proof -
  from assms obtain m' where t: "(m \<bind> f, t, m') \<in> Traces" and m': "final m'"
    by (auto simp: hasTrace_iff_Traces_final)
  note [simp] = hasTrace_iff_Traces_final hasFailure_iff_Traces_Fail hasException_iff_Traces_Exception
  from t show thesis
  proof (cases rule: bind_Traces_cases)
    case (Left m'')
    then show ?thesis
      using m' Fail Ex Bind[of t "[]"]
      by (fastforce elim!: final_bind_cases)
  next
    case (Bind tm am tf)
    then show ?thesis
      using m' that
      by fastforce
  qed
qed

lemma try_catch_T_cases:
  assumes "(try_catch m h, e, m') \<in> T"
  obtains (NoEx) m'' where "(m, e, m'') \<in> T" and "m' = try_catch m'' h"
  | (Ex) ex where "m = Exception ex" and "(h ex, e, m') \<in> T"
  using assms
  by (cases m) (auto elim!: T.cases)

lemma try_catch_Traces_cases:
  assumes "(try_catch m h, t, mtc) \<in> Traces"
  obtains (NoEx) m' where "(m, t, m') \<in> Traces" and "mtc = try_catch m' h"
  | (Ex) tm ex th where "(m, tm, Exception ex) \<in> Traces" and "(h ex, th, mtc) \<in> Traces" and "t = tm @ th"
proof (use assms in \<open>induction "try_catch m h" t mtc arbitrary: m rule: Traces.induct\<close>)
  case Nil
  then show ?case by auto
next
  case (Step e mtc' t mtc)
  note e = \<open>(try_catch m h, e, mtc') \<in> T\<close>
  note t = \<open>(mtc', t, mtc) \<in> Traces\<close>
  note IH = Step(3)
  note NoEx_ConsE = Step(4)
  note Ex_ConsE = Step(5)
  show ?case
  proof (use e in \<open>cases rule: try_catch_T_cases\<close>)
    case (NoEx m1)
    show ?thesis
    proof (rule IH)
      show "mtc' = try_catch m1 h" using NoEx by auto
    next
      fix m'
      assume "(m1, t, m') \<in> Traces" and "mtc = try_catch m' h"
      then show ?thesis
        using NoEx NoEx_ConsE[of m']
        by auto
    next
      fix tm ex th
      assume "(m1, tm, Exception ex) \<in> Traces" and "(h ex, th, mtc) \<in> Traces" and "t = tm @ th"
      then show ?thesis
        using NoEx Ex_ConsE[of "e # tm" ex th]
        by auto
    qed
  next
    case (Ex ex)
    then show ?thesis
      using t Ex_ConsE[of "[]" ex "e # t"]
      by auto
  qed
qed

lemma Done_Traces_iff[simp]: "(Done a, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Done a"
  by (auto elim: Traces_cases)

lemma Fail_Traces_iff[simp]: "(Fail msg, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Fail msg"
  by (auto elim: Traces_cases)

lemma Exception_Traces_iff[simp]: "(Exception e, t, m') \<in> Traces \<longleftrightarrow> t = [] \<and> m' = Exception e"
  by (auto elim: Traces_cases)

lemma Read_reg_TracesE:
  assumes "(Read_reg r k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Read_reg r k"
  | (Cons) v t' where "t = E_read_reg r v # t'" and "(k v, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)

lemma Write_reg_TracesE:
  assumes "(Write_reg r v k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Write_reg r v k"
  | (Cons) t' where "t = E_write_reg r v # t'" and "(k, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)

lemma Write_ea_TracesE:
  assumes "(Write_ea wk addr sz k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Write_ea wk addr sz k"
  | (Cons) t' where "t = E_write_ea wk addr sz # t'" and "(k, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)

lemma Write_memt_TracesE:
  assumes "(Write_memt wk addr sz v tag k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Write_memt wk addr sz v tag k"
  | (Cons) t' r where "t = E_write_memt wk addr sz v tag r # t'" and "(k r, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)

lemma Run_bindE:
  fixes m :: "('rv, 'b, 'e) monad" and a :: 'a
  assumes "Run (bind m f) t a"
  obtains tm am tf where "t = tm @ tf" and "Run m tm am" and "Run (f am) tf a"
proof (use assms in \<open>induction "bind m f" t "Done a :: ('rv, 'a, 'e) monad" arbitrary: m rule: Traces.induct\<close>)
  case Nil
  obtain am where "m = Done am" and "f am = Done a" using Nil(1) by (elim bind_DoneE)
  then show ?case by (intro Nil(2)) auto
next
  case (Step e s'' t m)
  show thesis using Step(1)
  proof (cases rule: bind_T_cases)
    case (Done am)
    then show ?thesis using Step(1,2) by (intro Step(4)[of "[]" "e # t" am]) auto
  next
    case (Bind m')
    show ?thesis proof (rule Step(3)[OF Bind(1)])
      fix tm tf am
      assume "t = tm @ tf" and "Run m' tm am" and "Run (f am) tf a"
      then show thesis using Bind by (intro Step(4)[of "e # tm" tf am]) auto
    qed
  qed
qed

lemma Run_bindE_ignore_trace:
  assumes "Run (m \<bind> f) t a"
  obtains tm tf am where "Run m tm am" and "Run (f am) tf a"
  using assms by (elim Run_bindE)

lemma Run_letE:
  assumes "Run (let x = y in f x) t a"
  obtains "Run (f y) t a"
  using assms by auto

lemma Run_ifE:
  assumes "Run (if b then f else g) t a"
  obtains "b" and "Run f t a" | "\<not>b" and "Run g t a"
  using assms by (auto split: if_splits)

lemma Run_returnE:
  assumes "Run (return x) t a"
  obtains "t = []" and "a = x"
  using assms by (auto simp: return_def)

lemma Run_early_returnE:
  assumes "Run (early_return x) t a"
  shows P
  using assms by (auto simp: early_return_def throw_def elim: Traces_cases)

lemma bind_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>t a. Run m2 t a \<Longrightarrow> f1 a = f2 a"
  shows "bind m1 f1 = bind m2 f2"
  unfolding m using f
  by (induction m2 f1 arbitrary: f2 rule: bind.induct; unfold bind.simps; blast)

lemma liftR_read_reg[simp]: "liftR (read_reg reg) = read_reg reg" by (auto simp: read_reg_def liftR_def split: option.splits)
lemma try_catch_return[simp]: "try_catch (return x) h = return x" by (auto simp: return_def)
lemma liftR_return[simp]: "liftR (return x) = return x" by (auto simp: liftR_def)
lemma assert_exp_True_return[simp]: "assert_exp True msg = return ()" by (auto simp: assert_exp_def return_def)
lemma try_catch_maybe_fail[simp]: "try_catch (maybe_fail msg v) h = maybe_fail msg v" by (cases v; auto simp: maybe_fail_def)
lemma liftR_choose_regval[simp]: "liftR (choose_regval descr) = choose_regval descr" by (auto simp: liftR_def choose_regval_def)
lemma liftR_choose_convert[simp]: "liftR (choose_convert of_rv descr) = choose_convert of_rv descr" by (auto simp: liftR_def choose_convert_def)
lemma liftR_choose_convert_default[simp]: "liftR (choose_convert_default of_rv x descr) = choose_convert_default of_rv x descr"
  by (auto simp: liftR_def choose_convert_default_def)
lemma liftR_choose_builtins[simp]:
  "liftR (choose_bool RV u) = choose_bool RV u"
  "liftR (choose_int RV u) = choose_int RV u"
  "liftR (choose_real RV u) = choose_real RV u"
  "liftR (choose_string RV u) = choose_string RV u"
  unfolding choose_bool_def choose_int_def choose_real_def choose_string_def
  by auto

text \<open>Precondition to ensure reading a register doesn't fail.\<close>

fun(sequential)
  register_reads_ok :: "(string \<Rightarrow> ('regval \<Rightarrow> bool) option) \<Rightarrow> 'regval event \<Rightarrow> bool"
  where
    "register_reads_ok f (E_read_reg nm v) = register_read_ok f nm v"
  | "register_reads_ok f _ = True"

lemma read_reg_non_failure:
  "(read_reg reg_ref, t, x) \<in> Traces \<Longrightarrow>
    f (name reg_ref) = Some (fst (register_ops_of reg_ref)) \<Longrightarrow>
    \<forall>event \<in> set t. register_reads_ok f event \<Longrightarrow>
    x \<noteq> Fail msg"
  by (auto simp: read_reg_def register_read_ok_def register_ops_of_def
        elim!: Read_reg_TracesE split: option.split_asm)

end
