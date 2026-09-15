theory Sail2_concurrency_interface_lemmas
  imports
    Sail2_concurrency_interface
    Sail2_values_lemmas
begin

notation bind (infixr "\<bind>" 54)
notation either_bind (infixr "\<bind>\<^sub>R" 54)

abbreviation seq (*:: "('rv,unit,'e)monad \<Rightarrow> ('rv,'b,'e)monad \<Rightarrow>('rv,'b,'e)monad"*) (infixr "\<then>" 54) where
  "m \<then> n \<equiv> m \<bind> (\<lambda>_ :: unit. n)"
abbreviation seqR (*:: "('e,unit)sum \<Rightarrow> ('e,'b)sum \<Rightarrow>('e,'b)sum"*) (infixr "\<then>\<^sub>R" 54) where
  "m \<then>\<^sub>R n \<equiv> m \<bind>\<^sub>R (\<lambda>_ :: unit. n)"

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

inductive_set T (*:: "(('rv, 'a, 'e) monad \<times> 'rv event \<times> ('rv, 'a, 'e) monad) set"*) where
  Choose: "((Choose descr k), E_choose descr v, k v) \<in> T"
| Read_reg: "((Read_reg r k), E_read_reg r v, k v) \<in> T"
| Write_reg: "((Write_reg r v k), E_write_reg r v, k) \<in> T"
| Read_mem: "((Mem_read_request req k), E_mem_read_request req v, k v) \<in> T"
| Write_mem: "((Mem_write_request req k), E_mem_write_request req r, k r) \<in> T"
| Write_announce: "((Mem_write_announce_address a k), E_mem_write_announce_address a, k) \<in> T"
| Translation_start: "((Translation_start ts k), E_translation_start ts, k) \<in> T"
| Translation_end: "((Translation_end te k), E_translation_end te, k) \<in> T"
| Branch_announce: "((Branch_announce_address a k), E_branch_announce_address a, k) \<in> T"
| Barrier_request: "((Barrier_request r k), E_barrier_request r, k) \<in> T"
| Cache_op_request: "((Cache_op_request r k), E_cache_op_request r, k) \<in> T"
| TLB_op_request: "((TLB_op_request r k), E_tlb_op_request r, k) \<in> T"
| Fault: "((Fault_announce f k), E_fault_announce f, k) \<in> T"
| Eret: "((Eret_announce a k), E_eret_announce a, k) \<in> T"

lemma emitEvent_iff_T: "emitEvent m e = Some m' \<longleftrightarrow> (m, e, m') \<in> T"
  by (cases e) (auto simp: emitEvent_def elim: T.cases intro: T.intros split: monad.splits)

lemmas emitEvent_intros = T.intros[folded emitEvent_iff_T]
(* lemmas emitEvent_cases = T.cases[folded emitEvent_iff_T, case_names Choose Read_reg Write_reg Read_mem Write_mem Write_announce Branch_announce Barrier Cache_op TLB_op Fault Eret] *)

lemma emitEvent_cases:
  assumes "emitEvent m e = Some m'"
  obtains
  (Choose) descr k v where "m = Choose descr k" and "e = E_choose descr v" and "m' = k v"
  | (Read_reg) r k v where "m = Read_reg r k" and "e = E_read_reg r v" and "m' =  k v"
  | (Write_reg) r k v where "m = Write_reg r v k" and "e = E_write_reg r v" and "m' = k"
  | (Read_mem) req k v where "m = Mem_read_request req k" and "e = E_mem_read_request req v" and "m' = k v"
  | (Write_mem) req k r where "m = Mem_write_request req k" and "e = E_mem_write_request req r" and "m' = k r"
  | (Write_announce) a k where "m = Mem_write_announce_address a k" and "e = E_mem_write_announce_address a" and "m' = k"
  | (Translation_start) ts k where "m = Translation_start ts k" and "e = E_translation_start ts" and "m' = k"
  | (Translation_end) te k where "m = Translation_end te k" and "e = E_translation_end te" and "m' = k"
  | (Branch_announce) a k where "m = Branch_announce_address a k" and "e = E_branch_announce_address a" and "m' = k"
  | (Barrier_request) r k where "m = Barrier_request r k" and "e = E_barrier_request r" and "m' = k"
  | (Cache_op_request) r k where "m = Cache_op_request r k" and "e = E_cache_op_request r" and "m' = k"
  | (TLB_op_request) r k where "m = TLB_op_request r k" and "e = E_tlb_op_request r" and "m' = k"
  | (Fault) f k where "m = Fault_announce f k" and "e = E_fault_announce f" and "m' = k"
  | (Eret) a k where "m = Eret_announce a k" and "e = E_eret_announce a" and "m' = k"
  using assms
  by (auto simp: emitEvent_def split: event.splits monad.splits if_splits)

inductive_set Traces (*:: "(('rv, 'a, 'e) monad \<times> 'rv event list \<times> ('rv, 'a, 'e) monad) set"*) where
  Nil: "(s, [], s) \<in> Traces"
| Step: "\<lbrakk>emitEvent s e = Some s''; (s'', t, s') \<in> Traces\<rbrakk> \<Longrightarrow> (s, e # t, s') \<in> Traces"

declare Traces.intros[intro]
(* declare T.intros[intro] *)

declare prod.splits[split]

lemmas Traces_ConsI = emitEvent_intros[THEN Step]

inductive_cases Traces_NilE[elim]: "(s, [], s') \<in> Traces"
inductive_cases Traces_ConsE[elim]: "(s, e # t, s') \<in> Traces"

lemma runTrace_iff_Traces: "runTrace t m = Some m' \<longleftrightarrow> (m, t, m') \<in> Traces"
  by (induction t m rule: runTrace.induct; fastforce simp: bind_eq_Some_conv)

lemma hasTrace_iff_Traces_final: "hasTrace t m \<longleftrightarrow> (\<exists>m'. (m, t, m') \<in> Traces \<and> final m')"
  by (auto simp: hasTrace_def runTrace_iff_Traces[symmetric] split: option.splits)

lemma runTrace_eq_iff_id:
  "(\<forall>t. runTrace t m1 = runTrace t m2) \<longleftrightarrow> (m1 = m2)"
  by (auto elim: allE[where x = "[]"])

lemma Traces_eq_iff_id:
  "(\<forall>t m'. (m1, t, m') \<in> Traces \<longleftrightarrow> (m2, t, m') \<in> Traces) \<longleftrightarrow> (m1 = m2)"
  by (auto elim: allE[where x = "[]"])

lemma Traces_cases:
  (* fixes m :: "('rv, 'a, 'e) monad" *)
  assumes Run: "(m, t, m') \<in> Traces"
  obtains (Nil) a where "m = m'" and "t = []"
  | (Choose) descr v k t' where "m = Choose descr k" and "t = E_choose descr v # t'" and "(k v, t', m') \<in> Traces"
  | (Read_reg) reg k t' v where "m = Read_reg reg k" and "t = E_read_reg reg v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_reg) reg v k t' where "m = Write_reg reg v k" and "t = E_write_reg reg v # t'" and "(k, t', m') \<in> Traces"
  | (Read_mem) req k t' v where "m = Mem_read_request req k" and "t = E_mem_read_request req v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_mem) req k v t' where "m = Mem_write_request req k" and "t = E_mem_write_request req v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_announce) a k t' where "m = Mem_write_announce_address a k" and "t = E_mem_write_announce_address a # t'" and "(k, t', m') \<in> Traces"
  | (Translation_start) ts k t' where "m = Translation_start ts k" and "t = E_translation_start ts # t'" and "(k, t', m') \<in> Traces"
  | (Translation_end) te k t' where "m = Translation_end te k" and "t = E_translation_end te # t'" and "(k, t', m') \<in> Traces"
  | (Branch_announce) a k t' where "m = Branch_announce_address a k" and "t = E_branch_announce_address a # t'" and "(k, t', m') \<in> Traces"
  | (Barrier) r k t' where "m = Barrier_request r k" and "t = E_barrier_request r # t'" and "(k, t', m') \<in> Traces"
  | (Cache_op) r k t' where "m = Cache_op_request r k" and "t = E_cache_op_request r # t'" and "(k, t', m') \<in> Traces"
  | (TLB_op) r k t' where "m = TLB_op_request r k" and "t = E_tlb_op_request r # t'" and "(k, t', m') \<in> Traces"
  | (Fault) f k t' where "m = Fault_announce f k" and "t = E_fault_announce f # t'" and "(k, t', m') \<in> Traces"
  | (Eret) pa k t' where "m = Eret_announce pa k" and "t = E_eret_announce pa # t'" and "(k, t', m') \<in> Traces"
proof (use Run in \<open>cases m t m' set: Traces\<close>)
  case Nil
  then show ?thesis by (auto intro: that(1))
next
  case (Step e m'' t')
  then show ?thesis
    by (cases m; cases e) (auto simp: emitEvent_def split: if_splits elim: that)
qed

lemma Traces_iffs:
  "\<And>a t m'. (Done a, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Done a)"
  "\<And>msg t m'. (Fail msg, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Fail msg)"
  "\<And>e t m'. (Exception e, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Exception e)"
  "\<And>descr k t m'. (Choose descr k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Choose descr k \<or> (\<exists>a t'. t = E_choose descr a # t' \<and> (k a, t', m') \<in> Traces))"
  "\<And>reg k t m'. (Read_reg reg k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Read_reg reg k \<or> (\<exists>a t'. t = E_read_reg reg a # t' \<and> (k a, t', m') \<in> Traces))"
  "\<And>reg a k t m'. (Write_reg reg a k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Write_reg reg a k \<or> (\<exists>t'. t = E_write_reg reg a # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>req k t m'. (Mem_read_request req k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Mem_read_request req k \<or> (\<exists>a t'. t = E_mem_read_request req a # t' \<and> (k a, t', m') \<in> Traces))"
  "\<And>req k t m'. (Mem_write_request req k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Mem_write_request req k \<or> (\<exists>a t'. t = E_mem_write_request req a # t' \<and> (k a, t', m') \<in> Traces))"
  "\<And>a k t m'. (Mem_write_announce_address a k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Mem_write_announce_address a k \<or> (\<exists>t'. t = E_mem_write_announce_address a # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>ts k t m'. (Translation_start ts k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Translation_start ts k \<or> (\<exists>t'. t = E_translation_start ts # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>te k t m'. (Translation_end te k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Translation_end te k \<or> (\<exists>t'. t = E_translation_end te # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>a k t m'. (Branch_announce_address a k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Branch_announce_address a k \<or> (\<exists>t'. t = E_branch_announce_address a # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>req k t m'. (Barrier_request req k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Barrier_request req k \<or> (\<exists>t'. t = E_barrier_request req # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>req k t m'. (Cache_op_request req k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Cache_op_request req k \<or> (\<exists>t'. t = E_cache_op_request req # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>req k t m'. (TLB_op_request req k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = TLB_op_request req k \<or> (\<exists>t'. t = E_tlb_op_request req # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>f k t m'. (Fault_announce f k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Fault_announce f k \<or> (\<exists>t'. t = E_fault_announce f # t' \<and> (k, t', m') \<in> Traces))"
  "\<And>pa k t m'. (Eret_announce pa k, t, m') \<in> Traces \<longleftrightarrow> (t = [] \<and> m' = Eret_announce pa k \<or> (\<exists>t'. t = E_eret_announce pa # t' \<and> (k, t', m') \<in> Traces))"
  by (auto elim: Traces_cases intro: Traces_ConsI)

lemmas Done_Traces_iff[iff] = Traces_iffs(1)
lemmas Fail_Traces_iff[iff] = Traces_iffs(2)
lemmas Exception_Traces_iff[iff] = Traces_iffs(3)
lemmas Traces_iff_Cons = Traces_iffs(4-)

abbreviation Run (*:: "('rv, 'a, 'e) monad \<Rightarrow> 'rv event list \<Rightarrow> 'a \<Rightarrow> bool"*)
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

lemma emitEvent_bind:
  assumes "emitEvent m e = Some m'"
  shows "emitEvent (bind m f) e = Some (bind m' f)"
  using assms
  by (cases rule: emitEvent_cases) (auto intro: emitEvent_intros)

lemma emitEvent_bind_cases:
  assumes "emitEvent (bind m f) e = Some m'"
  obtains (Done) a where "m = Done a" and "emitEvent (f a) e = Some m'"
  | (Bind) m'' where "m' = bind m'' f" and "emitEvent m e = Some m''"
proof (cases "emitEvent m e")
  case None
  then have "emitEvent (bind m f) e = None \<or> (\<exists>a. m = Done a)"
    by (auto simp: emitEvent_def split: event.splits monad.splits)
  then show ?thesis
    using assms
    by (auto intro: Done)
next
  case (Some m'')
  then show ?thesis
    using assms
    by (auto simp: emitEvent_bind intro: Bind)
qed

lemma bind_T_cases:
  assumes "(bind m f, e, s') \<in> T"
  obtains (Done) a where "m = Done a" and "(f a, e, s') \<in> T"
  | (Bind) m' where "s' = bind m' f" and "(m, e, m') \<in> T"
  using assms
  unfolding emitEvent_iff_T[symmetric]
  by (elim emitEvent_bind_cases)

lemma Traces_bindI:
  assumes "Run m t1 a1"
    and "(f a1, t2, m') \<in> Traces"
  shows "(m \<bind> f, t1 @ t2, m') \<in> Traces"
  using assms
  by (induction t1 arbitrary: m; fastforce intro: Traces_ConsI elim: emitEvent_cases)

lemma Run_Done_iff[iff]: "Run (Done a) t a' \<longleftrightarrow> t = [] \<and> a' = a" by auto

lemma Run_return_iff[iff]: "Run (return a) t a' \<longleftrightarrow> t = [] \<and> a' = a" by (auto simp: return_def)

lemma Run_throw[iff]: "Run (throw e) t a \<longleftrightarrow> False" by (auto simp: throw_def)

lemma Run_early_return_False[iff]: "Run (early_return x) t u \<longleftrightarrow> False"
  by (auto simp: early_return_def)

lemma Run_assert_exp_iff[iff]: "Run (assert_exp c msg) t u \<longleftrightarrow> t = [] \<and> c"
  by (auto simp: assert_exp_def)

lemma Run_DoneE:
  assumes "Run (Done a) t a'"
  obtains "t = []" and "a' = a"
  using assms
  by (auto)

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
  proof (use \<open>emitEvent (m \<bind> f) e = Some s''\<close> in \<open>cases rule: emitEvent_bind_cases\<close>)
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
      then show thesis using \<open>emitEvent m e = Some m'\<close> Left'[of m''] by auto
    next
      fix tm tf am
      assume "t = tm @ tf" and "Run m' tm am" and "(f am, tf, s') \<in> Traces"
      then show thesis using \<open>emitEvent m e = Some m'\<close> Bind'[of "e # tm" tf am] by auto
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

lemma emitEvent_try_catch_cases:
  assumes "emitEvent (try_catch m h) e = Some m'"
  obtains (NoEx) m'' where "emitEvent m e = Some m''" and "m' = try_catch m'' h"
  | (Ex) ex where "m = Exception ex" and "emitEvent (h ex) e = Some m'"
  using assms
  by (cases m) (auto elim: emitEvent_cases simp: emitEvent_intros)

(*lemma try_catch_T_cases:
  assumes "(try_catch m h, e, m') \<in> T"
  obtains (NoEx) m'' where "(m, e, m'') \<in> T" and "m' = try_catch m'' h"
  | (Ex) ex where "m = Exception ex" and "(h ex, e, m') \<in> T"
  using assms
  by (cases m) (auto elim!: T.cases)*)

lemma try_catch_Traces_cases:
  assumes "(try_catch m h, t, mtc) \<in> Traces"
  obtains (NoEx) m' where "(m, t, m') \<in> Traces" and "mtc = try_catch m' h"
  | (Ex) tm ex th where "(m, tm, Exception ex) \<in> Traces" and "(h ex, th, mtc) \<in> Traces" and "t = tm @ th"
proof (use assms in \<open>induction "try_catch m h" t mtc arbitrary: m rule: Traces.induct\<close>)
  case Nil
  then show ?case by auto
next
  case (Step e mtc' t mtc)
  note e = \<open>emitEvent (try_catch m h) e = Some mtc'\<close>
  note t = \<open>(mtc', t, mtc) \<in> Traces\<close>
  note IH = Step(3)
  note NoEx_ConsE = Step(4)
  note Ex_ConsE = Step(5)
  show ?case
  proof (use e in \<open>cases rule: emitEvent_try_catch_cases\<close>)
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

lemma Mem_write_request_TracesE:
  assumes "(Mem_write_request req k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Mem_write_request req k"
  | (Cons) t' r where "t = E_mem_write_request req r # t'" and "(k r, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)

(*lemma Write_ea_TracesE:
  assumes "(Write_ea wk addr sz k, t, m') \<in> Traces"
  obtains (Nil) "t = []" and "m' = Write_ea wk addr sz k"
  | (Cons) t' where "t = E_write_ea wk addr sz # t'" and "(k, t', m') \<in> Traces"
  using assms
  by (auto elim: Traces_cases)*)

lemma Run_bind_ex:
  assumes "Run (bind m f) t a"
  shows "\<exists>tm am tf. t = tm @ tf \<and> Run m tm am \<and> Run (f am) tf a"
proof (use assms in \<open>induction t arbitrary: m\<close>)
  case (Nil m)
  then show ?case
    by (cases m) auto
next
  case (Cons e t m)
  then consider (Step) m' where "emitEvent m e = Some m'" and "Run (bind m' f) t a"
    | (Done) a' where "m = Done a'"
    by (elim Traces_ConsE emitEvent_bind_cases) auto
  then show ?case
  proof cases
    case Step
    then obtain tm' am' tf where "t = tm' @ tf" and "Run m' tm' am'" and "Run (f am') tf a"
      using Cons.IH[of m']
      by blast
    then have "e # t = (e # tm') @ tf" and "Run m (e # tm') am'" and "Run (f am') tf a"
      using Step
      by auto
    then show ?thesis
      by blast
  next
    case Done
    with Cons.prems show ?thesis
      by auto
  qed
qed

lemma Run_bindE:
  assumes "Run (bind m f) t a"
  obtains tm am tf where "t = tm @ tf" and "Run m tm am" and "Run (f am) tf a"
  using Run_bind_ex[OF assms]
  by blast

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
  by (induction m2 f1 arbitrary: f2 rule: bind.induct; unfold bind.simps; blast intro: emitEvent_intros)

lemma liftR_read_reg[simp]: "liftR (read_reg reg) = read_reg reg" by (auto simp: read_reg_def liftR_def split: option.splits)
lemma try_catch_return[simp]: "try_catch (return x) h = return x" by (auto simp: return_def)
lemma liftR_return[simp]: "liftR (return x) = return x" by (auto simp: liftR_def)
lemma assert_exp_True_return[simp]: "assert_exp True msg = return ()" by (auto simp: assert_exp_def return_def)
lemma liftR_assert_exp[simp]: "liftR (assert_exp e msg) = assert_exp e msg" by (auto simp: liftR_def assert_exp_def)
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

lemma catch_early_return_bind_liftR:
  "catch_early_return (liftR m \<bind> f) = (m \<bind> (\<lambda>a. catch_early_return (f a)))"
  by (induction m) (auto simp: catch_early_return_def liftR_def throw_def)

lemma catch_early_return_bind_early_return:
  "catch_early_return (early_return a \<bind> f) = return a"
  by (auto simp: catch_early_return_def early_return_def throw_def)

lemmas catch_early_return_if_distrib = if_distrib[where f = catch_early_return]
lemmas catch_early_return_prod_distrib = prod.case_distrib[where h = catch_early_return]
lemmas catch_early_return_bind_if_distrib =
  if_distrib[where f = "\<lambda>m. m \<bind> f" for f, THEN refl[of catch_early_return, THEN cong]]

text \<open>Precondition to ensure reading a register doesn't fail.\<close>

fun(sequential)
  register_reads_ok (*:: "(string \<Rightarrow> ('regval \<Rightarrow> bool) option) \<Rightarrow> 'regval event \<Rightarrow> bool"*)
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
