theory Sail2_state_lemmas
  imports
    Sail2_state
    Sail2_state_lifting
    Add_Cancel_Distinct
begin

text \<open>Monad lifting\<close>

lemma All_liftState_dom: "liftState_dom (r, m)"
  by (induction m) (auto intro: liftState.domintros)
termination liftState using All_liftState_dom by auto

named_theorems liftState_simp

lemma liftState_bind[liftState_simp]:
  "liftState r (bind m f) = bindS (liftState r m) (liftState r \<circ> f)"
  by (induction m f rule: bind.induct) auto

lemma liftState_return[liftState_simp]: "liftState r (return a) = returnS a" by (auto simp: return_def)

lemma Value_liftState_Run:
  assumes "(Value a, s') \<in> liftState r m s"
  obtains t where "Run m t a"
  by (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>;
      simp add: failS_def throwS_def returnS_def del: read_regvalS.simps;
      blast elim: Value_bindS_elim)

lemmas liftState_if_distrib[liftState_simp] = if_distrib[where f = "liftState ra" for ra]

lemma Value_bindS_iff:
  "(Value b, s'') \<in> bindS m f s \<longleftrightarrow> (\<exists>a s'. (Value a, s') \<in> m s \<and> (Value b, s'') \<in> f a s')"
  by (auto elim!: bindS_cases intro: bindS_intros)

lemma Ex_bindS_iff:
  "(Ex e, s'') \<in> bindS m f s \<longleftrightarrow> (Ex e, s'') \<in> m s \<or> (\<exists>a s'. (Value a, s') \<in> m s \<and> (Ex e, s'') \<in> f a s')"
  by (auto elim!: bindS_cases intro: bindS_intros)

lemma liftState_throw[liftState_simp]: "liftState r (throw e) = throwS e"
  by (auto simp: throw_def)
lemma liftState_assert[liftState_simp]: "liftState r (assert_exp c msg) = assert_expS c msg"
  by (auto simp: assert_exp_def assert_expS_def)
lemma liftState_exit[liftState_simp]: "liftState r (exit0 ()) = exitS ()"
  by (auto simp: exit0_def exitS_def)
lemma liftState_exclResult[liftState_simp]: "liftState r (excl_result ()) = excl_resultS ()"
  by (auto simp: excl_result_def liftState_simp)
lemma liftState_barrier[liftState_simp]: "liftState r (barrier bk) = returnS ()"
  by (auto simp: barrier_def)
lemma liftState_footprint[liftState_simp]: "liftState r (footprint ()) = returnS ()"
  by (auto simp: footprint_def)
lemma liftState_maybe_fail[liftState_simp]: "liftState r (maybe_fail msg x) = maybe_failS msg x"
  by (auto simp: maybe_fail_def maybe_failS_def liftState_simp split: option.splits)
lemma liftState_and_boolM[liftState_simp]:
  "liftState r (and_boolM x y) = and_boolS (liftState r x) (liftState r y)"
  by (auto simp: and_boolM_def and_boolS_def liftState_simp cong: bindS_cong if_cong)
lemma liftState_or_boolM[liftState_simp]:
  "liftState r (or_boolM x y) = or_boolS (liftState r x) (liftState r y)"
  by (auto simp: or_boolM_def or_boolS_def liftState_simp cong: bindS_cong if_cong)

lemma liftState_try_catch[liftState_simp]:
  "liftState r (try_catch m h) = try_catchS (liftState r m) (liftState r \<circ> h)"
  by (induction m h rule: try_catch_induct) (auto simp: try_catchS_bindS_no_throw)

lemma liftState_early_return[liftState_simp]:
  "liftState r (early_return x) = early_returnS x"
  by (auto simp: early_return_def early_returnS_def liftState_simp)

lemma liftState_catch_early_return[liftState_simp]:
  "liftState r (catch_early_return m) = catch_early_returnS (liftState r m)"
  by (auto simp: catch_early_return_def catch_early_returnS_def sum.case_distrib liftState_simp cong: sum.case_cong)

lemma liftState_liftR[liftState_simp]:
  "liftState r (liftR m) = liftRS (liftState r m)"
  by (auto simp: liftR_def liftRS_def liftState_simp)

lemma liftState_try_catchR[liftState_simp]:
  "liftState r (try_catchR m h) = try_catchRS (liftState r m) (liftState r \<circ> h)"
  by (auto simp: try_catchR_def try_catchRS_def sum.case_distrib liftState_simp cong: sum.case_cong)

(*lemma liftState_bool_of_bitU_nondet[liftState_simp]:
  "liftState r (bool_of_bitU_nondet b) = bool_of_bitU_nondetS b"
  by (cases b; auto simp: bool_of_bitU_nondet_def bool_of_bitU_nondetS_def liftState_simp)*)

lemma liftState_read_memt[liftState_simp]:
  shows "liftState r (read_memt BCa BCb rk a sz) = read_memtS BCa BCb rk a sz"
  by (auto simp: read_memt_def read_memt_bytes_def maybe_failS_def read_memtS_def
                 prod.case_distrib option.case_distrib[where h = "liftState r"]
                 option.case_distrib[where h = "\<lambda>c. c \<bind>\<^sub>S f" for f] liftState_simp
           split: option.splits intro: bindS_cong)

lemma liftState_read_mem[liftState_simp]:
  shows "liftState r (read_mem BCa BCb rk asz a sz) = read_memS BCa BCb rk asz a sz"
  by (auto simp: read_mem_def read_mem_bytes_def read_memS_def read_mem_bytesS_def maybe_failS_def
                 read_memtS_def
                 prod.case_distrib option.case_distrib[where h = "liftState r"]
                 option.case_distrib[where h = "\<lambda>c. c \<bind>\<^sub>S f" for f] liftState_simp
           split: option.splits intro: bindS_cong)

lemma liftState_write_mem_ea_BC:
  assumes "unsigned_method BCa a = Some a'"
  shows "liftState r (write_mem_ea BCa rk asz a sz) = returnS ()"
  using assms by (auto simp: write_mem_ea_def nat_of_bv_def maybe_fail_def)

(*lemma liftState_write_mem_ea[liftState_simp]:
  "\<And>a. liftState r (write_mem_ea BC_mword rk a sz) = returnS ()"
  "\<And>a. liftState r (write_mem_ea BC_bitU_list rk a sz) = returnS ()"
  by (auto simp: liftState_write_mem_ea_BC)*)

(*lemma write_mem_bytesS_def_BC_bitU_list_BC_mword[simp]:
  "write_mem_bytesS BC_bitU_list wk (bits_of_method BC_mword addr) sz v t =
   write_mem_bytesS BC_mword wk addr sz v t"
  by (auto simp: write_mem_bytesS_def)*)

lemma liftState_write_memt[liftState_simp]:
  "liftState r (write_memt BCa BCv wk addr sz v t) = write_memtS BCa BCv wk addr sz v t"
  by (auto simp: write_memt_def write_memtS_def liftState_simp split: option.splits)

lemma liftState_write_mem[liftState_simp]:
  "liftState r (write_mem BCa BCv wk addrsize addr sz v) = write_memS BCa BCv wk addrsize addr sz v"
  by (auto simp: write_mem_def write_memS_def write_memtS_def write_mem_bytesS_def liftState_simp
           split: option.splits)

lemma liftState_read_reg:
  assumes "\<And>s. Option.bind (get_regval' (name reg) s) (of_regval reg) = Some (read_from reg s)"
  shows "liftState (get_regval', set_regval') (read_reg reg) = read_regS reg"
proof
  fix s :: "'a sequential_state"
  obtain rv v where "get_regval' (name reg) (regstate s) = Some rv"
    and "of_regval reg rv \<equiv> Some v" and "read_from reg (regstate s) = v"
    using assms unfolding bind_eq_Some_conv by blast
  then show "liftState (get_regval', set_regval') (read_reg reg) s = read_regS reg s"
    by (auto simp: read_reg_def bindS_def returnS_def read_regS_def readS_def)
qed

lemma liftState_write_reg:
  assumes "\<And>s. set_regval' (name reg) (regval_of reg v) s = Some (write_to reg v s)"
  shows "liftState (get_regval', set_regval') (write_reg reg v) = write_regS reg v"
  using assms by (auto simp: write_reg_def updateS_def returnS_def bindS_readS write_regS_def)

lemma liftState_iter_aux[liftState_simp]:
  shows "liftState r (iter_aux i f xs) = iterS_aux i (\<lambda>i x. liftState r (f i x)) xs"
  by (induction i "\<lambda>i x. liftState r (f i x)" xs rule: iterS_aux.induct)
     (auto simp: liftState_simp cong: bindS_cong)

lemma liftState_iteri[liftState_simp]:
  "liftState r (iteri f xs) = iteriS (\<lambda>i x. liftState r (f i x)) xs"
  by (auto simp: iteri_def iteriS_def liftState_simp)

lemma liftState_iter[liftState_simp]:
  "liftState r (iter f xs) = iterS (liftState r \<circ> f) xs"
  by (auto simp: iter_def iterS_def liftState_simp)

lemma liftState_foreachM[liftState_simp]:
  "liftState r (foreachM xs vars body) = foreachS xs vars (\<lambda>x vars. liftState r (body x vars))"
  by (induction xs vars "\<lambda>x vars. liftState r (body x vars)" rule: foreachS.induct)
     (auto simp: liftState_simp cong: bindS_cong)

lemma liftState_genlistM[liftState_simp]:
  "liftState r (genlistM f n) = genlistS (liftState r \<circ> f) n"
  by (auto simp: genlistM_def genlistS_def liftState_simp cong: bindS_cong)

(*lemma liftState_choose_bools[liftState_simp]:
  "liftState r (choose_bools descr n) = choose_boolsS n"
  by (auto simp: choose_bools_def choose_boolsS_def liftState_simp comp_def)

lemma liftState_bools_of_bits_nondet[liftState_simp]:
  "liftState r (bools_of_bits_nondet bs) = bools_of_bits_nondetS bs"
  unfolding bools_of_bits_nondet_def bools_of_bits_nondetS_def
  by (auto simp: liftState_simp comp_def)

lemma liftState_internal_pick[liftState_simp]:
  "liftState r (internal_pick xs) = internal_pickS xs"
  by (auto simp: internal_pick_def internal_pickS_def liftState_simp comp_def
                 chooseM_def
                 option.case_distrib[where h = "liftState r"]
           simp del: repeat.simps
           cong: option.case_cong)*)

lemma liftRS_returnS[simp]: "liftRS (returnS x) = returnS x"
  by (auto simp: liftRS_def)

lemma liftRS_bindS:
  fixes m :: "('regs, 'a, 'e) monadS" and f :: "'a \<Rightarrow> ('regs, 'b, 'e) monadS"
  shows "(liftRS (bindS m f) :: ('regs, 'b, 'r, 'e) monadRS) = bindS (liftRS m) (liftRS \<circ> f)"
proof (intro ext set_eqI iffI)
  fix s and rs' :: "('b, 'r + 'e) state_result \<times> 'regs sequential_state"
  assume lhs: "rs' \<in> liftRS (bindS m f) s"
  then show "rs' \<in> bindS (liftRS m) (liftRS \<circ> f) s"
    by (cases rs')
       (fastforce simp: liftRS_def throwS_def elim!: bindS_cases try_catchS_cases
                  intro: bindS_intros try_catchS_intros)
next
  fix s and rs' :: "('b, 'r + 'e) state_result \<times> 'regs sequential_state"
  assume "rs' \<in> bindS (liftRS m) (liftRS \<circ> f) s"
  then show "rs' \<in> liftRS (bindS m f) s"
    by (cases rs')
       (fastforce simp: liftRS_def throwS_def elim!: bindS_cases try_catchS_cases
                  intro: bindS_intros try_catchS_intros)
qed

lemma liftRS_assert_expS_True[simp]: "liftRS (assert_expS True msg) = returnS ()"
  by (auto simp: liftRS_def assert_expS_def)

lemma untilM_domI:
  fixes V :: "'vars \<Rightarrow> nat"
  assumes "Inv vars"
    and "\<And>vars t vars' t'. \<lbrakk>Inv vars; Run (body vars) t vars'; Run (cond vars') t' False\<rbrakk> \<Longrightarrow> V vars' < V vars \<and> Inv vars'"
  shows "untilM_dom (vars, cond, body)"
  using assms
  by (induction vars rule: measure_induct_rule[where f = V])
     (auto intro: untilM.domintros)

lemma untilM_dom_untilS_dom:
  assumes "untilM_dom (vars, cond, body)"
  shows "untilS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
  using assms
  by (induction vars cond body arbitrary: s rule: untilM.pinduct)
     (rule untilS.domintros, auto elim!: Value_liftState_Run)

lemma measure2_induct:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> nat"
  assumes "\<And>x1 y1. (\<And>x2 y2. f x2 y2 < f x1 y1 \<Longrightarrow> P x2 y2) \<Longrightarrow> P x1 y1"
  shows "P x y"
proof -
  have "P (fst x) (snd x)" for x
    by (induction x rule: measure_induct_rule[where f = "\<lambda>x. f (fst x) (snd x)"]) (auto intro: assms)
  then show ?thesis by auto
qed

lemma untilS_domI:
  fixes V :: "'vars \<Rightarrow> 'regs sequential_state \<Rightarrow> nat"
  assumes "Inv vars s"
    and "\<And>vars s vars' s' s''.
           \<lbrakk>Inv vars s; (Value vars', s') \<in> body vars s; (Value False, s'') \<in> cond vars' s'\<rbrakk>
            \<Longrightarrow> V vars' s'' < V vars s \<and> Inv vars' s''"
  shows "untilS_dom (vars, cond, body, s)"
  using assms
  by (induction vars s rule: measure2_induct[where f = V])
     (auto intro: untilS.domintros)

lemma whileS_dom_step:
  assumes "whileS_dom (vars, cond, body, s)"
    and "(Value True, s') \<in> cond vars s"
    and "(Value vars', s'') \<in> body vars s'"
  shows "whileS_dom (vars', cond, body, s'')"
  by (use assms in \<open>induction vars cond body s arbitrary: vars' s' s'' rule: whileS.pinduct\<close>)
     (auto intro: whileS.domintros)

lemma whileM_dom_step:
  assumes "whileM_dom (vars, cond, body)"
    and "Run (cond vars) t True"
    and "Run (body vars) t' vars'"
  shows "whileM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: whileM.pinduct\<close>)
     (auto intro: whileM.domintros)

lemma whileM_dom_ex_step:
  assumes "whileM_dom (vars, cond, body)"
    and "\<exists>t. Run (cond vars) t True"
    and "\<exists>t'. Run (body vars) t' vars'"
  shows "whileM_dom (vars', cond, body)"
  using assms by (blast intro: whileM_dom_step)

lemmas whileS_pinduct = whileS.pinduct[case_names Step]

lemma liftState_whileM:
  assumes "whileS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
    and "whileM_dom (vars, cond, body)"
  shows "liftState r (whileM vars cond body) s = whileS vars (liftState r \<circ> cond) (liftState r \<circ> body) s"
proof (use assms in \<open>induction vars "liftState r \<circ> cond" "liftState r \<circ> body" s rule: whileS.pinduct\<close>)
  case Step: (1 vars s)
  note domS = Step(1) and IH = Step(2) and domM = Step(3)
  show ?case unfolding whileS.psimps[OF domS] whileM.psimps[OF domM] liftState_bind
  proof (intro bindS_ext_cong, goal_cases cond while)
    case (while a s')
    have "bindS (liftState r (body vars)) (liftState r \<circ> (\<lambda>vars. whileM vars cond body)) s' =
          bindS (liftState r (body vars)) (\<lambda>vars. whileS vars (liftState r \<circ> cond) (liftState r \<circ> body)) s'"
      if "a"
    proof (intro bindS_ext_cong, goal_cases body while')
      case (while' vars' s'')
      have "whileM_dom (vars', cond, body)" proof (rule whileM_dom_ex_step[OF domM])
        show "\<exists>t. Run (cond vars) t True" using while that by (auto elim: Value_liftState_Run)
        show "\<exists>t'. Run (body vars) t' vars'" using while' that by (auto elim: Value_liftState_Run)
      qed
      then show ?case using while while' that IH by auto
    qed auto
    then show ?case by (auto simp: liftState_simp)
  qed auto
qed


lemma untilM_dom_step:
  assumes "untilM_dom (vars, cond, body)"
    and "Run (body vars) t vars'"
    and "Run (cond vars') t' False"
  shows "untilM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: untilM.pinduct\<close>)
     (auto intro: untilM.domintros)

lemma untilM_dom_ex_step:
  assumes "untilM_dom (vars, cond, body)"
    and "\<exists>t. Run (body vars) t vars'"
    and "\<exists>t'. Run (cond vars') t' False"
  shows "untilM_dom (vars', cond, body)"
  using assms by (blast intro: untilM_dom_step)

lemma liftState_untilM:
  assumes "untilS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
    and "untilM_dom (vars, cond, body)"
  shows "liftState r (untilM vars cond body) s = untilS vars (liftState r \<circ> cond) (liftState r \<circ> body) s"
proof (use assms in \<open>induction vars "liftState r \<circ> cond" "liftState r \<circ> body" s rule: untilS.pinduct\<close>)
  case Step: (1 vars s)
  note domS = Step(1) and IH = Step(2) and domM = Step(3)
  show ?case unfolding untilS.psimps[OF domS] untilM.psimps[OF domM] liftState_bind
  proof (intro bindS_ext_cong, goal_cases body k)
    case (k vars' s')
    show ?case unfolding comp_def liftState_bind
    proof (intro bindS_ext_cong, goal_cases cond until)
      case (until a s'')
      have "untilM_dom (vars', cond, body)" if "\<not>a"
      proof (rule untilM_dom_ex_step[OF domM])
        show "\<exists>t. Run (body vars) t vars'" using k by (auto elim: Value_liftState_Run)
        show "\<exists>t'. Run (cond vars') t' False" using until that by (auto elim: Value_liftState_Run)
      qed
      then show ?case using k until IH by (auto simp: comp_def liftState_simp)
    qed auto
  qed auto
qed

text \<open>Simplification rules for monadic Boolean connectives\<close>

lemma if_return_return[simp]: "(if a then return True else return False) = return a" by auto

lemma and_boolM_simps[simp]:
  "and_boolM (return b) (return c) = return (b \<and> c)"
  "and_boolM x (return True) = x"
  "and_boolM x (return False) = x \<bind> (\<lambda>_. return False)"
  "\<And>x y z. and_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. and_boolM (y r) z))"
  by (auto simp: and_boolM_def)

lemma and_boolM_return_if:
  "and_boolM (return b) y = (if b then y else return False)"
  by (auto simp: and_boolM_def)

lemma and_boolM_return_return_and[simp]: "and_boolM (return l) (return r) = return (l \<and> r)"
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

lemma or_boolM_return_return_or[simp]: "or_boolM (return l) (return r) = return (l \<or> r)"
  by (auto simp: or_boolM_def)

lemmas or_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolM x y" for y]

lemma if_returnS_returnS[simp]: "(if a then returnS True else returnS False) = returnS a" by auto

lemma and_boolS_simps[simp]:
  "and_boolS (returnS b) (returnS c) = returnS (b \<and> c)"
  "and_boolS x (returnS True) = x"
  "and_boolS x (returnS False) = bindS x (\<lambda>_. returnS False)"
  "\<And>x y z. and_boolS (bindS x y) z = (bindS x (\<lambda>r. and_boolS (y r) z))"
  by (auto simp: and_boolS_def)

lemma and_boolS_returnS_if:
  "and_boolS (returnS b) y = (if b then y else returnS False)"
  by (auto simp: and_boolS_def)

lemmas and_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolS x y" for y]

lemma and_boolS_returnS_True[simp]: "and_boolS (returnS True) c = c"
  by (auto simp: and_boolS_def)

lemma or_boolS_simps[simp]:
  "or_boolS (returnS b) (returnS c) = returnS (b \<or> c)"
  "or_boolS (returnS False) m = m"
  "or_boolS x (returnS True) = bindS x (\<lambda>_. returnS True)"
  "or_boolS x (returnS False) = x"
  "\<And>x y z. or_boolS (bindS x y) z = (bindS x (\<lambda>r. or_boolS (y r) z))"
  by (auto simp: or_boolS_def)

lemma or_boolS_returnS_if:
  "or_boolS (returnS b) y = (if b then returnS True else y)"
  by (auto simp: or_boolS_def)

lemmas or_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolS x y" for y]

lemma Run_or_boolM_E:
  assumes "Run (or_boolM l r) t a"
  obtains "Run l t True" and "a"
  | tl tr where "Run l tl False" and "Run r tr a" and "t = tl @ tr"
  using assms by (auto simp: or_boolM_def elim!: Run_bindE Run_ifE Run_returnE)

lemma Run_and_boolM_E:
  assumes "Run (and_boolM l r) t a"
  obtains "Run l t False" and "\<not>a"
  | tl tr where "Run l tl True" and "Run r tr a" and "t = tl @ tr"
  using assms by (auto simp: and_boolM_def elim!: Run_bindE Run_ifE Run_returnE)

lemma maybe_failS_Some[simp]: "maybe_failS msg (Some v) = returnS v"
  by (auto simp: maybe_failS_def)

text \<open>Event traces\<close>

lemma Some_eq_bind_conv: "Some x = Option.bind f g \<longleftrightarrow> (\<exists>y. f = Some y \<and> g y = Some x)"
  unfolding bind_eq_Some_conv[symmetric] by auto

lemma if_then_Some_eq_Some_iff: "((if b then Some x else None) = Some y) \<longleftrightarrow> (b \<and> y = x)"
  by auto

lemma Some_eq_if_then_Some_iff: "(Some y = (if b then Some x else None)) \<longleftrightarrow> (b \<and> y = x)"
  by auto

lemma emitEventS_update_cases:
  assumes "emitEventS ra e s = Some s'"
  obtains
    (Write_mem) wk addr sz v tag r
      where "e = E_write_memt wk addr sz v tag r \<or> (e = E_write_mem wk addr sz v r \<and> tag = B0)"
        and "s' = put_mem_bytes addr sz v tag s"
  | (Write_reg) r v rs'
      where "e = E_write_reg r v" and "(snd ra) r v (regstate s) = Some rs'"
        and "s' = s\<lparr>regstate := rs'\<rparr>"
  | (Read) "s' = s"
  using assms
  by (elim emitEventS.elims)
     (auto simp: Some_eq_bind_conv bind_eq_Some_conv if_then_Some_eq_Some_iff Some_eq_if_then_Some_iff)

lemma runTraceS_singleton[simp]: "runTraceS ra [e] s = emitEventS ra e s"
  by (cases "emitEventS ra e s"; auto)

lemma runTraceS_ConsE:
  assumes "runTraceS ra (e # t) s = Some s'"
  obtains s'' where "emitEventS ra e s = Some s''" and "runTraceS ra t s'' = Some s'"
  using assms by (auto simp: bind_eq_Some_conv)

lemma runTraceS_ConsI:
  assumes "emitEventS ra e s = Some s'" and "runTraceS ra t s' = Some s''"
  shows "runTraceS ra (e # t) s = Some s''"
  using assms by auto

lemma runTraceS_Cons_tl:
  assumes "emitEventS ra e s = Some s'"
  shows "runTraceS ra (e # t) s = runTraceS ra t s'"
  using assms by (elim emitEventS.elims) (auto simp: Some_eq_bind_conv bind_eq_Some_conv)

lemma runTraceS_appendE:
  assumes "runTraceS ra (t @ t') s = Some s'"
  obtains s'' where "runTraceS ra t s = Some s''" and "runTraceS ra t' s'' = Some s'"
proof -
  have "\<exists>s''. runTraceS ra t s = Some s'' \<and> runTraceS ra t' s'' = Some s'"
  proof (use assms in \<open>induction t arbitrary: s\<close>)
    case (Cons e t)
    from Cons.prems
    obtain s_e where "emitEventS ra e s = Some s_e" and "runTraceS ra (t @ t') s_e = Some s'"
      by (auto elim: runTraceS_ConsE simp: bind_eq_Some_conv)
    with Cons.IH[of s_e] show ?case by (auto intro: runTraceS_ConsI)
  qed auto
  then show ?thesis using that by blast
qed

lemma runTraceS_nth_split:
  assumes "runTraceS ra t s = Some s'" and n: "n < length t"
  obtains s1 s2 where "runTraceS ra (take n t) s = Some s1"
    and "emitEventS ra (t ! n) s1 = Some s2"
    and "runTraceS ra (drop (Suc n) t) s2 = Some s'"
proof -
  have "runTraceS ra (take n t @ t ! n # drop (Suc n) t) s = Some s'"
    using assms
    by (auto simp: id_take_nth_drop[OF n, symmetric])
  then show thesis by (blast elim: runTraceS_appendE runTraceS_ConsE intro: that)
qed

text \<open>Memory accesses\<close>

lemma get_mem_bytes_put_mem_bytes_same_addr:
  assumes "length v = sz"
  shows "get_mem_bytes addr sz (put_mem_bytes addr sz v tag s) = Some (v, if sz > 0 then tag else B1)"
proof (unfold assms[symmetric], induction v rule: rev_induct)
  case Nil
  then show ?case by (auto simp: get_mem_bytes_def)
next
  case (snoc x xs)
  then show ?case
    by (cases tag)
       (auto simp: get_mem_bytes_def put_mem_bytes_def Let_def and_bit_eq_iff foldl_and_bit_eq_iff
             cong: option.case_cong split: if_splits option.splits)
qed

lemma memstate_put_mem_bytes:
  assumes "length v = sz"
  shows "memstate (put_mem_bytes addr sz v tag s) addr' =
         (if addr' \<in> {addr..<addr+sz} then Some (v ! (addr' - addr)) else memstate s addr')"
  unfolding assms[symmetric]
  by (induction v rule: rev_induct) (auto simp: put_mem_bytes_def nth_Cons nth_append Let_def)

lemma tagstate_put_mem_bytes:
  assumes "length v = sz"
  shows "tagstate (put_mem_bytes addr sz v tag s) addr' =
         (if addr' \<in> {addr..<addr+sz} then Some tag else tagstate s addr')"
  unfolding assms[symmetric]
  by (induction v rule: rev_induct) (auto simp: put_mem_bytes_def nth_Cons nth_append Let_def)

lemma get_mem_bytes_cong:
  assumes "\<forall>addr'. addr \<le> addr' \<and> addr' < addr + sz \<longrightarrow>
                   (memstate s' addr' = memstate s addr' \<and> tagstate s' addr' = tagstate s addr')"
  shows "get_mem_bytes addr sz s' = get_mem_bytes addr sz s"
proof (use assms in \<open>induction sz\<close>)
  case 0
  then show ?case by (auto simp: get_mem_bytes_def)
next
  case (Suc sz)
  then show ?case
    by (auto simp: get_mem_bytes_def Let_def
             intro!: map_option_cong map_cong foldl_cong
                     arg_cong[where f = just_list] arg_cong2[where f = and_bit])
qed

lemma get_mem_bytes_tagged_tagstate:
  assumes "get_mem_bytes addr sz s = Some (v, B1)"
  shows "\<forall>addr' \<in> {addr..<addr + sz}. tagstate s addr' = Some B1"
  using assms
  by (auto simp: get_mem_bytes_def foldl_and_bit_eq_iff Let_def split: option.splits)

end
