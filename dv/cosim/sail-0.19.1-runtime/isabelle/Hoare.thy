theory Hoare
  imports
    Sail2_state_lemmas
    "HOL-Eisbach.Eisbach_Tools"
begin

(*adhoc_overloading
  Monad_Syntax.bind State_monad.bindS*)

section \<open>Hoare logic for the state, exception and nondeterminism monad\<close>

subsection \<open>Hoare triples\<close>

type_synonym 'regs predS = "'regs sequential_state \<Rightarrow> bool"

definition PrePost :: "'regs predS \<Rightarrow> ('regs, 'a, 'e) monadS \<Rightarrow> (('a, 'e) state_result \<Rightarrow> 'regs predS) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")
  where "PrePost P f Q \<equiv> (\<forall>s. P s \<longrightarrow> (\<forall>(r, s') \<in> f s. Q r s'))"

lemma PrePostI:
  assumes "\<And>s r s'. P s \<Longrightarrow> (r, s') \<in> f s \<Longrightarrow> Q r s'"
  shows "PrePost P f Q"
  using assms unfolding PrePost_def by auto

lemma PrePost_elim:
  assumes "PrePost P f Q" and "P s" and "(r, s') \<in> f s"
  obtains "Q r s'"
  using assms by (fastforce simp: PrePost_def)

lemma PrePost_consequence:
  assumes "PrePost A f B"
    and "\<And>s. P s \<Longrightarrow> A s" and "\<And>v s. B v s \<Longrightarrow> Q v s"
  shows "PrePost P f Q"
  using assms unfolding PrePost_def by (blast intro: list.pred_mono_strong)

lemma PrePost_strengthen_pre:
  assumes "PrePost A f C" and  "\<And>s. B s \<Longrightarrow> A s"
  shows "PrePost B f C"
  using assms by (rule PrePost_consequence)

lemma PrePost_weaken_post:
  assumes "PrePost A f B" and  "\<And>v s. B v s \<Longrightarrow> C v s"
  shows "PrePost A f C"
  using assms by (blast intro: PrePost_consequence)

named_theorems PrePost_compositeI
named_theorems PrePost_atomI

lemma PrePost_True_post[PrePost_atomI, intro, simp]:
  "PrePost P m (\<lambda>_ _. True)"
  unfolding PrePost_def by auto

lemma PrePost_any: "PrePost (\<lambda>s. \<forall>(r, s') \<in> m s. Q r s') m Q"
  unfolding PrePost_def by auto

lemma PrePost_returnS[intro, PrePost_atomI]: "PrePost (P (Value x)) (returnS x) P"
  unfolding PrePost_def returnS_def by auto

lemma PrePost_bindS[intro, PrePost_compositeI]:
  assumes f: "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> PrePost (R a) (f a) Q"
    and m: "PrePost P m (\<lambda>r. case r of Value a \<Rightarrow> R a | Ex e \<Rightarrow> Q (Ex e))"
  shows "PrePost P (bindS m f) Q"
proof (intro PrePostI)
  fix s r s'
  assume P: "P s" and bind: "(r, s') \<in> bindS m f s"
  from bind show "Q r s'"
  proof (cases r s' m f s rule: bindS_cases)
    case (Value a a' s'')
    then have "R a' s''" using P m by (auto elim: PrePost_elim)
    then show ?thesis using Value f by (auto elim: PrePost_elim)
  next
    case (Ex_Left e)
    then show ?thesis using P m by (auto elim: PrePost_elim)
  next
    case (Ex_Right e a s'')
    then have "R a s''" using P m by (auto elim: PrePost_elim)
    then show ?thesis using Ex_Right f by (auto elim: PrePost_elim)
  qed
qed

lemma PrePost_bindS_ignore:
  assumes f: "PrePost R f Q"
    and m : "PrePost P m (\<lambda>r. case r of Value a \<Rightarrow> R | Ex e \<Rightarrow> Q (Ex e))"
  shows "PrePost P (bindS m (\<lambda>_. f)) Q"
  using assms by auto

lemma PrePost_bindS_unit:
  fixes m :: "('regs, unit, 'e) monadS"
  assumes f: "PrePost R (f ()) Q"
    and m: "PrePost P m (\<lambda>r. case r of Value a \<Rightarrow> R | Ex e \<Rightarrow> Q (Ex e))"
  shows "PrePost P (bindS m f) Q"
  using assms by auto

lemma PrePost_readS[intro, PrePost_atomI]: "PrePost (\<lambda>s. P (Value (f s)) s) (readS f) P"
  unfolding PrePost_def readS_def returnS_def by auto

lemma PrePost_updateS[intro, PrePost_atomI]: "PrePost (\<lambda>s. P (Value ()) (f s)) (updateS f) P"
  unfolding PrePost_def updateS_def returnS_def by auto

lemma PrePost_read_regS[intro, PrePost_atomI]:
  "PrePost (\<lambda>s. P (Value (read_from reg (regstate s))) s) (read_regS reg) P"
  unfolding read_regS_def by (rule PrePost_readS)

lemma PrePost_write_regS[intro, PrePost_atomI]:
  "PrePost (\<lambda>s. P (Value ()) (s\<lparr>regstate := write_to reg v (regstate s)\<rparr>)) (write_regS reg v) P"
  unfolding write_regS_def by (rule PrePost_updateS)

lemma PrePost_if:
  assumes "b \<Longrightarrow> PrePost P f Q" and "\<not>b \<Longrightarrow> PrePost P g Q"
  shows "PrePost P (if b then f else g) Q"
  using assms by auto

lemma PrePost_if_branch[PrePost_compositeI]:
  assumes "b \<Longrightarrow> PrePost Pf f Q" and "\<not>b \<Longrightarrow> PrePost Pg g Q"
  shows "PrePost (if b then Pf else Pg) (if b then f else g) Q"
  using assms by auto

lemma PrePost_if_then:
  assumes "b" and "PrePost P f Q"
  shows "PrePost P (if b then f else g) Q"
  using assms by auto

lemma PrePost_if_else:
  assumes "\<not>b" and "PrePost P g Q"
  shows "PrePost P (if b then f else g) Q"
  using assms by auto

lemma PrePost_prod_cases[PrePost_compositeI]:
  assumes "PrePost P (f (fst x) (snd x)) Q"
  shows "PrePost P (case x of (a, b) \<Rightarrow> f a b) Q"
  using assms by (auto split: prod.splits)

lemma PrePost_option_cases[PrePost_compositeI]:
  assumes "\<And>a. PrePost (PS a) (s a) Q" and "PrePost PN n Q"
  shows "PrePost (case x of Some a \<Rightarrow> PS a | None \<Rightarrow> PN) (case x of Some a \<Rightarrow> s a | None \<Rightarrow> n) Q"
  using assms by (auto split: option.splits)

lemma PrePost_let[intro, PrePost_compositeI]:
  assumes "PrePost P (m y) Q"
  shows "PrePost P (let x = y in m x) Q"
  using assms by auto

lemma PrePost_and_boolS[PrePost_compositeI]:
  assumes r: "PrePost R r Q"
    and l: "PrePost P l (\<lambda>r. case r of Value True \<Rightarrow> R | _ \<Rightarrow> Q r)"
  shows "PrePost P (and_boolS l r) Q"
  unfolding and_boolS_def
proof (rule PrePost_bindS)
  fix s a s'
  assume "(Value a, s') \<in> l s"
  show "PrePost (if a then R else Q (Value False)) (if a then r else returnS False) Q"
    using r by auto
next
  show "PrePost P l (\<lambda>r. case r of Value a \<Rightarrow> if a then R else Q (Value False) | Ex e \<Rightarrow> Q (Ex e))"
    using l by (elim PrePost_weaken_post) (auto split: state_result.splits)
qed

lemma PrePost_or_boolS[PrePost_compositeI]:
  assumes r: "PrePost R r Q"
    and l: "PrePost P l (\<lambda>r. case r of Value False \<Rightarrow> R | _ \<Rightarrow> Q r)"
  shows "PrePost P (or_boolS l r) Q"
  unfolding or_boolS_def
proof (rule PrePost_bindS)
  fix s a s'
  assume "(Value a, s') \<in> l s"
  show "PrePost (if a then Q (Value True) else R) (if a then returnS True else r) Q"
    using r by auto
next
  show "PrePost P l (\<lambda>r. case r of Value a \<Rightarrow> if a then Q (Value True) else R | Ex e \<Rightarrow> Q (Ex e))"
    using l by (elim PrePost_weaken_post) (auto split: state_result.splits)
qed

lemma PrePost_assert_expS[intro, PrePost_atomI]: "PrePost (if c then P (Value ()) else P (Ex (Failure m))) (assert_expS c m) P"
  unfolding PrePost_def assert_expS_def by (auto simp: returnS_def failS_def)

lemma PrePost_chooseS[intro, PrePost_atomI]: "PrePost (\<lambda>s. \<forall>x \<in> xs. Q (Value x) s) (chooseS xs) Q"
  by (auto simp: PrePost_def chooseS_def)

lemma PrePost_failS[intro, PrePost_atomI]: "PrePost (Q (Ex (Failure msg))) (failS msg) Q"
  by (auto simp: PrePost_def failS_def)

lemma case_result_combine[simp]:
  "(case r of Value a \<Rightarrow> Q (Value a) | Ex e \<Rightarrow> Q (Ex e)) = Q r"
  by (auto split: state_result.splits)

lemma PrePost_foreachS_Nil[intro, simp, PrePost_atomI]:
  "PrePost (Q (Value vars)) (foreachS [] vars body) Q"
  by auto

lemma PrePost_foreachS_Cons:
  assumes "\<And>s vars' s'. (Value vars', s') \<in> body x vars s \<Longrightarrow> PrePost (Q (Value vars')) (foreachS xs vars' body) Q"
    and "PrePost (Q (Value vars)) (body x vars) Q"
  shows "PrePost (Q (Value vars)) (foreachS (x # xs) vars body) Q"
  using assms by fastforce

lemma PrePost_foreachS_invariant:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> PrePost (Q (Value vars)) (body x vars) Q"
  shows "PrePost (Q (Value vars)) (foreachS xs vars body) Q"
proof (use assms in \<open>induction xs arbitrary: vars\<close>)
  case (Cons x xs)
  have "PrePost (Q (Value vars)) (bindS (body x vars) (\<lambda>vars. foreachS xs vars body)) Q"
  proof (rule PrePost_bindS)
    fix vars'
    show "PrePost (Q (Value vars')) (foreachS xs vars' body) Q"
      using Cons by auto
    show "PrePost (Q (Value vars)) (body x vars) (\<lambda>r. case r of Value a \<Rightarrow> Q (Value a) | state_result.Ex e \<Rightarrow> Q (state_result.Ex e))"
      unfolding case_result_combine
      using Cons by auto
  qed
  then show ?case by auto
qed auto

subsection \<open>Hoare quadruples\<close>

text \<open>It is often convenient to treat the exception case separately.  For this purpose, we use
a Hoare logic similar to the one used in [1]. It features not only Hoare triples, but also quadruples
with two postconditions: one for the case where the computation succeeds, and one for the case where
there is an exception.

[1] D. Cock, G. Klein, and T. Sewell, ‘Secure Microkernels, State Monads and Scalable Refinement’,
in Theorem Proving in Higher Order Logics, 2008, pp. 167–182.\<close>

definition PrePostE :: "'regs predS \<Rightarrow> ('regs, 'a, 'e) monadS \<Rightarrow> ('a \<Rightarrow> 'regs predS) \<Rightarrow> ('e ex \<Rightarrow> 'regs predS) \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_ \<bar> _\<rbrace>")
  where "PrePostE P f Q E \<equiv> PrePost P f (\<lambda>v. case v of Value a \<Rightarrow> Q a | Ex e \<Rightarrow> E e)"

lemmas PrePost_defs = PrePost_def PrePostE_def

lemma PrePostE_I[case_names Val Err]:
  assumes "\<And>s a s'. P s \<Longrightarrow> (Value a, s') \<in> f s \<Longrightarrow> Q a s'"
    and "\<And>s e s'. P s \<Longrightarrow> (Ex e, s') \<in> f s \<Longrightarrow> E e s'"
  shows "PrePostE P f Q E"
  using assms unfolding PrePostE_def by (intro PrePostI) (auto split: state_result.splits)

lemma PrePostE_PrePost:
  assumes "PrePost P m (\<lambda>v. case v of Value a \<Rightarrow> Q a | Ex e \<Rightarrow> E e)"
  shows "PrePostE P m Q E"
  using assms unfolding PrePostE_def by auto

lemma PrePostE_elim:
  assumes "PrePostE P f Q E" and "P s" and "(r, s') \<in> f s"
  obtains
    (Val) v where "r = Value v" "Q v s'"
  | (Ex) e where "r = Ex e" "E e s'"
  using assms by (cases r; fastforce simp: PrePost_defs)

lemma PrePostE_consequence:
  assumes "PrePostE A f B C"
    and "\<And>s. P s \<Longrightarrow> A s" and "\<And>v s. B v s \<Longrightarrow> Q v s" and "\<And>e s. C e s \<Longrightarrow> E e s"
  shows "PrePostE P f Q E"
  using assms unfolding PrePostE_def by (auto elim: PrePost_consequence split: state_result.splits)

lemma PrePostE_strengthen_pre:
  assumes "PrePostE R f Q E" and "\<And>s. P s \<Longrightarrow> R s"
  shows "PrePostE P f Q E"
  using assms PrePostE_consequence by blast

lemma PrePostE_weaken_post:
  assumes "PrePostE A f B E" and  "\<And>v s. B v s \<Longrightarrow> C v s"
  shows "PrePostE A f C E"
  using assms by (blast intro: PrePostE_consequence)

named_theorems PrePostE_compositeI
named_theorems PrePostE_atomI

lemma PrePostE_conj_conds:
  assumes "PrePostE P1 m Q1 E1"
    and "PrePostE P2 m Q2 E2"
  shows "PrePostE (\<lambda>s. P1 s \<and> P2 s) m (\<lambda>r s. Q1 r s \<and> Q2 r s) (\<lambda>e s. E1 e s \<and> E2 e s)"
  using assms by (auto intro: PrePostE_I elim: PrePostE_elim)

lemmas PrePostE_conj_conds_consequence = PrePostE_conj_conds[THEN PrePostE_consequence]

lemma PrePostE_post_mp:
  assumes "PrePostE P m Q' E"
    and "PrePostE P m (\<lambda>r s. Q' r s \<longrightarrow> Q r s) E"
  shows "PrePostE P m Q E"
  using PrePostE_conj_conds[OF assms] by (auto intro: PrePostE_weaken_post)

lemma PrePostE_cong:
  assumes "\<And>s. P1 s \<longleftrightarrow> P2 s" and "\<And>s. P1 s \<Longrightarrow> m1 s = m2 s" and "\<And>r s. Q1 r s \<longleftrightarrow> Q2 r s"
    and "\<And>e s. E1 e s \<longleftrightarrow> E2 e s"
  shows "PrePostE P1 m1 Q1 E1 \<longleftrightarrow> PrePostE P2 m2 Q2 E2"
  using assms unfolding PrePostE_def PrePost_def
  by (auto split: state_result.splits)

lemma PrePostE_True_post[PrePostE_atomI, intro, simp]:
  "PrePostE P m (\<lambda>_ _. True) (\<lambda>_ _. True)"
  unfolding PrePost_defs by (auto split: state_result.splits)

lemma PrePostE_any: "PrePostE (\<lambda>s. \<forall>(r, s') \<in> m s. case r of Value a \<Rightarrow> Q a s' | Ex e \<Rightarrow> E e s') m Q E"
  by (intro PrePostE_I) auto

lemma PrePostE_returnS[PrePostE_atomI, intro, simp]:
  "PrePostE (P x) (returnS x) P Q"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_bindS[intro, PrePostE_compositeI]:
  assumes f: "\<And>s a s'. (Value a, s') \<in> m s \<Longrightarrow> PrePostE (R a) (f a) Q E"
    and m: "PrePostE P m R E"
  shows "PrePostE P (bindS m f) Q E"
  using assms
  by (fastforce simp: PrePostE_def cong: state_result.case_cong)

lemma PrePostE_bindS_ignore:
  assumes f: "PrePostE R f Q E"
    and m : "PrePostE  P m (\<lambda>_. R) E"
  shows "PrePostE P (bindS m (\<lambda>_. f)) Q E"
  using assms by auto

lemma PrePostE_bindS_unit:
  fixes m :: "('regs, unit, 'e) monadS"
  assumes f: "PrePostE R (f ()) Q E"
    and m: "PrePostE P m (\<lambda>_. R) E"
  shows "PrePostE P (bindS m f) Q E"
  using assms by auto

lemma PrePostE_readS[PrePostE_atomI, intro]: "PrePostE (\<lambda>s. Q (f s) s) (readS f) Q E"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_updateS[PrePostE_atomI, intro]: "PrePostE (\<lambda>s. Q () (f s)) (updateS f) Q E"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_read_regS[PrePostE_atomI, intro]:
  "PrePostE (\<lambda>s. Q (read_from reg (regstate s)) s) (read_regS reg) Q E"
  unfolding read_regS_def by (rule PrePostE_readS)

lemma PrePostE_write_regS[PrePostE_atomI, intro]:
  "PrePostE (\<lambda>s. Q () (s\<lparr>regstate := write_to reg v (regstate s)\<rparr>)) (write_regS reg v) Q E"
  unfolding write_regS_def by (rule PrePostE_updateS)

lemma PrePostE_if_branch[PrePostE_compositeI]:
  assumes "b \<Longrightarrow> PrePostE Pf f Q E" and "\<not>b \<Longrightarrow> PrePostE Pg g Q E"
  shows "PrePostE (if b then Pf else Pg) (if b then f else g) Q E"
  using assms by (auto)

lemma PrePostE_if:
  assumes "b \<Longrightarrow> PrePostE P f Q E" and "\<not>b \<Longrightarrow> PrePostE P g Q E"
  shows "PrePostE P (if b then f else g) Q E"
  using assms by auto

lemma PrePostE_if_then:
  assumes "b" and "PrePostE P f Q E"
  shows "PrePostE P (if b then f else g) Q E"
  using assms by auto

lemma PrePostE_if_else:
  assumes "\<not> b" and "PrePostE P g Q E"
  shows "PrePostE P (if b then f else g) Q E"
  using assms by auto

lemma PrePostE_prod_cases[PrePostE_compositeI]:
  assumes "PrePostE P (f (fst x) (snd x)) Q E"
  shows "PrePostE P (case x of (a, b) \<Rightarrow> f a b) Q E"
  using assms by (auto split: prod.splits)

lemma PrePostE_option_cases[PrePostE_compositeI]:
  assumes "\<And>a. PrePostE (PS a) (s a) Q E" and "PrePostE PN n Q E"
  shows "PrePostE (case x of Some a \<Rightarrow> PS a | None \<Rightarrow> PN) (case x of Some a \<Rightarrow> s a | None \<Rightarrow> n) Q E"
  using assms by (auto split: option.splits)

lemma PrePostE_sum_cases[PrePostE_compositeI]:
  assumes "\<And>a. PrePostE (Pl a) (l a) Q E" and "\<And>b. PrePostE (Pr b) (r b) Q E"
  shows "PrePostE (case x of Inl a \<Rightarrow> Pl a | Inr b \<Rightarrow> Pr b) (case x of Inl a \<Rightarrow> l a | Inr b \<Rightarrow> r b) Q E"
  using assms by (auto split: sum.splits)

lemma PrePostE_let[PrePostE_compositeI]:
  assumes "PrePostE P (m y) Q E"
  shows "PrePostE P (let x = y in m x) Q E"
  using assms by auto

lemma PrePostE_and_boolS[PrePostE_compositeI]:
  assumes r: "PrePostE R r Q E"
    and l: "PrePostE P l (\<lambda>r. if r then R else Q False) E"
  shows "PrePostE P (and_boolS l r) Q E"
  using assms unfolding PrePostE_def
  by (intro PrePost_and_boolS) (auto elim: PrePost_weaken_post split: if_splits state_result.splits)

lemma PrePostE_or_boolS[PrePostE_compositeI]:
  assumes r: "PrePostE R r Q E"
    and l: "PrePostE P l (\<lambda>r. if r then Q True else R) E"
  shows "PrePostE P (or_boolS l r) Q E"
  using assms unfolding PrePostE_def
  by (intro PrePost_or_boolS) (auto elim: PrePost_weaken_post split: if_splits state_result.splits)

lemma PrePostE_assert_expS[PrePostE_atomI, intro]:
  "PrePostE (if c then P () else Q (Failure m)) (assert_expS c m) P Q"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_failS[PrePostE_atomI, intro]:
  "PrePostE (E (Failure msg)) (failS msg) Q E"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_maybe_failS[PrePostE_atomI]:
  "PrePostE (\<lambda>s. case v of Some v \<Rightarrow> Q v s | None \<Rightarrow> E (Failure msg) s) (maybe_failS msg v) Q E"
  by (auto simp: maybe_failS_def split: option.splits)

lemma PrePostE_exitS[PrePostE_atomI, intro]: "PrePostE (E (Failure ''exit'')) (exitS msg) Q E"
  unfolding exitS_def PrePostE_def PrePost_def failS_def by auto

lemma PrePostE_chooseS[intro, PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>x \<in> xs. Q x s) (chooseS xs) Q E"
  unfolding PrePostE_def by (auto intro: PrePost_strengthen_pre)

lemma PrePostE_throwS[PrePostE_atomI]: "PrePostE (E (Throw e)) (throwS e) Q E"
  by (intro PrePostE_I) (auto simp: throwS_def)

lemma PrePostE_try_catchS[PrePostE_compositeI]:
  assumes Ph: "\<And>s e s'. (Ex (Throw e), s') \<in> m s \<Longrightarrow> PrePostE (Ph e) (h e) Q E"
    and m: "PrePostE P m Q (\<lambda>ex. case ex of Throw e \<Rightarrow> Ph e | Failure msg \<Rightarrow> E (Failure msg))"
  shows "PrePostE P (try_catchS m h) Q E"
  unfolding PrePostE_def
proof (intro PrePostI)
  fix s r s'
  assume "(r, s') \<in> try_catchS m h s" and P: "P s"
  then show "(case r of Value a \<Rightarrow> Q a | state_result.Ex e \<Rightarrow> E e) s'" using m
  proof (cases rule: try_catchS_cases)
    case (h e s'')
    then have "Ph e s''" using P m by (auto elim!: PrePostE_elim)
    then show ?thesis using Ph[OF h(1)] h(2) by (auto elim!: PrePostE_elim)
  qed (auto elim!: PrePostE_elim)
qed

lemma PrePostE_catch_early_returnS[PrePostE_compositeI]:
  assumes "PrePostE P m Q (\<lambda>ex. case ex of Throw (Inl a) \<Rightarrow> Q a | Throw (Inr e) \<Rightarrow> E (Throw e) | Failure msg \<Rightarrow> E (Failure msg))"
  shows "PrePostE P (catch_early_returnS m) Q E"
  unfolding catch_early_returnS_def
  by (rule PrePostE_try_catchS, rule PrePostE_sum_cases[OF PrePostE_returnS PrePostE_throwS])
     (auto intro: assms)

lemma PrePostE_early_returnS[PrePostE_atomI]: "PrePostE (E (Throw (Inl r))) (early_returnS r) Q E"
  by (auto simp: early_returnS_def intro: PrePostE_throwS)

lemma PrePostE_liftRS[PrePostE_compositeI]:
  assumes "PrePostE P m Q (\<lambda>ex. case ex of Throw e \<Rightarrow> E (Throw (Inr e)) | Failure msg \<Rightarrow> E (Failure msg))"
  shows "PrePostE P (liftRS m) Q E"
  using assms unfolding liftRS_def by (intro PrePostE_try_catchS[OF PrePostE_throwS])

lemma PrePostE_foreachS_Cons:
  assumes "\<And>s vars' s'. (Value vars', s') \<in> body x vars s \<Longrightarrow> PrePostE (Q vars') (foreachS xs vars' body) Q E"
    and "PrePostE (Q vars) (body x vars) Q E"
  shows "PrePostE (Q vars) (foreachS (x # xs) vars body) Q E"
  using assms by fastforce

lemma PrePostE_foreachS_invariant:
  assumes "\<And>x vars. x \<in> set xs \<Longrightarrow> PrePostE (Q vars) (body x vars) Q E"
  shows "PrePostE (Q vars) (foreachS xs vars body) Q E"
  using assms unfolding PrePostE_def
  by (intro PrePost_foreachS_invariant[THEN PrePost_strengthen_pre]) auto

lemma PrePostE_untilS:
  assumes dom: "\<And>s. Inv Q vars s \<Longrightarrow> untilS_dom (vars, cond, body, s)"
    and cond: "\<And>vars. PrePostE (Inv' Q vars) (cond vars) (\<lambda>c s'. Inv Q vars s' \<and> (c \<longrightarrow> Q vars s')) E"
    and body: "\<And>vars. PrePostE (Inv Q vars) (body vars) (Inv' Q) E"
  shows "PrePostE (Inv Q vars) (untilS vars cond body) Q E"
proof (unfold PrePostE_def, rule PrePostI)
  fix s r s'
  assume Inv_s: "Inv Q vars s" and r: "(r, s') \<in> untilS vars cond body s"
  with dom[OF Inv_s] cond body
  show "(case r of Value a \<Rightarrow> Q a | state_result.Ex e \<Rightarrow> E e) s'"
  proof (induction vars cond body s rule: untilS.pinduct[case_names Step])
    case (Step vars cond body s)
    consider
        (Value) vars' c sb sc where "(Value vars', sb) \<in> body vars s" and "(Value c, sc) \<in> cond vars' sb"
                                and "if c then r = Value vars' \<and> s' = sc else (r, s') \<in> untilS vars' cond body sc"
      | (Ex) e where "(Ex e, s') \<in> bindS (body vars) cond s" and "r = Ex e"
      using Step(1,6)
      by (auto simp: untilS.psimps returnS_def Ex_bindS_iff elim!: bindS_cases split: if_splits; fastforce)
    then show ?case
    proof cases
      case Value
      then show ?thesis using Step.IH[OF Value(1,2) _ Step(3,4)] Step(3,4,5)
        by (auto split: if_splits elim: PrePostE_elim)
    next
      case Ex
      then show ?thesis using Step(3,4,5) by (auto elim!: bindS_cases PrePostE_elim)
    qed
  qed
qed

lemma PrePostE_untilS_pure_cond:
  assumes dom: "\<And>s. Inv Q vars s \<Longrightarrow> untilS_dom (vars, returnS \<circ> cond, body, s)"
    and body: "\<And>vars. PrePostE (Inv Q vars) (body vars) (\<lambda>vars' s'. Inv Q vars' s' \<and> (cond vars' \<longrightarrow> Q vars' s')) E"
  shows "PrePostE (Inv Q vars) (untilS vars (returnS \<circ> cond) body) Q E"
  using assms by (intro PrePostE_untilS) (auto simp: comp_def)

lemma PrePostE_liftState_untilM:
  assumes dom: "\<And>s. Inv Q vars s \<Longrightarrow> untilM_dom (vars, cond, body)"
    and cond: "\<And>vars. PrePostE (Inv' Q vars) (liftState r (cond vars)) (\<lambda>c s'. Inv Q vars s' \<and> (c \<longrightarrow> Q vars s')) E"
    and body: "\<And>vars. PrePostE (Inv Q vars) (liftState r (body vars)) (Inv' Q) E"
  shows "PrePostE (Inv Q vars) (liftState r (untilM vars cond body)) Q E"
proof -
  have domS: "untilS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)" if "Inv Q vars s" for s
    using dom that by (intro untilM_dom_untilS_dom)
  then have "PrePostE (Inv Q vars) (untilS vars (liftState r \<circ> cond) (liftState r \<circ> body)) Q E"
    using cond body by (auto intro: PrePostE_untilS simp: comp_def)
  moreover have "liftState r (untilM vars cond body) s = untilS vars (liftState r \<circ> cond) (liftState r \<circ> body) s"
    if "Inv Q vars s" for s
    unfolding liftState_untilM[OF domS[OF that] dom[OF that]] ..
  ultimately show ?thesis by (auto cong: PrePostE_cong)
qed

lemma PrePostE_liftState_untilM_pure_cond:
  assumes dom: "\<And>s. Inv Q vars s \<Longrightarrow> untilM_dom (vars, return \<circ> cond, body)"
    and body: "\<And>vars. PrePostE (Inv Q vars) (liftState r (body vars)) (\<lambda>vars' s'. Inv Q vars' s' \<and> (cond vars' \<longrightarrow> Q vars' s')) E"
  shows "PrePostE (Inv Q vars) (liftState r (untilM vars (return \<circ> cond) body)) Q E"
  using assms by (intro PrePostE_liftState_untilM) (auto simp: comp_def liftState_simp)

lemma PrePostE_choose_boolS_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>b. Q b s)
            (choose_boolS unit) Q E"
  unfolding choose_boolS_def seqS_def
  by (auto intro: PrePostE_strengthen_pre)

lemma PrePostE_bool_of_bitU_nondetS_any:
  "PrePostE (\<lambda>s. \<forall>b. Q b s) (bool_of_bitU_nondetS b) Q E"
  unfolding bool_of_bitU_nondetS_def choose_boolS_def
  by (cases b; simp; rule PrePostE_strengthen_pre, rule PrePostE_atomI) auto

lemma PrePostE_bools_of_bits_nondetS_any:
  "PrePostE (\<lambda>s. \<forall>bs. Q bs s) (bools_of_bits_nondetS bs) Q E"
  unfolding bools_of_bits_nondetS_def
  by (rule PrePostE_weaken_post[where B = "\<lambda>_ s. \<forall>bs. Q bs s"], rule PrePostE_strengthen_pre,
      (rule PrePostE_foreachS_invariant[OF PrePostE_strengthen_pre] PrePostE_bindS PrePostE_returnS
            PrePostE_bool_of_bitU_nondetS_any)+)
     auto

lemma PrePostE_choose_boolsS_any:
  "PrePostE (\<lambda>s. \<forall>bs. Q bs s) (choose_boolsS n) Q E"
  unfolding choose_boolsS_def genlistS_def Let_def
  by (rule PrePostE_weaken_post[where B = "\<lambda>_ s. \<forall>bs. Q bs s"], rule PrePostE_strengthen_pre,
      (rule PrePostE_foreachS_invariant[OF PrePostE_strengthen_pre] PrePostE_bindS PrePostE_returnS
            PrePostE_choose_boolS_any)+)
     auto

end
