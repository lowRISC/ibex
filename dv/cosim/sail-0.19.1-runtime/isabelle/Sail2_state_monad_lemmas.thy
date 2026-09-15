theory Sail2_state_monad_lemmas
  imports
    Sail2_state_monad
    Sail2_values_lemmas
begin

(*context
  notes returnS_def[simp] and failS_def[simp] and throwS_def[simp] and readS_def[simp] and updateS_def[simp]
begin*)

notation bindS (infixr "\<bind>\<^sub>S" 54)
notation seqS (infixr "\<then>\<^sub>S" 54)

lemma bindS_ext_cong[fundef_cong]:
  assumes m: "m1 s = m2 s"
    and f: "\<And>a s'. (Value a, s') \<in> (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 s = bindS m2 f2 s"
  using assms unfolding bindS_def by (auto split: state_result.splits)

lemma bindS_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>s a s'. (Value a, s') \<in> (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 = bindS m2 f2"
  using assms by (intro ext bindS_ext_cong; blast)

lemma bindS_returnS_left[simp]: "bindS (returnS x) f = f x"
  by (auto simp add: bindS_def returnS_def)

lemma bindS_returnS_right[simp]: "bindS m returnS = (m :: ('regs, 'a, 'e) monadS)"
  by (intro ext) (auto simp: bindS_def returnS_def split: state_result.splits)

lemma bindS_readS: "bindS (readS f) m = (\<lambda>s. m (f s) s)"
  by (auto simp: bindS_def readS_def returnS_def)

lemma bindS_updateS: "bindS (updateS f) m = (\<lambda>s. m () (f s))"
  by (auto simp: bindS_def updateS_def returnS_def)

lemma bindS_assertS_True[simp]: "bindS (assert_expS True msg) f = f ()"
  by (auto simp: assert_expS_def)

lemma bindS_chooseS_returnS[simp]: "bindS (chooseS xs) (\<lambda>x. returnS (f x)) = chooseS (f ` xs)"
  by (intro ext) (auto simp: bindS_def chooseS_def returnS_def)

lemma result_cases:
  fixes r :: "('a, 'e) state_result"
  obtains (Value) a where "r = Value a"
  | (Throw) e where "r = Ex (Throw e)"
  | (Failure) msg where "r = Ex (Failure msg)"
proof (cases r)
  case (Ex ex) then show ?thesis by (cases ex; auto intro: that)
qed

lemma result_state_cases:
  fixes rs :: "('a, 'e) state_result \<times> 's"
  obtains (Value) a s where "rs = (Value a, s)"
  | (Throw) e s where "rs = (Ex (Throw e), s)"
  | (Failure) msg s where "rs = (Ex (Failure msg), s)"
proof -
  obtain r s where rs: "rs = (r, s)" by (cases rs)
  then show thesis by (cases r rule: result_cases) (auto intro: that)
qed

lemma monadS_ext_eqI:
  fixes m m' :: "('regs, 'a, 'e) monadS"
  assumes "\<And>a s'. (Value a, s') \<in> m s \<longleftrightarrow> (Value a, s') \<in> m' s"
    and "\<And>e s'. (Ex (Throw e), s') \<in> m s \<longleftrightarrow> (Ex (Throw e), s') \<in> m' s"
    and "\<And>msg s'. (Ex (Failure msg), s') \<in> m s \<longleftrightarrow> (Ex (Failure msg), s') \<in> m' s"
  shows "m s = m' s"
proof (intro set_eqI)
  fix x
  show "x \<in> m s \<longleftrightarrow> x \<in> m' s" using assms by (cases x rule: result_state_cases) auto
qed

lemma monadS_eqI:
  fixes m m' :: "('regs, 'a, 'e) monadS"
  assumes "\<And>s a s'. (Value a, s') \<in> m s \<longleftrightarrow> (Value a, s') \<in> m' s"
    and "\<And>s e s'. (Ex (Throw e), s') \<in> m s \<longleftrightarrow> (Ex (Throw e), s') \<in> m' s"
    and "\<And>s msg s'. (Ex (Failure msg), s') \<in> m s \<longleftrightarrow> (Ex (Failure msg), s') \<in> m' s"
  shows "m = m'"
  using assms by (intro ext monadS_ext_eqI)

lemma bindS_cases:
  assumes "(r, s') \<in> bindS m f s"
  obtains (Value) a a' s'' where "r = Value a" and "(Value a', s'') \<in> m s" and "(Value a, s') \<in> f a' s''"
  | (Ex_Left) e where "r = Ex e" and "(Ex e, s') \<in> m s"
  | (Ex_Right) e a s'' where "r = Ex e" and "(Value a, s'') \<in> m s" and "(Ex e, s') \<in> f a s''"
  using assms by (cases r; auto simp: bindS_def split: state_result.splits)

lemma bindS_intros:
  "\<And>m f s a s' a' s''. (Value a', s'') \<in> m s \<Longrightarrow> (Value a, s') \<in> f a' s'' \<Longrightarrow> (Value a, s') \<in> bindS m f s"
  "\<And>m f s e s'. (Ex e, s') \<in> m s \<Longrightarrow> (Ex e, s') \<in> bindS m f s"
  "\<And>m f s e s' a s''. (Ex e, s') \<in> f a s'' \<Longrightarrow> (Value a, s'') \<in> m s \<Longrightarrow> (Ex e, s') \<in> bindS m f s"
  by (auto simp: bindS_def intro: bexI[rotated])

lemma bindS_assoc[simp]: "bindS (bindS m f) g = bindS m (\<lambda>x. bindS (f x) g)"
  by (auto elim!: bindS_cases intro: bindS_intros monadS_eqI)

lemma bindS_failS[simp]: "bindS (failS msg) f = failS msg" by (auto simp: bindS_def failS_def)
lemma bindS_throwS[simp]: "bindS (throwS e) f = throwS e" by (auto simp: bindS_def throwS_def)
declare seqS_def[simp]

lemma Value_bindS_elim:
  assumes "(Value a, s') \<in> bindS m f s"
  obtains s'' a' where "(Value a', s'') \<in> m s" and "(Value a, s') \<in> f a' s''"
  using assms by (auto elim: bindS_cases)

lemma Ex_bindS_elim:
  assumes "(Ex e, s') \<in> bindS m f s"
  obtains (Left) "(Ex e, s') \<in> m s"
  | (Right) s'' a' where "(Value a', s'') \<in> m s" and "(Ex e, s') \<in> f a' s''"
  using assms by (auto elim: bindS_cases)

lemma try_catchS_returnS[simp]: "try_catchS (returnS a) h = returnS a"
  and try_catchS_failS[simp]: "try_catchS (failS msg) h = failS msg"
  and try_catchS_throwS[simp]: "try_catchS (throwS e) h = h e"
  by (auto simp: try_catchS_def returnS_def failS_def throwS_def)

lemma try_catchS_cong[cong]:
  assumes "\<And>s. m1 s = m2 s" and "\<And>e s. h1 e s = h2 e s"
  shows "try_catchS m1 h1 = try_catchS m2 h2"
  using assms by (intro arg_cong2[where f = try_catchS] ext) auto

lemma try_catchS_cases:
  assumes "(r, s') \<in> try_catchS m h s"
  obtains (Value) a where "r = Value a" and "(Value a, s') \<in> m s"
  | (Fail) msg where "r = Ex (Failure msg)" and "(Ex (Failure msg), s') \<in> m s"
  | (h) e s'' where "(Ex (Throw e), s'') \<in> m s" and "(r, s') \<in> h e s''"
  using assms
  by (cases r rule: result_cases) (auto simp: try_catchS_def returnS_def split: state_result.splits ex.splits)

lemma try_catchS_intros:
  "\<And>m h s a s'. (Value a, s') \<in> m s \<Longrightarrow> (Value a, s') \<in> try_catchS m h s"
  "\<And>m h s msg s'. (Ex (Failure msg), s') \<in> m s \<Longrightarrow> (Ex (Failure msg), s') \<in> try_catchS m h s"
  "\<And>m h s e s'' r s'. (Ex (Throw e), s'') \<in> m s \<Longrightarrow> (r, s') \<in> h e s'' \<Longrightarrow> (r, s') \<in> try_catchS m h s"
  by (auto simp: try_catchS_def returnS_def intro: bexI[rotated])

lemma no_Ex_basic_builtins[simp]:
  "\<And>s e s' a. (Ex e, s') \<in> returnS a s \<longleftrightarrow> False"
  "\<And>s e s' f. (Ex e, s') \<in> readS f s \<longleftrightarrow> False"
  "\<And>s e s' f. (Ex e, s') \<in> updateS f s \<longleftrightarrow> False"
  "\<And>s e s' xs. (Ex e, s') \<in> chooseS xs s \<longleftrightarrow> False"
  by (auto simp: readS_def updateS_def returnS_def chooseS_def)

fun ignore_throw_aux :: "(('a, 'e1) state_result \<times> 's) \<Rightarrow> (('a, 'e2) state_result \<times> 's) set" where
  "ignore_throw_aux (Value a, s') = {(Value a, s')}"
| "ignore_throw_aux (Ex (Throw e), s') = {}"
| "ignore_throw_aux (Ex (Failure msg), s') = {(Ex (Failure msg), s')}"
definition "ignore_throw m s \<equiv> \<Union>(ignore_throw_aux ` m s)"

lemma ignore_throw_cong:
  assumes "\<And>s. m1 s = m2 s"
  shows "ignore_throw m1 = ignore_throw m2"
  using assms by (auto simp: ignore_throw_def)

lemma ignore_throw_aux_member_simps[simp]:
  "(Value a, s') \<in> ignore_throw_aux ms \<longleftrightarrow> ms = (Value a, s')"
  "(Ex (Throw e), s') \<in> ignore_throw_aux ms \<longleftrightarrow> False"
  "(Ex (Failure msg), s') \<in> ignore_throw_aux ms \<longleftrightarrow> ms = (Ex (Failure msg), s')"
  by (cases ms rule: result_state_cases; auto)+

lemma ignore_throw_member_simps[simp]:
  "(Value a, s') \<in> ignore_throw m s \<longleftrightarrow> (Value a, s') \<in> m s"
  "(Value a, s') \<in> ignore_throw m s \<longleftrightarrow> (Value a, s') \<in> m s"
  "(Ex (Throw e), s') \<in> ignore_throw m s \<longleftrightarrow> False"
  "(Ex (Failure msg), s') \<in> ignore_throw m s \<longleftrightarrow> (Ex (Failure msg), s') \<in> m s"
  by (auto simp: ignore_throw_def)

lemma ignore_throw_cases:
  assumes no_throw: "ignore_throw m s = m s"
    and r: "(r, s') \<in> m s"
  obtains (Value) a where "r = Value a"
  | (Failure) msg where "r = Ex (Failure msg)"
  using r unfolding no_throw[symmetric]
  by (cases r rule: result_cases) (auto simp: ignore_throw_def)

lemma ignore_throw_bindS[simp]:
  "ignore_throw (bindS m f) = bindS (ignore_throw m) (ignore_throw \<circ> f)"
  by (intro monadS_eqI) (auto simp: ignore_throw_def elim!: bindS_cases intro: bindS_intros)

lemma try_catchS_bindS_no_throw:
  fixes m1 :: "('r, 'a, 'e1) monadS" and m2 :: "('r, 'a, 'e2) monadS"
  assumes m1: "\<And>s. ignore_throw m1 s = m1 s"
    and m2: "\<And>s. ignore_throw m1 s = m2 s"
  shows "try_catchS (bindS m1 f) h = bindS m2 (\<lambda>a. try_catchS (f a) h)"
proof
  fix s
  have "try_catchS (bindS m1 f) h s = bindS (ignore_throw m1) (\<lambda>a. try_catchS (f a) h) s"
    by (intro monadS_ext_eqI;
        auto elim!: bindS_cases try_catchS_cases elim: ignore_throw_cases[OF m1];
        auto simp: ignore_throw_def intro: bindS_intros try_catchS_intros)
  also have "\<dots> = bindS m2 (\<lambda>a. try_catchS (f a) h) s" using m2 by (intro bindS_ext_cong) auto
  finally show "try_catchS (bindS m1 f) h s = bindS m2 (\<lambda>a. try_catchS (f a) h) s" .
qed

lemma no_throw_basic_builtins[simp]:
  "ignore_throw (returnS a) = returnS a"
  "\<And>f. ignore_throw (readS f) = readS f"
  "\<And>f. ignore_throw (updateS f) = updateS f"
  "ignore_throw (chooseS xs) = chooseS xs"
  "ignore_throw (choose_boolS ()) = choose_boolS ()"
  "ignore_throw (failS msg) = failS msg"
  "ignore_throw (maybe_failS msg x) = maybe_failS msg x"
  unfolding ignore_throw_def returnS_def chooseS_def maybe_failS_def failS_def readS_def updateS_def choose_boolS_def
  by (intro ext; auto split: option.splits)+

lemmas ignore_throw_option_case_distrib =
  option.case_distrib[where h = "\<lambda>c. ignore_throw c s" and option = "c s" for c s]
  option.case_distrib[where h = "\<lambda>c. ignore_throw c" and option = "c" for c]

lemma ignore_throw_let_distrib: "ignore_throw (let x = y in f x) = (let x = y in ignore_throw (f x))"
  by auto

lemma no_throw_mem_builtins:
  "\<And>rk a sz s. ignore_throw (read_mem_bytesS rk a sz) s = read_mem_bytesS rk a sz s"
  "\<And>rk a sz s. ignore_throw (read_memt_bytesS rk a sz) s = read_memt_bytesS rk a sz s"
  "\<And>BC a s. ignore_throw (read_tagS BC a) s = read_tagS BC a s"
  "\<And>BCa BCv rk asz a sz s. ignore_throw (read_memS BCa BCv rk asz a sz) s = read_memS BCa BCv rk asz a sz s"
  "\<And>BCa BCv rk a sz s. ignore_throw (read_memtS BCa BCv rk a sz) s = read_memtS BCa BCv rk a sz s"
  "\<And>BC wk addr sz v s. ignore_throw (write_mem_bytesS wk addr sz v) s = write_mem_bytesS wk addr sz v s"
  "\<And>BC wk addr sz v t s. ignore_throw (write_memt_bytesS wk addr sz v t) s = write_memt_bytesS wk addr sz v t s"
  "\<And>BCa BCv wk asz addr sz v s. ignore_throw (write_memS BCa BCv wk asz addr sz v) s = write_memS BCa BCv wk asz addr sz v s"
  "\<And>BCa BCv wk addr sz v t s. ignore_throw (write_memtS BCa BCv wk addr sz v t) s = write_memtS BCa BCv wk addr sz v t s"
  "\<And>s. ignore_throw (excl_resultS ()) s = excl_resultS () s"
  unfolding read_mem_bytesS_def read_memt_bytesS_def read_memtS_def read_memS_def read_tagS_def
  unfolding write_memS_def write_memtS_def write_mem_bytesS_def write_memt_bytesS_def
  unfolding excl_resultS_def maybe_failS_def
  unfolding ignore_throw_bindS
  by (auto cong: bindS_cong bindS_ext_cong ignore_throw_cong option.case_cong
           simp: prod.case_distrib ignore_throw_option_case_distrib ignore_throw_let_distrib comp_def)

lemma no_throw_read_regvalS: "ignore_throw (read_regvalS r reg_name) s = read_regvalS r reg_name s"
  by (cases r) (auto simp: option.case_distrib cong: bindS_cong option.case_cong)

lemma no_throw_write_regvalS: "ignore_throw (write_regvalS r reg_name v) s = write_regvalS r reg_name v s"
  by (cases r) (auto simp: option.case_distrib cong: bindS_cong option.case_cong)

lemmas no_throw_builtins[simp] =
  no_throw_mem_builtins no_throw_read_regvalS no_throw_write_regvalS

(* end *)

end
