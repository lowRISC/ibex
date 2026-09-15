theory Add_Cancel_Distinct

imports
  "HOL-Library.Multiset"

begin

text \<open>
Cancelling of terms in an equality of additions, which can be applied
to multisets to prove lists are permutations of each other, and in
particular can be used to prove distinctness of lists by sorting them.
\<close>

locale add_cancel_many_helpers begin

lemma cancel_some_shape:
  fixes x :: "'a :: cancel_semigroup_add"
  shows "(x \<equiv> x_same + x_rest) \<Longrightarrow> (y \<equiv> y_same + y_rest) \<Longrightarrow>
    x_same = y_same \<Longrightarrow> (x = y) = (x_rest = y_rest)"
  by simp

lemma eq_split_rules:
  fixes x :: "'a :: {cancel_semigroup_add, ab_semigroup_add}"
  shows
  "((x + a) = ((x + b) + c)) = (a = b + c)"
  "((x + a) = (b + (x + c))) = (a = b + c)"
  by (simp_all add: add.assoc add.left_commute[where a=x and b=b])

end

ML \<open>

structure Add_Cancel_Many = struct

fun dest_sum ct = let
    val t = Thm.term_of ct
    val _ = HOLogic.dest_bin \<^const_name>\<open>Groups.plus\<close> dummyT t
    val (x, y) = Thm.dest_binop ct
  in x :: dest_sum y end handle TERM _ => [ct]

fun dest_sum_tree [] = []
  | dest_sum_tree (ct :: cts) = case dest_sum ct of
    [x] => x :: dest_sum_tree cts
  | xs => dest_sum_tree (xs @ cts)

fun dest_sum_tree_reassoc ct = let
    val xs = dest_sum_tree [ct]
    val ys = dest_sum ct
  in (length xs <> length ys, xs) end

fun mk_sum _ [ct] = ct
  | mk_sum _ [] = raise TERM ("mk_sum", [])
  | mk_sum plus (x :: y :: zs) = Thm.mk_binop plus x (mk_sum plus (y :: zs))

fun simp_only ctxt thms = simp_tac ((put_simpset HOL_basic_ss ctxt) addsimps thms)

fun mk_meta_eq ctxt x y = let
    val eq = Logic.mk_equals (Thm.term_of x, Thm.term_of y)
    val ct = head_of eq |> Thm.cterm_of ctxt
  in Thm.mk_binop ct x y end

(* tag which elements of a summation will be selected, using a fresh
    free variable, to avoid confusion involving identical elements. *)
fun tag_sum_conv ctxt select_elems x ct = let
    val ys = dest_sum_tree [ct]
    val plus = Thm.dest_fun2 ct
    val t_of = Thm.term_of
    val sel_tab = Termtab.make_list
        (map (fn ct => (t_of ct, ())) select_elems)
    val ty = fastype_of (t_of ct)
    val tag1 = HOLogic.pair_const (fastype_of x) ty $ x |> Thm.cterm_of ctxt
    val tag2 = HOLogic.mk_snd (HOLogic.mk_prod (x, t_of ct))
        |> head_of |> Thm.cterm_of ctxt
    val tag = Thm.apply tag1 #> Thm.apply tag2
    fun f _ [] = []
      | f tab (y :: ys) = (case Termtab.lookup tab (t_of y) of
            SOME (_ :: zs) => tag y :: f (Termtab.update (t_of y, zs) tab) ys
          | _ => y :: f tab ys)
    val rhs = f sel_tab ys |> mk_sum plus
    val eq = mk_meta_eq ctxt ct rhs
  in Goal.prove_internal ctxt [] eq
    (fn _ => simp_only ctxt @{thms add.assoc snd_conv} 1)
  end

fun prove_eq_split_tac ctxt =
    simp_only ctxt @{thms add_cancel_many_helpers.eq_split_rules}
        THEN_ALL_NEW simp_only ctxt @{thms refl add.commute}

fun prove_eq_split ctxt ct = Goal.prove_internal ctxt [] ct
    (fn _ => prove_eq_split_tac ctxt 1)

fun has_var v (f $ x) = has_var v f orelse has_var v x
  | has_var v (Abs (_, _, t)) = has_var v t
  | has_var v t = (t = v)

fun split_by_var_conv ctxt v ct = let
    val xs = dest_sum ct
    val choose_xs = filter (has_var v o Thm.term_of) xs
    val other_xs = filter_out (has_var v o Thm.term_of) xs
    val plus = Thm.dest_fun2 ct
    val rhs = Thm.mk_binop plus (mk_sum plus choose_xs) (mk_sum plus other_xs)
    val prop = mk_meta_eq ctxt ct rhs
  in Goal.prove_internal ctxt [] prop
    (fn _ => resolve_tac ctxt @{thms eq_reflection} 1
        THEN prove_eq_split_tac ctxt 1)
  end

fun cancel_step ctxt ct = let
    val t = Thm.term_of ct
    val _ = HOLogic.dest_eq t
    val (lhs, rhs) = Thm.dest_binop ct
    val lhs_bits = dest_sum_tree [lhs]
    val rhs_bits = dest_sum_tree [rhs]
    val lhs_sort = sort Thm.fast_term_ord lhs_bits
    val rhs_sort = sort Thm.fast_term_ord rhs_bits
    val choose = if list_ord Thm.fast_term_ord (lhs_sort, rhs_sort) = EQUAL
      then take (length lhs_sort div 2) lhs_sort
      else Ord_List.inter Thm.fast_term_ord lhs_sort rhs_sort
    val choose2 = if length choose < Int.min (length lhs_sort, length rhs_sort)
      then choose else List.tl choose
    val _ = List.hd choose2 (* raise Empty if no progress can be made *)
    val x = Variable.variant_frees ctxt [t] [("x", @{typ unit})]
        |> the_single |> Free
    val conv = tag_sum_conv ctxt choose2 x then_conv split_by_var_conv ctxt x
    val lhs_split = conv lhs
    val rhs_split = conv rhs
  in
    ([lhs_split, rhs_split]
        MRS @{thm add_cancel_many_helpers.cancel_some_shape})
    RS @{thm eq_reflection}
  end

fun cancel ctxt ct = let
    val thm1 = cancel_step ctxt ct
    fun prove_asm ct = Goal.prove_internal ctxt [] ct
      (fn _ => (simp_only ctxt @{thms refl add_left_cancel}
        THEN_ALL_NEW CONVERSION (Conv.arg_conv (cancel ctxt))
        THEN_ALL_NEW (simp_only ctxt @{thms refl})) 1)
    val prems = Thm.cprems_of thm1 |> map prove_asm
    val step1 = prems MRS thm1
  in ((fn _ => step1) then_conv cancel ctxt) ct
    handle Empty => step1
  end

end
\<close>

lemma distinct_mset:
  "distinct xs = (\<forall>x. count (mset xs) x \<le> 1)"
  apply (induct xs, simp_all add: all_conj_distrib)
  apply (metis count_mset_0_iff le_SucI order_refl)
  done

lemma distinct_mset_eq:
  "distinct xs \<Longrightarrow> mset xs = mset ys \<Longrightarrow> distinct ys"
  by (simp add: distinct_mset)

lemma mset_to_plus:
  "mset (x # y # zs) = mset [x] + mset (y # zs)"
  by simp

lemma distinct_sorted_wrt:
  "distinct xs = sorted_wrt (\<noteq>) xs"
  by (induct xs, auto)

lemma distinct_via_sorted:
  "irreflp R \<Longrightarrow> sorted_wrt R xs \<Longrightarrow> distinct xs"
  by (clarsimp simp: distinct_sorted_wrt irreflp_def
    elim!: sorted_wrt_mono_rel[rotated])

ML \<open>
structure Distinct_Tac = struct

val thm = @{thm distinct_via_sorted[THEN distinct_mset_eq]}

val simp_only = Add_Cancel_Many.simp_only

fun mset_eq_tac ctxt = simp_only ctxt @{thms mset_to_plus}
    THEN_ALL_NEW CONVERSION (Conv.arg_conv (Add_Cancel_Many.cancel ctxt))
    THEN_ALL_NEW simp_only ctxt @{thms refl}

fun solve nm tac = (tac THEN_ALL_NEW SUBGOAL
        (fn (t, _) => raise TERM (nm ^ ": unsolved subgoal", [t])))
    ORELSE' SUBGOAL (fn (t, _) => raise TERM (nm ^ ": tactic failed", [t]))

fun main_tac ctxt dest ord rel = SUBGOAL (fn (t, i) => let
    val xs_t = case HOLogic.dest_Trueprop t of
        Const (@{const_name distinct}, _) $ xs => xs
      | t => raise TERM ("distinct_tac: not distinct", [t])
    val xs = HOLogic.dest_list xs_t
    val ys = map (fn x => (dest x, x)) xs |> sort (ord o apply2 fst)
    val ys_t = HOLogic.mk_list (fastype_of (hd xs)) (map snd ys)
    val thm1 = Drule.infer_instantiate' ctxt
        (map (SOME o Thm.cterm_of ctxt) [fst rel, ys_t, xs_t])
        thm
  in (resolve_tac ctxt [thm1]
    THEN' solve "irreflp" (simp_only ctxt (snd rel))
    THEN' (solve "mset_eq_tac" (mset_eq_tac ctxt) o (fn j => j + 1))
    THEN' simp_only ctxt (@{thms sorted_wrt2_simps} @ snd rel))
    i
  end)

fun tac ctxt dest ord rel = simp_only ctxt @{thms distinct.simps(1) distinct_singleton}
    THEN_ALL_NEW main_tac ctxt dest ord rel

end

\<close>

definition
  fast_list_ord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> (bool \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "fast_list_ord R f xs ys = (length xs < length ys \<or>
    (length xs = length ys \<and> f (List.lexordp R xs ys)))"

lemma fast_list_ord_eq_lex:
  "fast_list_ord R (\<lambda>x. x) xs ys = ((xs, ys) \<in> (length <*mlex*> List.lexord {(x, y). R x y}))"
  by (simp add: fast_list_ord_def mlex_prod_def lexordp_def)

lemma fast_list_ord_simps[simp]:
  "fast_list_ord R f [] [] = f False"
  "fast_list_ord R b [] (y # ys) = True"
  "fast_list_ord R b (x # xs) [] = False"
  "fast_list_ord R f (x # xs) (y # ys) = fast_list_ord R (\<lambda>b. f (R x y \<or> (x = y \<and> b))) xs ys"
  by (simp_all add: fast_list_ord_def lexordp_def)

lemma fast_list_ord_irreflp:
  "irreflp R \<Longrightarrow> irreflp (fast_list_ord R (\<lambda>x. x))"
  by (simp add: fast_list_ord_def irreflp_def lexordp_def lexord_irreflexive)

lemma fast_list_ord_transp:
  "transp R \<Longrightarrow> transp (fast_list_ord R (\<lambda>x. x))"
  apply (simp add: transp_trans fast_list_ord_eq_lex mlex_prod_def del: in_inv_image)
  apply (simp add: trans_inv_image lexord_transI)
  done

lemma string_ord_transp:
  "transp (fast_list_ord (\<lambda>x y. (of_char x < (of_char y :: nat))) (\<lambda>x. x))"
  using trans_inv_image[of "measure id" of_char]
  apply (simp add: inv_image_def)
  apply (rule fast_list_ord_transp)
  apply (simp add: transp_trans trans_def[where r="measure _"])
  done

lemma string_ord_irreflp:
  "irreflp (fast_list_ord (\<lambda>x y. (of_char x < (of_char y :: nat))) (\<lambda>x. x))"
  by (simp add: irreflp_def fast_list_ord_def lexordp_def lexord_irreflexive)

method_setup distinct_string = \<open>
  Scan.succeed (fn ctxt => Method.SIMPLE_METHOD
    (Distinct_Tac.tac ctxt (HOLogic.dest_string) fast_string_ord
        (@{term "fast_list_ord (\<lambda>x y. of_char x < (of_char y :: nat)) (\<lambda>x. x)"},
            @{thms string_ord_irreflp string_ord_transp})
        1))
\<close>

ML \<open>
fun dest_nat (Const (@{const_name Suc}, _) $ n) = dest_nat n + 1
  | dest_nat n = snd (HOLogic.dest_number n)
\<close>

lemma irreflp_less:
  "irreflp ((<) :: ('a :: order) \<Rightarrow> _)"
  by (simp add: irreflpI)

method_setup distinct_nat = \<open>
  Scan.succeed (fn ctxt => Method.SIMPLE_METHOD
    (Distinct_Tac.tac ctxt dest_nat Int.compare
        (@{term "(<) :: nat \<Rightarrow> _"}, @{thms irreflp_less transp_on_less})
        1))
\<close>

method_setup distinct_int = \<open>
  Scan.succeed (fn ctxt => Method.SIMPLE_METHOD
    (Distinct_Tac.tac ctxt (snd o HOLogic.dest_number) Int.compare
        (@{term "(<) :: int \<Rightarrow> _"}, @{thms irreflp_less transp_on_less})
        1))
\<close>

notepad begin

have "distinct [''x'', ''y'', ''zyx'', ''a'', ''t'', ''hello there'', ''hello again'']"
  by (distinct_string; simp)

have "distinct [Suc 0, 4, 5, 9, 8, 7]"
  by (distinct_nat; simp)

have "distinct [(2 :: int), 4, 5, 9, 8, 7]"
  by (distinct_int; simp)

have "distinct (rev [12 ..< 80])"
  by (simp del: distinct.simps; distinct_nat; simp)

end

end