section\<open>Instantiations\<close>
subsection\<open>Neural Dynamic Logic\<close>
text\<open>
\label{subsec:inst:ndl}
TODO: Update
\<close>
theory NDL
  imports
    Complex_Main
    DynamicLogicCore
    DynamicLogic
    HavocDynamicLogic
    KATDynamicLogic
    KATRewriting

    "Deep_Learning.Tensor"
begin

datatype ('realvar, 'tensorvar) ndl_real_expr =
  Var 'realvar
  | Const real
  | Add "('realvar, 'tensorvar) ndl_real_expr" "('realvar, 'tensorvar) ndl_real_expr"
  | Mul "('realvar, 'tensorvar) ndl_real_expr" "('realvar, 'tensorvar) ndl_real_expr"
  | GetVal 'tensorvar "nat list"

datatype ('realvar, 'tensorvar) ndl_prog =
    RRAssign 'realvar "('realvar, 'tensorvar) ndl_real_expr"
    | TRAssign 'tensorvar "nat list" "('realvar, 'tensorvar) ndl_real_expr"
    | TTAssign 'tensorvar 'tensorvar
    | NNExec "((real tensor) list) \<Rightarrow> ((real tensor) list)" "'tensorvar list" "'tensorvar list"

datatype ('realvar, 'tensorvar) ndl_atom =
  Geq "('realvar, 'tensorvar) ndl_real_expr" "('realvar, 'tensorvar) ndl_real_expr"

type_synonym ndl_universe = "real + (real tensor)"

type_synonym ('realvar, 'tensorvar) ndl_state = "('realvar \<Rightarrow> real) \<times> ('tensorvar \<Rightarrow> (real tensor))"

type_synonym ('realvar, 'tensorvar) ndl_var = "'realvar + 'tensorvar"

fun ndl_real_var_eval :: "
  ('realvar, 'tensorvar) ndl_state \<Rightarrow>
  'realvar \<Rightarrow>
  real"
  where 
    "ndl_real_var_eval \<omega> x = ((fst \<omega>) x)"

fun ndl_tensor_var_eval :: "
  ('realvar, 'tensorvar) ndl_state \<Rightarrow>
  'tensorvar \<Rightarrow>
  real tensor"
  where 
    "ndl_tensor_var_eval \<omega> x = ((snd \<omega>) x)"

fun ndl_var_eval :: "
  ('realvar, 'tensorvar) ndl_state \<Rightarrow>
  ('realvar, 'tensorvar) ndl_var \<Rightarrow> 
  ndl_universe"
  where 
    "ndl_var_eval \<omega> (Inl v) = (Inl (ndl_real_var_eval \<omega> v))"
  | "ndl_var_eval \<omega> (Inr v) = (Inr (ndl_tensor_var_eval \<omega> v))"

fun ndl_expr_eval :: "
  (('realvar, 'tensorvar) ndl_real_expr) \<Rightarrow>
  (('realvar, 'tensorvar) ndl_state) \<Rightarrow> real"
  where
    "ndl_expr_eval (Var w) \<omega> = (ndl_real_var_eval \<omega> w)"
  | "ndl_expr_eval (Const v) \<omega> = v"
  | "ndl_expr_eval (Add e1 e2) \<omega> = (ndl_expr_eval e1 \<omega>) + (ndl_expr_eval e2 \<omega>)"
  | "ndl_expr_eval (Mul e1 e2) \<omega> = (ndl_expr_eval e1 \<omega>) * (ndl_expr_eval e2 \<omega>)"
  | "ndl_expr_eval (GetVal t p) \<omega> = (lookup (ndl_tensor_var_eval \<omega> t) p)"

fun ndl_atom_eval :: "(('realvar, 'tensorvar) ndl_atom) \<Rightarrow> (('realvar, 'tensorvar) ndl_state) \<Rightarrow> bool"
  where "ndl_atom_eval (Geq e1 e2) \<omega> = ( (ndl_expr_eval e1 \<omega> ) \<le> (ndl_expr_eval e2 \<omega> ) )"

fun var_not_in_list :: "'tensorvar list \<Rightarrow> ('realvar, 'tensorvar) ndl_var \<Rightarrow> bool"
  where
    "var_not_in_list _ (Inl rv) = True"
  | "var_not_in_list tenslit (Inr tv) = (\<not>(List.member tenslit tv))"

fun list_eval :: "'tensorvar list \<Rightarrow> (('realvar, 'tensorvar) ndl_state) \<Rightarrow> (real tensor) list"
  where
    "list_eval Nil \<mu> = []"
  | "list_eval (Cons x xs) \<mu> = (Cons (ndl_tensor_var_eval \<mu> x) (list_eval xs \<mu>))"

fun assert_list_eval_eq :: "'tensorvar list \<Rightarrow> (real tensor) list \<Rightarrow> (('realvar, 'tensorvar) ndl_state) \<Rightarrow> bool"
  where
    "assert_list_eval_eq Nil Nil \<mu> = True"
  | "assert_list_eval_eq (Cons x xs) (Cons y ys) \<mu> = (
      ((ndl_tensor_var_eval \<mu> x)=y) \<and> (assert_list_eval_eq xs ys \<mu>)
      )"
  | "assert_list_eval_eq _ _ \<mu> = False"

fun ndl_prog_eval :: "
  ('realvar, 'tensorvar) ndl_prog \<Rightarrow>
  (('realvar, 'tensorvar) ndl_state) \<Rightarrow>
  (('realvar, 'tensorvar) ndl_state) \<Rightarrow> bool"
  where
    "ndl_prog_eval (RRAssign rv e) \<mu> \<omega> = (
        (fol_equal_everywhere_but_gen ndl_var_eval (Inl rv) \<mu> \<omega>) \<and>
        ((ndl_real_var_eval \<omega> rv) = (ndl_expr_eval e \<mu>))
      )"
  | "ndl_prog_eval (TRAssign tv p e) \<mu> \<omega> = (
        (fol_equal_everywhere_but_gen ndl_var_eval (Inr tv) \<mu> \<omega>) \<and>
        ((lookup (ndl_tensor_var_eval \<omega> tv) p) = (ndl_expr_eval e \<mu>))
      )"
  | "ndl_prog_eval (TTAssign tv tp) \<mu> \<omega> = (
        (fol_equal_everywhere_but_gen ndl_var_eval (Inr tv) \<mu> \<omega>) \<and>
        ((ndl_tensor_var_eval \<omega> tv) = (ndl_tensor_var_eval \<mu> tp))
      )"
  | "ndl_prog_eval (NNExec net ins outs) \<mu> \<omega> = (
        (fol_states_agree_on_gen ndl_var_eval (var_not_in_list outs) \<mu> \<omega>) \<and>
        (let
          invals = (list_eval ins \<mu>);
          netout = (net invals)
        in (assert_list_eval_eq outs netout \<mu>))
    )"

fun ndl_fv_syn_expr :: "(('realvar, 'tensorvar) ndl_real_expr) \<Rightarrow> ('realvar, 'tensorvar) ndl_var \<Rightarrow> bool"
  where
    "ndl_fv_syn_expr (Var w) v = ((Inl w)=v)"
  | "ndl_fv_syn_expr (Const c) v = False"
  | "ndl_fv_syn_expr (Add e1 e2) v = ((ndl_fv_syn_expr e1 v) \<or> (ndl_fv_syn_expr e2 v))"
  | "ndl_fv_syn_expr (Mul e1 e2) v = ((ndl_fv_syn_expr e1 v) \<or> (ndl_fv_syn_expr e2 v))"
  | "ndl_fv_syn_expr (GetVal tw p) v = ((Inr tw)=v)"

fun ndl_fv_syn :: "(('realvar, 'tensorvar) ndl_atom) \<Rightarrow> ('realvar, 'tensorvar) ndl_var \<Rightarrow> bool"
  where
    "ndl_fv_syn (Geq e1 e2) v = ((ndl_fv_syn_expr e1 v) \<or> (ndl_fv_syn_expr e2 v))"


interpretation pdlFOL : folCore
  ndl_atom_eval ndl_fv_syn ndl_var_eval
proof
  show "\<And>a. finite (Collect (ndl_fv_syn a))"
    subgoal for a
    proof (induct a)
      case (Geq x1a x2a)
      then show ?case
        unfolding ndl_fv_syn.simps
      proof -
        have fact1: "\<And> y . finite {a. ndl_fv_syn_expr y a}"
          subgoal for y
          proof (induct y)
            case (Var x)
            then show ?case
              unfolding ndl_fv_syn_expr.simps
              by auto
          next
            case (Const x)
            then show ?case
              unfolding ndl_fv_syn_expr.simps
              by auto
          next
            case (Add y1 y2)
            then show ?case
              unfolding ndl_fv_syn_expr.simps
              by auto
          next
            case (Mul y1 y2)
            then show ?case
              unfolding ndl_fv_syn_expr.simps
              by auto
          next
            case (GetVal x1a x2a)
            then show ?case
              unfolding ndl_fv_syn_expr.simps
              by auto
          qed.
        have "finite {a. ndl_fv_syn_expr x1a a}"
          using fact1 by blast
        moreover have "finite {a. ndl_fv_syn_expr x2a a}"
          using fact1 by blast
        ultimately show "finite {a. ndl_fv_syn_expr x1a a \<or> ndl_fv_syn_expr x2a a}"
          by auto
      qed
    qed.
  show "\<And>a \<mu> \<omega>.
       fol_states_agree_on_gen ndl_var_eval (ndl_fv_syn a) \<mu> \<omega> \<Longrightarrow>
       ndl_atom_eval a \<mu> = ndl_atom_eval a \<omega>"
    subgoal for a \<mu> \<omega>
    proof (induct a)
      case (Geq x1a x2a)
      then show ?case
        unfolding ndl_atom_eval.simps
      proof -
        assume fv_eq_assm: "fol_states_agree_on_gen ndl_var_eval (ndl_fv_syn (Geq x1a x2a)) \<mu> \<omega>"
        have fact2: "\<And> y . 
              (fol_states_agree_on_gen ndl_var_eval (\<lambda>a. ndl_fv_syn_expr y a) \<mu> \<omega>)
              \<Longrightarrow> ndl_expr_eval y \<mu> = ndl_expr_eval y \<omega>"
          subgoal for y
            proof (induct y)
              case (Var x)
              then show ?case
                unfolding ndl_fv_syn_expr.simps fol_states_agree_on_gen_def
                unfolding ndl_expr_eval.simps
                using ndl_var_eval.simps
                by simp
            next
              case (Const x)
              then show ?case
                unfolding ndl_expr_eval.simps
                by simp
            next
              case (Add y1 y2)
              then show ?case
                unfolding ndl_fv_syn_expr.simps fol_states_agree_on_gen_def
                unfolding ndl_expr_eval.simps
                using ndl_var_eval.simps
                by simp
            next
              case (Mul y1 y2)
              then show ?case
                unfolding ndl_fv_syn_expr.simps fol_states_agree_on_gen_def
                unfolding ndl_expr_eval.simps
                using ndl_var_eval.simps
                by simp
            next
              case (GetVal x1a x2a)
              then show ?case
                unfolding ndl_fv_syn_expr.simps fol_states_agree_on_gen_def
                unfolding ndl_expr_eval.simps
                using ndl_var_eval.simps
                by simp
            qed.
        have "ndl_expr_eval x1a \<mu> = ndl_expr_eval x1a \<omega>"
          using fv_eq_assm fact2[of x1a]
          unfolding ndl_fv_syn.simps
          by auto
        moreover have "ndl_expr_eval x2a \<mu> = ndl_expr_eval x2a \<omega>"
          using fv_eq_assm fact2[of x2a]
          unfolding ndl_fv_syn.simps
          by auto
        ultimately show "(ndl_expr_eval x1a \<mu> \<le> ndl_expr_eval x2a \<mu>) =
                          (ndl_expr_eval x1a \<omega> \<le> ndl_expr_eval x2a \<omega>)"
          by auto
      qed
    qed.
  show "\<forall>\<omega> \<mu> V.
       \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> ndl_var_eval \<nu> v = ndl_var_eval \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> ndl_var_eval \<nu> v = ndl_var_eval \<omega> v)"
    apply (intro allI)
    subgoal for \<omega> \<mu> V
      apply (rule exI[of _ "(\<lambda>c. if Inl c \<in> V then ndl_real_var_eval \<mu> c else ndl_real_var_eval \<omega> c,
                              \<lambda>d. if Inr d \<in> V then ndl_tensor_var_eval \<mu> d else ndl_tensor_var_eval \<omega> d)"])
      using ndl_var_eval.simps
      apply (intro allI conjI impI)
      subgoal for v by (cases v) auto
      subgoal for v by (cases v) auto
      done
    done
qed

fun ndl_prog_fv_syn :: "(('realvar, 'tensorvar) ndl_prog) \<Rightarrow> ('realvar, 'tensorvar) ndl_var \<Rightarrow> bool"
  where
    "ndl_prog_fv_syn (RRAssign rv e) v = (ndl_fv_syn_expr e v)"
  | "ndl_prog_fv_syn (TRAssign tv p e) v = (ndl_fv_syn_expr e v)"
  | "ndl_prog_fv_syn (TTAssign tv tw) v = ((Inr tw) = v)"
  | "ndl_prog_fv_syn (NNExec net ins outs) (Inl v) = False"
  | "ndl_prog_fv_syn (NNExec net ins outs) (Inr v) = (List.member ins v)"

interpretation ndlDLFull : dynamic_theory
  ndl_atom_eval ndl_fv_syn ndl_var_eval
  ndl_prog_eval ndl_prog_fv_syn
proof
  show "\<And>\<pi>. finite (Collect (ndl_prog_fv_syn \<pi>))"
  proof -
    have fact1: "\<And>e. finite {v. ndl_fv_syn_expr e v}"
      subgoal for e by (induct e) auto
      done
    fix \<pi> :: "(('realvar, 'tensorvar) ndl_prog)"
    have "finite {v. (ndl_prog_fv_syn \<pi> v)}"
      proof (cases \<pi>)
        case (RRAssign rv e) then show ?thesis using fact1[of e] by simp
      next
        case (TRAssign tv p e) then show ?thesis using fact1[of e] by simp
      next
        case (TTAssign tv tw) then show ?thesis by simp
      next
        case (NNExec net ins outs)
        have "{v. ndl_prog_fv_syn (NNExec net ins outs) v} = Inr ` set ins"
          apply (intro set_eqI iffI)
          subgoal for x
          proof -
            assume assm1:"x \<in> {v. ndl_prog_fv_syn (NNExec net ins outs) v}"
            then show "x \<in> Inr ` set ins"
            proof (induct x)
              case (Inl a)
              then show ?case
                using ndl_prog_fv_syn.simps(4,5)
                by auto
            next
              case (Inr b)
              then show ?case
                using ndl_prog_fv_syn.simps(4,5)
                by (simp add: in_set_member)
            qed
          qed
        next
          fix v assume "v \<in> Inr ` set ins"
          then show "v \<in> {v. ndl_prog_fv_syn (NNExec net ins outs) v}"
            by (auto simp: simps in_set_member)
        qed
        then show ?thesis by simp
      qed
      then show "finite (Collect (ndl_prog_fv_syn \<pi>)) "
        by auto
    qed

  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. ndl_var_eval \<mu> v = ndl_var_eval \<omega> v) \<longrightarrow> ndl_prog_eval \<pi> \<mu> = ndl_prog_eval \<pi> \<omega>"
  proof (intro allI impI)
    fix \<pi> \<mu> \<omega>
    assume assm: "\<forall>v. ndl_var_eval \<mu> v = ndl_var_eval \<omega> v"
    have real_eq: "\<And>v. ndl_real_var_eval \<mu> v = ndl_real_var_eval \<omega> v"
      using assm[rule_format, of "Inl _"] by (simp add: ndl_var_eval.simps)
    have tensor_eq: "\<And>v. ndl_tensor_var_eval \<mu> v = ndl_tensor_var_eval \<omega> v"
      using assm[rule_format, of "Inr _"] by (simp add: ndl_var_eval.simps)
    have "\<mu> = \<omega>"
      using real_eq tensor_eq
      by (metis ext ndl_real_var_eval.simps ndl_tensor_var_eval.simps prod.collapse)
    then show "ndl_prog_eval \<pi> \<mu> = ndl_prog_eval \<pi> \<omega>" by simp
  qed


interpretation regular_pdl :
  regular_lifting "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
  unfolding regular_lifting_def
    using pdlDLFull.dynamic_theory_axioms
    by blast

interpretation regular_pdl_kat :
KleeneDynLog "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
  proof
    have pdl_state_eq_of_agree:
      "\<And>(\<sigma>::('atom,'ap) pdl_state) \<tau>. (\<forall>v. pdl_var_eval \<sigma> v = pdl_var_eval \<tau> v) \<Longrightarrow> \<sigma> = \<tau>"
    proof -
      fix \<sigma> \<tau> :: "('atom, 'ap) pdl_state"
      assume assms: "\<forall>v. pdl_var_eval \<sigma> v = pdl_var_eval \<tau> v"
      have fst_eq: "fst \<sigma> = fst \<tau>"
      proof
        fix x :: pdl_atom_var
        show "fst \<sigma> x = fst \<tau> x"
        proof (cases x)
          case singleton_var
          have h: "pdl_var_eval \<sigma> (Inl singleton_var) = pdl_var_eval \<tau> (Inl singleton_var)"
            using assms
            by blast
          show ?thesis
            unfolding singleton_var
            using h[unfolded pdl_var_eval.simps]
            by simp
        qed
      qed
      have snd_eq: "snd \<sigma> = snd \<tau>"
      proof
        fix p :: 'ap
        have h: "pdl_var_eval \<sigma> (Inr p) = pdl_var_eval \<tau> (Inr p)"
          using assms
          by blast
        show "snd \<sigma> p = snd \<tau> p"
          using h[unfolded pdl_var_eval.simps]
          by simp
      qed
      show "\<sigma> = \<tau>"
        using fst_eq snd_eq by (metis prod.collapse)
    qed

    show "\<forall>\<pi> \<mu> \<omega> \<mu>' \<omega>'.
           (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and> pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v) \<longrightarrow>
           pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
    proof (intro allI impI)
      fix \<pi> :: 'ap
      fix \<mu> \<omega> \<mu>' \<omega>' :: "('atom, 'ap) pdl_state"
      assume agree: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and> pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v"
      have agree1: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v"
        using agree by auto
      have agree2: "\<forall>v. pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v"
        using agree by auto
      have state_eq1: "\<mu> = \<omega>"
        using pdl_state_eq_of_agree[OF agree1] .
      have state_eq2: "\<mu>' = \<omega>'"
        using pdl_state_eq_of_agree[OF agree2] .
      show "pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
        using state_eq1 state_eq2
        by simp
    qed
  qed

end