subsection\<open>Semi-Ring First-Order Dynamic Logic\<close>
text\<open>
\label{subsec:inst:fodl}
As a more complex example of a dynamic logic,
we formalize a first-order dynamic logic with ordered semi-ring terms
\<close>

subsubsection\<open>First-Order Core\<close>
text\<open>
We first define the first-order core on which we build our first-order
dynamic logic
\<close>

theory SemiRingFOL
  imports
    Main
    FirstOrder
begin

type_synonym ('a,'b) fol_state = "'a \<Rightarrow> 'b"

datatype ('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term =
  Const 'semiringfol_val
  | Var "'semiring_var"
  | Add
    "('semiring_var,'semiringfol_val) semiringfol_term"
    "('semiring_var,'semiringfol_val) semiringfol_term"
  | Mul
    "('semiring_var,'semiringfol_val) semiringfol_term"
    "('semiring_var,'semiringfol_val) semiringfol_term"

datatype ('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_atom =
  Eq
    "('semiring_var,'semiringfol_val) semiringfol_term"
    "('semiring_var,'semiringfol_val) semiringfol_term"
  | Less
    "('semiring_var,'semiringfol_val) semiringfol_term"
    "('semiring_var,'semiringfol_val) semiringfol_term"

fun semiringfol_TermEval :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term \<Rightarrow> ('semiring_var, 'semiringfol_val) fol_state \<Rightarrow> 'semiringfol_val"
  where
    "semiringfol_TermEval (Const n) \<mu> = n"
  | "semiringfol_TermEval (Var v) \<mu> = (\<mu> v)"
  | "semiringfol_TermEval (Add a b) \<mu> = (semiringfol_TermEval a \<mu>) + (semiringfol_TermEval b \<mu>)"
  | "semiringfol_TermEval (Mul a b) \<mu> = (semiringfol_TermEval a \<mu>) * (semiringfol_TermEval b \<mu>)"

fun semiringfol_AtomEval
    :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_atom \<Rightarrow>
        ('semiring_var, 'semiringfol_val) fol_state \<Rightarrow>
        bool"
  where
    "semiringfol_AtomEval (Eq a b) \<mu> = ((semiringfol_TermEval a \<mu>) = (semiringfol_TermEval b \<mu>))"
  | "semiringfol_AtomEval (Less a b) \<mu> = ((semiringfol_TermEval a \<mu>) < (semiringfol_TermEval b \<mu>))"

fun semiringfol_TermFVSyn :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term \<Rightarrow> 'semiring_var \<Rightarrow> bool"
  where
    "semiringfol_TermFVSyn (Const n) v = False"
  | "semiringfol_TermFVSyn (Var w) v = (v=w)"
  | "semiringfol_TermFVSyn (Add a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"
  | "semiringfol_TermFVSyn (Mul a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"

fun semiringfol_AtomFVSyn :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_atom \<Rightarrow> 'semiring_var \<Rightarrow> bool"
  where
    "semiringfol_AtomFVSyn (Eq a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"
  | "semiringfol_AtomFVSyn (Less a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"

definition state_id :: "(('semiring_var, 'semiringfol_val) fol_state \<Rightarrow> ('semiring_var, 'semiringfol_val) fol_state)"
  where [simp]: "state_id = id"

lemma fv_term_overapprox:
      "\<And>(t :: ('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term) \<mu> \<omega>. fol_states_agree_on_gen id (semiringfol_TermFVSyn t) (state_eval \<mu>) (state_eval \<omega>) \<Longrightarrow> semiringfol_TermEval t (state_eval \<mu>) = semiringfol_TermEval t (state_eval \<omega>)"
  proof -
    fix t :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term"
    fix \<mu>
    fix \<omega>
    show "fol_states_agree_on_gen id (semiringfol_TermFVSyn t) \<mu> \<omega> \<Longrightarrow> semiringfol_TermEval t \<mu> = semiringfol_TermEval t \<omega>"
    proof (induct t)
      case (Const x)
      then show ?case by auto
    next
      case (Var x)
      then show ?case by (simp add: fol_states_agree_on_gen_def id_def)
    next
      case (Add t1 t2)
      then show ?case by (simp add: fol_states_agree_on_gen_def id_def)
    next
      case (Mul t1 t2)
      then show ?case by (simp add: fol_states_agree_on_gen_def id_def)
    qed
  qed

fun semiringfol_AtomEval_flex
    :: "('semiring_state \<Rightarrow> 'semiring_var \<Rightarrow> 'semiringfol_val :: ordered_semiring) \<Rightarrow>
        ('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_atom \<Rightarrow>
        'semiring_state \<Rightarrow>
        bool"
    where "semiringfol_AtomEval_flex state_eval a \<mu> = semiringfol_AtomEval a (state_eval \<mu>)"

lemma semiring_folCore_via:
  fixes state_eval :: "'semiring_state \<Rightarrow> 'semiring_var \<Rightarrow> 'semiringfol_val :: ordered_semiring"
  assumes semiring_state_space_convexity: "\<forall> \<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_eval \<nu> v = state_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_eval \<nu> v = state_eval \<omega> v)"
  shows "folCore (semiringfol_AtomEval_flex state_eval) semiringfol_AtomFVSyn state_eval"
proof
  fix a :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_atom"
  fix \<mu>
  fix \<omega>

  show "finite (Collect (semiringfol_AtomFVSyn a))"
  proof -
    have termFV_finite: "\<And> (t :: ('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term) .finite (Collect (semiringfol_TermFVSyn t))"
    proof -
      fix t :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiringfol_term"
      show "finite (Collect (semiringfol_TermFVSyn t))"
      proof (induct t)
        case (Const x)
        then show ?case by auto
      next
        case (Var x)
        then show ?case by auto
      next
        case (Add t1 t2)
        then show ?case by auto
      next
        case (Mul t1 t2)
        then show ?case by auto
      qed
    qed

    thus "finite (Collect (semiringfol_AtomFVSyn a))"
    proof (induct a)
      case (Eq x1 x2)
      then show ?case
        by simp
    next
      case (Less x1 x2)
      then show ?case
        by simp
    qed
  qed

  show "fol_states_agree_on_gen state_eval (semiringfol_AtomFVSyn a) \<mu> \<omega> \<Longrightarrow>
       semiringfol_AtomEval_flex state_eval a \<mu> =
       semiringfol_AtomEval_flex state_eval a \<omega>"
  proof (induct a)
    case (Eq x1 x2)
    then show ?case
      apply simp
      using fv_term_overapprox
      unfolding fol_states_agree_on_gen_def id_def
      by metis
  next
    case (Less x1 x2)
    then show ?case
      apply simp
      using fv_term_overapprox
      unfolding fol_states_agree_on_gen_def id_def
      by metis
  qed
  show "\<forall>\<omega> \<mu> V.
       \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_eval \<nu> v = state_eval \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> state_eval \<nu> v = state_eval \<omega> v)"
    using semiring_state_space_convexity
    by auto
qed

lemma state_id_convex:
  "(\<forall> \<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_id \<nu> v = state_id \<mu> v) \<and>
              (v \<notin> V \<longrightarrow> state_id \<nu> v = state_id \<omega> v))"
  proof (intro allI)
    fix \<omega>
    fix \<mu>
    fix V
      
    show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_id \<nu> v = state_id \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_id \<nu> v = state_id \<omega> v)"
      by (intro exI[where x="(\<lambda> v . if v \<in> V then (\<mu> v) else (\<omega> v))"],simp)
  qed

interpretation semiring_folCore : folCore "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id
  using state_id_convex
  using semiring_folCore_via[of state_id]
  unfolding semiringfol_AtomEval_flex.simps
  unfolding state_id_def id_def
  by auto

end