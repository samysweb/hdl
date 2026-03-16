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

type_synonym semiringfol_var = string

type_synonym ('a,'b) fol_state = "'a \<Rightarrow> 'b"

datatype ('semiringfol_val :: ordered_semiring) semiringfol_term =
  Const 'semiringfol_val
  | Var "semiringfol_var"
  | Add "'semiringfol_val semiringfol_term" "'semiringfol_val semiringfol_term"
  | Mul "'semiringfol_val semiringfol_term" "'semiringfol_val semiringfol_term"

datatype ('semiringfol_val :: ordered_semiring) semiringfol_atom =
  Eq "'semiringfol_val semiringfol_term" "'semiringfol_val semiringfol_term"
  | Less "'semiringfol_val semiringfol_term" "'semiringfol_val semiringfol_term"

fun semiringfol_TermEval :: "('semiringfol_val :: ordered_semiring) semiringfol_term \<Rightarrow> (semiringfol_var, 'semiringfol_val) fol_state \<Rightarrow> 'semiringfol_val"
  where
    "semiringfol_TermEval (Const n) \<mu> = n"
  | "semiringfol_TermEval (Var v) \<mu> = (\<mu> v)"
  | "semiringfol_TermEval (Add a b) \<mu> = (semiringfol_TermEval a \<mu>) + (semiringfol_TermEval b \<mu>)"
  | "semiringfol_TermEval (Mul a b) \<mu> = (semiringfol_TermEval a \<mu>) * (semiringfol_TermEval b \<mu>)"

fun semiringfol_AtomEval :: "('semiringfol_val :: ordered_semiring) semiringfol_atom \<Rightarrow> (semiringfol_var, 'semiringfol_val) fol_state \<Rightarrow> bool"
  where
    "semiringfol_AtomEval (Eq a b) \<mu> = ((semiringfol_TermEval a \<mu>) = (semiringfol_TermEval b \<mu>))"
  | "semiringfol_AtomEval (Less a b) \<mu> = ((semiringfol_TermEval a \<mu>) < (semiringfol_TermEval b \<mu>))"

fun semiringfol_TermFVSyn :: "('semiringfol_val :: ordered_semiring) semiringfol_term \<Rightarrow> semiringfol_var \<Rightarrow> bool"
  where
    "semiringfol_TermFVSyn (Const n) v = False"
  | "semiringfol_TermFVSyn (Var w) v = (v=w)"
  | "semiringfol_TermFVSyn (Add a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"
  | "semiringfol_TermFVSyn (Mul a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"

fun semiringfol_AtomFVSyn :: "('semiringfol_val :: ordered_semiring) semiringfol_atom \<Rightarrow> semiringfol_var \<Rightarrow> bool"
  where
    "semiringfol_AtomFVSyn (Eq a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"
  | "semiringfol_AtomFVSyn (Less a b) v = ((semiringfol_TermFVSyn a v) \<or> (semiringfol_TermFVSyn b v))"

definition state_id :: "((semiringfol_var, 'semiringfol_val) fol_state \<Rightarrow> (semiringfol_var, 'semiringfol_val) fol_state)"
  where [simp]: "state_id = id"

lemma fv_term_overapprox:
      "\<And>(t :: ('semiringfol_val :: ordered_semiring) semiringfol_term) \<mu> \<omega>. fol_states_agree_on_gen id (semiringfol_TermFVSyn t) \<mu> \<omega> \<Longrightarrow> semiringfol_TermEval t \<mu> = semiringfol_TermEval t \<omega>"
  proof -
    fix t :: "('semiringfol_val :: ordered_semiring) semiringfol_term"
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

interpretation semiring_folCore : folCore "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id
proof
  fix a :: "('semiringfol_val :: ordered_semiring) semiringfol_atom"
  fix \<mu> :: "(semiringfol_var \<Rightarrow> ('semiringfol_val :: ordered_semiring))"
  fix \<omega> :: "(semiringfol_var \<Rightarrow> ('semiringfol_val :: ordered_semiring))"

  show "finite (Collect (semiringfol_AtomFVSyn a))"
  proof -
    have termFV_finite: "\<And> (t :: ('semiringfol_val :: ordered_semiring) semiringfol_term) .finite (Collect (semiringfol_TermFVSyn t))"
    proof -
      fix t :: "('semiringfol_val :: ordered_semiring) semiringfol_term"
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

  show "fol_states_agree_on_gen state_id (semiringfol_AtomFVSyn a) \<mu> \<omega> \<Longrightarrow> semiringfol_AtomEval a \<mu> = semiringfol_AtomEval a \<omega>"
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
  show "\<forall>\<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_id \<nu> v = state_id \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_id \<nu> v = state_id \<omega> v)"
  proof (intro allI)
    fix \<omega>
    fix \<mu>
    fix V
      
    show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_id \<nu> v = state_id \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_id \<nu> v = state_id \<omega> v)"
      by (intro exI[where x="(\<lambda> v . if v \<in> V then (\<mu> v) else (\<omega> v))"],simp)
  qed
qed
end