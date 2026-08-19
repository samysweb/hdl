subsection\<open>Compiling NDL Formulas to Object-Level Properties\<close>
text\<open>
Implementation formalized by Claude Opus after
intensive discussion with Samuel Teuber on 19th of August 2026.
Cross-checked by Samuel Teuber.
\<close>

text\<open>
For the interface to a neural network verifier we need the pre- and
postcondition of a neural program as predicates over tensors, not as
deeply embedded formulas evaluated against a state.  This section defines
that translation and proves it correct.

The translation is parameterized by the source variable \<open>v\<close> and the target
variable \<open>w\<close> of the neural program: a lookup into \<open>w\<close> becomes a lookup into
the second tensor argument, every other lookup becomes a lookup into the
first.  A syntactic well-formedness predicate rules out the formulas that
have no tensor-level counterpart, namely those containing quantifiers,
modalities, or lookups into other variables.
\<close>

theory SemiRingNDLCompile
  imports
    "DynamicLogicProof"
    "SemiRingNDL"
    "HOL-Eisbach.Eisbach"
begin

subsubsection\<open>State Construction\<close>

definition st_upd :: "ndl_state \<Rightarrow> ndl_var \<Rightarrow> real tensor \<Rightarrow> ndl_state" where
  "st_upd \<mu> v t = (if dims t = var_shape v then Abs_ndl_state ((nst \<mu>)(v := t)) else \<mu>)"

lemma nst_st_upd [simp]:
  "dims t = var_shape v \<Longrightarrow> nst (st_upd \<mu> v t) = (nst \<mu>)(v := t)"
  by (simp add: st_upd_def wf_nstate_def)

definition base_state :: ndl_state where
  "base_state = Abs_ndl_state (\<lambda>v. tensor_from_lookup (var_shape v) (\<lambda>i. 0))"

lemma nst_pair_exists:
  assumes tv: "dims t = var_shape v"
      and sw: "dims s = var_shape w"
      and vw: "v \<noteq> w"
    shows "\<exists>\<mu>. nst \<mu> v = t \<and> nst \<mu> w = s"
  by (rule exI[of _ "st_upd (st_upd base_state v t) w s"]) (simp add: tv sw vw)

subsubsection\<open>The Translation\<close>

fun cmp_term :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> (ndl_var_lookup, real) semiringfol_term \<Rightarrow>
                 (real tensor \<Rightarrow> real tensor \<Rightarrow> real)"
  where
    "cmp_term v w (Const c) = (\<lambda>t s. c)"
  | "cmp_term v w (Var u) =
       (\<lambda>t s. if lk_var u = w then lookup s (lk_idx u) else lookup t (lk_idx u))"
  | "cmp_term v w (Add a b) = (\<lambda>t s. cmp_term v w a t s + cmp_term v w b t s)"
  | "cmp_term v w (Mul a b) = (\<lambda>t s. cmp_term v w a t s * cmp_term v w b t s)"

fun cmp_atom :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> (ndl_var_lookup, real) semiringfol_atom \<Rightarrow>
                 (real tensor \<Rightarrow> real tensor \<Rightarrow> bool)"
  where
    "cmp_atom v w (Eq a b)   = (\<lambda>t s. cmp_term v w a t s = cmp_term v w b t s)"
  | "cmp_atom v w (Less a b) = (\<lambda>t s. cmp_term v w a t s < cmp_term v w b t s)"

fun cmp_fol :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow>
                ((ndl_var_lookup, real) semiringfol_atom, ndl_var_lookup) fol_formula \<Rightarrow>
                (real tensor \<Rightarrow> real tensor \<Rightarrow> bool)"
  where
    "cmp_fol v w (ATOM a) = cmp_atom v w a"
  | "cmp_fol v w (\<phi> foland \<psi>) = (\<lambda>t s. cmp_fol v w \<phi> t s \<and> cmp_fol v w \<psi> t s)"
  | "cmp_fol v w (folnot \<phi>) = (\<lambda>t s. \<not> cmp_fol v w \<phi> t s)"
  | "cmp_fol v w (folall u \<phi>) = (\<lambda>t s. undefined)"

fun cmp_dyn :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> ndl_formula \<Rightarrow>
                (real tensor \<Rightarrow> real tensor \<Rightarrow> bool)"
  where
    "cmp_dyn v w (FOL \<phi>) = cmp_fol v w \<phi>"
  | "cmp_dyn v w (AND \<phi> \<psi>) = (\<lambda>t s. cmp_dyn v w \<phi> t s \<and> cmp_dyn v w \<psi> t s)"
  | "cmp_dyn v w (NOT \<phi>) = (\<lambda>t s. \<not> cmp_dyn v w \<phi> t s)"
  | "cmp_dyn v w (FOL_ALL u \<phi>) = (\<lambda>t s. undefined)"
  | "cmp_dyn v w (BOX \<pi> \<phi>) = (\<lambda>t s. undefined)"

subsubsection\<open>Compilable Formulas\<close>
text\<open>
A formula is compilable w.r.t. \<open>v\<close> and \<open>w\<close> if it is quantifier- and
modality-free and every lookup it contains reads one of the two variables.
This is decidable and replaces the semantic free-variable side conditions.
\<close>

fun ok_term :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> (ndl_var_lookup, real) semiringfol_term \<Rightarrow> bool"
  where
    "ok_term v w (Const c) = True"
  | "ok_term v w (Var u) = (lk_var u = v \<or> lk_var u = w)"
  | "ok_term v w (Add a b) = (ok_term v w a \<and> ok_term v w b)"
  | "ok_term v w (Mul a b) = (ok_term v w a \<and> ok_term v w b)"

fun ok_atom :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> (ndl_var_lookup, real) semiringfol_atom \<Rightarrow> bool"
  where
    "ok_atom v w (Eq a b)   = (ok_term v w a \<and> ok_term v w b)"
  | "ok_atom v w (Less a b) = (ok_term v w a \<and> ok_term v w b)"

fun ok_fol where
    "ok_fol v w (ATOM a) = ok_atom v w a"
  | "ok_fol v w (\<phi> foland \<psi>) = (ok_fol v w \<phi> \<and> ok_fol v w \<psi>)"
  | "ok_fol v w (folnot \<phi>) = ok_fol v w \<phi>"
  | "ok_fol v w (folall u \<phi>) = False"

fun ok_dyn :: "ndl_var \<Rightarrow> ndl_var \<Rightarrow> ndl_formula \<Rightarrow> bool" where
    "ok_dyn v w (FOL \<phi>) = ok_fol v w \<phi>"
  | "ok_dyn v w (AND \<phi> \<psi>) = (ok_dyn v w \<phi> \<and> ok_dyn v w \<psi>)"
  | "ok_dyn v w (NOT \<phi>) = ok_dyn v w \<phi>"
  | "ok_dyn v w (FOL_ALL u \<phi>) = False"
  | "ok_dyn v w (BOX \<pi> \<phi>) = False"

subsubsection\<open>Correctness of the Translation\<close>
text\<open>
The translation agrees with the deep embedding at any state that stores the
two given tensors in the two given variables.  Note that no shape assumptions
are needed: the tensors come out of a well-shaped state.
\<close>

lemma cmp_term_correct:
  assumes vw: "v \<noteq> w"
      and ok: "ok_term v w e"
      and tv: "nst \<mu> v = t"
      and sw: "nst \<mu> w = s"
    shows "cmp_term v w e t s = semiringfol_TermEval e (ndl_eval \<mu>)"
  using ok
proof (induct e)
  case (Const c) then show ?case by simp
next
  case (Var u)
  show ?case
  proof (cases "lk_var u = w")
    case True
    thus ?thesis using sw by (simp add: ndl_eval_def)
  next
    case False
    hence "lk_var u = v" using Var.prems by simp
    thus ?thesis using False tv by (simp add: ndl_eval_def)
  qed
next
  case (Add a b) then show ?case by simp
next
  case (Mul a b) then show ?case by simp
qed

lemma cmp_atom_correct:
  assumes "v \<noteq> w"
      and "ok_atom v w a"
      and "nst \<mu> v = t"
      and "nst \<mu> w = s"
  shows "cmp_atom v w a t s = semiringfol_AtomEval a (ndl_eval \<mu>)"
  using assms by (cases a) (simp_all add: cmp_term_correct)

lemma cmp_fol_correct:
  assumes vw: "v \<noteq> w" and tv: "nst \<mu> v = t" and sw: "nst \<mu> w = s"
      and ok: "ok_fol v w F"
    shows "cmp_fol v w F t s = ndl_dl.A.fol_eval F \<mu>"
  using ok
proof (induct F)
  case (ATOM a)
  then show ?case
    unfolding ndl_dl.A.fol_eval.simps
    unfolding semiringfol_AtomEval_flex.simps
    using vw tv sw cmp_atom_correct[of v w a \<mu> t s] by simp
next
  case (AND \<phi> \<psi>) then show ?case
    unfolding ok_fol.simps
    unfolding cmp_fol.simps
    unfolding ndl_dl.A.fol_eval.simps
    by blast
next
  case (NOT \<phi>) then show ?case
    unfolding ok_fol.simps
    unfolding cmp_fol.simps
    unfolding ndl_dl.A.fol_eval.simps
    by blast
next
  case (FOL_ALL u \<phi>) then show ?case by simp
qed

lemma cmp_dyn_correct:
  assumes vw: "v \<noteq> w" and tv: "nst \<mu> v = t" and sw: "nst \<mu> w = s"
      and ok: "ok_dyn v w F"
    shows "cmp_dyn v w F t s = ndl_dl.sum_dl.dyn_eval F \<mu>"
  using ok
proof (induct F arbitrary:)
  case (FOL \<phi>)
  then show ?case
    unfolding ok_dyn.simps
    unfolding cmp_dyn.simps
    unfolding ndl_dl.sum_dl.dyn_eval.simps
    using vw tv sw cmp_fol_correct by simp
next
  case (AND \<phi> \<psi>) then show ?case
    unfolding ok_dyn.simps
    unfolding cmp_dyn.simps
    unfolding ndl_dl.sum_dl.dyn_eval.simps
    by blast
next
  case (NOT \<phi>) then show ?case
    unfolding ok_dyn.simps
    unfolding cmp_dyn.simps
    unfolding ndl_dl.sum_dl.dyn_eval.simps
    by blast
next
  case (FOL_ALL u \<phi>) then show ?case by simp
next
  case (BOX \<pi> \<phi>) then show ?case by simp
qed

subsubsection\<open>The Compiled Box Reduction\<close>
text\<open>
A box property of a neural program over compilable pre- and postconditions is
equivalent to a property of the network function alone.  The second tensor
argument of the precondition is the pre-state value of the target variable;
it is unconstrained, and disappears from the postcondition because the
program overwrites the target.  If the precondition does not mention the
target variable, the \<open>\<forall>s\<close> can be dropped by a verifier.
\<close>

theorem nn_box_compile:
  assumes p_shape: "nnp p = NNApply w N v"
      and vw: "v \<noteq> w"
      and okP: "ok_dyn v w P"
      and okQ: "ok_dyn v w Q"
    shows "(\<Turnstile>[ndl_dl.sum_dl.dyn_eval] P \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> Q) =
           (\<forall>t s. dims t = var_shape v \<longrightarrow> dims s = var_shape w \<longrightarrow>
                  cmp_dyn v w P t s \<longrightarrow> cmp_dyn v w Q t (stf_apply N t))"
proof -
  have tgt: "ntgt p = w" and src: "nsrc p = v" and fn: "nfun p = N"
    using p_shape by simp_all

  text\<open>The successor state, described by its two relevant components.\<close>
  have succ: "\<And>\<mu> \<omega>. nn_eval p \<mu> \<omega> \<Longrightarrow>
                    nst \<omega> v = nst \<mu> v \<and> nst \<omega> w = stf_apply N (nst \<mu> v)"
    using tgt src fn vw by (simp add: nn_eval_def)

  show ?thesis
  proof (rule iffI)
    assume L: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] P \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> Q"
    show "\<forall>t s. dims t = var_shape v \<longrightarrow> dims s = var_shape w \<longrightarrow>
                cmp_dyn v w P t s \<longrightarrow> cmp_dyn v w Q t (stf_apply N t)"
    proof (intro allI impI)
      fix t s
      assume dt: "dims t = var_shape v" and ds: "dims s = var_shape w"
         and pre: "cmp_dyn v w P t s"
      obtain \<mu> where mu: "nst \<mu> v = t" "nst \<mu> w = s"
        using nst_pair_exists[OF dt ds vw] by blast
      have "ndl_dl.sum_dl.dyn_eval P \<mu>"
        using pre cmp_dyn_correct[OF vw mu okP] by simp
      hence box: "ndl_dl.sum_dl.dyn_eval (\<lbrakk>Inr p\<rbrakk> Q) \<mu>"
        using L by (auto simp add: dyn_sem)
      obtain \<omega> where step: "nn_eval p \<mu> \<omega>" using nn_total_det by blast
      have "nst \<omega> v = t" and "nst \<omega> w = stf_apply N t"
        using succ[OF step] mu by simp_all
      moreover have "ndl_dl.sum_dl.dyn_eval Q \<omega>" using box step by simp
      ultimately show "cmp_dyn v w Q t (stf_apply N t)"
        using cmp_dyn_correct[OF vw _ _ okQ] by metis
    qed
  next
    assume R: "\<forall>t s. dims t = var_shape v \<longrightarrow> dims s = var_shape w \<longrightarrow>
                     cmp_dyn v w P t s \<longrightarrow> cmp_dyn v w Q t (stf_apply N t)"
    show "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] P \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> Q"
    proof (unfold theory_valid_def, intro allI)
      fix \<mu>
      show "ndl_dl.sum_dl.dyn_eval (P \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> Q) \<mu>"
      proof (cases "ndl_dl.sum_dl.dyn_eval P \<mu>")
        case False
        thus ?thesis by (auto simp add: dyn_sem)
      next
        case True
        have "cmp_dyn v w P (nst \<mu> v) (nst \<mu> w)"
          using True cmp_dyn_correct[OF vw refl refl okP] by simp
        hence post: "cmp_dyn v w Q (nst \<mu> v) (stf_apply N (nst \<mu> v))"
          using R
          using nst_dims by blast
        have "\<And>\<omega>. nn_eval p \<mu> \<omega> \<Longrightarrow> ndl_dl.sum_dl.dyn_eval Q \<omega>"
        proof -
          fix \<omega> assume step: "nn_eval p \<mu> \<omega>"
          have "nst \<omega> v = nst \<mu> v" and "nst \<omega> w = stf_apply N (nst \<mu> v)"
            using succ[OF step] by simp_all
          thus "ndl_dl.sum_dl.dyn_eval Q \<omega>"
            using post cmp_dyn_correct[OF vw _ _ okQ] by metis
        qed
        thus ?thesis by (auto simp add: dyn_sem)
      qed
    qed
  qed
qed

lemma nn_box_compileI:
  assumes shape: "nnp p = NNApply w N v"
      and vw:   "v \<noteq> w"
      and okP:  "ok_dyn v w P"
      and okQ:  "ok_dyn v w Q"
      and obj:  "\<And>t s. dims t = var_shape v \<Longrightarrow> dims s = var_shape w \<Longrightarrow>
                        cmp_dyn v w P t s \<Longrightarrow> cmp_dyn v w Q t (stf_apply N t)"
    shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] P \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> Q"
  using nn_box_compile[OF shape vw okP okQ] obj by blast



named_theorems ndl_ok  "rules for discharging compilability side conditions"
named_theorems ndl_cmp "rules for unfolding the compiled object-level goal"

declare ok_dyn.simps ok_fol.simps ok_atom.simps ok_term.simps [ndl_ok]

declare cmp_dyn.simps cmp_fol.simps cmp_atom.simps cmp_term.simps [ndl_cmp]

method ndl_compile uses shape =
  (rule nn_box_compileI[OF shape] ;
     ((solves \<open>simp add: ndl_ok\<close>) | (simp add: ndl_cmp)?))

text\<open>
Quantifiers could be added by the auxiliary-variable trick: a lookup \<open>u\<close> with
\<open>lk_var u = v\<close> bound by \<open>\<bbbA> u\<close> corresponds to quantifying over a real and
updating the tensor at that index,
@{text "cmp_fol v w (FOL_ALL u \<phi>) = (\<lambda>t s. \<forall>r. cmp_fol v w \<phi> (upd t (lk_idx u) r) s)"},
with \<open>upd\<close> defined via \<open>tensor_from_lookup\<close>.  The correctness proof then needs
a substitution lemma relating the tensor update to the state update, which is
why this is left out here.
\<close>

end
