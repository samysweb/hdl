section \<open> Dynamic Theory Locale \<close>
text\<open>
\label{sec:dynlog}
We now define the dynamic theory locale which can be instantiated for a given
dynamic logic.
\<close>
theory DynamicLogicCore
  imports
    Main
    "FirstOrder"
begin
subsection \<open> Syntax and Assumptions \<close>
text \<open>
Dynamic Logic Formulas can consist of first-order formulas and the typical FOL connectives.
Additionally, we allow formulas with the box modality containing a program of type \texttt{'pr}.
All other connectives, operators and modalities are syntactic sugar.
\<close>

datatype ('a, 'vr, 'pr) dyn_formula =
  FOL "('a, 'vr) fol_formula"
  | AND "('a,'vr,'pr) dyn_formula" "('a,'vr,'pr) dyn_formula"
  | NOT "('a,'vr,'pr) dyn_formula"
  | FOL_ALL "'vr" "('a,'vr,'pr) dyn_formula"
  | BOX "'pr" "('a,'vr,'pr) dyn_formula"


text \<open>
For the dynamic theory locale, we first of all assume an instantiation of the
First Order Core Locale which gives us a way of evaluating atomic formulas and provides us
with the syntactic (overapproximate) free variable function.
To instantiate a dynamic theory we furthermore require a function evaluating programs of type \texttt{'prog}
(as a state relation) and syntactic overapproximations of free and bound variables of a program.

In the accompanying paper~\cite{DBLP:journals/corr/abs-2507-08581}
we present all results w.r.t. a slightly stricter variant of the assumption
\texttt{prog\_var\_determinance}.
This slightly stronger (proof see \Cref{sec:extensional-dl}) notion will
only be introduced in \Cref{subsec:kat-reasoning}.
All other results hold for both variants.
For simplicity, we omitted this difference in assumptions in the accompanying paper.
In practice, we are not (yet) aware of any dynamic theory which
only satisfies the weaker form of extensionality.
\<close>

locale dynamic_theory =
  folCore atom_eval atom_fv_syn state_eval
    for (* this is necessary because we need matching type variables *)
      atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
      and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
      and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  +
  fixes prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  assumes prog_fv_finite: "finite (Collect (dyn_prog_FV \<pi>))"
        and prog_fv_overapprox:
        "\<And> \<pi> V \<mu> \<omega> \<nu> . ((\<forall> v . ((dyn_prog_FV \<pi> v) \<longrightarrow> (V v))) \<and> fol_states_agree_on V \<mu> \<omega> \<and> prog_eval \<pi> \<mu> \<nu>) \<longrightarrow> (\<exists> \<upsilon> . prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
        and prog_var_determinance:
          "\<forall> \<pi> \<mu> \<omega> . ((\<forall> v. ((state_eval \<mu>) v = (state_eval \<omega>) v)) \<longrightarrow> prog_eval \<pi> \<mu> = prog_eval \<pi> \<omega>)"
begin

  sublocale fol:
    folCore atom_eval atom_fv_syn state_eval
    by (simp add: folCore_axioms)

  notation BOX ("\<lbrakk> _ \<rbrakk> _" [130, 130] 130)
  
  notation AND (infix "and" 120)
  (* OR 110 *)
  notation NOT ("\<rceil> _" [130] 130)
  notation FOL_ALL ("\<bbbA> _ . _" 200)

  text\<open>
  Based on the assumptions from above, we can introduce the following syntactic sugar.
  \<close>

  fun FOR_ALL_VEC :: "'var list \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula"
    ("\<bbbA>\<bbbA> _ . _" 190) where[dyn_sem]:
      "FOR_ALL_VEC [] \<phi> = \<phi>"
    | "FOR_ALL_VEC (x # xs) \<phi> = \<bbbA> x . (FOR_ALL_VEC xs \<phi>)"

  definition EX_VEC :: "'var list \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula"
  ("\<bbbE>\<bbbE> _ . _" 190)
  where "\<bbbE>\<bbbE> vs . \<phi> \<equiv> \<rceil>(\<bbbA>\<bbbA> vs . \<rceil>\<phi>)"

  definition DYNTRUE :: "('atom,'var,'prog) dyn_formula"
    where[dyn_sem]: "DYNTRUE = (FOL FOLTRUE)"

  definition IMP :: "('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula"
   (infixr "\<Rrightarrow>" 100)
   where[dyn_sem]: "(a :: ('atom,'var,'prog) dyn_formula) \<Rrightarrow> b = \<rceil>(a and \<rceil>b)"
  
  definition EQUIV :: "('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula"
   (infixr "\<Lleftarrow>\<Rrightarrow>" 90)
   where[dyn_sem]: "(a :: ('atom,'var,'prog) dyn_formula) \<Lleftarrow>\<Rrightarrow> b = (a \<Rrightarrow> b) and (b \<Rrightarrow> a)"

  definition OR :: "('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula"
  (infix "or" 110)
  where[dyn_sem]: "((a :: ('atom,'var,'prog) dyn_formula) or (b :: ('atom,'var,'prog) dyn_formula)) = \<rceil>(\<rceil>a and \<rceil>b)"
  
  definition DIAMOND :: "'prog \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula" 
    ("\<langle> _ \<rangle> _"  [130, 130] 130) where[dyn_sem]:
    "\<langle>\<pi>\<rangle>\<phi> \<equiv> (\<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi>)"

  definition DYN_EX :: "'var \<Rightarrow> ('atom,'var,'prog) dyn_formula \<Rightarrow> ('atom,'var,'prog) dyn_formula" 
    ("\<bbbE> _ . _" 190) where[dyn_sem]: "\<bbbE> v . \<phi> \<equiv> \<rceil>(\<bbbA> v . \<rceil>\<phi>)"

  subsection\<open>Semantics\<close>
  text\<open>
  We define the evaluation of dynamic theory formulas based on the evaluation of first-order formulas
  and the given evaluation of programs \texttt{prog\_eval}.
  \<close>

  fun dyn_eval :: "('atom,'var,'prog) dyn_formula \<Rightarrow> 'state \<Rightarrow> bool"
    where
      "dyn_eval (FOL \<phi>) \<mu> = fol_eval \<phi> \<mu>"
    | "dyn_eval (\<phi> and \<psi>) \<mu> = ((dyn_eval \<phi> \<mu>) \<and> (dyn_eval \<psi> \<mu>))"
    | "dyn_eval (\<rceil> \<phi>) \<mu> = (\<not> (dyn_eval \<phi> \<mu>))"
    | "dyn_eval (\<bbbA> v . \<phi>) \<mu> = (\<forall> \<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<longrightarrow> (dyn_eval \<phi> \<omega>))"
    | "dyn_eval (\<lbrakk>\<alpha>\<rbrakk>\<phi>) \<mu> = (\<forall> \<omega>. (prog_eval \<alpha> \<mu> \<omega>) \<longrightarrow> (dyn_eval \<phi> \<omega>))"

  (* Let's quickly show that our definition of true is correct *)
  lemma dyn_true_valid :"\<Turnstile>[dyn_eval] DYNTRUE" 
    unfolding DYNTRUE_def
    unfolding FOLTRUE_def
    unfolding theory_valid_def
    unfolding dyn_eval.simps
    by (auto simp add: dyn_sem)

  lemma ex_vec_single: "dyn_eval (\<bbbE>\<bbbE> (x # xs) . \<phi>) \<mu>
                       = (\<exists>\<nu>. fol_equal_everywhere_but x \<mu> \<nu> \<and> dyn_eval (\<bbbE>\<bbbE> xs . \<phi>) \<nu>)"
    unfolding EX_VEC_def FOR_ALL_VEC.simps(2)
    by auto

  subsection\<open>Free and Bound Variables\<close>

  text\<open>Based on the given functions \texttt{fol\_fv\_syn} (constructed from \texttt{atom\_fv\_syn}
  in the first-order logic locale) and \texttt{dyn\_prog\_FV} we extend the definition of
  free variables to dynamic theory formulas.
  \<close>
  fun dyn_FV :: "('atom,'var,'prog) dyn_formula \<Rightarrow> 'var \<Rightarrow> bool"
   where
      "dyn_FV (FOL \<phi>) v = fol_fv_syn \<phi> v"
    | "dyn_FV (\<phi> and \<psi>) v = (dyn_FV \<phi> v \<or> dyn_FV \<psi> v)"
    | "dyn_FV (\<rceil> \<phi>) v = (dyn_FV \<phi> v)"
    | "dyn_FV (\<bbbA> v . \<phi>) w = (if (v=w) then False else dyn_FV \<phi> w)"
    | "dyn_FV (\<lbrakk> \<pi> \<rbrakk> \<phi>) v = (dyn_FV \<phi> v \<or> dyn_prog_FV \<pi> v)"

  lemma dyn_FV_finite: "finite (Collect (dyn_FV \<phi>))"
    proof (induct \<phi>)
      case (FOL x)
      then show ?case
        using fol_fv_syn_finite
        by auto
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        by simp
    next
      case (FOL_ALL x1a \<phi>)
      then show ?case
      proof -
        assume induction_hyp: "finite {a. dyn_FV \<phi> a}"
        have "{a. dyn_FV (\<bbbA> x1a . \<phi>) a} \<subseteq> {a. dyn_FV \<phi> a}"
          unfolding dyn_FV.simps
          by auto
        thus ?thesis
          using induction_hyp
          using infinite_super by blast
      qed
    next
      case (BOX \<pi> \<phi>)
      then show ?case
        unfolding dyn_FV.simps
        using prog_fv_finite
        using finite_Collect_disjI by blast
    qed

  text\<open>
  We also provide \emph{semantic} definitions of free and bound variables:
  \<close>

  fun dyn_fv_sem :: "('atom,'var,'prog) dyn_formula \<Rightarrow> 'var \<Rightarrow> bool" where
    "dyn_fv_sem \<phi> v = (\<exists> \<mu> \<omega>. (fol_equal_everywhere_but v \<mu> \<omega> \<and> (dyn_eval \<phi> \<mu> \<noteq> dyn_eval \<phi> \<omega>)))"

  fun dyn_prog_fv_sem :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    where "dyn_prog_fv_sem \<pi> v = (
            \<exists> \<mu> \<omega> \<nu>.
              ((fol_equal_everywhere_but v \<mu> \<omega>) \<and>
              (prog_eval \<pi> \<mu> \<nu>) \<and>
              (\<forall> \<upsilon>. (prog_eval \<pi> \<omega> \<upsilon>) \<longrightarrow> \<not>(fol_equal_everywhere_but v \<nu> \<upsilon>)))
  )"
  
  fun dyn_prog_bv_sem :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    where "dyn_prog_bv_sem \<pi> v = (
          \<exists> \<mu> \<omega>.
            ((prog_eval \<pi> \<mu> \<omega>) \<and> ((state_eval \<mu>) v \<noteq> (state_eval \<omega>) v))
  )"

  text\<open>We begin by showing some elementary properties:\<close>

  lemma dyn_differing_state_eval_due_to_vars:
    assumes "dyn_eval F \<mu> \<noteq> dyn_eval F \<omega>"
    shows "(\<exists> v. ((state_eval \<mu>) v \<noteq> (state_eval \<omega>) v))"
    using assms
    proof (induct F)
      case (FOL x)
      then show ?case
        unfolding dyn_eval.simps
        using fol_fv_sem_coincidence
        by (meson fol_states_agree_on_def)
    next
      case (AND F1 F2)
      then show ?case
      using dyn_eval.simps(2) by blast
    next
      case (NOT F)
      then show ?case
      using dyn_eval.simps(3) by blast
    next
      case (FOL_ALL x1a F)
      then show ?case
        using dyn_eval.simps(4)
        unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
        by fastforce
    next
      case (BOX x1a F)
      then show ?case
      proof -
      have "((\<forall> v. ((state_eval \<mu>) v = (state_eval \<omega>) v)) \<Longrightarrow>  dyn_eval F \<mu> = dyn_eval F \<omega>)"
        using fol_fv_sem_coincidence
        using prog_var_determinance
        using dyn_eval.simps
        using BOX.hyps by blast
      then show ?thesis using assms
        by (metis (mono_tags, lifting) BOX.prems dynamic_theory.dyn_eval.simps(5) dynamic_theory_axioms prog_var_determinance)
    qed
  qed

  lemma dyn_fv_sem_all_not_free: "( \<not>(dyn_fv_sem (\<bbbA> v . \<phi>) v  ) )"
    unfolding dyn_fv_sem.simps
    unfolding dyn_eval.simps
    unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
    apply simp
    by metis

  lemma dyn_fv_sem_all_intro:
    assumes "\<not> dyn_fv_sem \<phi> v"
    shows "\<not> dyn_fv_sem (\<bbbA> a . \<phi>) v"
    using assms
  proof -
    assume not_free_before: "\<not> dyn_fv_sem \<phi> v"

    have dir: "\<And>\<mu>' \<omega>'. fol_equal_everywhere_but v \<mu>' \<omega>' \<Longrightarrow>
              (\<forall>\<omega>1. fol_equal_everywhere_but a \<mu>' \<omega>1 \<longrightarrow> dyn_eval \<phi> \<omega>1) \<Longrightarrow>
              (\<forall>\<omega>2. fol_equal_everywhere_but a \<omega>' \<omega>2 \<longrightarrow> dyn_eval \<phi> \<omega>2)"
    proof -
      fix \<mu>' \<omega>'
      assume hv: "fol_equal_everywhere_but v \<mu>' \<omega>'"
         and hall: "\<forall>\<omega>1. fol_equal_everywhere_but a \<mu>' \<omega>1 \<longrightarrow> dyn_eval \<phi> \<omega>1"
      show "\<forall>\<omega>2. fol_equal_everywhere_but a \<omega>' \<omega>2 \<longrightarrow> dyn_eval \<phi> \<omega>2"
      proof (intro allI impI)
        fix \<omega>2
        assume ha: "fol_equal_everywhere_but a \<omega>' \<omega>2"
  
        obtain \<nu> where nu_cond:
          "(state_eval \<nu>) a = (state_eval \<omega>2) a \<and> fol_equal_everywhere_but a \<nu> \<mu>'"
          using state_space_convexity
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by (meson singleton_iff)
  
        have nu_a: "fol_equal_everywhere_but a \<mu>' \<nu>"
          using nu_cond
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by metis
  
        have nu_v: "fol_equal_everywhere_but v \<nu> \<omega>2"
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
        proof (intro allI impI)
          fix x
          assume x_neq_v: "x \<noteq> v"
          show "(state_eval \<nu>) x = (state_eval \<omega>2) x"
          proof (cases "x = a")
            case True
            then show ?thesis using nu_cond by simp
          next
            case False
            have e1: "(state_eval \<nu>) x = (state_eval \<mu>') x"
              using nu_cond False
              unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
              by metis
            have e2: "(state_eval \<mu>') x = (state_eval \<omega>') x"
              using hv x_neq_v
              unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
              by metis
            have e3: "(state_eval \<omega>') x = (state_eval \<omega>2) x"
              using ha False
              unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
              by metis
            show ?thesis using e1 e2 e3 by simp
          qed
        qed
  
        have nu_sat: "dyn_eval \<phi> \<nu>"
          using hall nu_a by blast
  
        show "dyn_eval \<phi> \<omega>2"
          using not_free_before nu_v nu_sat
          unfolding dyn_fv_sem.simps
          by blast
      qed
    qed

    show "\<not> dyn_fv_sem (\<bbbA> a . \<phi>) v"
    unfolding dyn_fv_sem.simps
    proof (simp, intro allI, intro impI)
      fix \<mu> \<omega>
      assume vmu: "fol_equal_everywhere_but v \<mu> \<omega>"
  
      have omv: "fol_equal_everywhere_but v \<omega> \<mu>"
        using vmu
        unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
        by auto
  
      show "(\<forall>\<omega>1. fol_equal_everywhere_but a \<mu> \<omega>1 \<longrightarrow> dyn_eval \<phi> \<omega>1) =
            (\<forall>\<omega>2. fol_equal_everywhere_but a \<omega> \<omega>2 \<longrightarrow> dyn_eval \<phi> \<omega>2)"
        using dir[OF vmu] dir[OF omv]
        by blast
    qed
  qed

  text\<open>
  Decomposition of the semantic free variables of a quantifier.
  Note that only \<open>\<subseteq>\<close> holds, not equality: quantification can remove a
  dependence altogether (\<open>\<bbbA> x . (v = x)\<close> is unsatisfiable and hence has no
  free variables at all, although \<open>v\<close> is free in the body).
  \<close>
  
  lemma dyn_fv_sem_all_elim:
    assumes "dyn_fv_sem (\<bbbA> x . \<phi>) v"
    shows "v \<noteq> x \<and> dyn_fv_sem \<phi> v"
    using assms dyn_fv_sem_all_not_free dyn_fv_sem_all_intro
    by blast
  
  lemma dyn_fv_sem_all_subset:
    "Collect (dyn_fv_sem (\<bbbA> x . \<phi>)) \<subseteq> Collect (dyn_fv_sem \<phi>) - {x}"
    using dyn_fv_sem_all_elim
    by blast
  
  lemma dyn_fv_sem_all_vec_subset:
    "Collect (dyn_fv_sem (\<bbbA>\<bbbA> vs . \<phi>)) \<subseteq> Collect (dyn_fv_sem \<phi>) - set vs"
  proof (induct vs)
    case Nil
    then show ?case
      unfolding FOR_ALL_VEC.simps(1)
      by simp
  next
    case (Cons a vs)
    have "Collect (dyn_fv_sem (\<bbbA>\<bbbA> (a # vs) . \<phi>))
            \<subseteq> Collect (dyn_fv_sem (\<bbbA>\<bbbA> vs . \<phi>)) - {a}"
      unfolding FOR_ALL_VEC.simps(2)
      by (rule dyn_fv_sem_all_subset)
    also have "... \<subseteq> (Collect (dyn_fv_sem \<phi>) - set vs) - {a}"
      using Cons.hyps by blast
    finally show ?case
      by (metis Diff_insert list.simps(15))
  qed
  
  lemma dyn_fv_sem_all_vec_mono:
    "Collect (dyn_fv_sem (\<bbbA>\<bbbA> vs . \<phi>)) \<subseteq> Collect (dyn_fv_sem \<phi>)"
    using dyn_fv_sem_all_vec_subset by blast

  lemma dyn_fv_sem_all_vec_disjoint:
    "Collect (dyn_fv_sem (\<bbbA>\<bbbA> vs . \<phi>)) \<inter> set vs = {}"
    using dyn_fv_sem_all_vec_subset by blast

  lemma dyn_fv_sem_not_eq:
  "dyn_fv_sem (\<rceil> \<phi>) v = dyn_fv_sem \<phi> v"
  by auto

  lemma dyn_fv_sem_and_elim:
    assumes "dyn_fv_sem (\<phi> and \<psi>) v"
    shows "dyn_fv_sem \<phi> v \<or> dyn_fv_sem \<psi> v"
  proof (rule ccontr)
    assume nofree: "\<not> (dyn_fv_sem \<phi> v \<or> dyn_fv_sem \<psi> v)"
    obtain \<mu> \<omega> where
          eq: "fol_equal_everywhere_but v \<mu> \<omega>"
      and diff: "dyn_eval (\<phi> and \<psi>) \<mu> \<noteq> dyn_eval (\<phi> and \<psi>) \<omega>"
      using assms[unfolded dyn_fv_sem.simps] by blast
    have "dyn_eval \<phi> \<mu> = dyn_eval \<phi> \<omega>"
     and "dyn_eval \<psi> \<mu> = dyn_eval \<psi> \<omega>"
      using nofree eq by auto
    then show False
      using diff by simp
  qed
  
  lemma dyn_fv_sem_imp_elim:
    assumes "dyn_fv_sem (\<phi> \<Rrightarrow> \<psi>) v"
    shows "dyn_fv_sem \<phi> v \<or> dyn_fv_sem \<psi> v"
    using assms
    unfolding IMP_def
    using dyn_fv_sem_and_elim dyn_fv_sem_not_eq
    by blast
  
  lemma dyn_fv_sem_or_elim:
    assumes "dyn_fv_sem (\<phi> or \<psi>) v"
    shows "dyn_fv_sem \<phi> v \<or> dyn_fv_sem \<psi> v"
    using assms
    unfolding OR_def
    using dyn_fv_sem_and_elim dyn_fv_sem_not_eq
    by blast
  
  lemma dyn_fv_sem_equiv_elim:
    assumes "dyn_fv_sem (\<phi> \<Lleftarrow>\<Rrightarrow> \<psi>) v"
    shows "dyn_fv_sem \<phi> v \<or> dyn_fv_sem \<psi> v"
    using assms
    unfolding EQUIV_def
    using dyn_fv_sem_and_elim dyn_fv_sem_imp_elim
    by blast
  
  text\<open>Set-level forms.\<close>
  
  lemma dyn_fv_sem_and_subset:
    "Collect (dyn_fv_sem (\<phi> and \<psi>)) \<subseteq> Collect (dyn_fv_sem \<phi>) \<union> Collect (dyn_fv_sem \<psi>)"
    using dyn_fv_sem_and_elim by blast
  
  lemma dyn_fv_sem_imp_subset:
    "Collect (dyn_fv_sem (\<phi> \<Rrightarrow> \<psi>)) \<subseteq> Collect (dyn_fv_sem \<phi>) \<union> Collect (dyn_fv_sem \<psi>)"
    using dyn_fv_sem_imp_elim by blast
  
  lemma dyn_fv_sem_not_subset:
    "Collect (dyn_fv_sem (\<rceil> \<phi>)) \<subseteq> Collect (dyn_fv_sem \<phi>)"
    using dyn_fv_sem_not_eq by blast

  lemma dyn_fv_sem_cong:
    assumes "\<And>\<mu>. dyn_eval \<phi> \<mu> = dyn_eval \<psi> \<mu>"
    shows "dyn_fv_sem \<phi> v = dyn_fv_sem \<psi> v"
    unfolding dyn_fv_sem.simps
    by (simp only: assms)
  
  lemma dyn_fv_sem_valid:
    assumes "\<Turnstile>[dyn_eval] \<phi>"
    shows "\<not> dyn_fv_sem \<phi> v"
    using assms
    unfolding dyn_fv_sem.simps
    by (simp add: theory_valid_def)

  lemma dyn_fv_sem_box_elim:
  assumes "dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk> \<phi>) v"
  shows "dyn_prog_fv_sem \<pi> v \<or> dyn_fv_sem \<phi> v"
  proof (rule ccontr)
    assume nofree: "\<not> (dyn_prog_fv_sem \<pi> v \<or> dyn_fv_sem \<phi> v)"
    then have nprog: "\<not> dyn_prog_fv_sem \<pi> v"
          and nfml: "\<not> dyn_fv_sem \<phi> v"
      by auto
  
    have sym: "\<And>\<mu> \<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<Longrightarrow> fol_equal_everywhere_but v \<omega> \<mu>"
      unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
      by auto
  
    have transfer: "\<And>\<mu> \<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<Longrightarrow>
                          dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<mu> \<Longrightarrow> dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<omega>"
    proof -
      fix \<mu> \<omega>
      assume eq: "fol_equal_everywhere_but v \<mu> \<omega>"
      assume box: "dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<mu>"
      show "dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<omega>"
      proof (unfold dyn_eval.simps(5), intro allI impI)
        fix \<upsilon>
        assume step: "prog_eval \<pi> \<omega> \<upsilon>"
        have eq_rev: "fol_equal_everywhere_but v \<omega> \<mu>"
          using sym[OF eq] .
        obtain \<upsilon>' where
              step': "prog_eval \<pi> \<mu> \<upsilon>'"
          and match: "fol_equal_everywhere_but v \<upsilon> \<upsilon>'"
          using nprog eq_rev step
          unfolding dyn_prog_fv_sem.simps
          by blast
        have "dyn_eval \<phi> \<upsilon>'"
          using box step' by simp
        then show "dyn_eval \<phi> \<upsilon>"
          using nfml match
          unfolding dyn_fv_sem.simps
          by blast
      qed
    qed
  
    obtain \<mu> \<omega> where
          eq: "fol_equal_everywhere_but v \<mu> \<omega>"
      and diff: "dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<mu> \<noteq> dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<omega>"
      using assms[unfolded dyn_fv_sem.simps] by blast
  
    show False
      using diff transfer[OF eq] transfer[OF sym[OF eq]]
      by blast
  qed
  
  lemma dyn_fv_sem_box_subset:
    "Collect (dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk> \<phi>)) \<subseteq> Collect (dyn_prog_fv_sem \<pi>) \<union> Collect (dyn_fv_sem \<phi>)"
    using dyn_fv_sem_box_elim by blast
  
  lemma dyn_fv_sem_box_disjoint:
    assumes "Collect (dyn_prog_fv_sem \<pi>) \<inter> S = {}"
        and "Collect (dyn_fv_sem \<phi>) \<inter> S = {}"
      shows "Collect (dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk> \<phi>)) \<inter> S = {}"
    using assms dyn_fv_sem_box_subset by blast

  subsubsection\<open>Syntactic Coincidence\<close>
  text\<open>
  Just as before in our first-order locale, we first prove the coincidence property for our syntactic
  overapproximation of the free variables.
  Subsequently, we prove coincidence w.r.t. the semantic definition.
  \<close>

  definition dyn_FV_mirror_state :: "('atom,'var,'prog) dyn_formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    where "dyn_FV_mirror_state F \<mu> \<omega> = fol_states_agree_on (dyn_FV F) \<mu> \<omega>"

  lemma dyn_FV_coincidence:
      "\<forall> \<mu> \<omega> . dyn_FV_mirror_state F \<mu> \<omega> \<longrightarrow> dyn_eval F \<mu> = dyn_eval F \<omega>"
    proof (induction F)
      case (FOL x)
      then show ?case 
        using fv_overapprox
        unfolding dyn_FV_mirror_state_def
        unfolding dyn_eval.simps
        unfolding dyn_FV.simps
        using fol_fv_syn_coincidence
        unfolding fol_fv_syn_mirror_state_def
        unfolding fol_states_agree_on_def
        by presburger
    next
      case (AND F1 F2)
      then show ?case
        unfolding dyn_FV_mirror_state_def
        unfolding fol_states_agree_on_def
        unfolding dyn_FV.simps
        unfolding dyn_eval.simps
        by blast
    next
      case (NOT F)
      then show ?case
        unfolding dyn_FV_mirror_state_def
        unfolding fol_states_agree_on_def
        unfolding dyn_FV.simps
        unfolding dyn_eval.simps
        by blast
    next
      case (FOL_ALL x F)
    then show ?case
    proof -
  
      show ?thesis
      proof (rule allI, rule allI, rule impI)
        fix \<mu>
        fix \<omega>
        assume omega_is_mirror: "dyn_FV_mirror_state (\<bbbA> x . F) \<mu> \<omega>"
        thus "dyn_eval (\<bbbA> x . F) \<mu> = dyn_eval (\<bbbA> x . F) \<omega>"
        proof -
          let ?VDiff = "fol_state_var_diff_set \<mu> \<omega>"
          let ?VDiffRelevant = "fol_state_var_diff_set_filter \<mu> \<omega> (dyn_FV F)"

          obtain S :: "'var set \<Rightarrow> 'state"
            where S_cond: "\<forall> V. \<forall> w . (((state_eval (S V)) w) = (if w \<in> V then ((state_eval \<omega>) w) else ((state_eval \<mu>) w)))"
            using state_space_convexity
            by metis

          have "(state_eval \<mu>) = (state_eval (S {}))"
            using S_cond
            by fastforce
    
          then have eq1: "dyn_eval (\<bbbA> x . F) \<mu> = dyn_eval (\<bbbA> x . F) (S {})"
            unfolding fol_eval.simps fol_equal_everywhere_but_def
            unfolding fol_states_agree_on_def
            by (metis dyn_differing_state_eval_due_to_vars)

    
          have eq2: "dyn_eval (\<bbbA> x . F) \<omega> = dyn_eval (\<bbbA> x . F) (S ?VDiff)"
            proof -
              have "(state_eval \<omega>) = (state_eval (S ?VDiff))"
                apply (simp add: fol_state_var_diff_set_def)
                using S_cond
                by auto
              then show "dyn_eval (\<bbbA> x . F) \<omega> = dyn_eval (\<bbbA> x . F) (S ?VDiff)"
                unfolding fol_state_var_diff_set_def dyn_eval.simps
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                by simp
            qed
    
            have VDiff_VDiffRelevant_mirrors: "dyn_FV_mirror_state F (S ?VDiff) (S ?VDiffRelevant)"
              using S_cond
              by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def dyn_FV_mirror_state_def fol_state_var_diff_set_def fol_state_var_diff_set_filter_def)
    
    
          have diff_eval_equal: "dyn_eval F (S ?VDiff) = dyn_eval F (S ?VDiffRelevant)"
            using VDiff_VDiffRelevant_mirrors
            using FOL_ALL by blast
    
          
          have dir1: "( dyn_eval (\<bbbA> x . F) (S ?VDiff)) ==> (dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant))"
          proof -
            assume vdiff_state_satisfies_formula: "( dyn_eval (\<bbbA> x . F) (S ?VDiff))"
            show "(dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant))"
            proof (simp, rule ccontr, simp)
              assume cex_state: "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set_filter \<mu> \<omega> (dyn_FV F))) \<omega>' \<and>
                \<not> dyn_eval F \<omega>'"
              obtain \<sigma> where sigma_constraints: "fol_equal_everywhere_but x (S ?VDiffRelevant) \<sigma> \<and>  \<not> dyn_eval F \<sigma>"
                using cex_state by blast

              obtain \<gamma> where \<gamma>_cond1: "(state_eval \<gamma>) x = (state_eval \<sigma>) x"
                         and \<gamma>_cond2: "\<forall> v . v \<noteq> x \<longrightarrow> (state_eval \<gamma>) v = (state_eval (S ?VDiff)) v"
                using state_space_convexity
                by (meson emptyE insert_iff)
      
              have sigma_gamma_mirror: "dyn_FV_mirror_state F \<sigma> \<gamma>"
                using \<gamma>_cond1 \<gamma>_cond2
                using VDiff_VDiffRelevant_mirrors
                using sigma_constraints
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                apply (simp add: fol_state_var_diff_set_def fol_state_var_diff_set_filter_def)
                by (smt (verit, ccfv_SIG) dyn_FV_mirror_state_def fol_states_agree_on_def)
      
              have gamma_sat: "dyn_eval F \<gamma>"
              proof -
                have "fol_equal_everywhere_but x (S ?VDiff) \<gamma>"
                  using \<gamma>_cond1 \<gamma>_cond2
                  using vdiff_state_satisfies_formula fol_equal_everywhere_but_def fol_states_agree_on_def
                  by fastforce          
      
                thus ?thesis
                  using vdiff_state_satisfies_formula
                  using fol_eval.simps(4)
                  by simp
              qed
      
              have sigma_unsat: "\<not> (dyn_eval F \<sigma>)"
                using sigma_constraints by auto
      
              have gamma_unsat: "\<not> (dyn_eval F \<gamma>)"
                using sigma_gamma_mirror
                using sigma_unsat
                using FOL_ALL by blast
    
              show False
                using gamma_sat gamma_unsat by auto
          qed
        qed
    
        have dir2: "(dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant)) \<Longrightarrow> ( dyn_eval (\<bbbA> x . F) (S ?VDiff))"
          proof -
            assume vdiff_state_satisfies_formula: "(dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant))"
            show "( dyn_eval (\<bbbA> x . F) (S ?VDiff))"
            proof (simp, rule ccontr, simp)
              assume cex_state: "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set \<mu> \<omega>)) \<omega>' \<and> \<not> dyn_eval F \<omega>'"
              obtain \<sigma> where sigma_constraints: "fol_equal_everywhere_but x (S (fol_state_var_diff_set \<mu> \<omega>)) \<sigma> \<and>  \<not> dyn_eval F \<sigma>"
                using cex_state by blast
              
              obtain \<gamma> where \<gamma>_cond1: "(state_eval \<gamma>) x = (state_eval \<sigma>) x"
                         and \<gamma>_cond2: "\<forall> v . v \<noteq> x \<longrightarrow> (state_eval \<gamma>) v = (state_eval (S ?VDiffRelevant)) v"
                using state_space_convexity
                by (meson emptyE insert_iff)
      
              have sigma_gamma_mirror: "dyn_FV_mirror_state F \<sigma> \<gamma>"
                using \<gamma>_cond1 \<gamma>_cond2
                using VDiff_VDiffRelevant_mirrors
                using sigma_constraints
                apply (simp add: fol_state_var_diff_set_def fol_state_var_diff_set_filter_def fol_equal_everywhere_but_def fol_states_agree_on_def)
                by (smt (verit, ccfv_SIG) dyn_FV_mirror_state_def fol_states_agree_on_def)
      
              have gamma_sat: "dyn_eval F \<gamma>"
              proof -
                have "fol_equal_everywhere_but x (S ?VDiffRelevant) \<gamma>"
                  using \<gamma>_cond1 \<gamma>_cond2
                  using vdiff_state_satisfies_formula fol_equal_everywhere_but_def fol_states_agree_on_def
                  by fastforce          
      
                thus ?thesis
                  using vdiff_state_satisfies_formula
                  using fol_eval.simps(4)
                  by force
              qed
      
              have sigma_unsat: "\<not> (dyn_eval F \<sigma>)"
                using sigma_constraints by auto
      
              have gamma_unsat: "\<not> (dyn_eval F \<gamma>)"
                using sigma_gamma_mirror
                using sigma_unsat
                using FOL_ALL by blast
    
              show False
                using gamma_sat gamma_unsat by auto
          qed
        qed
    
        have eq3: "(dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant)) = ( dyn_eval (\<bbbA> x . F) (S ?VDiff))"
          using dir1 dir2 by blast
    
        have relevantAlmostEmpty: "?VDiffRelevant \<subseteq> {x}"
          using omega_is_mirror
          unfolding dyn_FV_mirror_state_def fol_fv_syn_mirror_state_def fol_states_agree_on_def
          unfolding fol_state_var_diff_set_filter_def dyn_FV.simps
          using Collect_mono by fastforce

        then have "fol_equal_everywhere_but x (S {x}) (S ?VDiffRelevant)"
          using S_cond
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by auto
    
        then have eq41: "dyn_eval (\<bbbA> x . F) (S {x}) = dyn_eval (\<bbbA> x . F) (S ?VDiffRelevant)"
          unfolding dyn_eval.simps
          using S_cond
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by simp

        have "fol_equal_everywhere_but x (S {}) (S {x})"
          by (smt (verit, ccfv_threshold) S_cond \<open>state_eval \<mu> = state_eval (S {})\<close> fol_equal_everywhere_but_def fol_states_agree_on_def singletonD)
        then have eq42: "dyn_eval (\<bbbA> x . F) (S {}) = dyn_eval (\<bbbA> x . F) (S {x})"
          unfolding dyn_eval.simps
          using S_cond
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by simp
          
    
        show ?thesis
          using eq1 eq2 eq3 eq41 eq42 by blast
      qed
    qed
  qed
    next
      case (BOX x F)
      then show ?case
      proof -
        assume induction_hypothesis: "\<forall>\<mu> \<omega>. dyn_FV_mirror_state F \<mu> \<omega> \<longrightarrow> dyn_eval F \<mu> = dyn_eval F \<omega>"
        show ?thesis
          unfolding dyn_FV_mirror_state_def
          unfolding dyn_eval.simps
        proof (intro allI, intro impI)
          fix \<mu>
          fix \<omega>

          assume fv_agree: "fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<mu> \<omega>"
          then have fv_agree2: "fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<omega> \<mu>"
            unfolding fol_states_agree_on_def
            by presburger

          have prog_fv_of_fv_syn: "\<forall>v. dyn_prog_FV x v \<longrightarrow> dyn_FV (\<lbrakk> x \<rbrakk> F) v"
            unfolding dyn_FV.simps
            by blast

          have inner_eq: "dyn_eval F \<mu> = dyn_eval F \<omega>"
            using fv_agree
            using induction_hypothesis
            unfolding dyn_FV_mirror_state_def
            unfolding dyn_FV.simps
            by (simp add: BOX dyn_FV_mirror_state_def fol_states_agree_on_def)
              

          have dir1: "(\<forall>\<omega>. prog_eval x \<mu> \<omega> \<longrightarrow> dyn_eval F \<omega>) \<Longrightarrow> (\<forall>\<nu>. prog_eval x \<omega> \<nu> \<longrightarrow> dyn_eval F \<nu>)"
          proof (intro allI, intro impI)
            fix \<nu>
            assume mu_assumption: "(\<forall>\<omega>. prog_eval x \<mu> \<omega> \<longrightarrow> dyn_eval F \<omega>)"
            assume transition_assumption: "prog_eval x \<omega> \<nu>"
            then show "dyn_eval F \<nu>"
              using fv_agree2
              using mu_assumption
              using prog_fv_of_fv_syn
              using transition_assumption
              using prog_fv_overapprox[of x "(dyn_FV (\<lbrakk> x \<rbrakk> F))" \<omega> \<mu> \<nu>]
            proof simp
              assume "\<exists>\<upsilon>. prog_eval x \<mu> \<upsilon> \<and> fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<nu> \<upsilon>"
              then obtain \<upsilon>
                where "prog_eval x \<mu> \<upsilon>"
                  and \<mu>_\<upsilon>_agree: "fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<nu> \<upsilon>"
                by auto

              then have \<upsilon>_satisfies: "dyn_eval F \<upsilon>"
                using mu_assumption by blast

              then have "fol_states_agree_on (dyn_FV F) \<nu> \<upsilon>"
                using \<mu>_\<upsilon>_agree
                unfolding dyn_FV.simps
                unfolding fol_states_agree_on_def
                by blast

              thus "dyn_eval F \<nu>"
                using \<upsilon>_satisfies
                using induction_hypothesis
                using BOX dynamic_theory.dyn_FV_mirror_state_def dynamic_theory_axioms
                by metis
            qed
          qed

          have dir2: "(\<forall>\<nu>. prog_eval x \<omega> \<nu> \<longrightarrow> dyn_eval F \<nu>) \<Longrightarrow> (\<forall>\<omega>. prog_eval x \<mu> \<omega> \<longrightarrow> dyn_eval F \<omega>)"
          proof (intro allI, intro impI)
            fix \<omega>'
            assume omega_assumption: "(\<forall>\<nu>. prog_eval x \<omega> \<nu> \<longrightarrow> dyn_eval F \<nu>)"
            assume transition_assumption: "prog_eval x \<mu> \<omega>'"
            then show "dyn_eval F \<omega>'"
              using fv_agree
              using omega_assumption
              using prog_fv_of_fv_syn
              using transition_assumption
              using prog_fv_overapprox[of x "(dyn_FV (\<lbrakk> x \<rbrakk> F))" \<mu> \<omega> \<omega>']
            proof simp
              assume "\<exists>\<upsilon>. prog_eval x \<omega> \<upsilon> \<and> fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<omega>' \<upsilon>"
              then obtain \<upsilon>
                where "prog_eval x \<omega> \<upsilon>"
                  and \<mu>_\<upsilon>_agree: "fol_states_agree_on (dyn_FV (\<lbrakk> x \<rbrakk> F)) \<omega>' \<upsilon>"
                by auto

              then have \<upsilon>_satisfies: "dyn_eval F \<upsilon>"
                using omega_assumption by blast

              then have "fol_states_agree_on (dyn_FV F) \<omega>' \<upsilon>"
                using \<mu>_\<upsilon>_agree
                unfolding dyn_FV.simps
                unfolding fol_states_agree_on_def
                by blast

              thus "dyn_eval F \<omega>'"
                using \<upsilon>_satisfies
                using induction_hypothesis
                using BOX dynamic_theory.dyn_FV_mirror_state_def dynamic_theory_axioms by metis
            qed
          qed
          thus "(\<forall>\<omega>. prog_eval x \<mu> \<omega> \<longrightarrow> dyn_eval F \<omega>) = (\<forall>\<omega>'. prog_eval x \<omega> \<omega>' \<longrightarrow> dyn_eval F \<omega>')"
            using dir1
          by argo
      qed
    qed
  qed

  subsubsection\<open>Semantic Coincidence\<close>

  text\<open>
  To prove the semantic coincidence properties, we first show that the syntactic variant indeed
  overapproximates the semantic variant:
  \<close>

  lemma dyn_FV_fml_sound:
    "dyn_fv_sem F v \<Longrightarrow> dyn_FV F v"
    unfolding dyn_fv_sem.simps
    using dyn_FV_coincidence
    by (smt (verit, ccfv_SIG) dyn_FV_mirror_state_def fol_equal_everywhere_but_def fol_states_agree_on_def)

  lemma dyn_FV_prog_sound:
    "dyn_prog_fv_sem \<pi> v \<Longrightarrow> dyn_prog_FV \<pi> v"
    unfolding dyn_prog_fv_sem.simps
    using prog_fv_overapprox[of \<pi> "(dyn_prog_FV \<pi>)"]
    by (smt (verit, ccfv_SIG) dynamic_theory.prog_fv_overapprox dynamic_theory_axioms fol_equal_everywhere_but_def)
  
  text\<open>
  Based of \texttt{dyn\_FV\_fml\_sound} and \texttt{dyn\_FV\_prog\_sound},
  we can derive that the semantic free variable definitions induce finite sets:
  \<close>
  
  lemma dyn_FV_prog_finite:
    "finite (Collect (dyn_prog_fv_sem \<pi>))"
    using dyn_FV_prog_sound prog_fv_finite
    by (metis Collect_mono_iff finite_subset)

  lemma dyn_fv_sem_finite:
    "finite (Collect (dyn_fv_sem F))"
  proof -
    have "(Collect (dyn_fv_sem F)) \<subseteq> (Collect (dyn_FV F))"
      using dyn_FV_fml_sound
      by blast

    thus ?thesis
      using dyn_FV_finite
      using rev_finite_subset by blast
  qed

  text\<open>
  These results, along with the syntactic coincidence property, now allow us to prove coincidence
  w.r.t. the semantic definition (for dynamic formulas):
  \<close>

  lemma dyn_fv_sem_coincidence:
    assumes dyn_states_agree_on_free: "(fol_states_agree_on (dyn_fv_sem F) \<mu> \<omega>)"
      shows "(dyn_eval F \<mu> = dyn_eval F \<omega>)"
  proof -
    let ?synFV = "Collect (dyn_FV F)"

    have synFV_finite: "finite ?synFV"
      using dyn_FV_finite
      by blast

    obtain \<nu> where \<nu>_cond1: "\<forall> v . ((v \<in> ?synFV) \<longrightarrow> (state_eval \<omega>) v = (state_eval \<nu>) v)"
               and \<nu>_cond2: "\<forall> v . ((v \<notin> ?synFV) \<longrightarrow> (state_eval \<mu>) v = (state_eval \<nu>) v)"
      using state_space_convexity
      by metis

    have eq1: "dyn_eval F \<nu> = dyn_eval F \<omega>"
    proof -
      have "dyn_FV_mirror_state F \<nu> \<omega>"
        using \<nu>_cond1 \<nu>_cond2
        by (simp add: fol_states_agree_on_def dyn_FV_mirror_state_def)

      thus ?thesis
        using dyn_FV_coincidence
        by blast
    qed

    have eq5: "fol_states_agree_on (dyn_fv_sem F) \<nu> \<omega>"
      unfolding fol_states_agree_on_def
      using dyn_FV_fml_sound
      using \<nu>_cond1 \<nu>_cond2
      by auto

    let ?V = "fol_state_var_diff_set \<mu> \<nu>"

    have "?V \<subseteq> ?synFV"
      unfolding fol_state_var_diff_set_def
      using \<nu>_cond1 \<nu>_cond2
      by (simp, force)

    then have V_finite: "finite ?V"
      using synFV_finite
      using rev_finite_subset by blast

    obtain S :: "'var set \<Rightarrow> 'state"
            where S_cond: "\<forall> V. \<forall> w . (((state_eval (S V)) w) = (if w \<in> V then ((state_eval \<nu>) w) else ((state_eval \<mu>) w)))"
            using state_space_convexity
            by metis

    have eq3: "(state_eval \<mu>) = (state_eval (S {}))"
      using S_cond
      by auto

    have eq2: "dyn_eval F (S ?V) = dyn_eval F \<nu>"
      unfolding fol_state_var_diff_set_def
      using dyn_FV_coincidence
      unfolding dyn_FV_mirror_state_def
      unfolding fol_states_agree_on_def
      using S_cond \<nu>_cond1 \<nu>_cond2
      by simp

    have inductive_argument: "\<And> x Vold . x \<in> ?V \<Longrightarrow>
          dyn_eval F (S {}) = dyn_eval F (S Vold) \<Longrightarrow>
          dyn_eval F (S {}) = dyn_eval F (S (insert x Vold))"
    proof -
      fix x
      fix Vold
      show "x \<in> ?V \<Longrightarrow>
          dyn_eval F (S {}) = dyn_eval F (S Vold) \<Longrightarrow>
          dyn_eval F (S {}) = dyn_eval F (S (insert x Vold))"
    proof (cases "dyn_fv_sem F x")
      assume x_in_diff: "x \<in> ?V"
      case True
      then show ?thesis
      proof -
        (* Variable cannot be part of fol_fv_sem because states must agree on those *)
        have "dyn_eval F (S {}) = dyn_eval F (S (insert x Vold))"
        proof (rule ccontr)
          have "(state_eval \<mu>) x \<noteq> (state_eval \<nu>) x"
            using x_in_diff
            unfolding fol_state_var_diff_set_def
            by blast

          also have "(state_eval \<mu>) x = (state_eval \<nu>) x"
            using dyn_states_agree_on_free
            unfolding fol_states_agree_on_def
            using True
            using \<nu>_cond1 \<nu>_cond2
            by metis
            
          thus False
            using calculation by blast
        qed

        thus ?thesis by simp
      qed
    next
      assume prev_equal: "dyn_eval F (S {}) = dyn_eval F (S Vold)"
        case False
        then show ?thesis 
        proof -
          assume x_not_free: "\<not> dyn_fv_sem F x"
          have "dyn_eval F (S Vold) = dyn_eval F (S (insert x Vold))"
          proof (rule ccontr)
            assume states_unequal_now: "\<not> ?thesis"
            then have "fol_equal_everywhere_but x (S Vold) (S (insert x Vold))"
              by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def S_cond)

            then have "dyn_fv_sem F x"
              apply simp
              apply (rule_tac x="(S Vold)" in exI)
              apply (rule_tac x="(S (insert x Vold))" in exI)
              using states_unequal_now by blast

            thus False
              using x_not_free
              by simp
          qed
          thus ?thesis
            using prev_equal
            by blast
        qed
      qed
    qed

    
            

      have "\<And> VarSet . VarSet \<subseteq> ?V \<Longrightarrow> dyn_eval F (S {}) = dyn_eval F (S VarSet)"
      proof -
        fix VarSet
        show "VarSet \<subseteq> ?V \<Longrightarrow> dyn_eval F (S {}) = dyn_eval F (S VarSet)"
        proof -
          assume "VarSet \<subseteq> ?V"
          have "finite VarSet"
            using V_finite
            using \<open>VarSet \<subseteq> fol_state_var_diff_set \<mu> \<nu>\<close> finite_subset by blast
  
          thus "VarSet \<subseteq> ?V \<Longrightarrow> dyn_eval F (S {}) = dyn_eval F (S VarSet)"
          proof (induction VarSet rule: finite_induct)
            case empty
              then show ?case by simp
            next
            case (insert x Vold)
              have "dyn_eval F (S {}) = dyn_eval F (S Vold)"
                using insert.IH insert.prems by blast
  
              also have "x \<in> ?V"
                using insert.prems by fastforce
  
              thus "dyn_eval F (S {}) = dyn_eval F (S (insert x Vold))"
                using inductive_argument[of "x" "Vold"] \<open>x \<in> ?V\<close> \<open>dyn_eval F (S {}) = dyn_eval F (S Vold)\<close>
                by fastforce
            qed
          qed
        qed

      then have eq4: "dyn_eval F (S {}) = dyn_eval F (S ?V)" 
        by blast

      thus ?thesis
        using eq1 eq2 eq3 eq4 eq5
        by (metis dyn_differing_state_eval_due_to_vars)
    qed

  text\<open>
  We can furthermore show that the set of semantically free variables
  is the smallest set with this property:
  \<close>

  lemma dyn_fv_sem_coincidence_smallest:
    fixes FVTest :: "('atom, 'var, 'prog) dyn_formula \<Rightarrow> 'var \<Rightarrow> bool"
    assumes FVTest_finite: "finite (Collect (FVTest F))"
    assumes semFVSmaller: "card (Collect (FVTest F)) < card (Collect (dyn_fv_sem F))"
    shows "\<exists> \<mu> \<omega> . ( (fol_states_agree_on (FVTest F) \<mu> \<omega>) \<and> dyn_eval F \<mu> \<noteq> dyn_eval F \<omega>)"
  proof (rule ccontr, simp)
    assume fv_complete: "\<forall>\<mu> \<omega>. fol_states_agree_on (FVTest F) \<mu> \<omega> \<longrightarrow> dyn_eval F \<mu> = dyn_eval F \<omega>"

    have "(Collect (FVTest F)) \<subseteq> (Collect (dyn_fv_sem F))"
    proof (rule ccontr)
      assume "\<not> ((Collect (FVTest F)) \<subseteq> (Collect (dyn_fv_sem F)))"

      obtain w where w_cond: "w \<notin> (Collect (FVTest F)) \<and> w \<in> (Collect (dyn_fv_sem F))"
        using semFVSmaller
        by (meson FVTest_finite card_mono leD subsetI)

      then obtain s 
        where w_may_differ: "fol_equal_everywhere_but w (fst s) (snd s)"
          and F_eval_unequal: "(dyn_eval F (fst s) \<noteq> dyn_eval F (snd s))"
        unfolding dyn_fv_sem.simps
        by (smt (verit, best) fst_conv mem_Collect_eq snd_conv)

      have F_eval_equal: "dyn_eval F (fst s) = dyn_eval F (snd s)"
        using w_may_differ
        using fv_complete
        using w_cond
        unfolding fol_equal_everywhere_but_def
        unfolding fol_states_agree_on_def
        by (metis CollectI)
      
      show False
        using F_eval_equal F_eval_unequal
        by blast
    qed

    then have semFVSubset: "(Collect (FVTest F)) \<subset> Collect (dyn_fv_sem F)"
      using semFVSmaller
      by force
      
    then have "\<exists> \<mu> \<omega> . ( (fol_states_agree_on (FVTest F) \<mu> \<omega>) \<and> dyn_eval F \<mu> \<noteq> dyn_eval F \<omega>)"
    proof -
      obtain w :: 'var where w_condition: "\<not>(FVTest F w) \<and> (dyn_fv_sem F w)" using semFVSubset by blast
    
      obtain \<mu> \<omega> where agree: "fol_states_agree_on (\<lambda>wa. wa \<noteq> w) \<mu> \<omega>"
                 and eval_diff: "dyn_eval F \<mu> = (\<not> dyn_eval F \<omega>)"
        using w_condition fol_equal_everywhere_but_def by auto
    
      then have "(fol_states_agree_on (FVTest F) \<mu> \<omega>)"
        using agree semFVSubset w_condition
        by (metis (mono_tags, lifting) fol_states_agree_on_def)
    
      thus ?thesis
        using eval_diff
        by blast
    qed
        
    thus "False"
      using fv_complete
      by blast
  qed

  text\<open>
  We can then prove the coincidence property for the definition of semantically
  free variables in a program.
  In contrast to the semantic coincidence property for formulas,
  we must assume that the considered states only differ on a finite set of
  variables in this instance.
  We can also establish a minimality property in this instance.
  \<close>
  
  lemma dyn_prog_fv_sem_coincidence:
    fixes \<mu>1 :: "'state"
      and \<mu>2 :: "'state"
      and \<omega>1 :: "'state"
      and \<omega>2 :: "'state"
      and \<pi> :: "'prog"
      and relevant_vars :: "'var \<Rightarrow> bool"
      and eq_vars :: "'var \<Rightarrow> bool"
    assumes mu_omega_transition: "prog_eval \<pi> \<mu>1 \<omega>1"
        and prog_fv_equal: "fol_states_agree_on eq_vars \<mu>1 \<mu>2"
        and nonrelevant_equal: "fol_states_agree_on (\<lambda> v . \<not> relevant_vars v) \<mu>1 \<mu>2"
        and relevant_finite: "finite (Collect relevant_vars)"
        and eq_vars_superset: "\<forall> v . dyn_prog_fv_sem \<pi> v \<longrightarrow> eq_vars v"
      shows "(\<exists> \<omega>2 . (prog_eval \<pi> \<mu>2 \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2) )"
  proof -
    have prog_fv_equal: "fol_states_agree_on (dyn_prog_fv_sem \<pi>) \<mu>1 \<mu>2"
      using eq_vars_superset
      using prog_fv_equal
      unfolding fol_states_agree_on_def
      by blast

    let ?V = "fol_state_var_diff_set \<mu>1 \<mu>2"
  
    have V_finite: "finite ?V"
      using prog_fv_equal nonrelevant_equal relevant_finite
      unfolding fol_states_agree_on_def
      unfolding fol_state_var_diff_set_def
      apply (simp add: dyn_sem)
      by (metis (mono_tags, lifting) Collect_mono finite_subset)

    obtain S :: "'var set \<Rightarrow> 'state"
            where S_cond: "\<forall> V. \<forall> w . (((state_eval (S V)) w) = (if w \<in> V then ((state_eval \<mu>2) w) else ((state_eval \<mu>1) w)))"
            using state_space_convexity
            by metis
  
    have "\<And> VarSet . VarSet \<subseteq> ?V \<Longrightarrow> (\<exists> \<omega>2 . (prog_eval \<pi> (S VarSet) \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2) )"
    proof -
      fix VarSet
  
      show "VarSet \<subseteq> ?V \<Longrightarrow> (\<exists> \<omega>2 . (prog_eval \<pi> (S VarSet) \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2) )"
      proof -
        assume "VarSet \<subseteq> ?V"
        then have "finite VarSet"
          using V_finite
          using finite_subset by blast
  
        thus "VarSet \<subseteq> ?V \<Longrightarrow> (\<exists> \<omega>2 . (prog_eval \<pi> (S VarSet) \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2) )"
        proof (induct VarSet rule: finite_induct)
          case empty
          then show ?case
          proof -
            have "(state_eval (S {})) = (state_eval \<mu>1)"
              using S_cond
              by auto
        
            thus ?thesis
              using mu_omega_transition
              unfolding fol_states_agree_on_def
              apply (rule_tac x="\<omega>1" in exI, simp)
              by (metis prog_var_determinance)
          qed
        next
          case (insert x F)
          then show ?case
          proof (simp)
            have "\<exists>\<omega>2. prog_eval \<pi> (S F) \<omega>2 \<and> fol_states_agree_on eq_vars \<omega>1 \<omega>2"
              using insert.hyps(3) insert.prems by blast
            
            then obtain \<omega>2_old
              where omega2_old_transition: "prog_eval \<pi> (S F) \<omega>2_old"
                and omega2_old_agrees: "fol_states_agree_on eq_vars \<omega>1 \<omega>2_old"
              by blast
  
            assume "x \<in> fol_state_var_diff_set \<mu>1 \<mu>2 \<and> F \<subseteq> fol_state_var_diff_set \<mu>1 \<mu>2"
  
            then have "x \<in> ?V"
              by (simp)
  
            then have x_not_prog_fv: "\<not> eq_vars x"
              using assms
              by (smt (verit, best) fol_state_var_diff_set_def fol_states_agree_on_def mem_Collect_eq)
  
            have equal_everywhere_but_x_pre: "fol_equal_everywhere_but x (S F) (S (insert x F))"
              unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
              using S_cond by auto
  
            then have "(\<exists>\<upsilon>. prog_eval \<pi> (S (insert x F)) \<upsilon> \<and> fol_equal_everywhere_but x \<omega>2_old \<upsilon>)"
              using omega2_old_transition
              using x_not_prog_fv
              unfolding dyn_prog_fv_sem.simps
              unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
            proof (cases "dyn_prog_fv_sem \<pi> x")
              case True
              then show "\<exists>\<upsilon>. prog_eval \<pi> (S (insert x F)) \<upsilon> \<and> (\<forall>v. v \<noteq> x \<longrightarrow> state_eval \<omega>2_old v = state_eval \<upsilon> v)"
                using S_cond
                using eq_vars_superset x_not_prog_fv by blast
            next
              case False
              then show "\<exists>\<upsilon>. prog_eval \<pi> (S (insert x F)) \<upsilon> \<and> (\<forall>v. v \<noteq> x \<longrightarrow> state_eval \<omega>2_old v = state_eval \<upsilon> v)"
                using S_cond
                unfolding dyn_prog_fv_sem.simps
                using equal_everywhere_but_x_pre
                using omega2_old_transition
                by (simp,smt (verit, best) fol_equal_everywhere_but_def fol_states_agree_on_def)
            qed
  
            then obtain \<omega>2_new
              where omega2_transition: "prog_eval \<pi> (S (insert x F)) \<omega>2_new"
                and "(fol_equal_everywhere_but x \<omega>2_old \<omega>2_new)"
              by blast
  
            then have "fol_states_agree_on eq_vars \<omega>1 \<omega>2_new"
              using omega2_old_agrees
              using x_not_prog_fv
              unfolding fol_equal_everywhere_but_def
              unfolding fol_states_agree_on_def
              by metis
  
            thus "\<exists>\<omega>2. prog_eval \<pi> (S (insert x F)) \<omega>2 \<and> fol_states_agree_on eq_vars \<omega>1 \<omega>2 "
              using omega2_transition
              unfolding dyn_prog_fv_sem.simps
              by blast
          qed
        qed
      qed
    qed
  
    then have "\<exists> \<omega>2 . (prog_eval \<pi> (S ?V) \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2)"
      by auto
  
    also have "(state_eval (S ?V)) = (state_eval \<mu>2)"
      unfolding fol_state_var_diff_set_def
      using S_cond by fastforce
  
    have "\<exists> \<omega>2 . (prog_eval \<pi> \<mu>2 \<omega>2) \<and> (fol_states_agree_on eq_vars \<omega>1 \<omega>2)"
      using calculation
      by (metis \<open>state_eval (S (fol_state_var_diff_set \<mu>1 \<mu>2)) = state_eval \<mu>2\<close> prog_var_determinance)
    thus ?thesis
      by blast
  qed

  lemma dyn_prog_fv_sem_coincidence_smallest:
    fixes \<pi> :: "'prog"
      and eq_vars :: "'var \<Rightarrow> bool"
    assumes eq_finite: "finite (Collect eq_vars)"
        and eq_smaller: "card (Collect eq_vars ) < card (Collect (dyn_prog_fv_sem \<pi>))"
      shows "\<exists> \<mu>1 \<mu>2 \<omega>1 V . (
                prog_eval \<pi> \<mu>1 \<omega>1 \<and>
                (\<forall> v . (eq_vars v) \<longrightarrow> (V v)) \<and>
                fol_states_agree_on V \<mu>1 \<mu>2 \<and>
                (\<forall> \<omega>2 . (prog_eval \<pi> \<mu>2 \<omega>2) \<longrightarrow> \<not> (fol_states_agree_on V \<omega>1 \<omega>2) )
            )"
  proof -
    obtain v where v_cond: "v \<notin> (Collect eq_vars) \<and> v \<in> (Collect (dyn_prog_fv_sem \<pi>))"
      using eq_smaller
      using eq_finite
      using dyn_FV_prog_finite
      by (meson card_mono leD subsetI)
    then have v_in_fv: "dyn_prog_fv_sem \<pi> v"
      by blast
    have v_not_in_eq: "\<not> eq_vars v"
      using v_cond
      by blast
    obtain \<mu> \<omega> \<nu> where mu_omega_nu_cond: "fol_equal_everywhere_but v \<mu> \<omega> \<and>
       prog_eval \<pi> \<mu> \<nu> \<and>
       (\<forall>\<upsilon>. prog_eval \<pi> \<omega> \<upsilon> \<longrightarrow> \<not> fol_equal_everywhere_but v \<nu> \<upsilon>)"
      using v_in_fv
      unfolding dyn_prog_fv_sem.simps
      by blast

    let ?V = "\<lambda> w . (eq_vars w) \<or> (w \<noteq> v \<and> (\<exists> \<upsilon> . prog_eval \<pi> \<omega> \<upsilon> \<and> ((state_eval \<nu> w)\<noteq>(state_eval \<upsilon> w))))"

    show ?thesis
      using mu_omega_nu_cond
    proof (rule_tac exI[of _ \<mu>], rule_tac exI[of _ \<omega>], rule_tac exI[of _ \<nu>], rule_tac exI[of _ ?V], intro conjI)
      assume all_assms: "fol_equal_everywhere_but v \<mu> \<omega> \<and>
                          prog_eval \<pi> \<mu> \<nu> \<and>
                          (\<forall>\<upsilon>. prog_eval \<pi> \<omega> \<upsilon> \<longrightarrow> \<not> fol_equal_everywhere_but v \<nu> \<upsilon>)"
      show "prog_eval \<pi> \<mu> \<nu>"
        using all_assms by simp
      show "\<forall>va. (eq_vars va) \<longrightarrow> ?V va"
        by simp
      show "fol_states_agree_on ?V \<mu> \<omega>"
        using all_assms
        using v_not_in_eq
        using fol_equal_everywhere_but_def fol_states_agree_on_def by fastforce

      show "(\<forall>\<upsilon>. prog_eval \<pi> \<omega> \<upsilon> \<longrightarrow> \<not> fol_states_agree_on ?V \<nu> \<upsilon>)"
      proof (intro allI, intro impI)
        fix \<upsilon>
        assume trans_assm: "prog_eval \<pi> \<omega> \<upsilon>"
        then have "\<not> fol_equal_everywhere_but v \<nu> \<upsilon>"
          using all_assms by blast
        then obtain w where w_cond: "w \<noteq> v \<and> (state_eval \<nu> w) \<noteq> (state_eval \<upsilon> w)"
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by blast
        then have "?V w"
          using trans_assm
          by blast

        then show "\<not> fol_states_agree_on ?V \<nu> \<upsilon>"
          using w_cond
          unfolding fol_states_agree_on_def by auto
      qed
    qed
  qed

  subsubsection\<open>Semantic Bounded Effect\<close>
  text\<open>
  In addition to the properties shown above,
  we also prove that the the effect of program execution is limited to
  semantically bound variables. We also establish a minimality property
  for this property.
  \<close>

  lemma dyn_prog_bv_sem_bounded:
    "\<forall> \<mu> \<omega> \<pi>. (prog_eval \<pi> \<mu> \<omega>) \<longrightarrow> fol_states_agree_on (\<lambda> v . \<not> dyn_prog_bv_sem \<pi> v) \<mu> \<omega>"
  proof (intro allI, intro impI)
    fix \<mu>
    fix \<omega>
    fix \<pi>
    assume in_eval_relation: "prog_eval \<pi> \<mu> \<omega>"

    then show "fol_states_agree_on (\<lambda> v . \<not> dyn_prog_bv_sem \<pi> v) \<mu> \<omega>"
      unfolding fol_states_agree_on_def
      unfolding dyn_prog_bv_sem.simps
      by blast
  qed

lemma dyn_prog_bv_sem_bounded_smallest1:
  fixes bv_smaller :: "'var \<Rightarrow> bool"
    and \<pi> :: "'prog"
  assumes "(((Collect bv_smaller) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) \<noteq> (Collect (dyn_prog_bv_sem \<pi>)))"
    shows "\<exists> \<mu> \<omega>. (prog_eval \<pi> \<mu> \<omega>) \<and> \<not>fol_states_agree_on (\<lambda> v . \<not> bv_smaller v) \<mu> \<omega>"
  using assms
proof -
  fix \<pi>
  assume "(((Collect bv_smaller) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) \<noteq> (Collect (dyn_prog_bv_sem \<pi>)))"
  then obtain v where "v \<notin> (Collect bv_smaller) \<and> v \<in> (Collect (dyn_prog_bv_sem \<pi>))"
    by blast
  then have "\<not> bv_smaller v \<and> dyn_prog_bv_sem \<pi> v"
    by blast
  thus ?thesis
    unfolding dyn_prog_bv_sem.simps
    using assms fol_states_agree_on_def by fastforce
qed

lemma dyn_prog_bv_sem_bounded_smallest2:
  fixes bv_smaller :: "'var \<Rightarrow> bool"
    and \<pi> :: "'prog"
  assumes "finite (Collect bv_smaller)"
      and "finite (Collect (dyn_prog_bv_sem \<pi>))"
      and "card (Collect bv_smaller) < card (Collect (dyn_prog_bv_sem \<pi>))"
    shows "\<exists> \<mu> \<omega>. (prog_eval \<pi> \<mu> \<omega>) \<and> \<not>fol_states_agree_on (\<lambda> v . \<not> bv_smaller v) \<mu> \<omega>"
  using assms
proof -
  fix \<pi>
  assume fin1: "finite (Collect bv_smaller)"
  assume fin2: "finite (Collect (dyn_prog_bv_sem \<pi>))"
  assume "card (Collect bv_smaller) < card (Collect (dyn_prog_bv_sem \<pi>))"
  then obtain v where "v \<notin> (Collect bv_smaller) \<and> v \<in> (Collect (dyn_prog_bv_sem \<pi>))"
    using fin1 fin2
    by (meson card_mono leD subsetI)
  then have "\<not> bv_smaller v \<and> dyn_prog_bv_sem \<pi> v"
    by blast
  thus ?thesis
    unfolding dyn_prog_bv_sem.simps
    by (smt (verit) Collect_mono_iff assms(3) card_mono dyn_prog_bv_sem.simps fin1 folCore.fol_states_agree_on_def folCore_axioms leD)
qed

subsection\<open>First-Order Axioms\<close>
text\<open>We again prove a number of first-order axioms and proof-rules\<close>

lemma dyn_hilbert_mp:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
    and \<psi> :: "('atom, 'var, 'prog) dyn_formula"
  assumes "\<Turnstile>[dyn_eval] \<phi>"
      and "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi>"
  shows "\<Turnstile>[dyn_eval] \<psi>"
  using assms
  unfolding fol_valid_def
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_1: "\<Turnstile>[dyn_eval]  \<phi> \<Rrightarrow> \<phi>"
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_2: "\<Turnstile>[dyn_eval]  (\<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<phi>))"
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_3: "\<Turnstile>[dyn_eval] (\<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<xi>)) \<Rrightarrow> ((\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<phi> \<Rrightarrow> \<xi>))"
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_4: "\<Turnstile>[dyn_eval] (\<rceil>\<phi> \<Rrightarrow> \<rceil>\<psi>) \<Rrightarrow> (\<psi> \<Rrightarrow> \<phi>)"
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_6: "\<Turnstile>[dyn_eval] (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ( (\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> v . \<psi>) )"
  by (auto simp add: dyn_sem)

lemma dyn_prop_axiom_rosser1: "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<phi> and \<phi>)"
  by (auto simp add: dyn_sem)

lemma dyn_prop_axiom_rosser2: "\<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<phi>"
  by (auto simp add: dyn_sem)

lemma dyn_prop_axiom_rosser3: "\<Turnstile>[dyn_eval] (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<rceil>(\<psi> and \<xi>) \<Rrightarrow> \<rceil>(\<xi> and \<phi>))"
  by (auto simp add: dyn_sem)

lemma dyn_fol_axiom_univ_elim: "\<Turnstile>[dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
  apply (auto simp add: dyn_sem)
  using fol_equal_everywhere_but_def fol_states_agree_on_def by blast

lemma dyn_hilbert_axiom_7:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
  assumes fv_assumption: "\<not> dyn_fv_sem \<phi> v"
  shows "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA> v . \<phi>"
proof ((simp add: dyn_sem), intro allI, intro impI)
  fix \<mu>
  assume phi_satisfied: "dyn_eval \<phi> \<mu>"
  
  show "\<forall>\<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<longrightarrow> dyn_eval \<phi> \<omega>"
  proof (rule ccontr, simp)
    assume "\<exists>\<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<and> \<not> dyn_eval \<phi> \<omega>"

    then obtain \<omega> where almost_equal: "fol_equal_everywhere_but v \<mu> \<omega>"
                    and not_satisfied: "\<not> dyn_eval \<phi> \<omega>" by blast

    have "dyn_eval \<phi> \<omega>"
      using phi_satisfied
      using almost_equal
      using fv_assumption
      by(simp add: fol_equal_everywhere_but_def)
    
    thus False
      using not_satisfied by simp
  qed
qed

lemma dyn_hilbert_axiom_conj_i:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
    and \<psi> :: "('atom, 'var, 'prog) dyn_formula"
  shows "\<Turnstile>[dyn_eval]  \<phi> \<Rrightarrow> \<psi> \<Rrightarrow> (\<phi> and \<psi>)"
  unfolding theory_valid_def
  by (auto simp add: dyn_sem)

lemma dyn_hilbert_axiom_conj_e1:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
    and \<psi> :: "('atom, 'var, 'prog) dyn_formula"
  shows "\<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<phi>"
  unfolding theory_valid_def
  by (auto simp add: dyn_sem)


lemma dyn_hilbert_axiom_conj_e2:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
    and \<psi> :: "('atom, 'var, 'prog) dyn_formula"
  shows "\<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<psi>"
  unfolding theory_valid_def
  by (auto simp add: dyn_sem)

lemma dyn_axiom_P1:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<phi> and \<phi>)"
  by (auto simp add: dyn_sem)


lemma dyn_axiom_P2:
  "\<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<phi>"
  by (auto simp add: dyn_sem)

lemma dyn_axiom_P3:
  "\<Turnstile>[dyn_eval] (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<rceil>(\<phi> and \<xi>) \<Rrightarrow> \<rceil>(\<xi> and \<phi>))"
  by (auto simp add: dyn_sem)

lemma dyn_axiom_A:
  fixes \<phi> :: "('atom, 'var, 'prog) dyn_formula"
    and v :: "'var"
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[dyn_eval] \<bbbA> v . \<phi>"
  using assms
  unfolding theory_valid_def
  unfolding dyn_eval.simps
  by simp

lemma dyn_axiom_F1:
  "\<Turnstile>[dyn_eval] (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ( (\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> v . \<psi>) )"
  using dyn_hilbert_axiom_6
  by simp

lemma dyn_axiom_F2:
  assumes fv_assumption: "\<not> dyn_fv_sem \<phi> v"
  shows "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA> v . \<phi>"
  using dyn_hilbert_axiom_7 assms
  by simp

lemma dyn_axiom_F3:
  shows "\<Turnstile>[dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
  apply (auto simp add: dyn_sem)
  by (metis folCore.fol_equal_everywhere_but_def folCore_axioms
      fol_states_agree_on_def)

lemma dyn_hilbert_imp_transitive:
  "\<Turnstile>[dyn_eval] ((\<phi>1 \<Rrightarrow> \<phi>2) \<Rrightarrow> (\<phi>2 \<Rrightarrow> \<phi>3) \<Rrightarrow> (\<phi>1 \<Rrightarrow> \<phi>3))"
  by (auto simp add: dyn_sem)

subsection\<open>Dynamic Theory Axioms\<close>
text\<open>
In addition, we prove four dynamic theory axioms and proof rules
that hold irrespective of the concrete instantiation of a dynamic theory.
\<close>

lemma dyn_axiom_G:
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  fixes \<pi> :: "'prog"
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi>"
  using assms
  unfolding theory_valid_def
  unfolding dyn_eval.simps
  by blast

lemma dyn_axiom_K:
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
    and \<psi> :: "('atom,'var,'prog) dyn_formula"
    and \<pi> :: "'prog"
  shows "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> ((\<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>))"
  unfolding theory_valid_def
  by (auto simp add: dyn_sem)

end
end