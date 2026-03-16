section\<open>Elementary Program Rewriting\<close>
text\<open>
\label{sec:dl-rewriting}
In addition to the calculus rules established so far,
it is also possible to reason about programs in the heterogeneous dynamic
logic framework via \emph{program rewriting}
in the style of Kleene Algebra with Tests.

To this end, we first define notions of program refinement and equivalence
which we will later use to introduce various (heterogeneous) rewriting rules.
The objective is hence not to reason about a program's equivalence or
refinement relation at the level of \emph{semantics}, but instead to leverage
\emph{syntactic} rewriting rules to prove equivalence/refinement relations
which can then be leveraged for dynamic theory proofs.
\<close>

subsection\<open>Basic Definitions\<close>

theory DLRewriting
  imports
    Main
    "DynamicLogic"
begin

context dynamic_theory
begin

definition progRefine :: "'prog \<Rightarrow> 'prog \<Rightarrow> bool"
  where "progRefine \<alpha> \<beta> = (\<forall> \<sigma> \<mu> . ((prog_eval \<alpha> \<sigma> \<mu>) \<longrightarrow> (prog_eval \<beta> \<sigma> \<mu>)))"

definition progEquiv :: "'prog \<Rightarrow> 'prog \<Rightarrow> bool"
  where "progEquiv \<alpha> \<beta> = ((progRefine \<alpha> \<beta>) \<and> (progRefine \<beta> \<alpha>))"

lemma progEquivSimplification:
  "progEquiv \<alpha> \<beta> = ((prog_eval \<alpha>) = (prog_eval \<beta>))"
  unfolding progEquiv_def progRefine_def
  by fastforce

notation progRefine ("_ \<le> _" [190, 190] 190)

notation progEquiv ("_ \<rightleftharpoons> _ " [200, 200] 200)

lemma progEquiv_refl:
  "reflp progEquiv"
  unfolding reflp_def
  unfolding progEquiv_def progRefine_def
  by simp

lemma progEquiv_symp:
  "symp progEquiv"
  unfolding symp_def
  unfolding progEquiv_def progRefine_def
  by simp

lemma progEquiv_transp:
  "transp progEquiv"
  unfolding transp_def
  unfolding progEquiv_def progRefine_def
  by blast

theorem progEquiv_equivp:
  "equivp progEquiv"
  using equivpI[of progEquiv]
  using progEquiv_refl progEquiv_symp progEquiv_transp
  by simp

declare progEquiv_equivp[quot_equiv]

lemma progEquiv_transp_expl:
  assumes "\<alpha> \<rightleftharpoons> \<beta>" and "\<beta> \<rightleftharpoons> \<gamma>"
  shows "\<alpha> \<rightleftharpoons> \<gamma>"
  using assms unfolding progEquiv_def progRefine_def by blast

lemma progEquiv_symp_expl:
  assumes "\<alpha> \<rightleftharpoons> \<beta>"
  shows "\<beta> \<rightleftharpoons> \<alpha>"
  using assms unfolding progEquiv_def by blast

declare progEquiv_transp_expl [trans]

declare progEquiv_symp_expl [sym]

lemma prog_eval_cong:
  "\<alpha> \<rightleftharpoons> \<beta> \<Longrightarrow> prog_eval \<alpha> = prog_eval \<beta>"
  using progEquivSimplification by simp

lemma prog_ref_imp:
  fixes \<alpha> \<beta> :: "'prog"
  assumes "\<alpha> \<le> \<beta>"
  assumes "prog_eval \<alpha> \<mu> \<omega>"
  shows "prog_eval \<beta> \<mu> \<omega>"
  using assms
  unfolding progRefine_def
  by simp

subsection\<open>Proof Rules\<close>
text\<open>The definitions established above enable us to derive the validity
of the following two axioms:\<close>

lemma refinementAxiomReplace:
  fixes \<alpha> \<beta> :: "'prog"
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  shows "\<beta> \<le> \<alpha> \<Longrightarrow> \<Turnstile>[dyn_eval] (\<lbrakk>\<alpha>\<rbrakk>\<phi>) \<Rrightarrow> (\<lbrakk>\<beta>\<rbrakk>\<phi>)"
  unfolding theory_valid_def
    using prog_ref_imp[of \<beta> \<alpha>]
    by auto

lemma rewriteAxiomReplace:
  fixes \<alpha> \<beta> :: "'prog"
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  shows "\<alpha> \<rightleftharpoons> \<beta> \<Longrightarrow> \<Turnstile>[dyn_eval] (\<lbrakk>\<alpha>\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<beta>\<rbrakk>\<phi>)"
  unfolding EQUIV_def
  unfolding progEquiv_def
  using refinementAxiomReplace
  by auto

end

end