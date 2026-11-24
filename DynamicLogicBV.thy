subsubsection\<open>Dynamic Theories with Finite Support\<close>

text\<open>
This theory formalizes dynamic theories
with a finite syntactic computation of bounded variables.

This allows us to discharge mentions of  \texttt{dyn\_prog\_bv\_sem}
via syntactic means for the concrete dynamic theory.
\<close>

theory DynamicLogicBV
  imports
    Main
    "DynamicLogic"
begin

locale dynamic_theory_bv =
  dynamic_theory atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
  for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
  and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
  and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  +
  fixes dyn_prog_BV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  assumes dyn_prog_BV_overapprox: "dyn_prog_bv_sem \<pi> v \<Longrightarrow> dyn_prog_BV \<pi> v"
      and prog_bv_finite: "finite (Collect (dyn_prog_BV \<pi>))"
begin

lemma dyn_prog_BV_subset:
  "Collect (dyn_prog_bv_sem \<pi>) \<subseteq> Collect (dyn_prog_BV \<pi>)"
  using dyn_prog_BV_overapprox by blast

text\<open>Contrapositive form, convenient for frame conditions.\<close>

lemma not_dyn_prog_bv_sem:
  assumes "\<not> dyn_prog_BV \<pi> v"
  shows "\<not> dyn_prog_bv_sem \<pi> v"
  using assms dyn_prog_BV_overapprox by blast

lemma dyn_prog_bv_sem_disjnt:
  assumes "Collect (dyn_prog_BV \<pi>) \<inter> A = {}"
  shows "Collect (dyn_prog_bv_sem \<pi>) \<inter> A = {}"
  using assms dyn_prog_BV_subset by blast

end

end
