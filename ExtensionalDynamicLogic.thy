subsubsection\<open>Extensional Dynamic Theories\<close>
text\<open>
\label{sec:extensional-dl}
For completeness, we prove here that the stronger form of extensionality
required by \texttt{KleeneDynLog} implies the weaker form of extensionality
required by the assumption from \texttt{dynamic\_theory}.
\<close>

theory ExtensionalDynamicLogic
  imports
    Main
    "FirstOrder"
    "DynamicLogicCore"
begin

locale extDynLogCore =
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
        and strong_extensionality:
        "\<forall> \<pi> \<mu> \<omega> \<mu>' \<omega>' . ((\<forall> v. (((state_eval \<mu>) v = (state_eval \<omega>) v) \<and> ((state_eval \<mu>') v = (state_eval \<omega>') v))) \<longrightarrow> prog_eval \<pi> \<mu> \<mu>' = prog_eval \<pi> \<omega> \<omega>')"
begin

sublocale dlc: dynamic_theory atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
  apply standard
  using prog_fv_finite apply simp
  using prog_fv_overapprox apply auto
  using strong_extensionality
  proof -
    fix \<pi> :: 'prog and \<mu> :: 'state and \<omega> :: 'state
    assume a1: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v"
    have "\<forall>p s sa sb sc. (\<forall>v. state_eval s v = state_eval sa v \<and> state_eval sb v = state_eval sc v) \<longrightarrow> prog_eval p s sb = prog_eval p sa sc"
      using strong_extensionality by blast
    then show "prog_eval \<pi> \<mu> = prog_eval \<pi> \<omega>"
      using a1 by blast
  qed

end

end