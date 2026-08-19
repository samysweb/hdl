subsection\<open>Combining Program Signatures\<close>
text\<open>
Implementation formalized by Claude Opus after
intensive discussion with Samuel Teuber on 19th of August 2026.
Cross-checked by Samuel Teuber.
\<close>

text\<open>
All three program-side assumptions of \texttt{dynamic\_theory} are stated
pointwise for a single program, with no interaction between different programs.
Hence the disjoint sum of the program types of two dynamic theories over the
same atoms, states and variables is again a dynamic theory.
This lets us build a dynamic theory constructor-by-constructor instead of
proving the obligations for a monolithic program datatype.
\<close>

theory DynamicTheorySum
  imports
    Main
    "DynamicLogicCore"
    "DynamicLogic"
    "DynamicLogicProof"
begin

locale dynamic_theory_sum =
  A: dynamic_theory atom_eval atom_fv_syn state_eval progA_eval progA_fv +
  B: dynamic_theory atom_eval atom_fv_syn state_eval progB_eval progB_fv
  for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
  and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
  and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and progA_eval :: "'progA \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  and progA_fv :: "'progA \<Rightarrow> 'var \<Rightarrow> bool"
  and progB_eval :: "'progB \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  and progB_fv :: "'progB \<Rightarrow> 'var \<Rightarrow> bool"
begin

definition sum_prog_eval :: "('progA + 'progB) \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where "sum_prog_eval = case_sum progA_eval progB_eval"

definition sum_prog_fv :: "('progA + 'progB) \<Rightarrow> 'var \<Rightarrow> bool"
  where "sum_prog_fv = case_sum progA_fv progB_fv"

lemma sum_prog_eval_simps [simp]:
  "sum_prog_eval (Inl p) = progA_eval p"
  "sum_prog_eval (Inr q) = progB_eval q"
  by (simp_all add: sum_prog_eval_def)

lemma sum_prog_fv_simps [simp]:
  "sum_prog_fv (Inl p) = progA_fv p"
  "sum_prog_fv (Inr q) = progB_fv q"
  by (simp_all add: sum_prog_fv_def)

sublocale sum_dl:
  dynamic_theory atom_eval atom_fv_syn state_eval sum_prog_eval sum_prog_fv
proof

  text\<open>The three first-order obligations are inherited verbatim from A.\<close>

  text\<open>The program obligations go through by case distinction on the sum.\<close>

  show "\<And>\<pi>. finite (Collect (sum_prog_fv \<pi>))"
  proof -
    fix \<pi> :: "'progA + 'progB"
    show "finite (Collect (sum_prog_fv \<pi>))"
      by (cases \<pi>) (simp_all add: A.prog_fv_finite B.prog_fv_finite)
  qed

  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
          ((\<forall>v. sum_prog_fv \<pi> v \<longrightarrow> V v) \<and>
           A.fol_states_agree_on V \<mu> \<omega> \<and>
           sum_prog_eval \<pi> \<mu> \<nu>) \<longrightarrow>
          (\<exists>\<upsilon>. sum_prog_eval \<pi> \<omega> \<upsilon> \<and> A.fol_states_agree_on V \<nu> \<upsilon>)"
  proof -
    fix \<pi> :: "'progA + 'progB"
    fix V \<mu> \<omega> \<nu>
    show "((\<forall>v. sum_prog_fv \<pi> v \<longrightarrow> V v) \<and>
           A.fol_states_agree_on V \<mu> \<omega> \<and>
           sum_prog_eval \<pi> \<mu> \<nu>) \<longrightarrow>
          (\<exists>\<upsilon>. sum_prog_eval \<pi> \<omega> \<upsilon> \<and> A.fol_states_agree_on V \<nu> \<upsilon>)"
    proof (cases \<pi>)
      case (Inl p)
      then show ?thesis
        using A.prog_fv_overapprox[of p V \<mu> \<omega> \<nu>] by simp
    next
      case (Inr p)
      then show ?thesis
        using B.prog_fv_overapprox[of p V \<mu> \<omega> \<nu>] by simp
    qed
  qed

  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow>
                  sum_prog_eval \<pi> \<mu> = sum_prog_eval \<pi> \<omega>"
  proof (intro allI impI)
    fix \<pi> :: "'progA + 'progB"
    fix \<mu> \<omega>
    assume agree: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v"
    show "sum_prog_eval \<pi> \<mu> = sum_prog_eval \<pi> \<omega>"
      using agree
      by (cases \<pi>) (simp_all add: A.prog_var_determinance B.prog_var_determinance)
  qed
qed

end


end
