theory DynamicLogic
  imports
    Main
    "DynamicLogicCore"
begin

context dynamic_theory
begin

lemma dyn_axiom_V:
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  fixes \<pi> :: "'prog"
  assumes "((Collect (dyn_FV \<phi>)) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) = {}"
  shows "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<phi>"
  unfolding theory_valid_def
  unfolding IMP_def
  unfolding dyn_eval.simps
proof (simp, intro allI, intro impI)
  fix \<mu>
  assume mu_satisfies_phi: "dyn_eval \<phi> \<mu>"
  have sem_vars_disjoint: "((Collect (dyn_fv_sem \<phi>)) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) = {}"
    using dyn_FV_fml_sound assms
    by blast

  show "\<forall>\<omega>. prog_eval \<pi> \<mu> \<omega> \<longrightarrow> dyn_eval \<phi> \<omega>"
  proof (intro allI, intro impI)
    fix \<omega>

    assume "prog_eval \<pi> \<mu> \<omega>"

    then have "fol_states_agree_on (\<lambda> v . \<not> dyn_prog_bv_sem \<pi> v) \<mu> \<omega>"
      using dyn_prog_bv_sem_bounded
      by blast

    then have "fol_states_agree_on (dyn_fv_sem \<phi>) \<mu> \<omega>"
      using sem_vars_disjoint
      by (smt (verit, best) Int_Collect equals0D fol_states_agree_on_def mem_Collect_eq) (* runs 1s *)

    then have "dyn_eval \<phi> \<mu> = dyn_eval \<phi> \<omega>"
      using dyn_fv_sem_coincidence
      by blast

    thus "dyn_eval \<phi> \<omega>"
      using mu_satisfies_phi
      by simp
  qed
qed

lemma dyn_axiom_B:
  fixes v :: "'var"
    and \<phi> :: "('atom,'var,'prog) dyn_formula"
    and \<pi> :: "'prog"
  assumes v_not_fv: "\<not> dyn_prog_FV \<pi> (Inl v)"
      and v_not_bv: "\<not> dyn_prog_bv_sem \<pi> (Inl v)"
    shows "\<Turnstile>[dyn_eval] (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>))"
proof -
  have dir1: "\<Turnstile>[dyn_eval] (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>))"
  proof (simp, intro allI)
    fix \<mu>
    have not_bv: "\<not> dyn_prog_bv_sem \<pi> (Inl v)"
      using assms
      by blast

    have not_fv: "\<not> dyn_prog_fv_sem \<pi> (Inl v)"
      using assms dyn_FV_prog_sound
      by blast
    have dir1: "dyn_eval (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<mu> \<Longrightarrow> dyn_eval (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<mu>"
    proof -
      assume mu_satisfies: "dyn_eval (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<mu>"

      show "dyn_eval (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<mu>"
      proof (rule ccontr)
        assume "\<not> dyn_eval (\<lbrakk> \<pi> \<rbrakk> \<bbbA> v . \<phi>) \<mu>"
        then obtain \<omega>1
          where nu_omega1_trans: "prog_eval \<pi> \<mu> \<omega>1"
            and omega1_unsatisfies: "\<not> dyn_eval (\<bbbA> v . \<phi>) \<omega>1"
          using dyn_eval.simps(5) by blast

        then obtain \<omega>2
          where omega2_almost_eq: "fol_equal_everywhere_but (Inl v) \<omega>1 \<omega>2"
            and omega2_unsatisfies: "\<not> dyn_eval \<phi> \<omega>2"
          using dyn_eval.simps(4) by blast

        obtain \<nu>1 where \<nu>1_cond: "(state_eval \<nu>1) (Inl v) = (state_eval \<omega>2) (Inl v) \<and> fol_equal_everywhere_but (Inl v) \<nu>1 \<mu>"
          using state_space_convexity
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by (meson singleton_iff)

        let ?relevant_vars = "(\<lambda> w. w=(Inl v))"

        have relevant_finite: "finite (Collect ?relevant_vars)"
          by simp

        have mu_nu1_almost_equal: "fol_equal_everywhere_but (Inl v) \<mu> \<nu>1"
          using \<nu>1_cond
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by simp

        then have "dyn_eval (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<nu>1"
          using mu_satisfies
          using dyn_fv_sem.simps dyn_fv_sem_all_not_free by blast

        have agree_on_irrelevant: "fol_states_agree_on (\<lambda> v . \<not> ?relevant_vars v) \<mu> \<nu>1"
          using mu_nu1_almost_equal
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by blast

        then have agree_on_fv: "fol_states_agree_on (dyn_prog_fv_sem \<pi>) \<mu> \<nu>1"
          using \<nu>1_cond
          using not_fv
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by metis

        have "\<forall> w . ((dyn_prog_fv_sem \<pi> w) \<longrightarrow> ((\<lambda> t . t \<noteq> (Inl v)) w))"
          using not_fv by force

        then have "(\<exists> \<omega>2 . (prog_eval \<pi> \<nu>1 \<omega>2) \<and> (fol_states_agree_on ((\<lambda> t . t \<noteq> (Inl v))) \<omega>1 \<omega>2) )"
          using nu_omega1_trans
          using agree_on_fv
          using agree_on_irrelevant
          using relevant_finite
          using dyn_prog_fv_sem_coincidence
          by auto

        then obtain \<omega>2_new
          where omega2_new_transition: "(prog_eval \<pi> \<nu>1 \<omega>2_new)"
            and omega2_new_agrees: "(fol_states_agree_on ((\<lambda> t . t \<noteq> (Inl v))) \<omega>1 \<omega>2_new)"
          by auto

        then have omega2_2new_eq_on_v: "(state_eval \<nu>1) (Inl v) = (state_eval \<omega>2_new) (Inl v)"
          using omega2_new_transition
          using not_bv
          using dyn_prog_bv_sem_bounded
          using dyn_prog_bv_sem.simps by blast

        have "fol_equal_everywhere_but (Inl v) \<omega>2_new \<omega>2"
          using omega2_new_agrees
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by (smt (verit, ccfv_SIG) fol_equal_everywhere_but_def fol_states_agree_on_def omega2_almost_eq)

        then have "(state_eval \<omega>2) = (state_eval \<omega>2_new)"
          using omega2_2new_eq_on_v
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          using \<nu>1_cond
          by (metis (lifting) ext)

        then have "\<not> dyn_eval \<phi> \<omega>2_new"
          using omega2_unsatisfies
          using dyn_differing_state_eval_due_to_vars by force

        then have "\<not> (dyn_eval (\<lbrakk>\<pi>\<rbrakk>\<phi>) \<nu>1)"
          using omega2_new_transition
          unfolding dyn_eval.simps
          by blast

        then have "\<not> (dyn_eval (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<mu>)"
          using mu_nu1_almost_equal
          unfolding dyn_eval.simps
          by blast

        thus False
          using mu_satisfies
          by blast
      qed
    qed

    thus "(\<exists>\<omega>. fol_equal_everywhere_but (Inl v) \<mu> \<omega> \<and> (\<exists>\<omega>'. prog_eval \<pi> \<omega> \<omega>' \<and> \<not> dyn_eval \<phi> \<omega>')) \<or>
         (\<forall>\<omega>. prog_eval \<pi> \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. fol_equal_everywhere_but (Inl v) \<omega> \<omega>' \<longrightarrow> dyn_eval \<phi> \<omega>'))"
      by (simp, blast)
  qed
  have dir2: "\<Turnstile>[dyn_eval] (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>)"
  proof -

    have not_inner_sem_fv: "\<not> dyn_fv_sem (\<bbbA> v . \<phi>) (Inl v)"
      unfolding dyn_fv_sem.simps
      unfolding dyn_eval.simps
      using dyn_fv_sem_all_not_free by force

    have "\<not> dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) (Inl v)"
    proof -
      have not_fv: "\<not> dyn_prog_fv_sem \<pi> (Inl v)"
        using dyn_FV_prog_sound
        using v_not_fv
        by blast

      have not_bv: "\<not> dyn_prog_bv_sem \<pi> (Inl v)"
        using v_not_bv
        by blast

      show ?thesis
        using not_fv not_bv not_inner_sem_fv
      proof -
        define \<psi> where "\<psi> \<equiv> (\<bbbA> v . \<phi>)"
        show "\<not> dyn_prog_fv_sem \<pi> (Inl v) \<Longrightarrow> \<not> dyn_prog_bv_sem \<pi> (Inl v) \<Longrightarrow> \<not> dyn_fv_sem \<psi> (Inl v) \<Longrightarrow> \<not> dyn_fv_sem (\<lbrakk> \<pi> \<rbrakk> \<psi>) (Inl v)"
          unfolding dyn_fv_sem.simps
          unfolding dyn_eval.simps
          unfolding dyn_prog_fv_sem.simps
          unfolding dyn_prog_bv_sem.simps
          by (simp, smt (verit, del_insts) fol_equal_everywhere_but_def fol_states_agree_on_def)
      qed
    qed

    then have all_omitable: "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<bbbA> v .(\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>))))"
      using dyn_hilbert_axiom_7
      by blast

    have "\<Turnstile>[dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
      unfolding theory_valid_def
      unfolding dyn_eval.simps
      using fol_equal_everywhere_but_def fol_states_agree_on_def by force

    then have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> ((\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>)"
      using dyn_axiom_G
      by blast

    then have "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using dyn_axiom_K
      using dyn_hilbert_mp
      by blast

    then have "\<Turnstile>[dyn_eval] \<bbbA> v . ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using dyn_hilbert_axiom_G
      by blast

    then have all_distributed: "\<Turnstile>[dyn_eval] ((\<bbbA> v . \<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using dyn_hilbert_axiom_6 dyn_hilbert_mp
      by blast

    thus "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using all_omitable dyn_hilbert_imp_transitive dyn_hilbert_mp
      by meson
  qed

  show ?thesis
    using dir1 dir2
    by simp
qed

end

end