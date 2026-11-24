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
  assumes "((Collect (dyn_fv_sem \<phi>)) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) = {}"
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
  assumes v_not_fv: "\<not> dyn_prog_FV \<pi> v"
      and v_not_bv: "\<not> dyn_prog_bv_sem \<pi> v"
    shows "\<Turnstile>[dyn_eval] (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>))"
proof -
  have dir1: "\<Turnstile>[dyn_eval] (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>))"
  proof ((simp add: dyn_sem), intro allI)
    fix \<mu>
    have not_bv: "\<not> dyn_prog_bv_sem \<pi> v"
      using assms
      by blast

    have not_fv: "\<not> dyn_prog_fv_sem \<pi> v"
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
          where omega2_almost_eq: "fol_equal_everywhere_but v \<omega>1 \<omega>2"
            and omega2_unsatisfies: "\<not> dyn_eval \<phi> \<omega>2"
          using dyn_eval.simps(4) by blast

        obtain \<nu>1 where \<nu>1_cond: "(state_eval \<nu>1) v = (state_eval \<omega>2) v \<and> fol_equal_everywhere_but v \<nu>1 \<mu>"
          using state_space_convexity
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by (meson singleton_iff)

        let ?relevant_vars = "(\<lambda> w. w=v)"

        have relevant_finite: "finite (Collect ?relevant_vars)"
          by simp

        have mu_nu1_almost_equal: "fol_equal_everywhere_but v \<mu> \<nu>1"
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

        have "\<forall> w . ((dyn_prog_fv_sem \<pi> w) \<longrightarrow> ((\<lambda> t . t \<noteq> v) w))"
          using not_fv by force

        then have "(\<exists> \<omega>2 . (prog_eval \<pi> \<nu>1 \<omega>2) \<and> (fol_states_agree_on ((\<lambda> t . t \<noteq> v)) \<omega>1 \<omega>2) )"
          using nu_omega1_trans
          using agree_on_fv
          using agree_on_irrelevant
          using relevant_finite
          using dyn_prog_fv_sem_coincidence
          by auto

        then obtain \<omega>2_new
          where omega2_new_transition: "(prog_eval \<pi> \<nu>1 \<omega>2_new)"
            and omega2_new_agrees: "(fol_states_agree_on ((\<lambda> t . t \<noteq> v)) \<omega>1 \<omega>2_new)"
          by auto

        then have omega2_2new_eq_on_v: "(state_eval \<nu>1) v = (state_eval \<omega>2_new) v"
          using omega2_new_transition
          using not_bv
          using dyn_prog_bv_sem_bounded
          using dyn_prog_bv_sem.simps by blast

        have "fol_equal_everywhere_but v \<omega>2_new \<omega>2"
          using omega2_new_agrees
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by (smt (verit, ccfv_SIG) fol_equal_everywhere_but_def fol_states_agree_on_def omega2_almost_eq)

        then have "(state_eval \<omega>2) = (state_eval \<omega>2_new)"
          using omega2_2new_eq_on_v
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          using \<nu>1_cond by fastforce

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

    thus "(\<exists>\<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<and> (\<exists>\<omega>'. prog_eval \<pi> \<omega> \<omega>' \<and> \<not> dyn_eval \<phi> \<omega>')) \<or>
         (\<forall>\<omega>. prog_eval \<pi> \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. fol_equal_everywhere_but v \<omega> \<omega>' \<longrightarrow> dyn_eval \<phi> \<omega>'))"
      by (simp, blast)
  qed
  have dir2: "\<Turnstile>[dyn_eval] (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<bbbA> v . \<lbrakk>\<pi>\<rbrakk>\<phi>)"
  proof -

    have not_inner_sem_fv: "\<not> dyn_fv_sem (\<bbbA> v . \<phi>) v"
      unfolding dyn_fv_sem.simps
      unfolding dyn_eval.simps
      using dyn_fv_sem_all_not_free by force

    have "\<not> dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) v"
    proof -
      have not_fv: "\<not> dyn_prog_fv_sem \<pi> v"
        using dyn_FV_prog_sound
        using v_not_fv
        by blast

      have not_bv: "\<not> dyn_prog_bv_sem \<pi> v"
        using v_not_bv
        by blast

      show ?thesis
        using not_fv not_bv not_inner_sem_fv
      proof -
        define \<psi> where "\<psi> \<equiv> (\<bbbA> v . \<phi>)"
        show "\<not> dyn_prog_fv_sem \<pi> v \<Longrightarrow> \<not> dyn_prog_bv_sem \<pi> v \<Longrightarrow> \<not> dyn_fv_sem \<psi> v \<Longrightarrow> \<not> dyn_fv_sem (\<lbrakk> \<pi> \<rbrakk> \<psi>) v"
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
      using fol_equal_everywhere_but_def fol_states_agree_on_def
      by (auto simp add: dyn_sem)

    then have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> ((\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>)"
      using dyn_axiom_G
      by blast

    then have "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using dyn_axiom_K
      using dyn_hilbert_mp
      by blast

    then have "\<Turnstile>[dyn_eval] \<bbbA> v . ((\<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . \<phi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<phi>))"
      using dyn_axiom_A
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
    by (auto simp add: dyn_sem)
qed


subsection\<open>Determinism and Totality\<close>
text\<open>
If a program has exactly one successor state, box and diamond coincide for it.
This is the generic core of the NDL axiom schema $[p]\phi \leftrightarrow \langle p \rangle \phi$.
\<close>

lemma box_diamond_iff:
  assumes total_det: "\<And>\<mu>. \<exists>!\<omega>. prog_eval \<pi> \<mu> \<omega>"
  shows "dyn_eval (\<langle>\<pi>\<rangle> \<phi>) \<mu> = dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<mu>"
proof -
  obtain \<omega> where succ: "prog_eval \<pi> \<mu> \<omega>" and uniq: "\<And>\<upsilon>. prog_eval \<pi> \<mu> \<upsilon> \<Longrightarrow> \<upsilon> = \<omega>"
    using total_det[of \<mu>] by blast
  have box: "dyn_eval (\<lbrakk>\<pi>\<rbrakk> \<phi>) \<mu> = dyn_eval \<phi> \<omega>"
    unfolding dyn_eval.simps
    using succ uniq
    by blast
  have "dyn_eval (\<langle>\<pi>\<rangle> \<phi>) \<mu> = (\<exists>\<upsilon>. prog_eval \<pi> \<mu> \<upsilon> \<and> dyn_eval \<phi> \<upsilon>)"
    unfolding DIAMOND_def by auto
  also have "... = dyn_eval \<phi> \<omega>"
    using succ uniq by blast
  finally show ?thesis using box by simp
qed

end

subsection\<open>Variants of Dynamic Theories\<close>

subsubsection\<open>Dynamic Theories with Equality\<close>

locale dynamic_theory_eq =
    dynamic_theory atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
+
fixes eqPred :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
(*assumes infinite_nat_vars: "\<not> (finite (nat_assignable_vars state_eval val2nat))"*)
assumes eqPred_sound: "\<forall> v1 v2 .
          (v1 \<noteq> v2)
          \<longrightarrow> (\<forall> \<mu> .
                dyn_eval (FOL (eqPred v1 v2)) \<mu>
                \<longleftrightarrow>
                ((state_eval \<mu> v2) = (state_eval \<mu> v1))
              )"
begin
lemma eq_all_axiom:
  fixes v :: "'var"
  and w :: "'var"
  and \<phi> :: "('atom,'var,'prog) dyn_formula"
assumes "v \<noteq> w"
shows "\<Turnstile>[dyn_eval] ((FOL (eqPred v w)) \<Rrightarrow> (\<phi> \<Rrightarrow>(\<bbbA> v . ((FOL (eqPred v w)) \<Rrightarrow> \<phi>))))"
  using eqPred_sound assms
  apply (auto simp add: dyn_sem)
  by (smt (verit, ccfv_SIG) dyn_differing_state_eval_due_to_vars dynamic_theory_def
      dynamic_theory_eq_axioms dynamic_theory_eq_def folCore.fol_equal_everywhere_but_def
      fol_states_agree_on_def)

lemma eqPred_fv_sem:
  assumes vw: "v \<noteq> w"
      and xv: "x \<noteq> v"
      and xw: "x \<noteq> w"
    shows "\<not> dyn_fv_sem (FOL (eqPred v w)) x"
  using eqPred_sound vw xv xw
  unfolding dyn_fv_sem.simps
  unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
  by metis

fun eqPredV :: "'var list \<Rightarrow> 'var list \<Rightarrow> ('atom, 'var) fol_formula"
  where
      "eqPredV (v # vs) (w # ws) = (eqPred v w) foland (eqPredV vs ws)"
    | "eqPredV [] [] = FOLTRUE"
    | "eqPredV vs ws = undefined"

lemma eqPredV_fv_sem_subset:
  fixes vs :: "'var list"
    and ws :: "'var list"
  assumes "disjnt (set vs) (set ws)"
      and "length vs = length ws"
    shows "Collect (dyn_fv_sem (FOL (eqPredV vs ws))) \<subseteq> set vs \<union> set ws"
  using assms
proof (induct vs arbitrary: ws)
  case Nil
  then have ws_nil: "ws = []" by simp
  have base: "\<And>u. \<not> dyn_fv_sem (FOL FOLTRUE) u"
    by (rule dyn_fv_sem_valid[OF dyn_true_valid[unfolded DYNTRUE_def]])
  have "Collect (dyn_fv_sem (FOL FOLTRUE)) = {}"
    using base by blast
  then show ?case
    unfolding ws_nil
    by (simp only: eqPredV.simps) simp
next
  case (Cons v vs)

  obtain w ws' where ws_def: "ws = w # ws'"
    using Cons.prems(2) by (cases ws) auto

  have vw_neq: "v \<noteq> w"
    using Cons.prems(1) ws_def by (auto simp add: disjnt_def)
  have disj': "disjnt (set vs) (set ws')"
    using Cons.prems(1) ws_def by (auto simp add: disjnt_def)
  have len': "length vs = length ws'"
    using Cons.prems(2) ws_def by simp

  have IH: "Collect (dyn_fv_sem (FOL (eqPredV vs ws'))) \<subseteq> set vs \<union> set ws'"
    by (rule Cons.hyps[OF disj' len'])

  have head: "Collect (dyn_fv_sem (FOL (eqPred v w))) \<subseteq> {v, w}"
    using eqPred_fv_sem
    using vw_neq by blast

  text\<open>\<open>eqPredV\<close> on a cons is semantically the conjunction of head and tail.\<close>
  have unfold_eq: "\<And>\<mu>. dyn_eval (FOL (eqPredV (v # vs) (w # ws'))) \<mu>
                     = dyn_eval ((FOL (eqPred v w)) and (FOL (eqPredV vs ws'))) \<mu>"
    using vw_neq
    by simp

  have main: "Collect (dyn_fv_sem (FOL (eqPredV (v # vs) (w # ws'))))
                \<subseteq> set (v # vs) \<union> set (w # ws')"
  proof -
    have "Collect (dyn_fv_sem (FOL (eqPredV (v # vs) (w # ws'))))
            = Collect (dyn_fv_sem ((FOL (eqPred v w)) and (FOL (eqPredV vs ws'))))"
      by auto
    also have "... \<subseteq> Collect (dyn_fv_sem (FOL (eqPred v w)))
                       \<union> Collect (dyn_fv_sem (FOL (eqPredV vs ws')))"
      by (rule dyn_fv_sem_and_subset)
    also have "... \<subseteq> {v, w} \<union> (set vs \<union> set ws')"
      using head IH by blast
    finally show ?thesis by auto
  qed

  show ?case
    unfolding ws_def
    by (rule main)
qed

lemma fol_eqPred_sound:
  assumes "v1 \<noteq> v2"
  shows "fol_eval (eqPred v1 v2) \<mu> \<longleftrightarrow> state_eval \<mu> v2 = state_eval \<mu> v1"
  using eqPred_sound assms by simp

lemma c_eqPred_fv_sem:
  assumes "v \<noteq> w" "x \<noteq> v" "x \<noteq> w"
  shows "\<not> dyn_fv_sem (FOL (eqPred v w)) x"
proof -
  have "dyn_fv_sem (FOL (eqPred v w)) x = dyn_fv_sem (FOL (eqPred v w)) x"
    by simp
  then show ?thesis
    using eqPred_fv_sem[OF assms] by simp
qed



end

end