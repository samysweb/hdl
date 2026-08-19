theory DynamicLogicProof
  imports
    Main
    "DynamicLogic"
begin

context dynamic_theory
begin


lemma dt_prop_id:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<phi>"
  by (auto simp add: dyn_sem)

lemma dt_prop_imp_trans [trans]:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<chi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<chi>"
  by (auto simp add: dyn_sem)

lemma dt_prop_imp_trans_rev:
  "\<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<chi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<chi>"
  by (auto simp add: dyn_sem)

lemma dt_prop_equivI [intro]:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Lleftarrow>\<Rrightarrow> \<psi>"
  by (auto simp add: dyn_sem)

lemma dt_prop_conjI [intro]:
  "\<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> (\<phi> and \<psi>)"
  by (auto simp add: dyn_sem)

lemma dt_prop_uncurry:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<chi>) \<Longrightarrow> \<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<chi>"
  by (auto simp add: dyn_sem)



lemma dt_box_diamond_iff:
  assumes total_det: "\<And>\<mu>. \<exists>!\<omega>. prog_eval \<pi> \<mu> \<omega>"
  shows "\<Turnstile>[dyn_eval] ((\<langle>\<pi>\<rangle> \<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> \<phi>))"
  apply (rule dt_prop_equivI)
  unfolding theory_valid_def IMP_def
  unfolding dyn_eval.simps(1,2,3)
  using assms
  using box_diamond_iff
  by auto

lemma dyn_axiom_F1V:
  "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ( (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<psi>) )"
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by (simp add: dyn_sem)
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
  proof -
    assume "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<psi>)"
    then have "\<Turnstile>[dyn_eval] \<bbbA> a . ((\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ((\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<psi>)))"
      using dyn_axiom_A
      by blast
    then have "\<Turnstile>[dyn_eval] (\<bbbA> a . (\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>))) \<Rrightarrow> (\<bbbA> a . ((\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<psi>)))"
      using dyn_axiom_F1
      using dyn_hilbert_mp
      by blast
    also have "\<Turnstile>[dyn_eval] (\<bbbA> a . ((\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA>\<bbbA> v . \<psi>)) \<Rrightarrow> ((\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> a . \<bbbA>\<bbbA> v . \<psi>))"
      using dyn_axiom_F1
      using dyn_hilbert_mp
      by blast
    finally show "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ((\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA> a . \<bbbA>\<bbbA> v . \<psi>)"
      by simp
  qed
qed

lemma all_vec_fv:
  assumes "\<not> dyn_fv_sem \<phi> v"
  shows "\<not> dyn_fv_sem (\<bbbA>\<bbbA> w . \<phi>) v"
proof (induct w)
  case Nil
  then show ?case
    using assms
    unfolding FOR_ALL_VEC.simps
    by simp
next
  case (Cons a w)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
    using dyn_fv_sem_all_intro
    by blast
qed

lemma dyn_axiom_F2V:
  assumes fv_assumption: "list_all (\<lambda> x . \<not> dyn_fv_sem \<phi> x) v"
  shows "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA>\<bbbA> v . \<phi>"
  using assms
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by (simp add: dyn_sem)
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
  proof -
    assume fact1: "list_all (\<lambda>x. \<not> dyn_fv_sem \<phi> x) (a # v)"
    
    assume "list_all (\<lambda>x. \<not> dyn_fv_sem \<phi> x) v \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<bbbA>\<bbbA> v . \<phi>)"
    then have fact2:"\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<bbbA>\<bbbA> v . \<phi>)"
      using fact1
      by auto
    have "\<not> dyn_fv_sem \<phi> a"
      using fact1
      by simp
    then have "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>)"
      using dyn_axiom_F2[of "\<bbbA>\<bbbA> v . \<phi>" a]
      using all_vec_fv[of \<phi> a v]
      by blast
    then show "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA> a . \<bbbA>\<bbbA> v . \<phi>"
      using fact2
      by (auto simp add: dyn_sem)
  qed
qed

lemma dyn_axiom_F3V:
  shows "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by (simp add: dyn_sem)
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
  proof -
    have "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA>\<bbbA> v . \<phi>"
      using dyn_axiom_F3
      by blast
    also assume "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
    finally show "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
      by simp
  qed
qed

lemma dyn_axiom_AV:
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[dyn_eval] \<bbbA>\<bbbA> v . \<phi>"
  using assms
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by simp
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
    using dyn_axiom_A[of "\<bbbA>\<bbbA> v . \<phi>" a]
    by simp
qed

lemma dt_box_K [intro]:
  "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> \<Rrightarrow> \<psi>) \<Longrightarrow> \<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>))"
  using dyn_axiom_K[of \<pi> \<phi> \<psi>]
  using dyn_hilbert_mp[of "\<lbrakk>\<pi>\<rbrakk>(\<phi> \<Rrightarrow> \<psi>)"]
  by simp

lemma dt_box_G:
  "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi>"
  using dyn_axiom_G by simp

lemma dt_box_M:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> \<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>"
  apply (rule dt_box_K)
  apply (rule dt_box_G).

lemma dt_box_MR:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<psi>"
  using dyn_hilbert_mp
  using dt_box_M
  by blast

lemma dt_diamond_K:
  "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<langle>\<pi>\<rangle> \<phi> \<Rrightarrow> \<langle>\<pi>\<rangle> \<psi>)"
proof -
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<lbrakk>\<pi>\<rbrakk>\<rceil>\<psi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi>)"
    using dyn_axiom_K
    by blast
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)"
    apply (intro dt_box_M)
    by (auto simp add: dyn_sem)
  also have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi> \<Rrightarrow> \<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<psi>)"
    by (auto simp add: dyn_sem)
  then have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<langle>\<pi>\<rangle>\<phi> \<Rrightarrow> \<langle>\<pi>\<rangle> \<psi>)"
    by (auto simp add: dyn_sem)
  finally show ?thesis.
qed
    

lemma dt_box_and:
  "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>) \<Lleftarrow>\<Rrightarrow> ((\<lbrakk>\<pi>\<rbrakk>\<phi>) and (\<lbrakk>\<pi>\<rbrakk>\<psi>))"
proof (rule dt_prop_equivI)
  show "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>) \<Rrightarrow> ((\<lbrakk>\<pi>\<rbrakk>\<phi>) and (\<lbrakk>\<pi>\<rbrakk>\<psi>))"
  proof (rule dt_prop_conjI)
    show "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<phi>"
      apply (rule dt_box_K)
      apply (rule dt_box_G)
      by (simp add: dyn_sem)
    show "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>"
      apply (rule dt_box_K)
      apply (rule dt_box_G)
      by (simp add: dyn_sem)
  qed
next
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<psi> \<Rrightarrow> (\<phi> and \<psi>))"
    apply (rule dt_box_K)
    apply (rule dt_box_G)
    by (simp add: dyn_sem)
  also have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<psi> \<Rrightarrow> (\<phi> and \<psi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<psi> \<Rrightarrow>  \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>))"
    by (rule dyn_axiom_K)
  finally have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<psi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>))"
    apply (rule dt_prop_imp_trans)
    by (rule dt_prop_id)
  thus "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk>\<phi>) and (\<lbrakk>\<pi>\<rbrakk>\<psi>)) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>)"
    by (rule dt_prop_uncurry)
qed

lemma dt_diamond_mp:
  assumes "\<And> w . dyn_prog_bv_sem \<pi> w \<longleftrightarrow> w=v"
  shows "\<Turnstile>[dyn_eval] (((\<langle>\<pi>\<rangle>\<phi>) and (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>))) \<Rrightarrow> \<langle>\<pi>\<rangle>\<psi>)"
proof -
  have "\<not> dyn_fv_sem (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) v"
    apply (auto simp add: dyn_sem fol_equal_everywhere_but_def fol_states_agree_on_def)
    apply metis
    by metis

  then have "\<Turnstile>[dyn_eval] (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>))"
    using dyn_axiom_V[of "(\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>))" \<pi>] assms(1)
    by (metis disjoint_iff mem_Collect_eq)

  also have "\<Turnstile>[dyn_eval] (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> (\<phi> \<Rrightarrow> \<psi>)"
    using dyn_axiom_F3
    by simp

  then have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>)"
    by (rule dt_box_M)

  also have "\<Turnstile>[dyn_eval] \<lbrakk> \<pi> \<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> \<langle>\<pi>\<rangle> \<phi> \<Rrightarrow> \<langle>\<pi>\<rangle>\<psi> "
    using dt_diamond_K[of \<pi> \<phi> \<psi>]
    by blast

  finally show ?thesis
    by (auto simp add: dyn_sem)
qed
    
  
    

end

end