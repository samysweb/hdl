theory DynamicLogicProof
  imports
    Main
    "DynamicLogic"
    "HOL-Eisbach.Eisbach"
begin

context dynamic_theory
begin

named_theorems dt_prop_unfold
  "propositional layer for dt_prop — do not add the BOX or \<forall>-equations here"

subsection\<open>Propositional skeleton\<close>

lemma dt_propI: "(\<And>\<mu>. dyn_eval \<chi> \<mu>) \<Longrightarrow> \<Turnstile>[dyn_eval] \<chi>"
  by (simp add: theory_valid_def)

lemma dt_propD: "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> dyn_eval \<phi> \<mu>"
  by (simp add: theory_valid_def)

text\<open>
The state of the conclusion determines \<open>\<mu>\<close>,
so \<open>erule\<close> instantiates it for us.\<close>
lemma dt_prop_localize:
  "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> (dyn_eval \<phi> \<mu> \<Longrightarrow> dyn_eval \<chi> \<mu>) \<Longrightarrow> dyn_eval \<chi> \<mu>"
  by (simp add: theory_valid_def)

text\<open>
Homomorphism equations.
Stated as named lemmas so that reordering the datatype
cannot silently change the bundle.\<close>

lemma dt_ev_and  [dt_prop_unfold]: "dyn_eval (\<phi> and \<psi>) \<mu> \<longleftrightarrow> (dyn_eval \<phi> \<mu> \<and> dyn_eval \<psi> \<mu>)" by simp
lemma dt_ev_not  [dt_prop_unfold]: "dyn_eval (\<rceil>\<phi>) \<mu> \<longleftrightarrow> (\<not> dyn_eval \<phi> \<mu>)" by simp
lemma dt_ev_fol  [dt_prop_unfold]: "dyn_eval (FOL \<phi>) \<mu> \<longleftrightarrow> fol_eval \<phi> \<mu>" by simp
lemma dt_fev_and [dt_prop_unfold]: "fol_eval (\<phi> foland \<psi>) \<mu> \<longleftrightarrow> (fol_eval \<phi> \<mu> \<and> fol_eval \<psi> \<mu>)" by simp
lemma dt_fev_not [dt_prop_unfold]: "fol_eval (folnot \<phi>) \<mu> \<longleftrightarrow> (\<not> fol_eval \<phi> \<mu>)" by simp

text\<open>Sugar. These rewrite inside boxes too, which normalises atoms — desirable.\<close>

declare IMP_def [dt_prop_unfold] OR_def [dt_prop_unfold]
        EQUIV_def [dt_prop_unfold] DIAMOND_def [dt_prop_unfold]
        DYN_EX_def [dt_prop_unfold] DYNTRUE_def [dt_prop_unfold]
        EX_VEC_def [dt_prop_unfold]
        FirstOrder.IMP_def [dt_prop_unfold] FirstOrder.OR_def [dt_prop_unfold]
        FirstOrder.EQUIV_def [dt_prop_unfold] FOLTRUE_def [dt_prop_unfold]
        

method dt_prop_setup uses facts declares dt_prop_unfold =
  (-,
   (insert facts)?,
   use nothing in
     \<open>(rule dt_propI)?,
      ((erule dt_prop_localize)+)?,
      (simp only: dt_prop_unfold)?\<close>)

method dt_prop uses facts declares dt_prop_unfold =
  (dt_prop_setup facts: facts ; satx)

method dt_prop_debug uses facts declares dt_prop_unfold =
  (dt_prop_setup facts: facts)


lemma dt_prop_id:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<phi>"
  by dt_prop

lemma dt_prop_imp_trans [trans]:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<chi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<chi>"
  by dt_prop

lemma dt_prop_imp_trans_rev:
  "\<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<chi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<chi>"
  by dt_prop

lemma dt_prop_equivI [intro]:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<psi> \<Rrightarrow> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Lleftarrow>\<Rrightarrow> \<psi>"
  by dt_prop

lemma dt_prop_conjI [intro]:
  "\<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<chi> \<Rrightarrow> (\<phi> and \<psi>)"
  by dt_prop

lemma dt_prop_uncurry:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<chi>) \<Longrightarrow> \<Turnstile>[dyn_eval] (\<phi> and \<psi>) \<Rrightarrow> \<chi>"
  by dt_prop



lemma dt_box_diamond_iff:
  assumes total_det: "\<And>\<mu>. \<exists>!\<omega>. prog_eval \<pi> \<mu> \<omega>"
  shows "\<Turnstile>[dyn_eval] ((\<langle>\<pi>\<rangle> \<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> \<phi>))"
  apply (rule dt_prop_equivI)
  unfolding theory_valid_def IMP_def
  unfolding dyn_eval.simps(1,2,3)
  using assms
  using box_diamond_iff
  by auto



lemma dt_fol_M:
  assumes "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi>"
  shows "\<Turnstile>[dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> v . \<psi>)"
  using assms
proof -
  have "\<Turnstile>[dyn_eval] \<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)"
    using assms
    by (rule dyn_axiom_A)
  then show "\<Turnstile>[dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> v . \<psi>)"
    using dyn_hilbert_mp[of "(\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>))" "(\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> v . \<psi>)"]
    using dyn_axiom_F1[of v \<phi> \<psi>]
    by dt_prop
qed

lemma dt_all_vec_M:
  assumes "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi>"
  shows "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> vs . \<psi>)"
  using assms
proof (induct vs)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps(1)
    by dt_prop
next
  case (Cons a vs)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
    using dt_fol_M
    by blast
qed

lemma dyn_axiom_F1V:
  "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ( (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> v . \<psi>) )"
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by dt_prop
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
      using dyn_axiom_F1[of a "\<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)" "(\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA>\<bbbA> v . \<psi>"]
      by dt_prop
    also have "\<Turnstile>[dyn_eval] (\<bbbA> a . ((\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA>\<bbbA> v . \<psi>)) \<Rrightarrow> ((\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> a . \<bbbA>\<bbbA> v . \<psi>))"
      using dyn_axiom_F1[of a "\<bbbA>\<bbbA> v . \<phi>" "\<bbbA>\<bbbA> v . \<psi>"]
      by dt_prop
    finally show "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ((\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA> a . \<bbbA>\<bbbA> v . \<psi>)"
      by dt_prop
  qed
qed

text\<open>Dual of \<open>dyn_axiom_F1V\<close>.\<close>
lemma dyn_axiom_F1VE:
  "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ((\<bbbE>\<bbbE> vs . \<phi>) \<Rrightarrow> (\<bbbE>\<bbbE> vs . \<psi>))"
proof -
  have contrapose: "\<Turnstile>[dyn_eval] (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)"
    by dt_prop
  have push: "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> (\<bbbA>\<bbbA> vs . (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>))"
    by (rule dt_all_vec_M[OF contrapose])
  have distr: "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)) \<Rrightarrow> ((\<bbbA>\<bbbA> vs . \<rceil>\<psi>) \<Rrightarrow> (\<bbbA>\<bbbA> vs . \<rceil>\<phi>))"
    by (rule dyn_axiom_F1V)
  show ?thesis
    using push distr by dt_prop
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

lemma all_vec_fv_bound:
  assumes "v \<in> set vs"
  shows "\<not> dyn_fv_sem (\<bbbA>\<bbbA> vs . \<phi>) v"
  using assms
proof (induct vs)
  case Nil
  then show ?case by simp
next
  case (Cons a vs)
  show ?case
  proof (cases "a = v")
    case True
    then show ?thesis
      unfolding FOR_ALL_VEC.simps(2)
      by (metis dyn_fv_sem_all_not_free)
  next
    case False
    then have "v \<in> set vs" using Cons.prems by simp
    then show ?thesis
      unfolding FOR_ALL_VEC.simps(2)
      using Cons.hyps dyn_fv_sem_all_intro
      by blast
  qed
qed

lemma dyn_axiom_F2V:
  assumes fv_assumption: "list_all (\<lambda> x . \<not> dyn_fv_sem \<phi> x) v"
  shows "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA>\<bbbA> v . \<phi>"
  using assms
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by dt_prop
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
  proof -
    assume fact1: "list_all (\<lambda>x. \<not> dyn_fv_sem \<phi> x) (a # v)"
    
    assume "list_all (\<lambda>x. \<not> dyn_fv_sem \<phi> x) v \<Longrightarrow> \<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<bbbA>\<bbbA> v . \<phi>)"
    then have fact2:"\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<bbbA>\<bbbA> v . \<phi>)"
      using fact1
      by simp
    have "\<not> dyn_fv_sem \<phi> a"
      using fact1
      by simp
    then have "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>)"
      using dyn_axiom_F2[of "\<bbbA>\<bbbA> v . \<phi>" a]
      using all_vec_fv[of \<phi> a v]
      by simp
    then show "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<bbbA> a . \<bbbA>\<bbbA> v . \<phi>"
      using fact2
      by dt_prop
  qed
qed

text\<open>Dual of \<open>dyn_axiom_F2V\<close>:
    a block of quantifiers over non-free variables can be dropped.\<close>
lemma dyn_axiom_F2VE:
  assumes fv_assumption: "list_all (\<lambda>x. \<not> dyn_fv_sem \<phi> x) vs"
  shows "\<Turnstile>[dyn_eval] (\<bbbE>\<bbbE> vs . \<phi>) \<Rrightarrow> \<phi>"
proof -
  have "list_all (\<lambda>x. \<not> dyn_fv_sem (\<rceil>\<phi>) x) vs"
    using fv_assumption by (simp add: list_all_iff dyn_fv_sem_not_eq)
  then have "\<Turnstile>[dyn_eval] (\<rceil>\<phi>) \<Rrightarrow> (\<bbbA>\<bbbA> vs . \<rceil>\<phi>)"
    by (rule dyn_axiom_F2V)
  then show ?thesis by dt_prop
qed

lemma dyn_axiom_F3V:
  shows "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by dt_prop
next
  case (Cons a v)
  then show ?case
    unfolding FOR_ALL_VEC.simps(2)
  proof -
    have "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<bbbA>\<bbbA> v . \<phi>"
      using dyn_axiom_F3[of a "\<bbbA>\<bbbA> v . \<phi>"]
      by dt_prop
    also assume "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
    finally show "\<Turnstile>[dyn_eval] (\<bbbA> a . \<bbbA>\<bbbA> v . \<phi>) \<Rrightarrow> \<phi>"
      by dt_prop
  qed
qed

text\<open>Dual of \<open>dyn_axiom_F3V\<close>.\<close>
lemma dyn_axiom_F3VE: "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> (\<bbbE>\<bbbE> vs . \<phi>)"
  using dyn_axiom_F3V[of vs "\<rceil>\<phi>"] by dt_prop


lemma dyn_axiom_AV:
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[dyn_eval] \<bbbA>\<bbbA> v . \<phi>"
  using assms
proof (induct v)
  case Nil
  then show ?case
    unfolding FOR_ALL_VEC.simps
    by dt_prop
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
  using dyn_hilbert_mp[of "\<lbrakk>\<pi>\<rbrakk>(\<phi> \<Rrightarrow> \<psi>)" "\<lbrakk> \<pi> \<rbrakk> \<phi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<psi>"]
  by dt_prop

lemma dt_box_G:
  "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi>"
  using dyn_axiom_G[of \<phi> \<pi>]
  by simp

lemma dt_box_M:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> \<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>"
  apply (rule dt_box_K)
  by (rule dt_box_G)

lemma dt_box_MR:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<psi>"
  using dyn_hilbert_mp[of "\<lbrakk> \<pi> \<rbrakk> \<phi>" "\<lbrakk> \<pi> \<rbrakk> \<psi>"]
  using dt_box_M[of \<phi> \<psi>  \<pi>]
  by simp

lemma dt_box_MRimp:
  "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<xi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> \<phi> \<Longrightarrow> \<Turnstile>[dyn_eval] \<xi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>"
  using dyn_hilbert_mp[of "\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<phi>" "\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<psi>"]
  using dt_box_M[of \<phi> \<psi>  \<pi>]
proof -
  assume assm1: "\<Turnstile>[dyn_eval] \<phi> \<Rrightarrow> \<psi>"
  assume assm2: "\<Turnstile>[dyn_eval] \<xi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> \<phi>"
  have "\<Turnstile>[dyn_eval] (\<lbrakk> \<pi> \<rbrakk> \<phi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<psi>) \<Longrightarrow> \<Turnstile>[dyn_eval]  ((\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<phi>) \<Rrightarrow> (\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<psi>))"
    by dt_prop
  then show ?thesis
    using dyn_hilbert_mp[of "\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<phi>" "\<xi> \<Rrightarrow> \<lbrakk> \<pi> \<rbrakk> \<psi>"]
    using dt_box_M[of \<phi> \<psi>  \<pi>]
    using assm1 assm2
    by blast
qed
    

lemma dt_diamond_K[intro]:
  "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<langle>\<pi>\<rangle> \<phi> \<Rrightarrow> \<langle>\<pi>\<rangle> \<psi>)"
proof -
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<lbrakk>\<pi>\<rbrakk>\<rceil>\<psi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi>)"
    using dyn_axiom_K[of \<pi> "\<rceil> \<psi>" "\<rceil> \<phi>"]
    by dt_prop
  then have fact: "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi> \<Rrightarrow> \<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<psi>)"
    by dt_prop
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)"
    apply (intro dt_box_M)
    by dt_prop
  also have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<rceil>\<psi> \<Rrightarrow> \<rceil>\<phi>)\<Rrightarrow>(\<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<phi> \<Rrightarrow> \<rceil>\<lbrakk>\<pi>\<rbrakk>\<rceil>\<psi>)"
    using fact by simp
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
      by dt_prop
    show "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<psi>"
      apply (rule dt_box_K)
      apply (rule dt_box_G)
      by dt_prop
  qed
next
  have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<psi> \<Rrightarrow> (\<phi> and \<psi>))"
    apply (rule dt_box_K)
    apply (rule dt_box_G)
    by dt_prop
  also have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<psi> \<Rrightarrow> (\<phi> and \<psi>)) \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<psi> \<Rrightarrow>  \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>))"
    by (rule dyn_axiom_K)
  finally have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk>\<phi> \<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk>\<psi> \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>))"
    apply (rule dt_prop_imp_trans)
    by dt_prop
  thus "\<Turnstile>[dyn_eval] ((\<lbrakk>\<pi>\<rbrakk>\<phi>) and (\<lbrakk>\<pi>\<rbrakk>\<psi>)) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>(\<phi> and \<psi>)"
    by dt_prop
qed

lemma dt_diamond_V:
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  fixes \<pi> :: "'prog"
  assumes "((Collect (dyn_fv_sem \<phi>)) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) = {}"
  shows "\<Turnstile>[dyn_eval] \<langle>\<pi>\<rangle>\<phi> \<Rrightarrow> \<phi>"
proof -
  have inv_fv: "((Collect (dyn_fv_sem (\<rceil> \<phi>))) \<inter> (Collect (dyn_prog_bv_sem \<pi>))) = {}"
    using assms dyn_fv_sem_not_subset by blast

  show ?thesis
    unfolding DIAMOND_def
    using dyn_axiom_V[OF inv_fv]
    by dt_prop
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
    using dyn_axiom_F3[of v "(\<phi> \<Rrightarrow> \<psi>)"]
    by dt_prop

  then have "\<Turnstile>[dyn_eval] \<lbrakk>\<pi>\<rbrakk> (\<bbbA> v . (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk> (\<phi> \<Rrightarrow> \<psi>)"
    by (rule dt_box_M)

  also have "\<Turnstile>[dyn_eval] \<lbrakk> \<pi> \<rbrakk> (\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> \<langle>\<pi>\<rangle> \<phi> \<Rrightarrow> \<langle>\<pi>\<rangle>\<psi> "
    using dt_diamond_K[of \<pi> \<phi> \<psi>]
    by dt_prop

  finally show ?thesis
    by dt_prop
qed
 
  


end

context dynamic_theory_eq
begin

lemma test:
  assumes "A \<Longrightarrow> (B \<Longrightarrow> C)"
    shows "A \<and> B \<Longrightarrow> C"
  using assms by blast


lemma eq_all_axiom_and:
  fixes v :: "'var"
  and w :: "'var"
  and \<phi> :: "('atom,'var,'prog) dyn_formula"
assumes "v \<noteq> w"
shows "\<Turnstile>[dyn_eval] ((FOL (eqPred v w)) and \<phi>) \<Rrightarrow> (\<bbbA> v . ((FOL (eqPred v w)) \<Rrightarrow> \<phi>))"
  using eq_all_axiom[OF assms, of \<phi>]
  by dt_prop


lemma eq_all_axiomV:
  fixes vs :: "'var list"
  and ws :: "'var list"
  and \<phi> :: "('atom,'var,'prog) dyn_formula"
assumes "disjnt (set vs) (set ws)"
    and "distinct vs"
    and "(length vs) = (length ws)"
  shows "\<Turnstile>[dyn_eval] ((FOL (eqPredV vs ws)) \<Rrightarrow> (\<phi> \<Rrightarrow>(\<bbbA>\<bbbA> vs . ((FOL (eqPredV vs ws)) \<Rrightarrow> \<phi>))))"
  using assms
  proof (induct vs arbitrary: ws)
    case Nil
      then have ws_nil: "ws = []" by simp
      show ?case
        unfolding ws_nil
        unfolding FOR_ALL_VEC.simps(1)
        by dt_prop
  next
    case (Cons v vs)
  
      obtain w ws' where ws_def: "ws = w # ws'"
        using Cons.prems(3) by (cases ws) auto
    
      let ?e    = "FOL (eqPred v w) :: ('atom,'var,'prog) dyn_formula"
      let ?E    = "FOL (eqPredV vs ws') :: ('atom,'var,'prog) dyn_formula"
      let ?A    = "FOL (eqPredV (v # vs) (w # ws')) :: ('atom,'var,'prog) dyn_formula"
      let ?Psi  = "\<bbbA>\<bbbA> vs . (?A \<Rrightarrow> \<phi>)"
    
      have vw_neq: "v \<noteq> w"
        using Cons.prems(1) ws_def by (auto simp add: disjnt_def)
      have w_notin: "w \<notin> set vs"
        using Cons.prems(1) ws_def by (auto simp add: disjnt_def)
      have disj': "disjnt (set vs) (set ws')"
        using Cons.prems(1) ws_def by (auto simp add: disjnt_def)
      have len': "length vs = length ws'"
        using Cons.prems(3) ws_def by simp
      have v_notin: "v \<notin> set vs"
        using Cons.prems(2) by simp
      have dist': "distinct vs"
        using Cons.prems(2) by simp
    
      text\<open>Induction hypothesis for the tails.\<close>
      have IH: "\<Turnstile>[dyn_eval] ?E \<Rrightarrow> (\<phi> \<Rrightarrow> (\<bbbA>\<bbbA> vs . (?E \<Rrightarrow> \<phi>)))"
        by (rule Cons.hyps[OF disj' dist' len'])
    
      text\<open>Splitting the head conjunct off the equality predicate.\<close>
      have eq_split: "\<Turnstile>[dyn_eval] ?A \<Rrightarrow> (?e and ?E)"
        apply (simp only: eqPredV.simps)
        by dt_prop
    
      text\<open>Strengthen the antecedent under the quantifier block.\<close>
      have weaken: "\<Turnstile>[dyn_eval] (?E \<Rrightarrow> \<phi>) \<Rrightarrow> (?A \<Rrightarrow> \<phi>)"
        using eq_split
        by dt_prop
      have step1: "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . (?E \<Rrightarrow> \<phi>)) \<Rrightarrow> ?Psi"
        by (rule dt_all_vec_M[OF weaken])
      have step2: "\<Turnstile>[dyn_eval] ?E \<Rrightarrow> (\<phi> \<Rrightarrow> ?Psi)"
        using IH step1 by dt_prop
    
      have main: "\<Turnstile>[dyn_eval] ?A \<Rrightarrow> (\<phi> \<Rrightarrow> (\<bbbA> v . ?Psi))"
      proof -
        text\<open>\<open>v\<close> and \<open>w\<close> are untouched by the block, so \<open>?e\<close> is rigid for it.\<close>
        have rigid: "list_all (\<lambda>x. \<not> dyn_fv_sem (\<rceil> ?e) x) vs"
          unfolding list_all_iff
        proof (intro ballI)
          fix x
          assume "x \<in> set vs"
          then have "x \<noteq> v" and "x \<noteq> w"
            using v_notin w_notin by auto
          then show "\<not> dyn_fv_sem (\<rceil> ?e) x"
            using eqPred_fv_sem vw_neq
            by simp
        qed
    
        have not_e_all: "\<Turnstile>[dyn_eval] (\<rceil> ?e) \<Rrightarrow> (\<bbbA>\<bbbA> vs . (\<rceil> ?e))"
          by (rule dyn_axiom_F2V[OF rigid])
    
        have "\<Turnstile>[dyn_eval] (\<rceil> ?e) \<Rrightarrow> (?A \<Rrightarrow> \<phi>)"
          using eq_split by dt_prop
        then have "\<Turnstile>[dyn_eval] (\<bbbA>\<bbbA> vs . (\<rceil> ?e)) \<Rrightarrow> ?Psi"
          by (rule dt_all_vec_M)
        with not_e_all have not_e_psi: "\<Turnstile>[dyn_eval] (\<rceil> ?e) \<Rrightarrow> ?Psi"
          by dt_prop
    
        text\<open>Hence the hypothesis \<open>?e\<close> can be discharged by cases.\<close>
        have "\<Turnstile>[dyn_eval] (?e \<Rrightarrow> ?Psi) \<Rrightarrow> ?Psi"
          using not_e_psi by dt_prop
        then have collapse: "\<Turnstile>[dyn_eval] (\<bbbA> v . (?e \<Rrightarrow> ?Psi)) \<Rrightarrow> (\<bbbA> v . ?Psi)"
          by (rule dt_fol_M)
    
        text\<open>The single-variable axiom, instantiated at \<open>?Psi\<close>.\<close>
        have ax: "\<Turnstile>[dyn_eval] ?e \<Rrightarrow> (?Psi \<Rrightarrow> (\<bbbA> v . (?e \<Rrightarrow> ?Psi)))"
          by (rule eq_all_axiom[OF vw_neq])
    
        show ?thesis
          using step2 eq_split ax collapse by dt_prop
      qed
    
      show ?case
        unfolding ws_def
        unfolding FOR_ALL_VEC.simps(2)
        using main by dt_prop
    qed

lemma eq_all_axiomV_and:
  fixes vs :: "'var list"
  and ws :: "'var list"
  and \<phi> :: "('atom,'var,'prog) dyn_formula"
assumes "disjnt (set vs) (set ws)"
    and "distinct vs"
    and "(length vs) = (length ws)"
  shows "\<Turnstile>[dyn_eval] (((FOL (eqPredV vs ws)) and \<phi>) \<Rrightarrow>(\<bbbA>\<bbbA> vs . ((FOL (eqPredV vs ws)) \<Rrightarrow> \<phi>)))"
  using eq_all_axiomV
  using assms
  using dt_prop_uncurry by blast

lemma eq_all_axiomV_and2:
  fixes vs :: "'var list"
  and ws :: "'var list"
  and \<phi> :: "('atom,'var,'prog) dyn_formula"
assumes "disjnt (set vs) (set ws)"
    and "distinct vs"
    and "(length vs) = (length ws)"
  shows "\<Turnstile>[dyn_eval] ((\<phi> and (FOL (eqPredV vs ws))) \<Rrightarrow>(\<bbbA>\<bbbA> vs . ((FOL (eqPredV vs ws)) \<Rrightarrow> \<phi>)))"
  using eq_all_axiomV
  using assms
  using dt_prop_uncurry
  by (meson dt_prop_conjI dt_prop_imp_trans dyn_hilbert_axiom_conj_e1
      dyn_hilbert_axiom_conj_e2)


end

end