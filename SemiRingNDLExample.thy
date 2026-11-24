subsection\<open>An Assume-Guarantee Example in NDL\<close>
text\<open>
Implementation formalized by Claude Opus after
intensive discussion with Samuel Teuber on 19th of August 2026.
Cross-checked by Samuel Teuber.
\<close>

text\<open>
Since NDL has no proof rules that look inside a neural network, a property of
the network's input-output behaviour has to enter the proof as an assumption.
Everything around it -- framing, conjunction, the step from box to diamond --
is then discharged by the generic dynamic-theory calculus.

The example uses three scalar variables: \<open>x\<close> is the network input, \<open>y\<close> its
output, and \<open>z\<close> is an unrelated variable that the network must not disturb.
\<close>

theory SemiRingNDLExample
  imports
    "DynamicLogicProof"
    "SemiRingNDL"
    "SemiRingNDLCompile"
begin

subsubsection\<open>Variables\<close>

abbreviation xv :: ndl_var where "xv \<equiv> NVar ''x'' [1]"
abbreviation yv :: ndl_var where "yv \<equiv> NVar ''y'' [1]"
abbreviation zv :: ndl_var where "zv \<equiv> NVar ''z'' [1]"

abbreviation lx :: ndl_var_lookup where "lx \<equiv> mk_lookup xv [0]"
abbreviation ly :: ndl_var_lookup where "ly \<equiv> mk_lookup yv [0]"
abbreviation lz :: ndl_var_lookup where "lz \<equiv> mk_lookup zv [0]"

lemma scalar_valid [simp]: "[] \<lhd> var_shape (NVar n [])"
  by (simp add: valid_index.Nil)

lemma lk_var_scalars [simp]:
  "lk_var lx = xv" "lk_var ly = yv" "lk_var lz = zv"
  apply (metis less_one mk_lookup_sel(1) ndl_var.sel(2) valid_index.simps)
  apply (metis less_one mk_lookup_sel(1) ndl_var.sel(2) valid_index.simps)
  by (metis less_one mk_lookup_sel(1) ndl_var.sel(2) valid_index.simps)

subsubsection\<open>The Property Language\<close>
text\<open>
We only need one shape of atom: a variable is (strictly) positive.
\<close>

definition pos :: "ndl_var_lookup \<Rightarrow> ndl_formula" where
  "pos u = FOL (ATOM (Less (Const 0) (Var u)))"

lemma pos_eval [simp]:
  "ndl_dl.sum_dl.dyn_eval (pos u) \<mu> = (0 < ndl_eval \<mu> u)"
  by (simp add: pos_def)

text\<open>
The semantic free variables of \<open>pos u\<close> are contained in \<open>{u}\<close>.  Note that
\<open>dyn_fv_sem\<close> is the semantic notion of the locale, so nothing syntactic is
needed here.
\<close>
(*print_interps folCore*)


lemma pos_FV [simp]: "ndl_dl.sum_dl.dyn_FV (pos u) v = (v = u)"
  by (simp add: pos_def)

lemma pos_fv:
  assumes "ndl_dl.sum_dl.dyn_fv_sem (pos u) x"
  shows "x = u"
  using ndl_dl.sum_dl.dyn_FV_fml_sound
  using assms pos_FV by blast

lemma pos_fv_set: "Collect (ndl_dl.sum_dl.dyn_fv_sem (pos x)) \<subseteq> {x}"
  using pos_fv by blast

subsubsection\<open>The Neural Program\<close>
text\<open>
A scalar-to-scalar network stored into \<open>y\<close> and read from \<open>x\<close>.  The shape
constraint of the program type is discharged by the declared shapes of the
two variables.
\<close>

lemma nn_prog_exists:
  assumes "stf_in Nsc = [1]" and "stf_out Nsc = [1]"
  shows "\<exists>p. nnp p = NNApply yv Nsc xv"
  apply (rule exI[of _ "Abs_ndl_nn_prog (NNApply yv Nsc xv)"])
  by (simp add: Abs_ndl_nn_prog_inverse assms(1,2) nnp_def wf_nn_def)

text\<open>
A neural program can only change its target variable.  This is what makes the
frame reasoning for \<open>z\<close> go through; it is proved directly from the semantics,
without a syntactic bound-variable function.
\<close>

lemma nn_bv_target:
  assumes "ndl_dl.sum_dl.dyn_prog_bv_sem (Inr p) x"
  shows "lk_var x = ntgt p"
proof (rule ccontr)
  assume ne: "lk_var x \<noteq> ntgt p"
  obtain \<mu> \<omega> where step: "nn_eval p \<mu> \<omega>" and diff: "ndl_eval \<mu> x \<noteq> ndl_eval \<omega> x"
    using assms by auto
  have "nst \<omega> (lk_var x) = nst \<mu> (lk_var x)"
    using step ne by (simp add: nn_eval_def)
  hence "ndl_eval \<mu> x = ndl_eval \<omega> x" by (simp add: ndl_eval_def)
  thus False using diff by simp
qed

subsubsection\<open>The Lookups of a Variable\<close>

definition nlk_set :: "ndl_var \<Rightarrow> ndl_var_lookup set" where
  "nlk_set v = {x. lk_var x = v}"

lemma nlk_setI [intro]: "lk_var x = v \<Longrightarrow> x \<in> nlk_set v"
  and nlk_setD [dest]: "x \<in> nlk_set v \<Longrightarrow> lk_var x = v"
  by (simp_all add: nlk_set_def)

lemma nlk_set_image: "nlk_set v = mk_lookup v ` {i. i \<lhd> var_shape v}"
proof
  show "nlk_set v \<subseteq> mk_lookup v ` {i. i \<lhd> var_shape v}"
  proof
    fix x assume "x \<in> nlk_set v"
    hence v: "lk_var x = v" by (rule nlk_setD)
    hence "x = mk_lookup v (lk_idx x)" and "lk_idx x \<lhd> var_shape v"
      using mk_lookup_lk lk_valid by auto
    thus "x \<in> mk_lookup v ` {i. i \<lhd> var_shape v}" by blast
  qed
  show "mk_lookup v ` {i. i \<lhd> var_shape v} \<subseteq> nlk_set v"
    by (auto simp add: mk_lookup_sel)
qed

lemma nlk_set_finite: "finite (nlk_set v)"
  by (simp add: nlk_set_def finite_lookups_of_var)

lemma nlk_set_disjoint: "v \<noteq> w \<Longrightarrow> nlk_set v \<inter> nlk_set w = {}"
  by (auto simp add: nlk_set_def)

lemma nst_upd_exists:
  assumes "dims T = var_shape v"
  shows "\<exists>\<mu>'. nst \<mu>' = (nst \<mu>)(v := T)"
proof -
  have "wf_nstate ((nst \<mu>)(v := T))" using assms by (simp add: wf_nstate_def)
  thus ?thesis by (metis nst_Abs)
qed

lemma nn_bv_subset:
  "Collect (ndl_dl.sum_dl.dyn_prog_bv_sem (Inr p)) \<subseteq> nlk_set (ntgt p)"
proof
  fix x assume "x \<in> Collect (ndl_dl.sum_dl.dyn_prog_bv_sem (Inr p))"
  then obtain \<mu> \<omega> where step: "nn_eval p \<mu> \<omega>" and diff: "ndl_eval \<mu> x \<noteq> ndl_eval \<omega> x"
    by auto
  have "lk_var x = ntgt p"
  proof (rule ccontr)
    assume ne: "lk_var x \<noteq> ntgt p"
    hence "nst \<omega> (lk_var x) = nst \<mu> (lk_var x)" using step by (simp add: nn_eval_def)
    hence "ndl_eval \<mu> x = ndl_eval \<omega> x" by (simp add: ndl_eval_def)
    thus False using diff by simp
  qed
  thus "x \<in> nlk_set (ntgt p)" by (rule nlk_setI)
qed


lemma nlk_singleton_disjoint:
  assumes "lk_var u \<noteq> v"
  shows "{u} \<inter> nlk_set v = {}"
  using assms by (simp add: nlk_set_def)

text\<open>
Hence \<open>z\<close> survives the network application.  This is the one place where
\<open>dyn_axiom_V\<close> is used; the disjointness side condition is discharged by the
two lemmas above.
\<close>


lemma frame_z:
  assumes tgt: "ntgt p = yv"
  shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lz) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos lz)"
proof -
  have "Collect (ndl_dl.sum_dl.dyn_fv_sem (pos lz)) \<inter>
        Collect (ndl_dl.sum_dl.dyn_prog_bv_sem (Inr p)) = {}"
    using pos_fv_set[of lz]
    using nn_bv_subset[of p]
    unfolding tgt
    using nlk_singleton_disjoint[of lz yv]
    using lk_var_scalars(3) by auto

  thus ?thesis
    using ndl_dl.sum_dl.dyn_axiom_V[of "pos lz" "Inr p"] by blast
qed

subsubsection\<open>The Assume-Guarantee Proof\<close>
text\<open>
Given a contract for the network -- a positive input yields a positive output --
we conclude that from a state where both \<open>x\<close> and \<open>z\<close> are positive, the network
application terminates in a state where both \<open>y\<close> and \<open>z\<close> are positive.

Only the propositional reshuffling steps are done semantically (as in the
\<open>dt_prop_*\<close> rules themselves); every modal step goes through the calculus.
\<close>

lemma ndl_assume_guarantee:
  fixes p :: ndl_nn_prog
  assumes p_shape: "nnp p = NNApply yv Nsc xv"
      and contract: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
    shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval]
             ((pos lx) and (pos lz)) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> ((pos ly) and (pos lz))"
proof -
  have tgt: "ntgt p = yv" using p_shape by simp

  text\<open>Step 1: the guarantee, weakened to the joint precondition.\<close>
  have a1: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] ((pos lx) and (pos lz)) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
    using contract by (auto simp add: dyn_sem)

  text\<open>Step 2: the frame property for \<open>z\<close>, likewise weakened.\<close>
  have a2: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] ((pos lx) and (pos lz)) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos lz)"
    using frame_z[OF tgt] by (auto simp add: dyn_sem)

  text\<open>Step 3: combine the two postconditions.\<close>
  have conj: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval]
                ((pos lx) and (pos lz)) \<Rrightarrow>
                ((\<lbrakk>Inr p\<rbrakk> (pos ly)) and (\<lbrakk>Inr p\<rbrakk> (pos lz)))"
    using a1 a2
    by (rule ndl_dl.sum_dl.dt_prop_conjI)

  text\<open>Step 4: push the conjunction under the box.\<close>
  have box_and: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval]
                   ((\<lbrakk>Inr p\<rbrakk> (pos ly)) and (\<lbrakk>Inr p\<rbrakk> (pos lz))) \<Rrightarrow>
                   \<lbrakk>Inr p\<rbrakk> ((pos ly) and (pos lz))"
    using ndl_dl.sum_dl.dt_box_and
    by (auto simp add: dyn_sem)

  have boxed: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval]
                 ((pos lx) and (pos lz)) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> ((pos ly) and (pos lz))"
    using conj box_and by (rule ndl_dl.sum_dl.dt_prop_imp_trans)

  show ?thesis using boxed by (auto simp add: dyn_sem)
qed

lemma idx0_valid [simp]: "[0] \<lhd> var_shape (NVar n [1])"
  by (simp add: valid_index.Cons valid_index.Nil)


lemma nst_surj:
  assumes "dims t = var_shape v"
  shows "\<exists>\<mu>. nst \<mu> v = t"
proof -
  obtain \<mu>0 :: ndl_state where True by simp
  obtain \<mu> where "nst \<mu> = (nst \<mu>0)(v := t)" using nst_upd_exists[OF assms] by blast
  thus ?thesis by (intro exI[of _ \<mu>]) simp
qed

lemma valid_impE:
  assumes "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] \<phi> \<Rrightarrow> \<psi>"
      and "ndl_dl.sum_dl.dyn_eval \<phi> \<mu>"
    shows "ndl_dl.sum_dl.dyn_eval \<psi> \<mu>"
  using assms by (auto simp add: dyn_sem)

lemma valid_impI:
  assumes "\<And>\<mu>. ndl_dl.sum_dl.dyn_eval \<phi> \<mu> \<Longrightarrow> ndl_dl.sum_dl.dyn_eval \<psi> \<mu>"
  shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] \<phi> \<Rrightarrow> \<psi>"
  using assms by (auto simp add: dyn_sem)

lemma pos_box_reduce:
  assumes p_shape: "nnp p = NNApply yv Nsc xv"
  shows "(\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)) =
         (\<forall>t. dims t = [1] \<longrightarrow> 0 < lookup t [0] \<longrightarrow> 0 < lookup (stf_apply Nsc t) [0])"
proof -
  have tgt: "ntgt p = yv" and src: "nsrc p = xv" and fn: "nfun p = Nsc"
    using p_shape by simp_all
  have box: "\<And>\<mu>. ndl_dl.sum_dl.dyn_eval (\<lbrakk>Inr p\<rbrakk> (pos ly)) \<mu> =
                 (0 < lookup (stf_apply Nsc (nst \<mu> xv)) [0])"
  proof -
    fix \<mu>
    have "\<And>\<omega>. nn_eval p \<mu> \<omega> \<Longrightarrow> nst \<omega> yv = stf_apply Nsc (nst \<mu> xv)"
      using tgt src fn by (simp add: nn_eval_def)
    moreover obtain \<omega> where "nn_eval p \<mu> \<omega>" using nn_total_det by blast
    ultimately show "ndl_dl.sum_dl.dyn_eval (\<lbrakk>Inr p\<rbrakk> (pos ly)) \<mu> =
                     (0 < lookup (stf_apply Nsc (nst \<mu> xv)) [0])"
      using idx0_valid by force
  qed
  have pre: "\<And>\<mu>. ndl_dl.sum_dl.dyn_eval (pos lx) \<mu> = (0 < lookup (nst \<mu> xv) [0])"
    using idx0_valid by auto
   show ?thesis
    proof (rule iffI)
      assume L: "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
      show "\<forall>t. dims t = [1] \<longrightarrow> 0 < lookup t [0] \<longrightarrow> 0 < lookup (stf_apply Nsc t) [0]"
      proof (intro allI impI)
        fix t :: "real tensor"
        assume dt: "dims t = [1]" and pt: "0 < lookup t [0]"
        obtain \<mu> where mu: "nst \<mu> xv = t"
          using nst_surj[of t xv] dt
          using ndl_var.sel(2) by presburger
        have "ndl_dl.sum_dl.dyn_eval (pos lx) \<mu>" using pt mu pre by simp
        hence "ndl_dl.sum_dl.dyn_eval (\<lbrakk>Inr p\<rbrakk> (pos ly)) \<mu>" using L by (rule_tac valid_impE)
        thus "0 < lookup (stf_apply Nsc t) [0]" using box mu by simp
      qed
    next
      assume R: "\<forall>t. dims t = [1] \<longrightarrow> 0 < lookup t [0] \<longrightarrow> 0 < lookup (stf_apply Nsc t) [0]"
      show "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
      proof (rule valid_impI)
        fix \<mu> assume "ndl_dl.sum_dl.dyn_eval (pos lx) \<mu>"
        hence "0 < lookup (nst \<mu> xv) [0]" using pre by simp
        moreover have "dims (nst \<mu> xv) = [1]" by simp
        ultimately have "0 < lookup (stf_apply Nsc (nst \<mu> xv)) [0]" using R by blast
        thus "ndl_dl.sum_dl.dyn_eval (\<lbrakk>Inr p\<rbrakk> (pos ly)) \<mu>" using box by simp
      qed
    qed
qed

definition myNN where "myNN = (\<lambda> v . v)"

definition shapedNN where "shapedNN = mk_stf myNN [1] [1]"

lemma shapedNN_ok: "\<And>x. dims x = [1] \<Longrightarrow> dims (myNN x) = [1]"
    unfolding myNN_def
    by simp

lemma ndl_nn_guarantee:
  fixes p :: ndl_nn_prog
  assumes p_shape: "nnp p = NNApply yv shapedNN xv"
    shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
proof -
  show ?thesis
    unfolding pos_box_reduce[OF p_shape]
    unfolding shapedNN_def
    apply (simp add: mk_stf_sel shapedNN_ok)
    unfolding myNN_def
    by simp
qed

lemma lk_idx_vecs [simp]: "lk_idx lx = [0]" "lk_idx ly = [0]" "lk_idx lz = [0]"
  using idx0_valid mk_lookup_sel(2) apply blast
  using idx0_valid mk_lookup_sel(2) apply blast
  using idx0_valid mk_lookup_sel(2) by blast
  

declare pos_def [ndl_ok, ndl_cmp]
declare lk_var_scalars lk_idx_vecs ndl_var.inject [ndl_ok, ndl_cmp]

lemma ndl_full_guarantee:
  assumes p_shape: "nnp p = NNApply yv shapedNN xv"
  shows "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] (pos lx) \<Rrightarrow> \<lbrakk>Inr p\<rbrakk> (pos ly)"
  apply (ndl_compile shape: p_shape ndl_cmp: shapedNN_def mk_stf_sel shapedNN_ok)
  by (simp add: myNN_def)
  




end
