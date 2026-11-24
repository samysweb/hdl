theory CounterfactualsInfFlow
  imports
    Main
    "ExtensionalDynamicLogic"
    "DynamicLogicBV"
    "DynamicLogicProof"
    "ConverseDynamicLogic"
begin

section\<open>Counterfactuals and Information Flow\<close>

locale converse_dynamic_logic_eq =
  dynamic_theory_eq atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV eqPred
  +
  ConverseDynLog atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV dyn_prog_BV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    and eqPred :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
    and dyn_prog_BV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
begin


lemma eqPred_fv_sem_only:
  assumes "converse_dl.dlc.dyn_fv_sem (FOL (eqPred v w)) x"
    and "v \<noteq> w"
  shows "x=v \<or> x=w"
  using assms eqPred_sound
  apply (auto simp add: dyn_sem fol_equal_everywhere_but_def)
  using fol_states_agree_on_def apply force
  using fol_states_agree_on_def by force

lemma eq_bv_disjoint:
  assumes "v \<noteq> w" "\<not> full_prog_bv_syn \<pi> v" "\<not> full_prog_bv_syn \<pi> w"
  shows "Collect (converse_dl.dlc.dyn_fv_sem (FOL (eqPred v w)))
           \<inter> Collect (converse_dl.dlc.dyn_prog_bv_sem \<pi>) = {}"
proof -
  have "Collect (converse_dl.dlc.dyn_fv_sem (FOL (eqPred v w))) \<subseteq> {v,w}"
  using eqPred_fv_sem_only[of v w] assms
  by blast
  thus ?thesis
    using assms c_bv_sound by blast
qed

(*
d,e,r, and G are distinct variables
e and r are fresh variables (not read or written by C or D
*)

lemma inf_flow_cf:
  assumes de: "d \<noteq> e" and dr: "d \<noteq> r" and er: "e \<noteq> r"
      and Ge: "G \<noteq> e" and Gr: "G \<noteq> r"
      and eC: "\<not> full_prog_bv_syn C e" and eD: "\<not> full_prog_bv_syn D e"
      and rCb: "\<not> full_prog_bv_syn C r" and rDb: "\<not> full_prog_bv_syn D r"
      and rCf: "\<not> full_prog_fv_syn C r" and rDf: "\<not> full_prog_fv_syn D r"
  assumes weak_tot: "\<Turnstile>[converse_dl.dlc.dyn_eval] \<langle>D\<rangle> converse_dl.dlc.DYNTRUE"
  assumes ni: "\<Turnstile>[converse_dl.dlc.dyn_eval] \<bbbE> r . \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d r))"
    shows "\<Turnstile>[converse_dl.dlc.dyn_eval]
            (\<lbrakk>D\<rbrakk>(FOL (eqPred d e)))
            \<Rrightarrow> (\<lbrakk>(CONVERSE C)\<rbrakk> \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d e)))"
proof -
  text \<open>
    Proof idea.
    Noninterference statement:
    for some fixed value r, every G and every run of C;D ends with d = r.
    If one C-run followed by D yields d = e, then e = r,
    hence every G and every run of C;D yields d = e.
    Finally, the converse axiom from above \<open>\<langle>C\<rangle>P \<Rrightarrow> Q\<close> into \<open>P \<Rrightarrow> [C\<^sup>-\<^sup>1]Q\<close>.\<close>

  \<comment> \<open>Atomic equalities and truth\<close>
  let ?d_eq_e = "FOL (eqPred d e) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?d_eq_r = "FOL (eqPred d r) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?e_eq_r = "FOL (eqPred e r) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?top    = "converse_dl.dlc.DYNTRUE :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"

  \<comment> \<open>Some C-run after which D always yields d = e\<close>
  let ?some_run = "\<langle>C\<rangle>\<lbrakk>D\<rbrakk> ?d_eq_e"
  \<comment> \<open>For every G and all runs of C;D we get d = e afterwards\<close>
  let ?all_runs = "\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?d_eq_e"
  \<comment> \<open>Noninterference instance for a fixed output value r\<close>
  let ?NI_r     = "\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?d_eq_r"

  \<comment> \<open>Necessitation of D-totality: after any C-run, D can still run\<close>
  have tot: "\<Turnstile>[converse_dl.dlc.dyn_eval] \<lbrakk>C\<rbrakk>\<langle>D\<rangle> converse_dl.dlc.DYNTRUE"
    using weak_tot converse_dl.dlc.dyn_axiom_G by auto

  text \<open>Equality reasoning on atoms (transitivity/symmetry).\<close>
  text\<open>d = e \<and> d = r \<Longrightarrow> e = r\<close>
  have eq1: "\<Turnstile>[converse_dl.dlc.dyn_eval] (?d_eq_e and ?d_eq_r) \<Rrightarrow> ?e_eq_r"
  proof (rule converse_dl.dlc.dt_propI)
    fix \<mu>
    show "converse_dl.dlc.dyn_eval ((?d_eq_e and ?d_eq_r) \<Rrightarrow> ?e_eq_r) \<mu>"
      using fol_eqPred_sound[OF de, of \<mu>] fol_eqPred_sound[OF dr, of \<mu>]
            fol_eqPred_sound[OF er, of \<mu>]
      by (simp add: dyn_sem)
  qed
  text\<open>d = r \<and> e = r \<Longrightarrow> d = e\<close>
  have eq2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (?d_eq_r and ?e_eq_r) \<Rrightarrow> ?d_eq_e"
  proof (rule converse_dl.dlc.dt_propI)
    fix \<mu>
    show "converse_dl.dlc.dyn_eval ((?d_eq_r and ?e_eq_r) \<Rrightarrow> ?d_eq_e) \<mu>"
      using fol_eqPred_sound[OF de, of \<mu>] fol_eqPred_sound[OF dr, of \<mu>]
            fol_eqPred_sound[OF er, of \<mu>]
      by (simp add: dyn_sem)
  qed

  text \<open>Step 1: instantiate G in NI:  \<forall>G.[C][D] d=r \<Longrightarrow> [C][D] d=r.\<close>
  have s1: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI_r \<Rrightarrow> \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?d_eq_r"
    by (rule converse_dl.dlc.dyn_axiom_F3)

  text \<open>
  Step 2:
    [C][D] d=r,  [C]\<langle>D\<rangle>\<top>,  \<langle>C\<rangle>[D] d=e  \<Longrightarrow>  \<langle>C\<rangle>\<langle>D\<rangle> e=r.
    Inside D:
      [D] d=r \<and> [D] d=e gives [D] e=r; totality upgrades it to \<langle>D\<rangle> e=r.
    Inside C:
      lift with box-K, then use diamond-K.
  \<close>
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?d_eq_r \<Rrightarrow> (?d_eq_e \<Rrightarrow> ?e_eq_r)"
    using eq1 by converse_dl.dlc.dt_prop
  text\<open>[D] d=r \<Longrightarrow> [D] d=e \<Longrightarrow> [D] e=r\<close>
  then have inD1: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?d_eq_e) \<Rrightarrow> (\<lbrakk>D\<rbrakk>?e_eq_r))"
    by (rule converse_dl.dlc.dt_box_K2)
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (?top \<Rrightarrow> ?e_eq_r)"
    by converse_dl.dlc.dt_prop
  text\<open>[D] e=r \<Longrightarrow> \<langle>D\<rangle>\<top> \<Longrightarrow> \<langle>D\<rangle> e=r\<close>
  then have inD2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?e_eq_r) \<Rrightarrow> ((\<langle>D\<rangle>?top) \<Rrightarrow> (\<langle>D\<rangle>?e_eq_r))"
    by (rule converse_dl.dlc.dt_box_dia_K)
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> ((\<langle>D\<rangle>?top) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?d_eq_e) \<Rrightarrow> (\<langle>D\<rangle>?e_eq_r)))"
    using inD1 inD2 by converse_dl.dlc.dt_prop
  text\<open>Lift under [C]\<close>
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval]
               (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> ((\<lbrakk>C\<rbrakk>\<langle>D\<rangle>?top) \<Rrightarrow> (\<lbrakk>C\<rbrakk>((\<lbrakk>D\<rbrakk>?d_eq_e) \<Rrightarrow> (\<langle>D\<rangle>?e_eq_r))))"
    by (rule converse_dl.dlc.dt_box_K2)
  text\<open>Combine with the C-run from ?some_run\<close>
  moreover have "\<Turnstile>[converse_dl.dlc.dyn_eval]
               (\<lbrakk>C\<rbrakk>((\<lbrakk>D\<rbrakk>?d_eq_e) \<Rrightarrow> (\<langle>D\<rangle>?e_eq_r))) \<Rrightarrow> (?some_run \<Rrightarrow> (\<langle>C\<rangle>\<langle>D\<rangle>?e_eq_r))"
    by (rule converse_dl.dlc.dt_diamond_K)
  ultimately have s2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> (?some_run \<Rrightarrow> (\<langle>C\<rangle>\<langle>D\<rangle>?e_eq_r))"
    using tot by converse_dl.dlc.dt_prop

  text \<open>
    Step 3:
      C and D do not bind e or r.
      Therefore, e = r is rigid: \<langle>C\<rangle>\<langle>D\<rangle> e=r \<Longrightarrow> e=r.
  \<close>
  have dD: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>D\<rangle>?e_eq_r) \<Rrightarrow> ?e_eq_r"
    by (rule converse_dl.dlc.dt_diamond_V[OF eq_bv_disjoint[OF er eD rDb]])
  have dC: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>?e_eq_r) \<Rrightarrow> ?e_eq_r"
    by (rule converse_dl.dlc.dt_diamond_V[OF eq_bv_disjoint[OF er eC rCb]])
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>\<langle>D\<rangle>?e_eq_r) \<Rrightarrow> (\<langle>C\<rangle>?e_eq_r)"
    using dD by (rule converse_dl.dlc.c_dia_mono)
  then have s3: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>\<langle>D\<rangle>?e_eq_r) \<Rrightarrow> ?e_eq_r"
    using dC by converse_dl.dlc.dt_prop

  text \<open>
    Step 4:
      conversely, push e = r under \<forall>G [C][D] 
      via rigidity + G \<notin> {e, r}.
    \<close>
  text \<open>e=r \<Longrightarrow> [C][D] e=r via V\<close>
  have vD: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (\<lbrakk>D\<rbrakk>?e_eq_r)"
    by (rule converse_dl.dlc.dyn_axiom_V[OF eq_bv_disjoint[OF er eD rDb]])
  have vC: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (\<lbrakk>C\<rbrakk>?e_eq_r)"
    by (rule converse_dl.dlc.dyn_axiom_V[OF eq_bv_disjoint[OF er eC rCb]])
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>?e_eq_r) \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r)"
    using vD by (rule converse_dl.dlc.dt_box_M)
  then have erCD: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r)"
    using vC by converse_dl.dlc.dt_prop
  text\<open>e=r \<Longrightarrow> \<forall>G. e=r   (G not free in e = r)\<close>
  have erG: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (\<bbbA> G . ?e_eq_r)"
    apply (rule converse_dl.dlc.dyn_axiom_F2)
    using Ge Gr eqPred_fv_sem_only er by blast
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<bbbA> G . ?e_eq_r) \<Rrightarrow> (\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r)"
    using erCD by (rule converse_dl.dlc.dt_fol_M)
  text\<open>Combined result:\<close>
  then have s4: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?e_eq_r \<Rrightarrow> (\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r)"
    using erG by converse_dl.dlc.dt_prop

  text \<open>Step 5:
          transitivity under \<forall>G [C][D]:
          NI_r gives us the postcondition d=r
          The second assumptions gives us the postcondition e=r
          Together, this yields d=e
          NI_r \<and> \<forall>G.[C][D] e=r \<Longrightarrow> \<forall>G.[C][D] d=e.
  \<close>
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?d_eq_r \<Rrightarrow> (?e_eq_r \<Rrightarrow> ?d_eq_e)"
    using eq2 by converse_dl.dlc.dt_prop
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?e_eq_r) \<Rrightarrow> (\<lbrakk>D\<rbrakk>?d_eq_e))"
    by (rule converse_dl.dlc.dt_box_K2)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?d_eq_r) \<Rrightarrow> ((\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r) \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?d_eq_e))"
    by (rule converse_dl.dlc.dt_box_K2)
  then have s5: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI_r \<Rrightarrow> ((\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?e_eq_r) \<Rrightarrow> ?all_runs)"
    by (rule converse_dl.dlc.c_all_K2)

  \<comment> \<open>Chain s1–s5:  NI_r \<Longrightarrow> ?some_run \<Longrightarrow> ?all_runs\<close>
  have main: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI_r \<Rrightarrow> (?some_run \<Rrightarrow> ?all_runs)"
    using s1 s2 s3 s4 s5 by converse_dl.dlc.dt_prop

  text \<open>Step 6:
          \<exists>-elimination on r.
          Since r is not free in \<open>?some_run \<Rrightarrow> ?all_runs\<close>,
          contrapose main,
          generalise over r,
          combine with ni = \<not>\<forall>r.\<not>NI_r.\<close>
  have r_free: "\<not> converse_dl.dlc.dyn_fv_sem (?some_run \<Rrightarrow> ?all_runs) r"
  proof -
    have f0: "\<not> converse_dl.dlc.dyn_fv_sem ?d_eq_e r"
      using de dr eqPred_fv_sem_only er by blast
    have f1: "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>D\<rbrakk>?d_eq_e) r"
      using rDf f0 by (rule fv_box_free)
    have f2: "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?d_eq_e) r"
      using rCf f1 by (rule fv_box_free)
    have fA: "\<not> converse_dl.dlc.dyn_fv_sem ?some_run r"
      using rCf f1 by (rule fv_dia_free)
    have fB: "\<not> converse_dl.dlc.dyn_fv_sem ?all_runs r"
      using f2 by (rule converse_dl.dlc.dyn_fv_sem_all_intro)
    show ?thesis
      using fA fB converse_dl.dlc.dyn_fv_sem_imp_elim by blast
  qed
  have rnf: "\<not> converse_dl.dlc.dyn_fv_sem (\<rceil>(?some_run \<Rrightarrow> ?all_runs)) r"
    using r_free converse_dl.dlc.dyn_fv_sem_not_eq by metis
  \<comment> \<open>\<not>(A \<Rrightarrow> B) \<Longrightarrow> \<forall>r. \<not>(A \<Rrightarrow> B)\<close>
  have F2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<rceil>(?some_run \<Rrightarrow> ?all_runs)) \<Rrightarrow> (\<bbbA> r . \<rceil>(?some_run \<Rrightarrow> ?all_runs))"
    using rnf by (rule converse_dl.dlc.dyn_axiom_F2)
  \<comment> \<open>Contrapositive of main, then generalise over r\<close>
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<rceil>(?some_run \<Rrightarrow> ?all_runs)) \<Rrightarrow> (\<rceil> ?NI_r)"
    using main by converse_dl.dlc.dt_prop
  then have M: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<bbbA> r . \<rceil>(?some_run \<Rrightarrow> ?all_runs)) \<Rrightarrow> (\<bbbA> r . \<rceil> ?NI_r)"
    by (rule converse_dl.dlc.dt_fol_M)
  have fwd: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?some_run \<Rrightarrow> ?all_runs"
    using ni F2 M by converse_dl.dlc.dt_prop

  text \<open>Step 7: converse adjunction:  \<langle>C\<rangle>P \<Rrightarrow> Q  \<Longrightarrow>  P \<Rrightarrow> [C⁻]Q.\<close>
  show ?thesis
    using fwd
    by (rule dt_l_converse)
qed

lemma inf_flow_cf_reduced:
  assumes de: "d \<noteq> e" and dr: "d \<noteq> r" and er: "e \<noteq> r"
      and Ge: "G \<noteq> e" and Gr: "G \<noteq> r"
      and eC: "\<not> dyn_prog_BV C e" and eD: "\<not> dyn_prog_BV D e"
      and rCb: "\<not> dyn_prog_BV C r" and rDb: "\<not> dyn_prog_BV D r"
      and rCf: "\<not> dyn_prog_FV C r" and rDf: "\<not> dyn_prog_FV D r"
  assumes weak_tot: "\<Turnstile>[dyn_eval] \<langle>D\<rangle> DYNTRUE"
  assumes ni: "\<Turnstile>[dyn_eval] \<bbbE> r . \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d r))"
    shows "\<Turnstile>[converse_dl.dlc.dyn_eval]
            (\<lbrakk>(CPROG D)\<rbrakk>(FOL (eqPred d e)))
            \<Rrightarrow> (\<lbrakk>(CONVERSE (CPROG C))\<rbrakk> \<bbbA> G . \<lbrakk>(CPROG C)\<rbrakk>\<lbrakk>(CPROG D)\<rbrakk> (FOL (eqPred d e)))"
proof -
  show ?thesis
  proof (rule inf_flow_cf[where r=r],
          (simp_all add: de dr er Ge Gr eC eD rCb rDb rCf rDf))
    show "\<Turnstile>[converse_dl.dlc.dyn_eval] \<langle>(CPROG D)\<rangle> converse_dl.dlc.DYNTRUE"
      using dyn_axiom_CR[of "\<langle>D\<rangle> DYNTRUE"]
      using weak_tot
      unfolding DIAMOND_def DYNTRUE_def
      unfolding translate.simps
      unfolding converse_dl.dlc.DIAMOND_def
      unfolding converse_dl.dlc.DYNTRUE_def
      by auto
    show "\<Turnstile>[converse_dl.dlc.dyn_eval] \<bbbE> r . \<bbbA> G . \<lbrakk>(CPROG C)\<rbrakk>\<lbrakk>(CPROG D)\<rbrakk> (FOL (eqPred d r))"
      using dyn_axiom_CR[of "\<bbbE> r . \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d r))"]
      using ni
      unfolding DYN_EX_def converse_dl.dlc.DYN_EX_def
      unfolding translate.simps
      by auto
  qed
qed
end
end