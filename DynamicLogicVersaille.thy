theory DynamicLogicVersaille
  imports
    Main
    "DynamicLogic"
    "DynamicLogicProof"
    "DynamicLogicHelpers"
    "KATDynamicLogic"
    "HOL-Eisbach.Eisbach"
begin

locale dynamic_theory_versaille =
    dynamic_theory_eq atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV eqPred
    +
    regular_lifting atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    and eqPred :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
begin 

interpretation kat_dl_eq:
  dynamic_theory_eq "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"
  by (smt (verit, best) dynamic_theory.dt_ev_fol dynamic_theory_eq_axioms
      dynamic_theory_eq_axioms_def dynamic_theory_eq_def
      kat_dl.dynamic_theory_axioms)

lemma eqPredV_ex:
  assumes twins: "twin_vec ws wsplus"
      and dist: "distinct wsplus"
      and disj: "disjnt (set ws) (set wsplus)"
    shows "\<Turnstile>[kat_dl.dyn_eval] \<bbbE>\<bbbE> wsplus . (FOL (eqPredV ws wsplus))"
  unfolding theory_valid_def
proof (intro allI)
  fix \<mu>
  obtain \<omega> where "fol_states_agree_on (\<lambda>v. v \<notin> set wsplus) \<mu> \<omega>"
              and "dyn_eval (FOL (eqPredV ws wsplus)) \<omega>"
    using kat_dl_eq.eqPredV_copy[OF twins dist disj]
    using dt_ev_fol kat_dl.dt_ev_fol by blast
  then show "kat_dl.dyn_eval (\<bbbE>\<bbbE> wsplus . (FOL (eqPredV ws wsplus))) \<mu>"
    using kat_dl.ex_vec_witnessI
    using dt_ev_fol kat_dl.dt_ev_fol by blast
qed

lemma dt_monitorminus_elim:
  fixes ws wsplus :: "'var list"
  assumes twins: "twin_vec ws wsplus"
      and dist:  "distinct wsplus"
      and disj:  "disjnt (set ws) (set wsplus)"
      and fresh: "\<And>x. x \<in> set wsplus \<Longrightarrow> \<not> kat_dl.dyn_fv_sem \<psi> x"
    shows "\<Turnstile>[kat_dl.dyn_eval]
            (\<bbbA>\<bbbA> wsplus . (M \<Rrightarrow> (\<bbbA>\<bbbA> ws . ((FOL (kat_dl_eq.eqPredV ws wsplus)) \<Rrightarrow> \<psi>))))
            \<Rrightarrow> ((\<bbbA>\<bbbA> wsplus . ((FOL (kat_dl_eq.eqPredV ws wsplus)) \<Rrightarrow> M)) \<Rrightarrow> \<psi>)"
proof -
  let ?E      = "FOL (kat_dl_eq.eqPredV ws wsplus)"
  let ?mm     = "\<bbbA>\<bbbA> wsplus . (?E \<Rrightarrow> M)"
  let ?\<phi>      = "?mm \<Rrightarrow> \<psi>"
  let ?\<phi>plus  = "M \<Rrightarrow> (\<bbbA>\<bbbA> ws . (?E \<Rrightarrow> \<psi>))"

  have inst_mm: "\<Turnstile>[kat_dl.dyn_eval] ?mm \<Rrightarrow> (?E \<Rrightarrow> M)"
    by (rule kat_dl.dyn_axiom_F3V)
  have inst_ws: "\<Turnstile>[kat_dl.dyn_eval] (\<bbbA>\<bbbA> ws . (?E \<Rrightarrow> \<psi>)) \<Rrightarrow> (?E \<Rrightarrow> \<psi>)"
    by (rule kat_dl.dyn_axiom_F3V)
  have step: "\<Turnstile>[kat_dl.dyn_eval] ?\<phi>plus \<Rrightarrow> (?E \<Rrightarrow> ?\<phi>)"
    using inst_mm inst_ws by dt_prop

  have gen: "\<Turnstile>[kat_dl.dyn_eval] (\<bbbA>\<bbbA> wsplus . ?\<phi>plus) \<Rrightarrow> (\<bbbA>\<bbbA> wsplus . (?E \<Rrightarrow> ?\<phi>))"
    by (rule kat_dl.dt_all_vec_M[OF step])

  have ex_E: "\<Turnstile>[kat_dl.dyn_eval] \<bbbE>\<bbbE> wsplus . ?E"
    by (rule eqPredV_ex[OF twins dist disj])

  have dual1: "\<Turnstile>[kat_dl.dyn_eval] (\<bbbA>\<bbbA> wsplus . (?E \<Rrightarrow> ?\<phi>))
                            \<Rrightarrow> ((\<bbbE>\<bbbE> wsplus . ?E) \<Rrightarrow> (\<bbbE>\<bbbE> wsplus . ?\<phi>))"
    by (rule kat_dl.dyn_axiom_F1VE)

  have rigid: "list_all (\<lambda>x. \<not> kat_dl.dyn_fv_sem ?\<phi> x) wsplus"
    unfolding list_all_iff
  proof (intro ballI)
    fix x assume x: "x \<in> set wsplus"
    have "\<not> kat_dl.dyn_fv_sem ?mm x"
      by (rule kat_dl.all_vec_fv_bound[OF x])
    then show "\<not> kat_dl.dyn_fv_sem ?\<phi> x"
      using fresh[OF x] kat_dl.dyn_fv_sem_imp_elim by blast
  qed
  have dual2: "\<Turnstile>[kat_dl.dyn_eval] (\<bbbE>\<bbbE> wsplus . ?\<phi>) \<Rrightarrow> ?\<phi>"
    by (rule kat_dl.dyn_axiom_F2VE[OF rigid])

  show ?thesis
    using gen dual1 dual2 ex_E by dt_prop
qed

definition fresh_vars :: "nat \<Rightarrow> 'a set \<Rightarrow> bool" where
  "fresh_vars n A \<longleftrightarrow> (\<exists>us. distinct us \<and> length us = n \<and> disjnt (set us) A)"

lemma fresh_varsE:
  assumes "fresh_vars n A"
  obtains us where "distinct us" "length us = n" "disjnt (set us) A"
  using assms unfolding fresh_vars_def by blast

lemma fresh_varsI:
  assumes "infinite (UNIV - A) \<or> n \<le> card (UNIV - A)"
  shows "fresh_vars n A"
proof -
  from assms obtain T :: "'a set" where T: "T \<subseteq> UNIV - A" "card T = n" "finite T"
    using infinite_arbitrarily_large obtain_subset_with_card_n by metis
  then obtain us where "set us = T" "distinct us"
    using finite_distinct_list by blast
  with T show ?thesis
    unfolding fresh_vars_def by (metis distinct_card disjnt_iff Diff_iff subsetD)
qed

corollary fresh_vars_infinite:
  "infinite (UNIV::'a set) \<Longrightarrow> finite A \<Longrightarrow> fresh_vars n (A::'a set)"
  by (simp add: fresh_varsI Diff_infinite_finite)

corollary fresh_vars_card:
  "finite (UNIV::'a set) \<Longrightarrow> card A + n \<le> card (UNIV::'a set) \<Longrightarrow> fresh_vars n (A::'a set)"
  by (metis add.commute add_le_imp_le_diff card_Diff_subset fresh_varsI
      infinite_super subset_UNIV)

definition fresh_twins :: "'var list \<Rightarrow> 'var set \<Rightarrow> 'var list \<Rightarrow> bool"
  where "fresh_twins ws A us \<longleftrightarrow> (distinct us) \<and> (twin_vec ws us) \<and> disjnt A (set us)"

theorem dt_versaille:
  fixes ctl :: "('atom,'var,'prog) kat_prog"
    and env :: "('atom,'var,'prog) kat_prog"
    and impl :: "('atom,'var,'prog) kat_prog"
    and pre :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and post :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and J :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and monitor :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and Read :: "'var set"
    and ws :: "'var list"
    and wsplus :: "'var list"
  defines "AllV \<equiv> (
            (Collect (kat_dl.dyn_fv_sem J)) \<union>
            (Collect (kat_dl.dyn_fv_sem pre)) \<union>
            (Collect (kat_dl.dyn_fv_sem post)) \<union>
            (Collect (kat_dl.dyn_prog_fv_sem ctl)) \<union>
            (Collect (kat_dl.dyn_prog_fv_sem env)) \<union> (set ws) \<union> Read
            )"
  defines "monitorminus \<equiv> (\<bbbA>\<bbbA> wsplus . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> monitor))"
  (* ws describes the free and bound variabels of ctl*)
  assumes ws_bound: "(Collect (kat_dl.dyn_prog_bv_sem ctl)) \<subseteq> set ws"
      (* no writing of read model variables *)
      and Read_ws_disjnt: "disjnt Read (set ws)"
      (* ws has no duplicates *)
      and ws_dist: "distinct ws"
      (* Read and wsplus are the only variables in monitor *)
      and fv_monitor: "(Collect (kat_dl.dyn_fv_sem monitor)) \<subseteq> (Read \<union> (set wsplus))"
      (*wsplus copy is well-formed (same length as ws) and fresh *)
      and ws_fresh_twins: "fresh_twins ws AllV wsplus"
      (* Model variables bound by impl are subset of ws *)
      and impl_bound: "(Collect (kat_dl.dyn_prog_bv_sem impl)) \<inter> AllV \<subseteq> (set ws)"
  (* J is a loop invariant *)
  assumes inv_init: "\<Turnstile>[kat_dl.dyn_eval] pre \<Rrightarrow> J"
      and inv_pres: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk>ctl\<rbrakk>\<lbrakk>env\<rbrakk> J"
      and inv_post: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> post"
  (* NN verification worked *)
  assumes nnv: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk>impl\<rbrakk> monitorminus"
  (* Modelplex worked *)
  assumes modelplex: "\<Turnstile>[kat_dl.dyn_eval] monitor \<Rrightarrow> \<langle>ctl\<rangle> (FOL (eqPredV ws wsplus))"
  
  shows "\<Turnstile>[kat_dl.dyn_eval] pre \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> post "
proof -
  have wsplus_dist: "distinct wsplus"
    using ws_fresh_twins unfolding fresh_twins_def by blast
  have ws_wsplus_twin: "twin_vec ws wsplus"
    using ws_fresh_twins unfolding fresh_twins_def by blast
  have wsplus_AllV: "disjnt AllV (set wsplus)"
    using ws_fresh_twins unfolding fresh_twins_def by blast
  have wsplus_length: "(length ws) = (length wsplus)"
    using ws_wsplus_twin
    using list_all2_lengthD by blast
  have wsplus_disjnt_ws: "disjnt (set ws) (set wsplus)"
    using wsplus_AllV
    unfolding AllV_def
    using disjnt_Un1 by blast
  have wsplus_disjnt_Read: "disjnt Read (set wsplus)"
    using wsplus_AllV
    unfolding AllV_def
    using disjnt_Un1 by blast

  let ?\<psi> = "\<lbrakk>env\<rbrakk> J"
  let ?\<psi>plus = "(FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>"
  let ?\<phi> = "monitorminus \<Rrightarrow> ?\<psi>"
  let ?\<phi>plus = "monitor \<Rrightarrow> \<bbbA>\<bbbA> ws . ?\<psi>plus"

  have helper1: "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>ctl\<rbrakk>?\<psi>) \<Rrightarrow> (\<bbbA>\<bbbA> wsplus . \<lbrakk>ctl\<rbrakk>?\<psi>)"
  proof-
    have "(Collect (kat_dl.dyn_fv_sem (\<lbrakk>ctl\<rbrakk>?\<psi>))) \<inter> (set wsplus) = {}"
    proof -
      have "(Collect (kat_dl.dyn_fv_sem (\<lbrakk>ctl\<rbrakk>?\<psi>))) \<subseteq> 
              ((Collect (kat_dl.dyn_prog_fv_sem ctl)) \<union> (Collect (kat_dl.dyn_fv_sem ?\<psi>)))"
        using kat_dl.dyn_fv_sem_box_subset
        by blast
      also have "... \<subseteq> 
              ((Collect (kat_dl.dyn_prog_fv_sem ctl)) \<union> 
                (Collect (kat_dl.dyn_prog_fv_sem env)) \<union>
                (Collect (kat_dl.dyn_fv_sem J)))"
        using kat_dl.dyn_fv_sem_box_subset
        by blast
      also have "... \<subseteq> AllV"
        unfolding AllV_def
        by blast
      finally show ?thesis
        using wsplus_AllV
        by (meson disjnt_def disjnt_subset1)
    qed
    then have "list_all (\<lambda>x. \<not> kat_dl.dyn_fv_sem (\<lbrakk>ctl\<rbrakk>?\<psi>) x) wsplus"
      using Ball_set
      by blast
    then show ?thesis
    using kat_dl.dyn_axiom_F2V
    by blast
  qed

  have envJ_inclusion: "Collect (kat_dl.dyn_fv_sem (\<lbrakk>env\<rbrakk> J)) \<subseteq> (
          Collect (kat_dl.dyn_fv_sem (J)) \<union>
          Collect (kat_dl.dyn_prog_fv_sem env))"
    by (simp add: inf_sup_aci(5) kat_dl.dyn_fv_sem_box_subset)

  then have fresh_\<psi>: "\<And>x. x \<in> set wsplus \<Longrightarrow> \<not> kat_dl.dyn_fv_sem (\<lbrakk>env\<rbrakk> J) x"
    using wsplus_AllV unfolding AllV_def
    by (smt (verit, ccfv_threshold) Un_iff disjnt_iff mem_Collect_eq subsetD)

  have fact3: "\<Turnstile>[kat_dl.dyn_eval] (\<bbbA>\<bbbA> wsplus . ?\<phi>plus) \<Rrightarrow> ?\<phi>"
    unfolding monitorminus_def
    by (rule dt_monitorminus_elim
              [OF ws_wsplus_twin wsplus_dist wsplus_disjnt_ws fresh_\<psi>])

  

  have "\<Turnstile>[kat_dl.dyn_eval] (
          (?\<psi> and (FOL (eqPredV ws wsplus))) \<Rrightarrow>
          (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>))
        )"
    using kat_dl_eq.eq_all_axiomV_and2[of ws wsplus ?\<psi>]
    using wsplus_length wsplus_disjnt_ws ws_dist wsplus_dist
    by blast
  then have "\<Turnstile>[kat_dl.dyn_eval] \<lbrakk>ctl\<rbrakk>(
          (?\<psi> and (FOL (eqPredV ws wsplus))) \<Rrightarrow>
          (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>))
        )"
    using kat_dl.dt_box_G
    by blast
  then have chain_fact2: "\<Turnstile>[kat_dl.dyn_eval] (
          (\<langle>ctl\<rangle>(?\<psi> and (FOL (eqPredV ws wsplus)))) \<Rrightarrow>
          (\<langle>ctl\<rangle>(\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))
        )"
    using kat_dl.dt_diamond_K
    using kat_dl.dyn_hilbert_mp
    by blast

  have "\<Turnstile>[kat_dl.dyn_eval] (?\<psi> \<Rrightarrow> (FOL (eqPredV ws wsplus)) \<Rrightarrow> (?\<psi> and (FOL (eqPredV ws wsplus))))"
    by dt_prop
  then have "\<Turnstile>[kat_dl.dyn_eval] \<lbrakk>ctl\<rbrakk>(?\<psi> \<Rrightarrow> (FOL (eqPredV ws wsplus)) \<Rrightarrow> (?\<psi> and (FOL (eqPredV ws wsplus))))"
    using kat_dl.dyn_axiom_G by blast
  then have "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> \<lbrakk>ctl\<rbrakk>((FOL (eqPredV ws wsplus)) \<Rrightarrow> (?\<psi> and (FOL (eqPredV ws wsplus)))))"
    by auto
  then have "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> (\<langle>ctl\<rangle>(FOL (eqPredV ws wsplus)) \<Rrightarrow> \<langle>ctl\<rangle>(?\<psi> and (FOL (eqPredV ws wsplus)))))"
    using kat_dl.dt_prop_imp_trans_rev by blast
  (* the fact below is step 3 in pen and paper *)
  then have chain_fact1: "\<Turnstile>[kat_dl.dyn_eval] (
            \<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> (monitor \<Rrightarrow>
                 \<langle>ctl\<rangle>(?\<psi> and (FOL (eqPredV ws wsplus))))
          )"
    using modelplex
    by dt_prop

  have chain_fact12:"\<Turnstile>[kat_dl.dyn_eval] (
            \<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> (monitor \<Rrightarrow>
            (\<langle>ctl\<rangle>(\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))
            ))"
    using chain_fact1 chain_fact2
    by dt_prop

  have chain_fact3: "\<Turnstile>[kat_dl.dyn_eval] (
        (\<langle>ctl\<rangle>(\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))
        \<Rrightarrow>
        (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))"
  proof -
    have "Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))
           \<inter> Collect (kat_dl.dyn_prog_bv_sem ctl) = {}"
    proof -
      have "Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>)))
              \<subseteq>
              (Collect (kat_dl.dyn_fv_sem ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>))) - (set ws)"
        by (simp add: kat_dl.dyn_fv_sem_all_vec_subset)
      then have "Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> ws . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> ?\<psi>))) \<inter> (set ws) = {}"
        by blast
      then show ?thesis
        using ws_bound
        by blast
    qed
    then show ?thesis
      using kat_dl.dt_diamond_V
      by blast
  qed
  have "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> ?\<phi>plus)"
    using chain_fact12 chain_fact3
    by dt_prop
  then have "\<Turnstile>[kat_dl.dyn_eval] \<bbbA>\<bbbA> wsplus . (\<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> ?\<phi>plus)"
    using kat_dl.dyn_axiom_AV by blast
  then have "\<Turnstile>[kat_dl.dyn_eval] (\<bbbA>\<bbbA> wsplus . \<lbrakk>ctl\<rbrakk>?\<psi>) \<Rrightarrow> (\<bbbA>\<bbbA> wsplus . ?\<phi>plus)"
    using kat_dl.dyn_axiom_F1V
    using kat_dl.dyn_hilbert_mp
    by blast
  then have "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>ctl\<rbrakk>?\<psi> \<Rrightarrow> (\<bbbA>\<bbbA> wsplus . ?\<phi>plus))"
    using helper1
    by dt_prop
  then have fact4: "\<Turnstile>[kat_dl.dyn_eval] (J \<Rrightarrow> (\<bbbA>\<bbbA> wsplus . ?\<phi>plus))"
    using inv_pres
    by dt_prop
  have "\<Turnstile>[kat_dl.dyn_eval] (J \<Rrightarrow> \<lbrakk>impl\<rbrakk> (\<bbbA>\<bbbA> wsplus . ?\<phi>plus))"
  proof -
    have no_v_intersect: "Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> wsplus . ?\<phi>plus)) \<inter> Collect (kat_dl.dyn_prog_bv_sem impl) = {}"
    proof -

      have helper_fact: "(AllV - set ws) \<inter> (Collect (kat_dl.dyn_prog_bv_sem impl)) = {}"
        using impl_bound
        by blast

      have "Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> wsplus . ?\<phi>plus)) \<subseteq>
              ((Collect (kat_dl.dyn_fv_sem (?\<phi>plus))) - (set wsplus))"
        using kat_dl.dyn_fv_sem_all_vec_subset by presburger
      also have "... \<subseteq>
              ((
                  (Collect (kat_dl.dyn_fv_sem monitor)) \<union>
                  (Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> ws . ?\<psi>plus)))
                ) - (set wsplus))"
        by (simp add: Diff_mono kat_dl.dyn_fv_sem_imp_subset)
      also have "... \<subseteq>
              ((
                  (Read \<union> (set wsplus)) \<union>
                  (Collect (kat_dl.dyn_fv_sem (\<bbbA>\<bbbA> ws . ?\<psi>plus)))
                ) - (set wsplus))"
        using fv_monitor by blast
      also have "... \<subseteq>
              ((
                  (Read \<union> (set wsplus)) \<union>
                  ((Collect (kat_dl.dyn_fv_sem (?\<psi>plus))) - (set ws))
                ) - (set wsplus))"
        using kat_dl.dyn_fv_sem_all_vec_subset by blast
      also have "... \<subseteq>
              ((
                  (Read \<union> (set wsplus)) \<union>
                  ((
                      (Collect (kat_dl.dyn_fv_sem (FOL (kat_dl_eq.eqPredV ws wsplus))))
                      \<union>
                      (Collect (kat_dl.dyn_fv_sem (\<lbrakk> env \<rbrakk> J)))
                    ) - (set ws))
                ) - (set wsplus))"
        using Diff_mono kat_dl.dyn_fv_sem_imp_subset by blast
      also have "... \<subseteq> 
              ((
                  (Read \<union> (set wsplus)) \<union>
                  ((
                      ((set ws) \<union> (set wsplus))
                      \<union>
                      (Collect (kat_dl.dyn_fv_sem (\<lbrakk> env \<rbrakk> J)))
                    ) - (set ws))
                ) - (set wsplus))"
        by (metis Diff_mono Un_absorb kat_dl_eq.eqPredV_fv_sem_subset sup.cobounded2
            sup.mono wsplus_disjnt_ws wsplus_length)
      also have "... \<subseteq> 
              ((
                  (Read \<union> (set wsplus)) \<union>
                  ((
                      ((set ws) \<union> (set wsplus))
                      \<union>
                      (
                        (Collect (kat_dl.dyn_fv_sem (J))) \<union>
                        (Collect (kat_dl.dyn_prog_fv_sem env))
                      )
                    ) - (set ws))
                ) - (set wsplus))"
        using envJ_inclusion by blast
      also have "... \<subseteq> 
              ((
                  (Read \<union> (set wsplus)) \<union>
                  ((
                      ((set ws) \<union> (set wsplus))
                      \<union>
                      AllV
                    ) - (set ws))
                ) - (set wsplus))"
        using AllV_def by auto
      also have "... \<subseteq> AllV - (set ws)"
        using Read_ws_disjnt wsplus_disjnt_ws wsplus_disjnt_Read
        by (smt (verit) AllV_def Diff_iff UnCI UnE disjnt_iff subsetI)
      finally show ?thesis
        using helper_fact
        by blast
    qed
    show ?thesis
      using kat_dl.dyn_axiom_V[OF no_v_intersect]
      using fact4 kat_dl.dt_prop_imp_trans by blast
  qed
  then have fact2: "\<Turnstile>[kat_dl.dyn_eval] (J \<Rrightarrow> \<lbrakk>impl\<rbrakk>?\<phi>)"
    using kat_dl.dt_box_MRimp[OF fact3]
    by blast
  have "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk>impl\<rbrakk>?\<phi> \<Rrightarrow> \<lbrakk>impl\<rbrakk> monitorminus \<Rrightarrow> \<lbrakk>impl\<rbrakk> ?\<psi>)"
    using kat_dl.dyn_axiom_K[of impl monitorminus "\<lbrakk> env \<rbrakk> J"]
    by blast
  then have "\<Turnstile>[kat_dl.dyn_eval] ((J \<Rrightarrow> \<lbrakk>impl\<rbrakk>?\<phi>) \<Rrightarrow> ((J \<Rrightarrow> \<lbrakk>impl\<rbrakk> monitorminus) \<Rrightarrow> (J \<Rrightarrow> \<lbrakk>impl\<rbrakk> ?\<psi>)))"
    by dt_prop
  then have "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk>impl\<rbrakk> ?\<psi>"
    using fact2
    using nnv
    by dt_prop
  then have "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk> (impl;env) \<rbrakk> J"
    using dyn_axiom_seq[of impl env J]
    by dt_prop
  then have "\<Turnstile>[kat_dl.dyn_eval] \<lbrakk> ((impl;env) *) \<rbrakk> (J \<Rrightarrow> \<lbrakk> (impl;env) \<rbrakk> J)"
    by (rule kat_dl.dt_box_G)
  then have "\<Turnstile>[kat_dl.dyn_eval]
          (J \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> J)"
    using dyn_axiom_I
    using kat_dl.dyn_hilbert_mp by blast
  then have fact1: "\<Turnstile>[kat_dl.dyn_eval]
          (J \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> post)"
    using kat_dl.dt_box_MRimp[OF inv_post]
    by blast
  have "\<Turnstile>[kat_dl.dyn_eval]
          (J \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> post)
          \<Rrightarrow>
          (pre \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> post)"
    using inv_init
    by dt_prop
  then show ?thesis
    using fact1
    by dt_prop
qed

end

end