theory KATRewriting
  imports
    Main
    "DynamicLogic"
    "DLRewriting"
    "KATDynamicLogic"
begin

locale KleeneDynLog =
  KATDynLog atom_eval atom_fv_syn state_eval prog_eval
      dyn_prog_FV
  for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  +
  assumes strong_extensionality:
    "\<forall> \<pi> \<mu> \<omega> \<mu>' \<omega>' . ((\<forall> v. (((state_eval \<mu>) v = (state_eval \<omega>) v) \<and> ((state_eval \<mu>') v = (state_eval \<omega>') v))) \<longrightarrow> prog_eval \<pi> \<mu> \<mu>' = prog_eval \<pi> \<omega> \<omega>')"
begin

lemma kleene_strong_extensionality:
  "\<forall> \<pi> \<mu> \<omega> \<mu>' \<omega>' . ((\<forall> v. (((state_eval \<mu>) v = (state_eval \<omega>) v) \<and> ((state_eval \<mu>') v = (state_eval \<omega>') v))) \<longrightarrow> full_prog_eval \<pi> \<mu> \<mu>' = full_prog_eval \<pi> \<omega> \<omega>')"
  apply (intro allI)
  subgoal for \<pi> \<mu> \<omega> \<mu>' \<omega>'
  proof (induct \<pi> arbitrary: \<mu> \<omega> \<mu>' \<omega>')
    case (KATPROG x)
    then show ?case
      using strong_extensionality
      using full_prog_eval_def full_prog_eval_int.simps(1) by presburger
  next
    case (CHECK x)
    then show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
      apply simp
      by (metis (mono_tags, opaque_lifting) dyn_eval.simps(1) full_prog_eval_int.simps(2) full_prog_var_determinance_n)
  next
    case (SEQ \<pi>1 \<pi>2)
    show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
(*      using SEQ.hyps(1)[of \<mu>]*)
    proof (intro impI, standard)
      assume eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
        state_eval \<mu>' v = state_eval \<omega>' v"
      assume "\<exists>n \<nu>. full_prog_eval_int n \<pi>1 \<mu> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<mu>'"
      then obtain n \<nu> where n\<nu>_cond: "full_prog_eval_int n \<pi>1 \<mu> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<mu>'"
        by blast
      show "\<exists>n \<nu>. full_prog_eval_int n \<pi>1 \<omega> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<omega>'"
        using eq n\<nu>_cond
        using SEQ.hyps(1)[of \<mu> \<omega> \<nu>]
        by (metis (no_types, opaque_lifting) KATDynLog.full_prog_rewrite_seq KATDynLog_axioms SEQ.hyps(2) full_prog_eval_def full_prog_eval_int.simps(3))
    next
       assume eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
        state_eval \<mu>' v = state_eval \<omega>' v"
       assume "\<exists>n \<nu>. full_prog_eval_int n \<pi>1 \<omega> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<omega>'"
       then obtain n \<nu> where n\<nu>_cond: "full_prog_eval_int n \<pi>1 \<omega> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<omega>'"
         by blast
       show "\<exists>n \<nu>. full_prog_eval_int n \<pi>1 \<mu> \<nu> \<and>
          full_prog_eval_int n \<pi>2 \<nu> \<mu>'"
        using eq n\<nu>_cond
        using SEQ.hyps(1)[of \<mu> \<omega> \<nu>]
        by (metis (no_types, opaque_lifting) KATDynLog.full_prog_rewrite_seq KATDynLog_axioms SEQ.hyps(2) full_prog_eval_def full_prog_eval_int.simps(3))
    qed
  next
    case (CHOICE \<pi>1 \<pi>2)
    then show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
      by blast
  next
    case (LOOP \<pi>)
    show ?case
      unfolding kleene_rep_rewrite
    proof (intro impI,standard)
      assume states_eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
        state_eval \<mu>' v = state_eval \<omega>' v"
      assume "\<exists>n. full_prog_eval (REP \<pi> n) \<mu> \<mu>'"
      then obtain n where n_cond: "full_prog_eval (REP \<pi> n) \<mu> \<mu>'"
        by blast
      show "\<exists>n. full_prog_eval (REP \<pi> n) \<omega> \<omega>'"
        apply (intro exI[where x=n])
          using states_eq
          using n_cond
      proof (induct n arbitrary: \<mu> \<mu>' \<omega> \<omega>')
        case 0
        then show ?case
          apply simp
            unfolding
              full_prog_eval_def full_prog_eval_int.simps
              dyn_eval.simps fol_eval.simps
            using states_eq
            by presburger
      next
        case (Suc n)
        assume start_end_eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
        state_eval \<mu>' v = state_eval \<omega>' v"
        have "full_prog_eval (REP \<pi> (Suc n)) \<mu> \<mu>'"
          using Suc.prems
          by blast
        then have "\<exists>\<nu>. full_prog_eval \<pi> \<mu> \<nu> \<and>
          full_prog_eval (REP \<pi> n) \<nu> \<mu>'"
          apply simp
          unfolding full_prog_rewrite_seq
          by blast
        then obtain \<nu> where m\<nu>_cond: "full_prog_eval \<pi> \<mu> \<nu> \<and>
          full_prog_eval (REP \<pi> n) \<nu> \<mu>'"
          by blast
        then have "full_prog_eval \<pi> \<mu> \<nu>"
          unfolding full_prog_eval_def
          by blast
        then obtain \<nu>' where \<nu>'_cond: "full_prog_eval \<pi> \<omega> \<nu>' \<and>
              (\<forall>v. state_eval \<nu> v = state_eval \<nu>' v)" 
          using kat_dl.prog_fv_overapprox[of \<pi> "\<lambda> v . True" \<mu> \<omega> \<nu>]
          unfolding fol_states_agree_on_def
          using start_end_eq
          apply simp
          by blast
        then show ?case
          apply simp
          unfolding full_prog_rewrite_seq
          apply (intro exI[where x=\<nu>'])
        proof (intro conjI)
          show "full_prog_eval \<pi> \<omega> \<nu>'"
            using \<nu>'_cond by blast
          show "full_prog_eval (REP \<pi> n) \<nu>' \<omega>'"
            using m\<nu>_cond
            using \<nu>'_cond
            using start_end_eq
            using Suc.hyps by blast
        qed
      qed
    next
      assume states_eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
        state_eval \<mu>' v = state_eval \<omega>' v"
      assume "\<exists>n. full_prog_eval (REP \<pi> n) \<omega> \<omega>'"
      then obtain n where n_cond: "full_prog_eval (REP \<pi> n) \<omega> \<omega>'"
        by blast
      show "\<exists>n. full_prog_eval (REP \<pi> n) \<mu> \<mu>'"
        apply (intro exI[where x=n])
          using states_eq
          using n_cond
      proof (induct n arbitrary: \<omega> \<omega>' \<mu> \<mu>')
        case 0
        then show ?case
          apply simp
            unfolding
              full_prog_eval_def full_prog_eval_int.simps
              dyn_eval.simps fol_eval.simps
            using states_eq
            by presburger
      next
        case (Suc n)
        assume start_end_eq: "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
           state_eval \<mu>' v = state_eval \<omega>' v"
        have "full_prog_eval (REP \<pi> (Suc n)) \<omega> \<omega>'"
          using Suc.prems
          by blast
        then have "\<exists>\<nu>. full_prog_eval \<pi> \<omega> \<nu> \<and>
          full_prog_eval (REP \<pi> n) \<nu> \<omega>'"
          apply simp
          unfolding full_prog_rewrite_seq
          by blast
        then obtain \<nu> where m\<nu>_cond: "full_prog_eval \<pi> \<omega> \<nu> \<and>
          full_prog_eval (REP \<pi> n) \<nu> \<omega>'"
          by blast
        then have "full_prog_eval \<pi> \<omega> \<nu>"
          unfolding full_prog_eval_def
          by blast
        then obtain \<nu>' where \<nu>'_cond: "full_prog_eval \<pi> \<mu> \<nu>' \<and>
              (\<forall>v. state_eval \<nu> v = state_eval \<nu>' v)" 
          using kat_dl.prog_fv_overapprox[of \<pi> "\<lambda> v . True" \<omega> \<mu> \<nu>]
          unfolding fol_states_agree_on_def
          using start_end_eq
          apply simp
          by blast
        then show ?case
          apply simp
          unfolding full_prog_rewrite_seq
          apply (intro exI[where x=\<nu>'])
        proof (intro conjI)
          show "full_prog_eval \<pi> \<mu> \<nu>'"
            using \<nu>'_cond by blast
          show "full_prog_eval (REP \<pi> n) \<nu>' \<mu>'"
            using m\<nu>_cond
            using \<nu>'_cond
            using start_end_eq
            using Suc.hyps
            by metis
        qed
      qed
    qed
  qed.

lemma rep_reordered:
  "full_prog_eval (REP \<pi> (Suc n)) \<sigma> \<mu> = (full_prog_eval ((REP \<pi> n) ; \<pi>)) \<sigma> \<mu>"
  unfolding REP.simps
  apply (simp add: full_prog_rewrite_seq)
  proof (induct n arbitrary: \<sigma> \<mu>)
    case 0
    then show ?case
      apply simp
        unfolding
          full_prog_eval_def full_prog_eval_int.simps
          dyn_eval.simps fol_eval.simps
        apply simp
        using kleene_strong_extensionality
        by (metis full_prog_eval_def)
  next
    case (Suc n)
    then show ?case
    proof -
      have inductive_rewrite: "\<And>\<nu> .
        (\<exists>\<nu>'. full_prog_eval \<pi> \<nu> \<nu>' \<and> full_prog_eval (REP \<pi> n) \<nu>' \<mu>) =
        (\<exists>\<nu>'. full_prog_eval (REP \<pi> n) \<nu> \<nu>' \<and> full_prog_eval \<pi> \<nu>' \<mu>)"
        subgoal for \<nu>
          unfolding Suc.hyps[of \<nu> \<mu>]
          by simp.
      show ?thesis
      apply (subst (1) REP.simps)
        unfolding full_prog_rewrite_seq
        unfolding inductive_rewrite
        apply (subst (1) REP.simps)
        unfolding full_prog_rewrite_seq
        by blast
    qed
  qed

notation kat_dl.progRefine ("_ \<le> _" [190, 190] 190)

notation kat_dl.progEquiv ("_ \<rightleftharpoons> _ " [200, 200] 200)

theorem kat_rule1:
  fixes \<alpha> \<beta> \<gamma> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha>\<squnion>(\<beta>\<squnion>\<gamma>)) \<rightleftharpoons> ((\<alpha>\<squnion>\<beta>)\<squnion>\<gamma>)"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule2:
  fixes \<alpha> \<beta> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha>\<squnion>\<beta>) \<rightleftharpoons> (\<beta>\<squnion>\<alpha>)"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule3:
  fixes \<alpha> \<beta> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha>\<squnion>(? (folnot FOLTRUE))) \<rightleftharpoons> \<alpha>"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by (simp add: FOLTRUE_def  OR_def dyn_eval.simps fol_eval.simps)

theorem kat_rule4:
  fixes \<alpha> \<beta> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha>\<squnion>\<alpha>) \<rightleftharpoons> \<alpha>"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule5:
  fixes \<alpha> \<beta> \<gamma> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha>; (\<beta>; \<gamma>)) \<rightleftharpoons> ((\<alpha>; \<beta>); \<gamma>)"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule6:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "(? FOLTRUE ; \<alpha>) \<rightleftharpoons> \<alpha>"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  apply (simp add: FOLTRUE_def dyn_eval.simps fol_eval.simps)
  by (metis full_prog_var_determinance_n)

theorem kat_rule7:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha> ; ? FOLTRUE) \<rightleftharpoons> \<alpha>"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
  apply (subst (2 6) full_prog_eval_def)
  unfolding full_prog_eval_int.simps dyn_eval.simps fol_eval.simps
  apply (simp)
  apply (intro conjI, intro allI, intro impI)
  subgoal for \<sigma> \<mu>
  proof -
    assume "\<exists>\<nu>. full_prog_eval \<alpha> \<sigma> \<nu> \<and> state_eval \<nu> = state_eval \<mu>"
    then obtain \<nu> where \<nu>_cond: "full_prog_eval \<alpha> \<sigma> \<nu> \<and> state_eval \<nu> = state_eval \<mu>"
      by blast
    have fact1: "(\<forall> v. (((state_eval \<sigma>) v = (state_eval \<sigma>) v) \<and> ((state_eval \<nu>) v = (state_eval \<mu>) v)))"
      using \<nu>_cond
      by force
    have fact2: "full_prog_eval \<alpha> \<sigma> \<nu>"
      using \<nu>_cond
      by force
    then show ?thesis
      using fact1 fact2 kleene_strong_extensionality
      by blast
  qed
  apply (intro allI, intro impI)
  subgoal for \<sigma> \<mu>
  proof -
    assume "full_prog_eval \<alpha> \<sigma> \<mu>"
    then obtain \<nu> where \<nu>_cond: "full_prog_eval \<alpha> \<sigma> \<nu> \<and> state_eval \<nu> = state_eval \<mu>"
      by blast
    have fact1: "(\<forall> v. (((state_eval \<sigma>) v = (state_eval \<sigma>) v) \<and> ((state_eval \<nu>) v = (state_eval \<mu>) v)))"
      using \<nu>_cond
      by force
    have fact2: "full_prog_eval \<alpha> \<sigma> \<nu>"
      using \<nu>_cond
      by force
    then show ?thesis
      using fact1 fact2 strong_extensionality
      by blast
  qed.

theorem kat_rule8:
  fixes \<alpha> \<beta> \<gamma> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha> ; (\<beta> \<squnion> \<gamma>)) \<rightleftharpoons> ((\<alpha> ; \<beta>) \<squnion> (\<alpha> ; \<gamma>))"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule9:
  fixes \<alpha> \<beta> \<gamma> :: "('atom,'var,'prog) kat_prog"
  shows "((\<alpha> \<squnion> \<beta>) ; \<gamma>) \<rightleftharpoons> ((\<alpha> ; \<gamma>) \<squnion> (\<beta> ; \<gamma>))"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by blast

theorem kat_rule10:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "(? (folnot FOLTRUE) ; \<alpha>) \<rightleftharpoons> (? (folnot FOLTRUE))"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by (simp add: FOLTRUE_def dyn_eval.simps fol_eval.simps)

theorem kat_rule11:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "(\<alpha> ; ? (folnot FOLTRUE)) \<rightleftharpoons> (? (folnot FOLTRUE))"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def full_prog_eval_int.simps
  by (simp add: FOLTRUE_def dyn_eval.simps fol_eval.simps)

theorem kat_rule12:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "((? FOLTRUE) \<squnion> (\<alpha> ; ((\<alpha>)*) )) \<rightleftharpoons> ( (\<alpha>)* )"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding kleene_rep_rewrite
  apply (intro conjI, intro allI, intro impI)
  subgoal for \<sigma> \<mu>
    apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
    apply (elim disjE)
    subgoal
      apply (intro exI[where x="0"])
      unfolding REP.simps
      by force
    subgoal
    proof -
      assume "\<exists>\<nu>. full_prog_eval \<alpha> \<sigma> \<nu> \<and> full_prog_eval (\<alpha>*) \<nu> \<mu>"
      then have "\<exists>n. full_prog_eval (REP \<alpha> (Suc n)) \<sigma> \<mu>"
        unfolding REP.simps
        apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
        using kleene_rep_rewrite[of \<alpha> _ \<mu>]
        by blast
      then show ?thesis
        by blast
    qed.
  apply (intro allI, intro impI)
  subgoal for \<sigma> \<mu>
    apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
    apply (erule exE)
    subgoal for n
    proof (induct n)
      case 0
      then show ?case
        unfolding REP.simps
        by simp
    next
      case (Suc n)
      assume "full_prog_eval (REP \<alpha> (Suc n)) \<sigma> \<mu>"
      then show ?case
        unfolding REP.simps
        apply (intro disjI2)
        apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
        using kleene_rep_rewrite[of \<alpha> _ \<mu>]
        by blast
    qed.
  .

theorem kat_rule13:
  fixes \<alpha> :: "('atom,'var,'prog) kat_prog"
  shows "(? FOLTRUE \<squnion> ((\<alpha>)* ; \<alpha>) ) \<rightleftharpoons> ((\<alpha>)* )"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding kleene_rep_rewrite
  apply (intro conjI, intro allI, intro impI)
  subgoal for \<sigma> \<mu>
    apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
    apply (elim disjE)
    subgoal
      apply (intro exI[where x="0"])
      unfolding REP.simps
      by force
    subgoal
    proof -
      assume "\<exists>\<nu>. full_prog_eval (\<alpha>* ) \<sigma> \<nu> \<and> full_prog_eval \<alpha> \<nu> \<mu>"
      then have "\<exists>n. full_prog_eval (REP \<alpha> (Suc n)) \<sigma> \<mu>"
        unfolding kleene_rep_rewrite
        unfolding rep_reordered
        unfolding full_prog_rewrite_seq
        by blast
      then show ?thesis
        by blast
    qed.
  apply (intro allI, intro impI)
  subgoal for \<sigma> \<mu>
    apply (simp add: full_prog_rewrite_seq full_prog_rewrite_choice)
    apply (erule exE)
    subgoal for n
    proof (induct n)
      case 0
      then show ?case
        unfolding REP.simps
        by simp
    next
      case (Suc n)
      assume "full_prog_eval (REP \<alpha> (Suc n)) \<sigma> \<mu>"
      then show ?case
        unfolding rep_reordered
        apply (intro disjI2)
        unfolding full_prog_rewrite_seq
        unfolding kleene_rep_rewrite
        apply (elim exE)
        subgoal for \<nu>
          apply (intro exI[of _ \<nu>])
          apply (intro conjI)
           apply (intro exI[of _ n])
           apply simp
          apply simp.
        .
    qed.
  .


theorem kat_rule14:
  fixes p q r :: "('atom,'var,'prog) kat_prog"
  assumes "(q \<squnion> (p ; r)) \<le> r"
  shows "((p)* ; q) \<le> r"
proof -

  have pr_refine: "(p ; r) \<le> r"
    using assms
    by (simp add: full_prog_rewrite_choice kat_dl.progRefine_def)

  have q_refine: "q \<le> r"
    using assms
    by (simp add: full_prog_rewrite_choice kat_dl.progRefine_def)

  show ?thesis
    unfolding kat_dl.progRefine_def full_prog_rewrite_seq kleene_rep_rewrite
    apply (standard, intro allI, intro impI, elim exE, elim conjE, elim exE)
    subgoal for \<sigma> \<mu> \<nu> n
  proof (induct n arbitrary: \<sigma> \<mu> \<nu>)
    case 0
    then show ?case
      apply simp
      unfolding
        full_prog_eval_def full_prog_eval_int.simps
        dyn_eval.simps fol_eval.simps
      apply simp
      using q_refine
      by (metis full_prog_eval_def full_prog_var_determinance_n kat_dl.progRefine_def)
  next
    case (Suc n)
    show ?case
      using Suc.prems
      unfolding REP.simps full_prog_rewrite_seq
      using Suc.hyps[of \<nu> \<mu>]
      using pr_refine full_prog_rewrite_seq kat_dl.progRefine_def by blast
  qed.
qed

theorem kat_rule15:
  fixes p q r :: "('atom,'var,'prog) kat_prog"
  assumes "(q \<squnion> (r ; p)) \<le> r"
  shows "(q ; ((p)*) ) \<le> r"
proof -

  have rp_refine: "(r ; p) \<le> r"
    using assms
    by (simp add: full_prog_rewrite_choice kat_dl.progRefine_def)

  have q_refine: "q \<le> r"
    using assms
    by (simp add: full_prog_rewrite_choice kat_dl.progRefine_def)

  show ?thesis
    unfolding kat_dl.progRefine_def full_prog_rewrite_seq kleene_rep_rewrite
    apply (standard, intro allI, intro impI, elim exE, elim conjE, elim exE)
    subgoal for \<sigma> \<mu> \<nu> n
  proof (induct n arbitrary: \<sigma> \<mu> \<nu>)
    case 0
    then show ?case
      apply simp
      unfolding
        full_prog_eval_def full_prog_eval_int.simps
        dyn_eval.simps fol_eval.simps
      apply simp
      using q_refine
      by (metis "0.prems"(1) full_prog_eval_def kat_dl.progRefine_def kleene_strong_extensionality)
  next
    case (Suc n)
    show ?case
      using Suc.prems
      unfolding rep_reordered
      unfolding full_prog_rewrite_seq
      using Suc.hyps[of \<sigma> \<nu>]
      using rp_refine full_prog_rewrite_seq kat_dl.progRefine_def by blast
  qed.
qed

lemma seq_helper1:
    fixes p :: "('atom, 'var, 'prog) kat_prog"
  assumes "p \<rightleftharpoons> q"
  shows "(p ; r) \<rightleftharpoons> (q ; r)"
  by (meson assms full_prog_rewrite_seq kat_dl.progEquiv_def kat_dl.progRefine_def)

lemma seq_helper2:
    fixes r :: "('atom, 'var, 'prog) kat_prog"
  assumes "r \<rightleftharpoons> q"
  shows "(p ; r) \<rightleftharpoons> (p ; q)"
  by (meson assms full_prog_rewrite_seq kat_dl.progEquiv_def kat_dl.progRefine_def)

lemma choice_helper1:
    fixes p :: "('atom, 'var, 'prog) kat_prog"
  assumes "p \<rightleftharpoons> q"
  shows "(p \<squnion> r) \<rightleftharpoons> (q \<squnion> r)"
  using assms full_prog_rewrite_choice kat_dl.progEquivSimplification by fastforce

lemma choice_helper2:
    fixes p :: "('atom, 'var, 'prog) kat_prog"
  assumes "p \<rightleftharpoons> q"
  shows "(r \<squnion> p) \<rightleftharpoons> (r \<squnion> q)"
  using choice_helper1 kat_rule2 kat_dl.progEquiv_transp_expl assms
  by meson

lemma loop_helper:
  fixes p :: "('atom, 'var, 'prog) kat_prog"
  assumes "p \<rightleftharpoons> q"
  shows "((p)* ) \<rightleftharpoons> ((q)* )"
  using assms
  unfolding kat_dl.progEquivSimplification
  unfolding full_prog_eval_def
proof -
  have "\<forall>\<mu> \<omega>. (\<exists>n. full_prog_eval_int n (p*) \<mu> \<omega>) =
               (\<exists>n. full_prog_eval_int n (q*) \<mu> \<omega>)"
  proof (intro allI)
    fix \<mu> \<omega>
    show "(\<exists>n. full_prog_eval_int n (LOOP p) \<mu> \<omega>) = (\<exists>n. full_prog_eval_int n (LOOP q) \<mu> \<omega>)"
    proof
      assume A: "\<exists>n. full_prog_eval_int n (LOOP p) \<mu> \<omega>"
      then obtain n where FN: "full_prog_eval_int n (LOOP p) \<mu> \<omega>"
        by blast
      then show "\<exists>n. full_prog_eval_int n (LOOP q) \<mu> \<omega>"
      proof (induct n arbitrary: \<mu> \<omega>)
        case 0
        then show ?case by (simp add: full_prog_eval_int.simps)
      next
        case (Suc n)
        from Suc.prems have
          "(state_eval \<mu> = state_eval \<omega>) \<or>
           full_prog_eval_int n (SEQ p (LOOP p)) \<mu> \<omega> \<or>
           full_prog_eval_int n (LOOP p) \<mu> \<omega>"
          by (simp add: full_prog_eval_int.simps)
        then show ?case
        proof
          assume "state_eval \<mu> = state_eval \<omega>"
          then show ?thesis
            apply (intro exI[where x="1"])
            by (simp add: full_prog_eval_int.simps)
        next
          assume "full_prog_eval_int n (p;(p* )) \<mu> \<omega> \<or> full_prog_eval_int n (p*) \<mu> \<omega>"
          thus "\<exists>n. full_prog_eval_int n (q*) \<mu> \<omega>"
          proof
            assume "full_prog_eval_int n (SEQ p (LOOP p)) \<mu> \<omega>"
            then obtain \<nu> where A1: "full_prog_eval_int n p \<mu> \<nu>" and A2: "full_prog_eval_int n (LOOP p) \<nu> \<omega>"
              unfolding full_prog_eval_int.simps(3)
              by blast
            from A1 and \<open>p \<rightleftharpoons> q\<close> have "\<exists>m. full_prog_eval_int m q \<mu> \<nu>"
              using assms unfolding kat_dl.progEquivSimplification full_prog_eval_def
              by meson
            then obtain m where B1: "full_prog_eval_int m q \<mu> \<nu>" by auto
            from A2 Suc.hyps[of \<nu> \<omega>] obtain k where B2: "full_prog_eval_int k (LOOP q) \<nu> \<omega>"
              by blast
            then have "\<exists>N. full_prog_eval_int N (SEQ q (LOOP q)) \<mu> \<omega>"
              apply (intro exI[where x="max m k"])
              by (meson B1 full_prog_eval_int.simps(3) full_prog_eval_int_n_monotone max.cobounded1 max.cobounded2)
            then show "\<exists>n. full_prog_eval_int n (q*) \<mu> \<omega>"
              by (metis One_nat_def diff_Suc_Suc diff_zero full_prog_eval_int.simps(5) zero_less_Suc)
        next
          assume "full_prog_eval_int n (LOOP p) \<mu> \<omega>"
          then obtain k where "full_prog_eval_int k (LOOP q) \<mu> \<omega>"
            using Suc.hyps by blast
          then show ?thesis by blast
        qed
      qed
    qed
    next
      (* symmetric direction: from q* to p* *)
      assume A: "\<exists>n. full_prog_eval_int n (LOOP q) \<mu> \<omega>"
      then obtain n where FN: "full_prog_eval_int n (LOOP q) \<mu> \<omega>"
        by blast
      then show "\<exists>n. full_prog_eval_int n (LOOP p) \<mu> \<omega>"
        using \<open>p \<rightleftharpoons> q\<close>
      proof (induct n arbitrary: \<mu> \<omega>)
        case 0
        then show ?case by (simp add: full_prog_eval_int.simps)
      next
        case (Suc n)
        from Suc.prems have
          "(state_eval \<mu> = state_eval \<omega>) \<or>
           full_prog_eval_int n (SEQ q (LOOP q)) \<mu> \<omega> \<or>
           full_prog_eval_int n (LOOP q) \<mu> \<omega>"
          by (simp add: full_prog_eval_int.simps)
        then show ?case
        proof
          assume "state_eval \<mu> = state_eval \<omega>"
          then show ?thesis by (intro exI[where x="1"]) (simp add: full_prog_eval_int.simps)
        next
          assume "full_prog_eval_int n (q;(q* )) \<mu> \<omega> \<or> full_prog_eval_int n (q*) \<mu> \<omega>"
          thus "\<exists>n. full_prog_eval_int n (p*) \<mu> \<omega>"
          proof 
          assume H: "full_prog_eval_int n (SEQ q (LOOP q)) \<mu> \<omega>"
          then obtain \<nu> where A1: "full_prog_eval_int n q \<mu> \<nu>" and A2: "full_prog_eval_int n (LOOP q) \<nu> \<omega>"
            unfolding full_prog_eval_int.simps(3)
            by blast
          from A1 and \<open>p \<rightleftharpoons> q\<close> have "\<exists>m. full_prog_eval_int m p \<mu> \<nu>"
            using assms unfolding kat_dl.progEquivSimplification full_prog_eval_def by meson
          then obtain m where B1: "full_prog_eval_int m p \<mu> \<nu>" by auto
          from A2 Suc.hyps[of \<nu> \<omega>] obtain k where B2: "full_prog_eval_int k (LOOP p) \<nu> \<omega>"
            using Suc.prems(2) by blast
          have "\<exists>N. full_prog_eval_int N (SEQ p (LOOP p)) \<mu> \<omega>"
          proof (intro exI[where x="Suc (max m k)"])
            show "full_prog_eval_int (Suc (max m k)) (SEQ p (LOOP p)) \<mu> \<omega>"
            proof -
              have "full_prog_eval_int (max m k) p \<mu> \<nu>"
                using B1 full_prog_eval_int_n_monotone max.cobounded1 by blast
              moreover have "full_prog_eval_int (max m k) (LOOP p) \<nu> \<omega>"
                using B2 full_prog_eval_int_n_monotone max.cobounded2 by blast
              ultimately show ?thesis
                unfolding full_prog_eval_int.simps(3)
                using Suc_leD full_prog_eval_int_n_monotone by blast
            qed
          qed
          then show "\<exists>n. full_prog_eval_int n (p*) \<mu> \<omega>"
            by (metis diff_Suc_1 full_prog_eval_int.simps(5) zero_less_Suc)
          next
            assume "full_prog_eval_int n (LOOP q) \<mu> \<omega>"
            then obtain k where "full_prog_eval_int k (LOOP p) \<mu> \<omega>"
              using Suc.hyps
              using assms by blast
            then show ?thesis
              by blast
          qed
        qed
      qed
    qed
  qed
  then show "(\<lambda>\<mu> \<omega>. \<exists>n. full_prog_eval_int n (p* ) \<mu> \<omega>) =
    (\<lambda>\<mu> \<omega>. \<exists>n. full_prog_eval_int n (q* ) \<mu> \<omega>)"
    by (simp add: fun_eq_iff)
qed

  

lemma check_helper_and:
  "((? F1);(? F2)) \<rightleftharpoons> (? F1 foland F2)"
  unfolding kat_dl.progEquiv_def
  unfolding kat_dl.progRefine_def
  unfolding full_prog_eval_def
  apply (intro conjI, intro allI)
  subgoal for \<sigma> \<mu>
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps fol_eval.simps
    by (metis kat_dl.dyn_differing_state_eval_due_to_vars kat_dl.dyn_eval.simps(1))
  apply (intro allI)
  subgoal for \<sigma> \<mu>
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps fol_eval.simps
    by blast
  .


lemma check_helper_or:
  "((? F1)\<squnion>(? F2)) \<rightleftharpoons> (? F1 or F2)"
  unfolding kat_dl.progEquiv_def
  unfolding kat_dl.progRefine_def
  unfolding full_prog_eval_def
  apply (intro conjI, intro allI)
  subgoal for \<sigma> \<mu>
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps fol_eval.simps
    by fastforce
  apply (intro allI)
  subgoal for \<sigma> \<mu>
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps fol_eval.simps
    by fastforce
  .


fun get_fml :: "('atom, 'var, 'prog) kat_prog \<Rightarrow> ('atom, 'var) fol_formula"
  where
    "get_fml (KATPROG _) = undefined"
  | "get_fml (CHECK x) = x"
  | "get_fml (SEQ x y) = (get_fml x) foland (get_fml y)"
  | "get_fml (CHOICE x y) = (get_fml x) or (get_fml y)"
  | "get_fml (LOOP x) = (FOLTRUE)"

fun is_purely_check :: "('atom, 'var, 'prog) kat_prog \<Rightarrow> bool"
  where
    "is_purely_check (KATPROG _) = False"
  | "is_purely_check (CHECK x) = True"
  | "is_purely_check (SEQ x y) = ((is_purely_check x) \<and> (is_purely_check y))"
  | "is_purely_check (CHOICE x y) = ((is_purely_check x) \<and> (is_purely_check y))"
  | "is_purely_check (LOOP x) = (is_purely_check x)"

lemma eq_if_pure:
  assumes "is_purely_check P"
  shows "P \<rightleftharpoons> (CHECK (get_fml P))"
  using assms
proof (induct P)
  case (KATPROG x)
  then show ?case
    unfolding is_purely_check.simps
    by simp    
next
  case (CHECK x)
  then show ?case
    unfolding get_fml.simps
    using progEquiv_refl
    using kat_dl.progEquivSimplification by blast
next
  case (SEQ P1 P2)
  then show ?case
    unfolding is_purely_check.simps
    unfolding get_fml.simps
    apply simp
  proof -
    assume local_assm1: "P1 \<rightleftharpoons> (? get_fml P1)"
        and local_assm2: "P2 \<rightleftharpoons> (? get_fml P2)"
    have fact1: "(P1;P2) \<rightleftharpoons> ((? get_fml P1);P2)"
      using seq_helper1[of P1 "(? get_fml P1)" P2]
      using local_assm1
      by simp
    also have fact2: "... \<rightleftharpoons> ((? get_fml P1);(? get_fml P2))"
      using seq_helper2 [of P2 "(? get_fml P2)" "(? get_fml P1)"]
      using local_assm2
      by simp
    also have "... \<rightleftharpoons> (? get_fml P1 foland get_fml P2)"
      using check_helper_and
      by simp
    ultimately show "(P1;P2) \<rightleftharpoons> (? get_fml P1 foland get_fml P2)"
      using kat_dl.progEquiv_transp_expl by blast
  qed
next
  case (CHOICE P1 P2)
  then show ?case
    unfolding is_purely_check.simps
    unfolding get_fml.simps
    apply simp
  proof -
    assume local_assm1: "P1 \<rightleftharpoons> (? get_fml P1)"
        and local_assm2: "P2 \<rightleftharpoons> (? get_fml P2)"
    have fact1: "(P1\<squnion>P2) \<rightleftharpoons> ((? get_fml P1)\<squnion>P2)"
      using choice_helper1[of P1 "(? get_fml P1)" P2]
      using local_assm1
      by simp
    also have fact2: "... \<rightleftharpoons> ((? get_fml P1)\<squnion>(? get_fml P2))"
      using choice_helper2 [of P2 "(? get_fml P2)" "(? get_fml P1)"]
      using local_assm2
      by simp
    also have "... \<rightleftharpoons> (? get_fml P1 or get_fml P2)"
      using check_helper_or
      by simp
    ultimately have "(P1\<squnion>P2) \<rightleftharpoons> (? get_fml P1 or get_fml P2)"
      using kat_dl.progEquiv_transp_expl by blast
    then show "(P1\<squnion>P2) \<rightleftharpoons> (? folnot (folnot get_fml P1 foland folnot get_fml P2))"
      by force
  qed    
next
  case (LOOP P)
  then show ?case
    unfolding is_purely_check.simps
    unfolding get_fml.simps
    apply (simp del: FirstOrder.OR_def FOLTRUE_def)
  proof -
    have fact: "\<And> n \<mu> \<omega> . full_prog_eval_int n (? get_fml P;((? get_fml P)* )) \<mu> \<omega> \<Longrightarrow> state_eval \<mu> = state_eval \<omega>"
      unfolding full_prog_eval_int.simps(2,3)
      subgoal for n \<mu> \<omega>
    proof (induct n arbitrary: \<mu> \<omega>)
      case 0
      then show ?case
        unfolding full_prog_eval_int.simps(5)[of 0]
        by simp
    next
      case (Suc n)
      show ?case
        using Suc.prems
        unfolding full_prog_eval_int.simps(5)[of "(Suc n)"]
        apply (simp del: full_prog_eval_int.simps)
        apply (elim conjE, elim exE, elim conjE, elim disjE)
          apply simp
        using Suc.hyps
         apply (metis full_prog_eval_int.simps(2) full_prog_eval_int.simps(3))
        using Suc.hyps
        using Suc.prems by blast
    qed.
    have "(P *) \<rightleftharpoons> ((? get_fml P)* )"
      using loop_helper[of P "(? get_fml P)"]
      using LOOP
      unfolding is_purely_check.simps
      by simp
    also have "... \<rightleftharpoons> ( (? FOLTRUE) \<squnion> ((? get_fml P);((? get_fml P)* )))"
      using kat_rule12[of "(? get_fml P)"]
      using kat_dl.progEquiv_symp_expl by blast
    also have "... \<rightleftharpoons> (? FOLTRUE)"
      unfolding kat_dl.progEquivSimplification
      unfolding full_prog_eval_def
      unfolding full_prog_eval_int.simps(2,4)
      unfolding dyn_eval.simps FOLTRUE_def FirstOrder.OR_def
      unfolding fol_eval.simps
      using fact
      by blast
    ultimately show "(P*) \<rightleftharpoons> (? FOLTRUE)"
      using kat_dl.progEquiv_transp_expl by blast
  qed
qed

fun COMPLEMENT :: "('atom, 'var, 'prog) kat_prog \<Rightarrow> ('atom, 'var, 'prog) kat_prog"
  where
    "COMPLEMENT x = (CHECK (folnot (get_fml x)))"

(* Boolean Algebra as defined on page 137 of Dynamic Logic *)

(* TODO: This could be simplified by eliminatig bool_lemma* *)
(* This stems from v1 but I realized we must be more general than individual checks *)
(* For completeness I am reiterating all rules here, in practice
   quite a few of them already hold through the kleene algebera above... *)

lemma bool_rule1: "(((? x) \<squnion> (? y)) \<squnion> (? z)) \<rightleftharpoons> ((? x) \<squnion> ((? y) \<squnion> (? z)))"
  using kat_rule1
  using kat_dl.progEquiv_symp_expl by blast

theorem bool_rule1_general:
  assumes "is_purely_check x"
      and "is_purely_check y"
      and "is_purely_check z"
    shows "((x \<squnion> y) \<squnion> z) \<rightleftharpoons> (x \<squnion> (y \<squnion> z))"
proof -
  have "((x \<squnion> y) \<squnion> z) \<rightleftharpoons> (? (get_fml ((x \<squnion> y) \<squnion> z)))"
    using eq_if_pure[of "((x \<squnion> y) \<squnion> z)"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> (((? (get_fml x)) \<squnion> (? (get_fml y))) \<squnion> (? (get_fml z)))"
    unfolding get_fml.simps
    using check_helper_or check_helper_and
    by (meson choice_helper1 kat_dl.progEquiv_symp_expl kat_dl.progEquiv_transp_expl)
  also have "... \<rightleftharpoons> ((? (get_fml x)) \<squnion> ((? (get_fml y)) \<squnion> (? (get_fml z))))"
    using bool_rule1
    by blast
  also have "... \<rightleftharpoons> (x \<squnion> (y \<squnion> z))"
    using assms
    using eq_if_pure[of x]
    using eq_if_pure[of y]
    using eq_if_pure[of z]
    using calculation kat_dl.progEquiv_symp_expl kat_dl.progEquiv_transp_expl kat_rule1 by blast
  finally show ?thesis
    by blast
qed

lemma bool_rule2: "(((? x) ; (? y)) ; (? z)) \<rightleftharpoons> ((? x) ; ((? y) ; (? z)))"
  using kat_rule5
  using kat_dl.progEquiv_symp_expl by blast

theorem bool_rule2_general:
  assumes "is_purely_check x"
      and "is_purely_check y"
      and "is_purely_check z"
    shows "((x ; y) ; z) \<rightleftharpoons> (x ; (y ; z))"
proof -
  have "((x ; y) ; z) \<rightleftharpoons> (? (get_fml ((x ; y) ; z)))"
    using eq_if_pure[of "((x ; y) ; z)"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> (((? (get_fml x)) ; (? (get_fml y))) ; (? (get_fml z)))"
    unfolding get_fml.simps
    using check_helper_and
    by (meson kat_dl.progEquiv_symp_expl kat_dl.progEquiv_transp_expl seq_helper1)
  also have "... \<rightleftharpoons> ((? (get_fml x)) ; ((? (get_fml y)) ; (? (get_fml z))))"
    using bool_rule2
    by blast
  also have "... \<rightleftharpoons> (x ; (y ; z))"
    using assms
    using eq_if_pure[of x]
    using eq_if_pure[of y]
    using eq_if_pure[of z]
    using calculation kat_dl.progEquivSimplification kat_rule5 by force
  finally show ?thesis
    by blast
qed

lemma bool_rule3: "((? x) \<squnion> (? y)) \<rightleftharpoons> ((? y) \<squnion> (? x))"
  using kat_rule2
  using kat_dl.progEquiv_symp_expl by blast

theorem bool_rule3_general:
  assumes "is_purely_check x"
      and "is_purely_check y"
    shows "(x \<squnion> y) \<rightleftharpoons> (y \<squnion> x)"
proof -
  have "(x \<squnion> y) \<rightleftharpoons> (? (get_fml (x \<squnion> y)))"
    using eq_if_pure[of "x \<squnion> y"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> ((? (get_fml x)) \<squnion> (? (get_fml y)))"
    unfolding get_fml.simps
    using check_helper_or
    using kat_dl.progEquiv_symp_expl by blast
  also have "... \<rightleftharpoons> ((? (get_fml y)) \<squnion> (? (get_fml x)))"
    using bool_rule3
    by blast
  also have "... \<rightleftharpoons> (y \<squnion> x)"
    using assms
    using eq_if_pure[of x]
    using eq_if_pure[of y]
    using calculation kat_dl.progEquivSimplification kat_rule2 by force
  finally show ?thesis
    by blast
qed

lemma bool_rule4: "((? x) ; (? y)) \<rightleftharpoons> ((? y) ; (? x))"
  using check_helper_and[of x y]
  using check_helper_and[of y x]
  using bool_and_comm
proof -
  obtain ss :: "('atom, 'var, 'prog) kat_prog \<Rightarrow> ('atom, 'var, 'prog) kat_prog \<Rightarrow> 'state" and ssa :: "('atom, 'var, 'prog) kat_prog \<Rightarrow> ('atom, 'var, 'prog) kat_prog \<Rightarrow> 'state" where
    "\<forall>x0 x1. (\<exists>v2 v3. full_prog_eval x1 v2 v3 \<and> \<not> full_prog_eval x0 v2 v3) = (full_prog_eval x1 (ss x0 x1) (ssa x0 x1) \<and> \<not> full_prog_eval x0 (ss x0 x1) (ssa x0 x1))"
    by moura
  then have "\<forall>k ka. (\<not> k \<le> ka \<or> (\<forall>s sa. \<not> full_prog_eval k s sa \<or> full_prog_eval ka s sa)) \<and> (k \<le> ka \<or> full_prog_eval k (ss ka k) (ssa ka k) \<and> \<not> full_prog_eval ka (ss ka k) (ssa ka k))"
    using kat_dl.progRefine_def by auto
  then show ?thesis
    by (smt (z3) \<open>(? x;? y) \<rightleftharpoons> (? x foland y)\<close> \<open>(? y;? x) \<rightleftharpoons> (? y foland x)\<close> bool_and_comm dyn_eval.simps(1) full_prog_eval_def full_prog_eval_int.simps(2) kat_dl.progEquiv_def)
qed

theorem bool_rule4_general:
  assumes "is_purely_check x"
      and "is_purely_check y"
    shows "(x ; y) \<rightleftharpoons> (y ; x)"
proof -
  have "(x ; y) \<rightleftharpoons> (? (get_fml (x ; y)))"
    using eq_if_pure[of "x ; y"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> (? (get_fml x) ; ? (get_fml y))"
    unfolding get_fml.simps
    using check_helper_and
    using kat_dl.progEquiv_symp_expl by blast
  also have "... \<rightleftharpoons> (? (get_fml y) ; ? (get_fml x))"
    using bool_rule4
    by blast
  also have "... \<rightleftharpoons> (y ; x)"
    using assms
    using eq_if_pure[of x]
    using eq_if_pure[of y]
    by (metis check_helper_and eq_if_pure get_fml.simps(3) is_purely_check.simps(3) kat_dl.progEquivSimplification)
  finally show ?thesis
    by blast
qed

lemma bool_rule5: "((? x) \<squnion> ((? y) ; (? z))) \<rightleftharpoons> (((? x) \<squnion> (? y)) ; ((? x) \<squnion>  (? z)))"
proof -
  have "(? x\<squnion>(? y;? z)) \<rightleftharpoons> (? x\<squnion>(? ( y foland  z)))"
    using check_helper_and[of y z]
    using choice_helper2
    by blast
  also have "... \<rightleftharpoons> (? (x or ( y foland  z)))"
    using check_helper_or
    by blast
  also have "... \<rightleftharpoons> (? ( (x or y) foland  (x or z)))"
    using bool_or_distrib[of x y z]
    unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by simp
  also have "... \<rightleftharpoons> (? ( (x or y)) ; (?  (x or z)))"
    using check_helper_and
    using kat_dl.progEquiv_symp_expl by blast
  also have "... \<rightleftharpoons> (((? x) \<squnion> (? y)) ; ((? x) \<squnion>  (? z)))"
    using check_helper_or
    by (meson kat_dl.progEquiv_symp_expl kat_dl.progEquiv_transp_expl seq_helper1 seq_helper2)
  finally show ?thesis
    by blast
qed

lemma bool_rule6: "((? x) ; ((? y) \<squnion> (? z))) \<rightleftharpoons> (((? x) ; (? y)) \<squnion> ((? x) ; (? z)))"
  using kat_rule8
  by blast

theorem bool_rule6_general:
  assumes "is_purely_check x"
      and "is_purely_check y"
      and "is_purely_check z"
    shows "(x ; (y \<squnion> z)) \<rightleftharpoons> ((x ; y) \<squnion> (x ; z))"
proof -
  have "(x ; (y \<squnion> z)) \<rightleftharpoons> (? (get_fml (x ; (y \<squnion> z))))"
    using eq_if_pure[of "x ; (y \<squnion> z)"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> (? (get_fml x) ; (? (get_fml y) \<squnion> ? (get_fml z)))"
    unfolding get_fml.simps
    using check_helper_and check_helper_or
    by (meson kat_dl.progEquiv_symp_expl kat_dl.progEquiv_transp_expl seq_helper2)
  also have "... \<rightleftharpoons> ((? (get_fml x) ; ? (get_fml y)) \<squnion> (? (get_fml x) ; ? (get_fml z)))"
    using bool_rule6
    by blast
  also have "... \<rightleftharpoons> ((x ; y) \<squnion> (x ; z))"
    using assms
    using eq_if_pure[of x]
    using eq_if_pure[of y]
    using eq_if_pure[of z]
    using calculation kat_dl.progEquivSimplification kat_rule8 by auto
  finally show ?thesis
    by blast
qed

lemma bool_rule7: "((? x) \<squnion> ?(folnot FOLTRUE)) \<rightleftharpoons> (? x)"
  using kat_rule3
  by blast

theorem bool_rule7_general:
  assumes "is_purely_check x"
    shows "(x \<squnion> ?(folnot FOLTRUE)) \<rightleftharpoons> x"
proof -
  have "(x \<squnion> ?(folnot FOLTRUE)) \<rightleftharpoons> (?(get_fml (x \<squnion> ?(folnot FOLTRUE))))"
    using eq_if_pure[of "x \<squnion> ?(folnot FOLTRUE)"]
    using assms
    unfolding is_purely_check.simps
    by simp
  also have "... \<rightleftharpoons> ((? (get_fml x)) \<squnion> ?(folnot FOLTRUE))"
    unfolding get_fml.simps
    using check_helper_or
    using kat_dl.progEquiv_symp_expl by blast
  also have "... \<rightleftharpoons> (? (get_fml x))"
    using bool_rule7
    by blast
  also have "... \<rightleftharpoons> x"
    using assms
    using eq_if_pure[of x]
    using kat_dl.progEquiv_symp_expl by blast
  finally show ?thesis
    by blast
qed

lemma bool_rule8: "((? x) ; ?(FOLTRUE)) \<rightleftharpoons> (? x)"
  using kat_rule7
  by blast

theorem bool_rule8_general:
  assumes "is_purely_check x"
    shows "(x ; (? FOLTRUE)) \<rightleftharpoons> x"
proof -
  have "(x ; (? FOLTRUE)) \<rightleftharpoons> ((? (get_fml x)) ; (? FOLTRUE))"
    using eq_if_pure[of "x"]
    using assms
    unfolding is_purely_check.simps
    using seq_helper1
    by simp
  also have "... \<rightleftharpoons> (? (get_fml x))"
    using bool_rule8
    by blast
  also have "... \<rightleftharpoons> x"
    using assms
    using eq_if_pure[of x]
    using kat_dl.progEquiv_symp_expl by blast
  finally show ?thesis
    by blast
qed

lemma bool_rule9: "((? x) \<squnion> ?(FOLTRUE)) \<rightleftharpoons> (? FOLTRUE)"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def
  unfolding full_prog_eval_int.simps
  unfolding dyn_eval.simps
  by simp

theorem bool_rule9_general:
  assumes "is_purely_check x"
    shows "(x \<squnion> (? FOLTRUE)) \<rightleftharpoons> (? FOLTRUE)"
proof -
  have "(x \<squnion> (? FOLTRUE)) \<rightleftharpoons> ((? (get_fml x)) \<squnion> (? FOLTRUE))"
    using eq_if_pure[of "x"]
    using assms
    unfolding is_purely_check.simps
    using choice_helper1
    by simp
  also have "... \<rightleftharpoons> (? FOLTRUE)"
    using bool_rule9
    by blast
  finally show ?thesis
    by blast
qed

lemma bool_rule10: "((? x) ; ?(folnot FOLTRUE)) \<rightleftharpoons> (? (folnot FOLTRUE))"
  unfolding kat_dl.progEquiv_def kat_dl.progRefine_def
  unfolding full_prog_eval_def
  unfolding full_prog_eval_int.simps
  unfolding dyn_eval.simps
  by simp

theorem bool_rule10_general:
  assumes "is_purely_check x"
    shows "(x ; ?(folnot FOLTRUE)) \<rightleftharpoons> (? (folnot FOLTRUE))"
proof -
  have "(x ; (? (folnot FOLTRUE))) \<rightleftharpoons> ((? (get_fml x)) ; (? (folnot FOLTRUE)))"
    using eq_if_pure[of "x"]
    using assms
    unfolding is_purely_check.simps
    using seq_helper1
    by simp
  also have "... \<rightleftharpoons> (? (folnot FOLTRUE))"
    using bool_rule10
    by blast
  finally show ?thesis
    by blast
qed

theorem bool_rule11_general:
  assumes "is_purely_check x"
  shows "(x \<squnion> (COMPLEMENT x)) \<rightleftharpoons> (? FOLTRUE)"
proof -
  have "(x \<squnion> (COMPLEMENT x)) \<rightleftharpoons> ((? (get_fml x)) \<squnion> (COMPLEMENT x))"
    using assms
    using eq_if_pure[of x]
    using choice_helper1
    by simp
  also have "... \<rightleftharpoons> ( (? (get_fml x)) \<squnion> (? (folnot (get_fml x))))"
    unfolding COMPLEMENT.simps
    using kat_dl.progEquivSimplification by blast

  also have "... \<rightleftharpoons> (? ((get_fml x) or (folnot (get_fml x))))"
    using check_helper_or
    by force

  also have "... \<rightleftharpoons> (? FOLTRUE)"
    unfolding kat_dl.progEquiv_def
    unfolding kat_dl.progRefine_def
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    unfolding FirstOrder.OR_def fol_eval.simps
    by simp
  finally show ?thesis
    by blast
qed

theorem bool_rule12_general:
  assumes "is_purely_check x"
  shows "(x ; (COMPLEMENT x)) \<rightleftharpoons> (? (folnot FOLTRUE))"
proof -
  have "(x ; (COMPLEMENT x)) \<rightleftharpoons> ((? (get_fml x)) ; (COMPLEMENT x))"
    using assms
    using eq_if_pure[of x]
    using seq_helper1
    by simp
  also have "... \<rightleftharpoons> ( (? (get_fml x)) ; (? (folnot (get_fml x))))"
    unfolding COMPLEMENT.simps
    using kat_dl.progEquivSimplification by blast

  also have "... \<rightleftharpoons> (? ((get_fml x) foland (folnot (get_fml x))))"
    using check_helper_and
    by force

  also have "... \<rightleftharpoons> (? (folnot FOLTRUE))"
    unfolding kat_dl.progEquiv_def
    unfolding kat_dl.progRefine_def
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    unfolding FirstOrder.OR_def fol_eval.simps
    by simp
  finally show ?thesis
    by blast
qed


theorem bool_rule13_general:
  assumes "is_purely_check x"
  shows "(x \<squnion> x) \<rightleftharpoons> x"
proof -
  have "(x \<squnion> x) \<rightleftharpoons> ((? (get_fml x)) \<squnion> (? (get_fml x)))"
    using assms
    using eq_if_pure[of x]
    using choice_helper1 choice_helper2
    apply simp
    using kat_dl.progEquiv_transp_expl by blast

  also have "... \<rightleftharpoons> (? (get_fml x))"
    unfolding kat_dl.progEquiv_def
    unfolding kat_dl.progRefine_def
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    unfolding FirstOrder.OR_def fol_eval.simps
    by simp

  also have "... \<rightleftharpoons> x"
    using assms
    using eq_if_pure[of x]
    apply simp
    using kat_dl.progEquiv_symp_expl by blast

  finally show ?thesis
    by blast
qed
    
    
  

theorem bool_rule14_general:
  assumes "is_purely_check x"
  shows "(x ; x) \<rightleftharpoons> x"
proof -
  have "(x ; x) \<rightleftharpoons> ((? (get_fml x)) ; (? (get_fml x)))"
    using assms
    using eq_if_pure[of x]
    using seq_helper1 seq_helper2
    apply simp
    using kat_dl.progEquiv_transp_expl by blast

  also have "... \<rightleftharpoons> (? (get_fml x))"
    unfolding kat_dl.progEquiv_def
    unfolding kat_dl.progRefine_def
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    unfolding fol_eval.simps
    by fastforce

  also have "... \<rightleftharpoons> x"
    using assms
    using eq_if_pure[of x]
    apply simp
    using kat_dl.progEquiv_symp_expl by blast

  finally show ?thesis
    by blast
qed



end



end