theory ConverseDynamicLogic
  imports
    Main
    "ExtensionalDynamicLogic"
    "DynamicLogicProof"
begin

datatype ('a,'vr,'pr) converse_prog  =
  CPROG "'pr"
  | CONVERSE "('a,'vr,'pr) converse_prog"

notation CONVERSE ("_\<^sup>-\<^sup>1" 30)

locale ConverseDynLog =
    extDynLogCore atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  +
  fixes dyn_prog_BV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
assumes prog_bv_overapprox: "\<And> \<pi> v . (
          \<exists> \<mu> \<omega>.
            ((prog_eval \<pi> \<mu> \<omega>) \<and> ((state_eval \<mu>) v \<noteq> (state_eval \<omega>) v))
  ) \<longrightarrow> dyn_prog_BV \<pi> v"
    and prog_bv_finite: "\<And> \<pi> . finite (Collect (dyn_prog_BV \<pi>))"
begin

sublocale original_dl : extDynLogCore atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
  by (simp add: extDynLogCore_axioms)

fun full_prog_eval :: "('atom,'var,'prog) converse_prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where
      "full_prog_eval (CPROG \<pi>) \<mu> \<omega> = prog_eval \<pi> \<mu> \<omega>"
    | "full_prog_eval (CONVERSE \<pi>) \<mu> \<omega> = full_prog_eval \<pi> \<omega> \<mu>"

fun full_prog_bv_syn :: "('atom,'var,'prog) converse_prog \<Rightarrow> 'var \<Rightarrow> bool" and
    full_prog_fv_syn :: "('atom,'var,'prog) converse_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_prog_bv_syn (CPROG \<pi>) v = dyn_prog_BV \<pi> v" (*TODO: make syntactic *)
  | "full_prog_bv_syn (CONVERSE \<pi>) v = full_prog_bv_syn \<pi> v"
  | "full_prog_fv_syn (CPROG \<pi>) v = dyn_prog_FV \<pi> v"
  | "full_prog_fv_syn (CONVERSE \<pi>) v = ((full_prog_fv_syn \<pi> v) \<or> (full_prog_bv_syn \<pi> v))"

lemma full_prog_bv_syn_overapprox:
  "\<And> \<pi> v . (
          \<exists> \<mu> \<omega>.
            ((full_prog_eval \<pi> \<mu> \<omega>) \<and> ((state_eval \<mu>) v \<noteq> (state_eval \<omega>) v))
            ) \<longrightarrow> full_prog_bv_syn \<pi> v"
  subgoal for \<pi>
  proof (induct \<pi>)
    case (CPROG x)
    then show ?case
      unfolding full_prog_bv_syn.simps full_prog_eval.simps
      by (simp add: prog_bv_overapprox)
  next
    case (CONVERSE \<pi>)
    then show ?case
      unfolding full_prog_bv_syn.simps full_prog_eval.simps
      using CONVERSE.hyps
      by auto
  qed.

sublocale converse_dl : extDynLogCore
  "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"
proof
  show fvFinite: "\<And> \<pi> . finite (Collect (full_prog_fv_syn \<pi>))"
  subgoal for \<pi>
  proof (induct \<pi>)
    case (CPROG x)
    then show ?case
      unfolding full_prog_fv_syn.simps
      by (simp add: prog_fv_finite)
  next
    case (CONVERSE x)
    then show ?case
    proof (induct x)
      case (CPROG x)
      then show ?case
      unfolding full_prog_fv_syn.simps
      unfolding full_prog_bv_syn.simps
      by (simp add: prog_bv_finite)
    next
      case (CONVERSE x)
      then show ?case
      unfolding full_prog_fv_syn.simps
      unfolding full_prog_bv_syn.simps
      by (simp add: prog_bv_finite)
    qed
  qed.
  have strongExt: "\<And> \<pi> \<mu> \<omega> \<mu>' \<omega>'.
       (\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
            state_eval \<mu>' v = state_eval \<omega>' v) \<longrightarrow>
       full_prog_eval \<pi> \<mu> \<mu>' = full_prog_eval \<pi> \<omega> \<omega>'"
    subgoal for \<pi> \<mu> \<omega> \<mu>' \<omega>'
    proof (induct \<pi> arbitrary: \<mu> \<omega> \<mu>' \<omega>')
      case (CPROG x)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        using strong_extensionality by blast
    next
      case (CONVERSE \<pi>)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        using CONVERSE.hyps
          by presburger
      qed.
  then show "\<forall>\<pi> \<mu> \<omega> \<mu>' \<omega>'.
     (\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<and>
          state_eval \<mu>' v = state_eval \<omega>' v) \<longrightarrow>
     full_prog_eval \<pi> \<mu> \<mu>' = full_prog_eval \<pi> \<omega> \<omega>'"
    by blast
  have "\<And>\<pi> V \<mu> \<omega> \<nu>.
       (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>) \<and>
        (fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v) \<nu> \<mu>)"
    subgoal for \<pi> V \<mu> \<omega> \<nu>
    proof (induct \<pi> arbitrary: V \<mu> \<omega> \<nu>)
      case (CPROG x)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        using prog_fv_overapprox
        apply (intro impI,intro conjI)
         apply blast
        by (metis (no_types, lifting) fol_states_agree_on_def full_prog_bv_syn.simps(1) prog_bv_overapprox)
    next
      case (CONVERSE \<pi>)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        proof (intro impI,elim conjE,intro conjI)
          assume H_all: " \<forall>v. full_prog_fv_syn \<pi> v \<or> full_prog_bv_syn \<pi> v \<longrightarrow> V v"
          assume H_agree: "fol_states_agree_on V \<mu> \<omega>"
          assume H_run: "full_prog_eval \<pi> \<nu> \<mu>"

          have \<nu>_\<mu>_almost_agree: "fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v) \<nu> \<mu>"
            using H_run fol_states_agree_on_def full_prog_bv_syn_overapprox by blast

          have \<nu>_\<omega>_almost_agree: "fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v \<and> V v) \<nu> \<omega>"
            using \<nu>_\<mu>_almost_agree H_agree
            unfolding fol_states_agree_on_def by presburger

          show "fol_states_agree_on (\<lambda>v. \<not> full_prog_bv_syn (\<pi>\<^sup>-\<^sup>1) v) \<nu> \<mu>"
            unfolding full_prog_bv_syn.simps
            using \<nu>_\<mu>_almost_agree by force

          have H_agree_fv: "fol_states_agree_on (full_prog_fv_syn \<pi>) \<mu> \<omega>"
            using H_all H_agree
            using fol_states_agree_on_def by force

          have H_agree_bv: "fol_states_agree_on (full_prog_bv_syn \<pi>) \<mu> \<omega>"
            using H_all H_agree
            using fol_states_agree_on_def by force

          obtain \<nu>' where \<upsilon>_def: "\<And> v . (
            (full_prog_bv_syn \<pi> v \<longrightarrow> (state_eval \<nu>' v = state_eval \<nu> v)) \<and>
            (\<not>(full_prog_bv_syn \<pi> v) \<longrightarrow> (state_eval \<nu>' v = state_eval \<omega> v))
            )"
            using state_space_convexity
            by (metis mem_Collect_eq)

          have uvf_def: "\<forall>v. state_eval \<nu>' v = (if full_prog_bv_syn \<pi> v then state_eval \<nu> v else state_eval \<omega> v)"
            using \<upsilon>_def by (simp add: \<upsilon>_def)

          (*have "fol_states_agree_on (\<lambda> v . ((V v) \<and> \<not>(full_prog_bv_syn \<pi> v))) \<nu> \<omega>"
            using H_agree H_run
            unfolding fol_states_agree_on_def
            using full_prog_bv_syn_overapprox[of \<pi>]
            by metis*)

          have \<upsilon>_\<nu>_agree: "fol_states_agree_on V \<nu>' \<nu>"
            using uvf_def H_agree H_run
            unfolding fol_states_agree_on_def
            using full_prog_bv_syn_overapprox[of \<pi>]
            by metis

          obtain \<mu>' where \<upsilon>2_cond: "full_prog_eval \<pi> \<nu>' \<mu>' \<and> fol_states_agree_on V \<mu> \<mu>'"
            using CONVERSE.hyps[of V \<nu> \<nu>' \<mu>]
            using H_run \<upsilon>_\<nu>_agree H_all
            using fol_states_agree_on_def by auto

          have "fol_states_agree_on (\<lambda> v . True) \<mu>' \<omega>"
            using H_agree \<upsilon>2_cond
            using fol_states_agree_on_def
            by (metis H_all full_prog_bv_syn_overapprox uvf_def)

          

          then have "full_prog_eval \<pi> \<nu>' \<omega>"
            using strongExt[of \<nu>' \<nu>' \<mu>' \<omega> \<pi>]
            unfolding fol_states_agree_on_def
            using \<upsilon>2_cond by blast

          then show "\<exists>\<upsilon>. full_prog_eval \<pi> \<upsilon> \<omega> \<and> fol_states_agree_on V \<nu> \<upsilon>"
            using \<upsilon>_\<nu>_agree
            using fol_states_agree_on_def by force
      qed
    qed.
  then show "\<And>\<pi> V \<mu> \<omega> \<nu>.
       (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
    by blast
qed


lemma c_bv_sound:
  "converse_dl.dlc.dyn_prog_bv_sem \<pi> v \<Longrightarrow> full_prog_bv_syn \<pi> v"
  unfolding converse_dl.dlc.dyn_prog_bv_sem.simps
  using full_prog_bv_syn_overapprox by blast



lemma fv_box_free:
  assumes "\<not> full_prog_fv_syn \<pi> x" "\<not> converse_dl.dlc.dyn_fv_sem \<phi> x"
  shows "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk>\<phi>) x"
  using assms converse_dl.dlc.dyn_fv_sem_box_elim converse_dl.dlc.dyn_FV_prog_sound
  by blast

lemma fv_dia_free:
  assumes "\<not> full_prog_fv_syn \<pi> x" "\<not> converse_dl.dlc.dyn_fv_sem \<phi> x"
  shows "\<not> converse_dl.dlc.dyn_fv_sem (\<langle>\<pi>\<rangle>\<phi>) x"
proof -
  have "\<not> converse_dl.dlc.dyn_fv_sem (\<rceil>\<phi>) x"
    using assms(2) converse_dl.dlc.dyn_fv_sem_not_eq by metis
  then have "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>\<pi>\<rbrakk>(\<rceil>\<phi>)) x"
    by (rule fv_box_free[OF assms(1)])
  then have "\<not> converse_dl.dlc.dyn_fv_sem (\<rceil>(\<lbrakk>\<pi>\<rbrakk>(\<rceil>\<phi>))) x"
    using converse_dl.dlc.dyn_fv_sem_not_eq by metis
  then show ?thesis
    by (simp add: converse_dl.dlc.DIAMOND_def)
qed

lemma dt_converse_box_diamond:
  "\<Turnstile>[converse_dl.dlc.dyn_eval] (P \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<langle>(CONVERSE \<pi>)\<rangle>P)"
  apply (simp add: dyn_sem)
  by auto


lemma dt_converse_diamond_box:
  "\<Turnstile>[converse_dl.dlc.dyn_eval] (P \<Rrightarrow> \<lbrakk>(CONVERSE \<pi>)\<rbrakk>\<langle>\<pi>\<rangle>P)"
  apply (simp add: dyn_sem)
  by auto

lemma dt_l_converse:
  assumes "\<Turnstile>[converse_dl.dlc.dyn_eval] \<langle>\<pi>\<rangle> P \<Rrightarrow> Q"
  shows "\<Turnstile>[converse_dl.dlc.dyn_eval] P \<Rrightarrow> \<lbrakk>(CONVERSE \<pi>)\<rbrakk> Q"
proof -
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] \<lbrakk>(CONVERSE \<pi>)\<rbrakk>(\<langle>\<pi>\<rangle> P \<Rrightarrow> Q)"
    using assms
    by (rule converse_dl.dlc.dyn_axiom_G)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>(CONVERSE \<pi>)\<rbrakk>\<langle>\<pi>\<rangle> P) \<Rrightarrow> \<lbrakk>(CONVERSE \<pi>)\<rbrakk>Q"
    by (rule converse_dl.dlc.dt_box_K)
  thus ?thesis
    using dt_converse_diamond_box[of P \<pi>]
    by converse_dl.dlc.dt_prop
qed


lemma dt_r_converse:
  assumes "\<Turnstile>[converse_dl.dlc.dyn_eval] P \<Rrightarrow> \<lbrakk>(CONVERSE \<pi>)\<rbrakk> Q"
    shows "\<Turnstile>[converse_dl.dlc.dyn_eval] \<langle>\<pi>\<rangle> P \<Rrightarrow> Q"
proof -
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<rceil>\<lbrakk>(CONVERSE \<pi>)\<rbrakk> Q \<Rrightarrow> \<rceil>P)"
    using assms
    by converse_dl.dlc.dt_prop
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>(CONVERSE \<pi>)\<rangle> \<rceil>Q \<Rrightarrow> \<rceil>P)"
    by (simp add: dyn_sem)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] \<lbrakk>\<pi>\<rbrakk>(\<langle>(CONVERSE \<pi>)\<rangle> \<rceil>Q \<Rrightarrow> \<rceil>P)"
    by (rule converse_dl.dlc.dyn_axiom_G)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>\<pi>\<rbrakk>\<langle>(CONVERSE \<pi>)\<rangle> \<rceil>Q) \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<rceil>P"
    by (rule converse_dl.dlc.dt_box_K)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] \<rceil>Q \<Rrightarrow> \<lbrakk>\<pi>\<rbrakk>\<rceil>P"
    using dt_converse_box_diamond[of "\<rceil>Q" \<pi>]
    by converse_dl.dlc.dt_prop
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] \<rceil> \<lbrakk>\<pi>\<rbrakk>\<rceil>P \<Rrightarrow> Q"
    by converse_dl.dlc.dt_prop
  thus ?thesis
    by converse_dl.dlc.dt_prop
qed


end

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

lemma inf_flow_cf:
  assumes de: "d \<noteq> e" and dr: "d \<noteq> r" and er: "e \<noteq> r"
      and Ge: "G \<noteq> e" and Gr: "G \<noteq> r"
      and eC: "\<not> full_prog_bv_syn C e" and eD: "\<not> full_prog_bv_syn D e"
      and eCb: "\<not> full_prog_bv_syn C e" and eDb: "\<not> full_prog_bv_syn D e"
      and rCb: "\<not> full_prog_bv_syn C r" and rDb: "\<not> full_prog_bv_syn D r"
      and rCf: "\<not> full_prog_fv_syn C r" and rDf: "\<not> full_prog_fv_syn D r"
  assumes tot: "\<Turnstile>[converse_dl.dlc.dyn_eval] \<lbrakk>C\<rbrakk>\<langle>D\<rangle> converse_dl.dlc.DYNTRUE"
  assumes ni: "\<Turnstile>[converse_dl.dlc.dyn_eval] \<bbbE> r . \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d r))"
    shows "\<Turnstile>[converse_dl.dlc.dyn_eval]
            (\<lbrakk>D\<rbrakk>(FOL (eqPred d e)))
            \<Rrightarrow> (\<lbrakk>(CONVERSE C)\<rbrakk> \<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> (FOL (eqPred d e)))"
proof -
  let ?de = "FOL (eqPred d e) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?dr = "FOL (eqPred d r) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?er = "FOL (eqPred e r) :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?T  = "converse_dl.dlc.DYNTRUE :: ('atom,'var,('atom,'var,'prog) converse_prog) dyn_formula"
  let ?A  = "\<langle>C\<rangle>\<lbrakk>D\<rbrakk> ?de"
  let ?B  = "\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?de"
  let ?NI = "\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?dr"

  text \<open>Equality reasoning on atoms (the only semantic step).\<close>
  have eq1: "\<Turnstile>[converse_dl.dlc.dyn_eval] (?de and ?dr) \<Rrightarrow> ?er"
  proof (rule converse_dl.dlc.dt_propI)
    fix \<mu>
    show "converse_dl.dlc.dyn_eval ((?de and ?dr) \<Rrightarrow> ?er) \<mu>"
      using fol_eqPred_sound[OF de, of \<mu>] fol_eqPred_sound[OF dr, of \<mu>]
            fol_eqPred_sound[OF er, of \<mu>]
      by (simp add: dyn_sem)
  qed
  have eq2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (?dr and ?er) \<Rrightarrow> ?de"
  proof (rule converse_dl.dlc.dt_propI)
    fix \<mu>
    show "converse_dl.dlc.dyn_eval ((?dr and ?er) \<Rrightarrow> ?de) \<mu>"
      using fol_eqPred_sound[OF de, of \<mu>] fol_eqPred_sound[OF dr, of \<mu>]
            fol_eqPred_sound[OF er, of \<mu>]
      by (simp add: dyn_sem)
  qed

  text \<open>Step 1: instantiate G in NI.\<close>
  have s1: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI \<Rrightarrow> \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk> ?dr"
    by (rule converse_dl.dlc.dyn_axiom_F3)

  text \<open>Step 2: factual diamond + NI box + totality give \<langle>C\<rangle>\<langle>D\<rangle>(e = r).\<close>
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?dr \<Rrightarrow> (?de \<Rrightarrow> ?er)"
    using eq1 by converse_dl.dlc.dt_prop
  then have inD1: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?de) \<Rrightarrow> (\<lbrakk>D\<rbrakk>?er))"
    by (rule converse_dl.dlc.dt_box_K2)
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (?T \<Rrightarrow> ?er)"
    by converse_dl.dlc.dt_prop
  then have inD2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?er) \<Rrightarrow> ((\<langle>D\<rangle>?T) \<Rrightarrow> (\<langle>D\<rangle>?er))"
    by (rule converse_dl.dlc.dt_box_dia_K)
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> ((\<langle>D\<rangle>?T) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?de) \<Rrightarrow> (\<langle>D\<rangle>?er)))"
    using inD1 inD2 by converse_dl.dlc.dt_prop
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval]
               (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> ((\<lbrakk>C\<rbrakk>\<langle>D\<rangle>?T) \<Rrightarrow> (\<lbrakk>C\<rbrakk>((\<lbrakk>D\<rbrakk>?de) \<Rrightarrow> (\<langle>D\<rangle>?er))))"
    by (rule converse_dl.dlc.dt_box_K2)
  moreover have "\<Turnstile>[converse_dl.dlc.dyn_eval]
               (\<lbrakk>C\<rbrakk>((\<lbrakk>D\<rbrakk>?de) \<Rrightarrow> (\<langle>D\<rangle>?er))) \<Rrightarrow> (?A \<Rrightarrow> (\<langle>C\<rangle>\<langle>D\<rangle>?er))"
    by (rule converse_dl.dlc.dt_diamond_K)
  ultimately have s2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> (?A \<Rrightarrow> (\<langle>C\<rangle>\<langle>D\<rangle>?er))"
    using tot by converse_dl.dlc.dt_prop

  text \<open>Step 3: e = r is rigid for C and D, so the diamonds can be dropped.\<close>
  have dD: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>D\<rangle>?er) \<Rrightarrow> ?er"
    by (rule converse_dl.dlc.dt_diamond_V[OF eq_bv_disjoint[OF er eDb rDb]])
  have dC: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>?er) \<Rrightarrow> ?er"
    by (rule converse_dl.dlc.dt_diamond_V[OF eq_bv_disjoint[OF er eCb rCb]])
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>\<langle>D\<rangle>?er) \<Rrightarrow> (\<langle>C\<rangle>?er)"
    using dD by (rule converse_dl.dlc.c_dia_mono)
  then have s3: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<langle>C\<rangle>\<langle>D\<rangle>?er) \<Rrightarrow> ?er"
    using dC by converse_dl.dlc.dt_prop

  text \<open>Step 4: push e = r back under \<forall>G [C][D].\<close>
  have vD: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (\<lbrakk>D\<rbrakk>?er)"
    by (rule converse_dl.dlc.dyn_axiom_V[OF eq_bv_disjoint[OF er eDb rDb]])
  have vC: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (\<lbrakk>C\<rbrakk>?er)"
    by (rule converse_dl.dlc.dyn_axiom_V[OF eq_bv_disjoint[OF er eCb rCb]])
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>?er) \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er)"
    using vD by (rule converse_dl.dlc.dt_box_M)
  then have erCD: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er)"
    using vC by converse_dl.dlc.dt_prop
  have erG: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (\<bbbA> G . ?er)"
    apply (rule converse_dl.dlc.dyn_axiom_F2)
    using Ge Gr eqPred_fv_sem_only er by blast
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<bbbA> G . ?er) \<Rrightarrow> (\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er)"
    using erCD by (rule converse_dl.dlc.dt_fol_M)
  then have s4: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?er \<Rrightarrow> (\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er)"
    using erG by converse_dl.dlc.dt_prop

  text \<open>Step 5: transitivity under \<forall>G [C][D].\<close>
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] ?dr \<Rrightarrow> (?er \<Rrightarrow> ?de)"
    using eq2 by converse_dl.dlc.dt_prop
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> ((\<lbrakk>D\<rbrakk>?er) \<Rrightarrow> (\<lbrakk>D\<rbrakk>?de))"
    by (rule converse_dl.dlc.dt_box_K2)
  then have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?dr) \<Rrightarrow> ((\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er) \<Rrightarrow> (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?de))"
    by (rule converse_dl.dlc.dt_box_K2)
  then have s5: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI \<Rrightarrow> ((\<bbbA> G . \<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?er) \<Rrightarrow> ?B)"
    by (rule converse_dl.dlc.c_all_K2)

  have main: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?NI \<Rrightarrow> (?A \<Rrightarrow> ?B)"
    using s1 s2 s3 s4 s5 by converse_dl.dlc.dt_prop

  text \<open>Step 6: \<exists>-elimination on r (r is not free in A \<Rrightarrow> B).\<close>
  have r_free: "\<not> converse_dl.dlc.dyn_fv_sem (?A \<Rrightarrow> ?B) r"
  proof -
    have f0: "\<not> converse_dl.dlc.dyn_fv_sem ?de r"
      using de dr eqPred_fv_sem_only er by blast
    have f1: "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>D\<rbrakk>?de) r"
      using rDf f0 by (rule fv_box_free)
    have f2: "\<not> converse_dl.dlc.dyn_fv_sem (\<lbrakk>C\<rbrakk>\<lbrakk>D\<rbrakk>?de) r"
      using rCf f1 by (rule fv_box_free)
    have fA: "\<not> converse_dl.dlc.dyn_fv_sem ?A r"
      using rCf f1 by (rule fv_dia_free)
    have fB: "\<not> converse_dl.dlc.dyn_fv_sem ?B r"
      using f2 by (rule converse_dl.dlc.dyn_fv_sem_all_intro)
    show ?thesis
      using fA fB converse_dl.dlc.dyn_fv_sem_imp_elim by blast
  qed
  have rnf: "\<not> converse_dl.dlc.dyn_fv_sem (\<rceil>(?A \<Rrightarrow> ?B)) r"
    using r_free converse_dl.dlc.dyn_fv_sem_not_eq by metis
  have F2: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<rceil>(?A \<Rrightarrow> ?B)) \<Rrightarrow> (\<bbbA> r . \<rceil>(?A \<Rrightarrow> ?B))"
    using rnf by (rule converse_dl.dlc.dyn_axiom_F2)
  have "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<rceil>(?A \<Rrightarrow> ?B)) \<Rrightarrow> (\<rceil> ?NI)"
    using main by converse_dl.dlc.dt_prop
  then have M: "\<Turnstile>[converse_dl.dlc.dyn_eval] (\<bbbA> r . \<rceil>(?A \<Rrightarrow> ?B)) \<Rrightarrow> (\<bbbA> r . \<rceil> ?NI)"
    by (rule converse_dl.dlc.dt_fol_M)
  have fwd: "\<Turnstile>[converse_dl.dlc.dyn_eval] ?A \<Rrightarrow> ?B"
    using ni F2 M by converse_dl.dlc.dt_prop

  text \<open>Step 7: abduction via the converse adjunction.\<close>
  show ?thesis
    using fwd
    by (rule dt_l_converse)
qed
end
