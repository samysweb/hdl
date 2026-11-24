theory ConverseDynamicLogic
  imports
    Main
    "ExtensionalDynamicLogic"
    "DynamicLogicBV"
    "DynamicLogicProof"
begin

subsection\<open>Converse Lifting\<close>

datatype ('a,'vr,'pr) converse_prog  =
  CPROG "'pr"
  | CONVERSE "('a,'vr,'pr) converse_prog"

notation CONVERSE ("_\<^sup>-\<^sup>1" 30)

locale ConverseDynLog =
    EDL: extDynLogCore atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    +
    BVDL: dynamic_theory_bv atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV dyn_prog_BV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    and dyn_prog_BV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"

begin

sublocale original_dl : extDynLogCore atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
  by (simp add: EDL.extDynLogCore_axioms)

sublocale bv_dl : dynamic_theory_bv atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV dyn_prog_BV
  by (simp add: BVDL.dynamic_theory_bv_axioms)

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
      by (simp add: BVDL.dyn_prog_BV_overapprox)
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
      by (simp add: EDL.prog_fv_finite)
  next
    case (CONVERSE x)
    then show ?case
    proof (induct x)
      case (CPROG x)
      then show ?case
      unfolding full_prog_fv_syn.simps
      unfolding full_prog_bv_syn.simps
      by (simp add: BVDL.prog_bv_finite)
    next
      case (CONVERSE x)
      then show ?case
      unfolding full_prog_fv_syn.simps
      unfolding full_prog_bv_syn.simps
      by (simp add: BVDL.prog_bv_finite)
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
        using EDL.strong_extensionality by blast
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
       EDL.fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> EDL.fol_states_agree_on V \<nu> \<upsilon>) \<and>
        (EDL.fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v) \<nu> \<mu>)"
    subgoal for \<pi> V \<mu> \<omega> \<nu>
    proof (induct \<pi> arbitrary: V \<mu> \<omega> \<nu>)
      case (CPROG x)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        using EDL.prog_fv_overapprox
        apply (intro impI,intro conjI)
         apply blast
        by (metis (no_types, lifting) EDL.fol_states_agree_on_def
            full_prog_bv_syn_overapprox full_prog_eval.simps(1))
    next
      case (CONVERSE \<pi>)
      then show ?case
        unfolding full_prog_fv_syn.simps
        unfolding full_prog_eval.simps
        proof (intro impI,elim conjE,intro conjI)
          assume H_all: " \<forall>v. full_prog_fv_syn \<pi> v \<or> full_prog_bv_syn \<pi> v \<longrightarrow> V v"
          assume H_agree: "EDL.fol_states_agree_on V \<mu> \<omega>"
          assume H_run: "full_prog_eval \<pi> \<nu> \<mu>"

          have \<nu>_\<mu>_almost_agree: "EDL.fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v) \<nu> \<mu>"
            using H_run EDL.fol_states_agree_on_def full_prog_bv_syn_overapprox
            by blast

          have \<nu>_\<omega>_almost_agree: "EDL.fol_states_agree_on (\<lambda> v . \<not> full_prog_bv_syn \<pi> v \<and> V v) \<nu> \<omega>"
            using \<nu>_\<mu>_almost_agree H_agree
            unfolding EDL.fol_states_agree_on_def by presburger

          show "EDL.fol_states_agree_on (\<lambda>v. \<not> full_prog_bv_syn (\<pi>\<^sup>-\<^sup>1) v) \<nu> \<mu>"
            unfolding full_prog_bv_syn.simps
            using \<nu>_\<mu>_almost_agree by force

          have H_agree_fv: "EDL.fol_states_agree_on (full_prog_fv_syn \<pi>) \<mu> \<omega>"
            using H_all H_agree
            using EDL.fol_states_agree_on_def by force

          have H_agree_bv: "EDL.fol_states_agree_on (full_prog_bv_syn \<pi>) \<mu> \<omega>"
            using H_all H_agree
            using EDL.fol_states_agree_on_def by force

          obtain \<nu>' where \<upsilon>_def: "\<And> v . (
            (full_prog_bv_syn \<pi> v \<longrightarrow> (state_eval \<nu>' v = state_eval \<nu> v)) \<and>
            (\<not>(full_prog_bv_syn \<pi> v) \<longrightarrow> (state_eval \<nu>' v = state_eval \<omega> v))
            )"
            using EDL.state_space_convexity
            by (metis mem_Collect_eq)

          have uvf_def: "\<forall>v. state_eval \<nu>' v = (if full_prog_bv_syn \<pi> v then state_eval \<nu> v else state_eval \<omega> v)"
            using \<upsilon>_def by (simp add: \<upsilon>_def)

          (*have "fol_states_agree_on (\<lambda> v . ((V v) \<and> \<not>(full_prog_bv_syn \<pi> v))) \<nu> \<omega>"
            using H_agree H_run
            unfolding fol_states_agree_on_def
            using full_prog_bv_syn_overapprox[of \<pi>]
            by metis*)

          have \<upsilon>_\<nu>_agree: "EDL.fol_states_agree_on V \<nu>' \<nu>"
            using uvf_def H_agree H_run
            unfolding EDL.fol_states_agree_on_def
            using full_prog_bv_syn_overapprox[of \<pi>]
            by metis

          obtain \<mu>' where \<upsilon>2_cond: "full_prog_eval \<pi> \<nu>' \<mu>' \<and> EDL.fol_states_agree_on V \<mu> \<mu>'"
            using CONVERSE.hyps[of V \<nu> \<nu>' \<mu>]
            using H_run \<upsilon>_\<nu>_agree H_all
            using EDL.fol_states_agree_on_def by auto

          have "EDL.fol_states_agree_on (\<lambda> v . True) \<mu>' \<omega>"
            using H_agree \<upsilon>2_cond
            using EDL.fol_states_agree_on_def
            by (metis H_all full_prog_bv_syn_overapprox uvf_def)

          

          then have "full_prog_eval \<pi> \<nu>' \<omega>"
            using strongExt[of \<nu>' \<nu>' \<mu>' \<omega> \<pi>]
            unfolding EDL.fol_states_agree_on_def
            using \<upsilon>2_cond by blast

          then show "\<exists>\<upsilon>. full_prog_eval \<pi> \<upsilon> \<omega> \<and> EDL.fol_states_agree_on V \<nu> \<upsilon>"
            using \<upsilon>_\<nu>_agree
            using EDL.fol_states_agree_on_def by force
      qed
    qed.
  then show "\<And>\<pi> V \<mu> \<omega> \<nu>.
       (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       EDL.fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> EDL.fol_states_agree_on V \<nu> \<upsilon>)"
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

fun translate :: "('atom, 'var, 'prog) dyn_formula \<Rightarrow>('atom, 'var, ('atom, 'var, 'prog) converse_prog) dyn_formula"
  where
      "translate (FOL \<phi>) = (FOL \<phi>)"
    | "translate (\<phi> and \<psi>) = ((translate \<phi>) and (translate \<psi>))"
    | "translate (\<rceil> \<phi>) = (\<rceil> (translate \<phi>))"
    | "translate (\<bbbA> v . \<phi>) = (\<bbbA> v . (translate \<phi>))"
    | "translate (\<lbrakk>\<alpha>\<rbrakk>\<phi>) = (\<lbrakk>(CPROG \<alpha>)\<rbrakk> (translate \<phi>))"

lemma dyn_axiom_CR:
  assumes "\<Turnstile>[EDL.dlc.dyn_eval] \<phi>"
  shows "\<Turnstile>[converse_dl.dlc.dyn_eval] (translate \<phi>)"
  using assms
proof -
  fix \<phi>
  have "\<And> \<mu> . ((EDL.dlc.dyn_eval \<phi> \<mu>) = (converse_dl.dlc.dyn_eval (translate \<phi>) \<mu>))"
  proof (induct \<phi>)
    case (FOL x)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding converse_dl.dlc.dyn_eval.simps
      unfolding EDL.dlc.dyn_eval.simps
      by simp
  next
    case (AND \<phi>1 \<phi>2)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding converse_dl.dlc.dyn_eval.simps
      unfolding EDL.dlc.dyn_eval.simps
      by blast
  next
    case (NOT \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding converse_dl.dlc.dyn_eval.simps
      unfolding EDL.dlc.dyn_eval.simps
      by blast
  next
    case (FOL_ALL x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding converse_dl.dlc.dyn_eval.simps
      unfolding EDL.dlc.dyn_eval.simps
      by blast
  next
    case (BOX x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding converse_dl.dlc.dyn_eval.simps
      unfolding EDL.dlc.dyn_eval.simps
      unfolding full_prog_eval.simps
      by blast
  qed
  thus "\<Turnstile>[EDL.dlc.dyn_eval] \<phi> \<Longrightarrow> \<Turnstile>[converse_dl.dlc.dyn_eval] translate \<phi>"
    unfolding theory_valid_def
    by blast
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
end

