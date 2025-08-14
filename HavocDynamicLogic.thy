theory HavocDynamicLogic
  imports
    Main
    "DynamicLogic"
begin

datatype ('a,'vr,'pr) havoc_prog  =
  HPROG "'pr"
  | HAVOC "'vr"

notation HAVOC ("_:=*" 20)

locale HavocDynLog =
    dynLog atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
begin

fun full_prog_eval :: "('atom,'var,'prog) havoc_prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where
    "full_prog_eval (HPROG \<pi>) \<mu> \<omega> = prog_eval \<pi> \<mu> \<omega>"
  | "full_prog_eval (HAVOC v) \<mu> \<omega> = fol_equal_everywhere_but v \<mu> \<omega>"


fun full_prog_FV :: "('atom,'var,'prog) havoc_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_prog_FV (HPROG \<pi>) v = dyn_prog_FV \<pi> v"
  | "full_prog_FV (HAVOC v) w = False"

fun full_prog_BV :: "('prog \<Rightarrow> 'var \<Rightarrow> bool) \<Rightarrow> ('atom,'var,'prog) havoc_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_prog_BV BV (HPROG \<pi>) v = BV \<pi> v"
  | "full_prog_BV BV (HAVOC v) w = (v=w)"

sublocale havoc_dl : dynLog
    atom_eval atom_fv_syn state_eval full_prog_eval full_prog_FV
proof
  have dynLogCore_instantiated: "dynLogCore atom_eval atom_fv_syn state_eval full_prog_eval full_prog_FV"
  proof 
    show "\<And>\<pi>. finite (Collect (full_prog_FV \<pi>))"
    proof -
      fix \<pi>
      show "finite (Collect (full_prog_FV \<pi>))"
      proof (induct \<pi>)
        case (HPROG x)
        then show ?case
          using prog_fv_finite by simp
      next
        case (HAVOC x)
        then show ?case
          unfolding full_prog_FV.simps
          by simp
      qed
    qed
    show "\<And>\<pi> V \<mu> \<omega> \<nu>.
           (\<forall>v. full_prog_FV \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
           (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
    proof -
      fix \<pi>
      show "\<And>V \<mu> \<omega> \<nu>.
         (\<forall>v. full_prog_FV \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
      proof (induct \<pi>)
        case (HPROG x)
        then show ?case
          using prog_fv_overapprox by force
      next
        case (HAVOC x)
        then show ?case
          unfolding full_prog_eval.simps(2)
          unfolding full_prog_FV.simps(2)
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
        proof 
          assume havoc_assms: "(\<forall>v. False \<longrightarrow> V v) \<and>
            (\<forall>v. V v \<longrightarrow> state_eval \<mu> v = state_eval \<omega> v) \<and> (\<forall>v. v \<noteq> x \<longrightarrow> state_eval \<mu> v = state_eval \<nu> v)"
        obtain \<nu>1 where \<nu>1_cond: "(state_eval \<nu>1) x = (state_eval \<nu>) x \<and> fol_equal_everywhere_but x \<nu>1 \<omega>"
          using state_space_convexity
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by (meson singleton_iff)
        show "\<exists>\<upsilon>. (\<forall>v. v \<noteq> x \<longrightarrow> state_eval \<omega> v = state_eval \<upsilon> v) \<and> (\<forall>v. V v \<longrightarrow> state_eval \<nu> v = state_eval \<upsilon> v)"
          using \<nu>1_cond
          apply (intro exI[where x="\<nu>1"],intro conjI)
          using fol_equal_everywhere_but_def fol_states_agree_on_def apply force
          using havoc_assms
          unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
          by metis
      qed
    qed
  qed
  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
  proof (intro allI)
    fix \<pi> \<mu> \<omega>
    show "(\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
    proof (induct \<pi>)
      case (HPROG x)
      then show ?case
        using full_prog_eval.simps(1) prog_var_determinance by presburger
    next
      case (HAVOC x)
      then show ?case
        unfolding full_prog_eval.simps
        unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
        by simp
    qed
  qed
qed

  show "\<And>\<pi>. finite (Collect (full_prog_FV \<pi>))"
    using dynLogCore_instantiated
    by (simp add: dynLogCore.prog_fv_finite)

  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
           (\<forall>v. full_prog_FV \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
           (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
    using dynLogCore_instantiated
    using dynLogCore.prog_fv_overapprox
    by (smt (verit, ccfv_threshold))
  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
    using dynLogCore_instantiated
    using dynLogCore.prog_var_determinance
    by blast
qed

lemma BV_overapprox:
  assumes "\<And> \<pi> v . dyn_prog_bv_sem \<pi> v \<Longrightarrow> BV \<pi> v"
  shows "havoc_dl.dyn_prog_bv_sem \<pi> v \<Longrightarrow> full_prog_BV BV \<pi> v"
proof (induct \<pi>)
  case (HPROG x)
  then show ?case
    by (simp add: assms)
next
  case (HAVOC x)
  then show ?case
    unfolding havoc_dl.dyn_prog_bv_sem.simps
    unfolding full_prog_eval.simps
    unfolding full_prog_BV.simps
    unfolding fol_equal_everywhere_but_def
    unfolding fol_states_agree_on_def
    by auto
qed

lemma dyn_axiom_havoc:
  fixes v :: "'var"
    and \<psi> :: "('atom,'var,('atom,'var,'prog) havoc_prog) dyn_formula"
  shows "\<Turnstile>[havoc_dl.dyn_eval] (\<lbrakk>(v:=*)\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<bbbA> v . \<phi>)"
proof -
  have dir1: "\<Turnstile>[havoc_dl.dyn_eval] (\<lbrakk>(v:=*)\<rbrakk>\<phi>) \<Rrightarrow> (\<bbbA> v . \<phi>)"
    unfolding havoc_dl.IMP_def
    unfolding theory_valid_def
    unfolding havoc_dl.dyn_eval.simps
    unfolding full_prog_eval.simps
    by blast

  have dir2: "\<Turnstile>[havoc_dl.dyn_eval] (\<bbbA> v . \<phi>) \<Rrightarrow> (\<lbrakk>(v:=*)\<rbrakk>\<phi>)"
    unfolding havoc_dl.IMP_def
    unfolding theory_valid_def
    unfolding havoc_dl.dyn_eval.simps
    unfolding full_prog_eval.simps
    by blast

  show ?thesis
    using dir1 dir2
    by simp
qed

fun translate :: "('atom, 'var, 'prog) dyn_formula \<Rightarrow>('atom, 'var, ('atom, 'var, 'prog) havoc_prog) dyn_formula"
  where
      "translate (FOL \<phi>) = (FOL \<phi>)"
    | "translate (\<phi> and \<psi>) = ((translate \<phi>) and (translate \<psi>))"
    | "translate (\<rceil> \<phi>) = (\<rceil> (translate \<phi>))"
    | "translate (\<bbbA> v . \<phi>) = (\<bbbA> v . (translate \<phi>))"
    | "translate (\<lbrakk>\<alpha>\<rbrakk>\<phi>) = (\<lbrakk>(HPROG \<alpha>)\<rbrakk> (translate \<phi>))"

lemma dyn_axiom_HR:
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[havoc_dl.dyn_eval] (translate \<phi>)"
  using assms
proof -
  fix \<phi>
  have "\<And> \<mu> . ((dyn_eval \<phi> \<mu>) = (havoc_dl.dyn_eval (translate \<phi>) \<mu>))"
  proof (induct \<phi>)
    case (FOL x)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding havoc_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by simp
  next
    case (AND \<phi>1 \<phi>2)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding havoc_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (NOT \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding havoc_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (FOL_ALL x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding havoc_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (BOX x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding havoc_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      unfolding full_prog_eval.simps
      by blast
  qed
  thus "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> \<Turnstile>[havoc_dl.dyn_eval] translate \<phi>"
    unfolding theory_valid_def
    by blast
qed
end


end