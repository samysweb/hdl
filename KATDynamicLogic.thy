theory KATDynamicLogic
  imports
    Main
    "DynamicLogic"
begin

datatype ('a,'vr,'pr) kat_prog  =
  KATPROG "'pr"
  | CHECK "('a,'vr) fol_formula"
  | SEQ "('a,'vr,'pr) kat_prog" "('a,'vr,'pr) kat_prog"
  | CHOICE "('a,'vr,'pr) kat_prog" "('a,'vr,'pr) kat_prog"
  | LOOP "('a,'vr,'pr) kat_prog"

notation CHECK ("? _" 30)
notation SEQ ("_;_" 40)
notation CHOICE ("_\<squnion>_" 50)
notation LOOP ("(_)*" 60)

locale KATDynLog =
    dynLog atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
begin

fun full_prog_eval_int :: "nat \<Rightarrow> ('atom,'var,'prog) kat_prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where
    "full_prog_eval_int n (KATPROG \<pi>) \<mu> \<omega> = prog_eval \<pi> \<mu> \<omega>"
  | "full_prog_eval_int n (CHECK \<phi>) \<mu> \<omega> = (dyn_eval (FOL \<phi>) \<mu> \<and> (state_eval \<mu> = state_eval \<omega>))"
  | "full_prog_eval_int n (SEQ \<pi>1 \<pi>2) \<mu> \<omega> = (\<exists> \<nu> . ( full_prog_eval_int n \<pi>1 \<mu> \<nu> \<and> full_prog_eval_int n \<pi>2 \<nu> \<omega> ) )"
  | "full_prog_eval_int n (CHOICE \<pi>1 \<pi>2) \<mu> \<omega> = (full_prog_eval_int n \<pi>1 \<mu> \<omega> \<or> full_prog_eval_int n \<pi>2 \<mu> \<omega>)"
  | "full_prog_eval_int n (LOOP \<pi>) \<mu> \<omega> = (if n>0 then ((state_eval \<mu> = state_eval \<omega>) \<or> (full_prog_eval_int (n-1) (SEQ \<pi> (LOOP \<pi>)) \<mu> \<omega>)  \<or> (full_prog_eval_int (n-1) (LOOP \<pi>) \<mu> \<omega>)) else False)"

lemma full_prog_eval_int_n_one_monotone:
  "\<And> n1 n2 \<mu>1 \<omega>1 n2 . full_prog_eval_int n1 \<pi>1 \<mu>1 \<omega>1 \<Longrightarrow> n2=(n1+1) \<Longrightarrow> full_prog_eval_int n2 \<pi>1 \<mu>1 \<omega>1"
proof (induct \<pi>1)
  case (KATPROG x)
  then show ?case
    unfolding full_prog_eval_int.simps
    by auto
next
  case (CHECK x)
  then show ?case
    unfolding full_prog_eval_int.simps
    by auto
next
  case (SEQ \<pi>11 \<pi>12)
  then show ?case
    unfolding full_prog_eval_int.simps
    by blast
next
  case (CHOICE \<pi>11 \<pi>12)
  then show ?case
    unfolding full_prog_eval_int.simps
    by blast
next
  case (LOOP \<pi>1)
  then show ?case
    using full_prog_eval_int.simps(5)
  proof (cases "0 < n1")
    case True
    have "(state_eval \<mu>1 = state_eval \<omega>1) \<or> full_prog_eval_int (n1 - 1) (SEQ \<pi>1 (LOOP \<pi>1)) \<mu>1 \<omega>1 \<or> full_prog_eval_int (n1 - 1) (LOOP \<pi>1) \<mu>1 \<omega>1"
      by (meson LOOP.prems(1) full_prog_eval_int.simps(5))
    have "0<n2"
      using LOOP.prems(2)
      by auto
    then show "full_prog_eval_int n2 (LOOP \<pi>1) \<mu>1 \<omega>1"
      using full_prog_eval_int.simps(5)[of n2 \<pi>1 \<mu>1 \<omega>1]
      using LOOP.prems(1) LOOP.prems(2) by force
  next
    case False
    assume assm1:  "full_prog_eval_int n1 (LOOP \<pi>1) \<mu>1 \<omega>1"
    assume assm2: "n2 = n1 + 1"
    have "0\<ge>n1"
      using assm2 False by force
    then have "False"
      using assm1 by simp
    then show "full_prog_eval_int n2 (LOOP \<pi>1) \<mu>1 \<omega>1"
      by auto
  qed
qed
lemma full_prog_eval_int_n_monotone:
  assumes eval_for_some_n: "full_prog_eval_int n1 \<pi>1 \<mu>1 \<omega>1"
      and n2_larger: "n2\<ge>n1"
    shows "full_prog_eval_int n2 \<pi>1 \<mu>1 \<omega>1"
proof -
  have "n2 \<ge> n1"
    using n2_larger
    by simp

  then show ?thesis
  proof (induct n2 rule: nat_induct_at_least[of n1])
    case base
    then show ?case
      using eval_for_some_n
      by simp
  next
    case (Suc n)
    then show ?case
      using full_prog_eval_int_n_one_monotone
      by simp
  qed
qed
lemma full_prog_eval_int_n_combinable:
  assumes \<pi>1_assm: "full_prog_eval_int n1 \<pi>1 \<mu>1 \<omega>1"
      and \<pi>2_assm: "full_prog_eval_int n2 \<pi>2 \<mu>2 \<omega>2"
    shows "\<exists> n . (full_prog_eval_int n \<pi>1 \<mu>1 \<omega>1 \<and> full_prog_eval_int n \<pi>1 \<mu>1 \<omega>1)"
  apply (rule exI[where x="(max n1 n2)"])
  using \<pi>1_assm \<pi>2_assm
  using full_prog_eval_int_n_monotone[of n1 \<pi>1 \<mu>1 \<omega>1 "(max n1 n2)"] 
  using full_prog_eval_int_n_monotone[of n2 \<pi>2 \<mu>2 \<omega>2 "(max n1 n2)"] 
  by simp

definition full_prog_eval :: "('atom,'var,'prog) kat_prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where "full_prog_eval \<pi> \<mu> \<omega> = (\<exists> n . (full_prog_eval_int n \<pi> \<mu> \<omega>))"

fun full_prog_fv_syn :: "('atom,'var,'prog) kat_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_prog_fv_syn (KATPROG \<pi>) v = dyn_prog_FV \<pi> v"
  | "full_prog_fv_syn (CHECK \<phi>) v = fol_fv_syn \<phi> v"
  | "full_prog_fv_syn (SEQ \<pi>1 \<pi>2) v = ((full_prog_fv_syn \<pi>1 v) \<or> (full_prog_fv_syn \<pi>2 v))"
  | "full_prog_fv_syn (CHOICE \<pi>1 \<pi>2) v = ((full_prog_fv_syn \<pi>1 v) \<or> (full_prog_fv_syn \<pi>2 v))"
  | "full_prog_fv_syn (LOOP \<pi>) v = (full_prog_fv_syn \<pi> v)"

(*
fun full_dyn_FV_prog :: "('atom,'var,'prog) kat_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_dyn_FV_prog (KATPROG \<pi>) v = dyn_prog_FV \<pi> v"
  | "full_dyn_FV_prog (CHECK \<phi>) v = dyn_FV  (FOL \<phi>) v"
  | "full_dyn_FV_prog (SEQ \<pi>1 \<pi>2) v =((full_dyn_FV_prog \<pi>1 v) \<or> (full_dyn_FV_prog \<pi>2 v))"
  | "full_dyn_FV_prog (CHOICE \<pi>1 \<pi>2) v =((full_dyn_FV_prog \<pi>1 v) \<or> (full_dyn_FV_prog \<pi>2 v))"
  | "full_dyn_FV_prog (LOOP \<pi>) v =(full_dyn_FV_prog \<pi> v)"
*)

fun full_dyn_FV_fml :: "('atom,'var,('atom, 'var, 'prog) kat_prog) dyn_formula \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_dyn_FV_fml (FOL \<phi>) v = dyn_FV (FOL \<phi>) v"
  | "full_dyn_FV_fml (AND \<phi> \<psi>) v = ((full_dyn_FV_fml \<phi> v) \<or> (full_dyn_FV_fml \<psi> v))"
  | "full_dyn_FV_fml (NOT \<phi>) v = (full_dyn_FV_fml \<phi> v)"
  | "full_dyn_FV_fml (FOL_ALL v \<phi>) w = (if (v=w) then False else (full_dyn_FV_fml \<phi> v))"
  | "full_dyn_FV_fml (BOX \<pi> \<phi>) v = ((full_prog_fv_syn \<pi> v) \<or> (full_dyn_FV_fml \<phi> v))"

fun full_dyn_prog_BV :: " ('prog \<Rightarrow> 'var \<Rightarrow> bool) \<Rightarrow>('atom,'var,'prog) kat_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where
    "full_dyn_prog_BV BV (KATPROG \<pi>) v = BV \<pi> v"
  | "full_dyn_prog_BV BV (CHECK \<phi>) v = False"
  | "full_dyn_prog_BV BV (SEQ \<pi>1 \<pi>2) v =((full_dyn_prog_BV BV \<pi>1 v) \<or> (full_dyn_prog_BV BV \<pi>2 v))"
  | "full_dyn_prog_BV BV (CHOICE \<pi>1 \<pi>2) v =((full_dyn_prog_BV BV \<pi>1 v) \<or> (full_dyn_prog_BV BV \<pi>2 v))"
  | "full_dyn_prog_BV BV (LOOP \<pi>) v =(full_dyn_prog_BV BV \<pi> v)"

lemma full_prog_var_determinance_n:
 "\<forall> n \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval_int n \<pi> \<mu> = full_prog_eval_int n \<pi> \<omega>"
  proof (induct \<pi>)
    case (KATPROG x)
    then show ?case
      using prog_var_determinance
      unfolding full_prog_eval_def full_prog_eval_int.simps
      by presburger
  next
    case (CHECK x)
    then show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
      unfolding dyn_eval.simps
    proof (intro allI,intro impI)
      fix \<mu> \<omega>
      assume "(\<forall>v. state_eval \<mu> v = state_eval \<omega> v)"
  
      thus "(\<lambda>a. fol_eval x \<mu> \<and> state_eval \<mu> = state_eval a) =
            (\<lambda>a. fol_eval x \<omega> \<and> state_eval \<omega> = state_eval a) "
        using fol_fv_sem_coincidence[of x \<mu> \<omega>]
        unfolding fol_states_agree_on_def
        by presburger
    qed        
  next
    case (SEQ \<pi>1 \<pi>2)
    then show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
      by (meson full_prog_eval_int_n_monotone nle_le)
  next
    case (CHOICE \<pi>1 \<pi>2)
    then show ?case
      unfolding full_prog_eval_def full_prog_eval_int.simps
      by (meson full_prog_eval_int_n_monotone nle_le)
  next
    case (LOOP \<pi>)
    then show ?case
      unfolding full_prog_eval_def
    proof (intro allI, intro impI)
      fix \<mu> \<omega>
      assume outer_ind_hyp: "\<forall>n \<mu> \<omega>.
        (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval_int n \<pi> \<mu> = full_prog_eval_int n \<pi> \<omega>"
      have "\<forall> n \<mu> \<omega> a . (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow>full_prog_eval_int n (\<pi>*) \<mu> a \<longleftrightarrow> full_prog_eval_int n (\<pi>*) \<omega> a"
      proof (rule allI)
        fix n
        show "\<forall> \<mu> \<omega> a. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval_int n (\<pi>*) \<mu> a \<longleftrightarrow> full_prog_eval_int n (\<pi>*) \<omega> a"
        proof (induct n)
          case 0
          then show ?case
            unfolding full_prog_eval_int.simps(5)[of 0]
            by simp
        next
          case (Suc n)
          then show ?case
          proof (intro allI, intro impI)
            fix \<mu> \<omega> a
            assume inner_ind_assm: "\<forall>\<mu> \<omega> a.
                   (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow>
                   full_prog_eval_int n (\<pi>*) \<mu> a = full_prog_eval_int n (\<pi>*) \<omega> a"
            assume "\<forall>v. state_eval \<mu> v = state_eval \<omega> v"
            then have eval_eq: "state_eval \<mu> = state_eval \<omega>"
              by blast
  
            have "(state_eval \<mu> = state_eval a \<or>
                   full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<or> 
                    full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a) = 
                  (state_eval \<omega> = state_eval a \<or>
                    full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a)"
            proof (standard,elim disjE)
              show "state_eval \<mu> = state_eval a \<Longrightarrow>
                      state_eval \<omega> = state_eval a \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a"
                using eval_eq
                by presburger
              show "full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<Longrightarrow>
                      state_eval \<omega> = state_eval a \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a"
                unfolding full_prog_eval_int.simps(3)
              proof -
                assume "\<exists>\<nu>. full_prog_eval_int (Suc n - 1) \<pi> \<mu> \<nu> \<and> full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                then obtain \<nu> where \<nu>_cond1: "full_prog_eval_int (Suc n - 1) \<pi> \<mu> \<nu>"
                                and \<nu>_cond2: "full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                  by blast
                have part1: "full_prog_eval_int (Suc n - 1) \<pi> \<omega> \<nu>"
                  using \<nu>_cond1 outer_ind_hyp eval_eq
                  by metis
                have part2: "full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                  using inner_ind_assm \<nu>_cond2
                  by metis
                show "state_eval \<omega> = state_eval a \<or>
                      (\<exists>\<nu>. full_prog_eval_int (Suc n - 1) \<pi> \<omega> \<nu> \<and> full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a) \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a"
                  using part1 part2 by blast
              qed
            show "full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a \<Longrightarrow>
                    state_eval \<omega> = state_eval a \<or>
                    full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a"
              using inner_ind_assm
              using eval_eq
            by (metis diff_Suc_1)
          show "state_eval \<omega> = state_eval a \<or>
                full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a \<Longrightarrow>
                state_eval \<mu> = state_eval a \<or>
                full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a"
          proof (elim disjE)
            show "state_eval \<omega> = state_eval a \<Longrightarrow>
                    state_eval \<mu> = state_eval a \<or>
                    full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a"
              using eval_eq
              by presburger
            show "full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<omega> a \<Longrightarrow>
                    state_eval \<mu> = state_eval a \<or>
                    full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a"
              unfolding full_prog_eval_int.simps(3)
              proof -
                assume "\<exists>\<nu>. full_prog_eval_int (Suc n - 1) \<pi> \<omega> \<nu> \<and> full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                then obtain \<nu> where \<nu>_cond1: "full_prog_eval_int (Suc n - 1) \<pi> \<omega> \<nu>"
                                and \<nu>_cond2: "full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                  by blast
                have part1: "full_prog_eval_int (Suc n - 1) \<pi> \<mu> \<nu>"
                  using \<nu>_cond1 outer_ind_hyp eval_eq
                  by metis
                have part2: "full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a"
                  using inner_ind_assm \<nu>_cond2
                  by metis
                show "state_eval \<mu> = state_eval a \<or>
                      (\<exists>\<nu>. full_prog_eval_int (Suc n - 1) \<pi> \<mu> \<nu> \<and> full_prog_eval_int (Suc n - 1) (\<pi>*) \<nu> a) \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a"
                  using part1 part2 by blast
              qed
              show "full_prog_eval_int (Suc n - 1) (\<pi>*) \<omega> a \<Longrightarrow>
                      state_eval \<mu> = state_eval a \<or>
                      full_prog_eval_int (Suc n - 1) (\<pi>;(\<pi>*)) \<mu> a \<or> full_prog_eval_int (Suc n - 1) (\<pi>*) \<mu> a"
              using inner_ind_assm
              using eval_eq
            by (metis diff_Suc_1)
        qed
      qed
            thus "\<forall>v. state_eval \<mu> v = state_eval \<omega> v \<Longrightarrow>
                    full_prog_eval_int (Suc n) (\<pi>*) \<mu> a = full_prog_eval_int (Suc n) (\<pi>*) \<omega> a"
              by auto
          qed
        qed
      qed
      thus "\<And>n \<mu> \<omega>.
       \<forall>n \<mu> \<omega>.
          (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval_int n \<pi> \<mu> = full_prog_eval_int n \<pi> \<omega> \<Longrightarrow>
       \<forall>n \<mu> \<omega>.
          (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval_int n \<pi> \<mu> = full_prog_eval_int n \<pi> \<omega> \<Longrightarrow>
       \<forall>v. state_eval \<mu> v = state_eval \<omega> v \<Longrightarrow> full_prog_eval_int n (\<pi>*) \<mu> = full_prog_eval_int n (\<pi>*) \<omega>"
        by blast
    qed
  qed

sublocale kat_dl : dynLog
  "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"
proof

  have dynLogCore_instantiated: "dynLogCore atom_eval atom_fv_syn state_eval full_prog_eval full_prog_fv_syn"
    proof
    show "\<And>\<pi>. finite (Collect (full_prog_fv_syn \<pi>))"
    proof -
      fix \<pi>
      show "finite (Collect (full_prog_fv_syn \<pi>))"
      proof (induct \<pi>)
        case (KATPROG x)
        then show ?case
          using prog_fv_finite
          by simp
      next
        case (CHECK x)
        then show ?case
          using fol_fv_syn_finite
          by simp
      next
        case (SEQ \<pi>1 \<pi>2)
        then show ?case
          by auto
      next
        case (CHOICE \<pi>1 \<pi>2)
        then show ?case
          by auto
      next
        case (LOOP \<pi>)
        then show ?case 
          by auto
      qed
    qed
    have "\<And>\<pi> V n \<mu> \<omega> \<nu>.
         (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int n \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. full_prog_eval_int n \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
    proof -
      fix \<pi> V
      show "\<And>n \<mu> \<omega> \<nu> . (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int n \<pi> \<mu> \<nu> \<longrightarrow>
            (\<exists>\<upsilon>. full_prog_eval_int n \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
      proof (induct \<pi>)
        case (KATPROG x)
        then show ?case
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps
          using prog_fv_overapprox
          by simp
      next
        case (CHECK x)
        then show ?case
          unfolding full_prog_fv_syn.simps
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps
          unfolding dyn_eval.simps
          unfolding fol_states_agree_on_def
          by (simp,metis (mono_tags, lifting) fol_fv_syn_coincidence fol_fv_syn_mirror_state_def fol_states_agree_on_def)
      next
        case (SEQ \<pi>1 \<pi>2)
        then show ?case 
          unfolding full_prog_fv_syn.simps(4)
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps(4)
        proof (simp,intro impI)
          assume cur_assm:
            "(\<forall>v. (full_prog_fv_syn \<pi>1 v \<longrightarrow> V v) \<and> (full_prog_fv_syn \<pi>2 v \<longrightarrow> V v)) \<and>
              fol_states_agree_on V \<mu> \<omega> \<and> (\<exists> \<nu>'. full_prog_eval_int n \<pi>1 \<mu> \<nu>' \<and> full_prog_eval_int n \<pi>2 \<nu>' \<nu>)"
          assume \<pi>1_assm:
            "(\<And>\<mu> \<omega> n \<nu>.
              (\<forall>v. full_prog_fv_syn \<pi>1 v \<longrightarrow> V v) \<and>
              fol_states_agree_on V \<mu> \<omega> \<and> (full_prog_eval_int n \<pi>1 \<mu> \<nu>) \<longrightarrow>
              (\<exists>\<upsilon>. full_prog_eval_int n \<pi>1 \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>))"
          assume \<pi>2_assm:
            "(\<And>\<mu> \<omega> n \<nu>.
              (\<forall>v. full_prog_fv_syn \<pi>2 v \<longrightarrow> V v) \<and>
              fol_states_agree_on V \<mu> \<omega> \<and> (full_prog_eval_int n \<pi>2 \<mu> \<nu>) \<longrightarrow>
              (\<exists>\<upsilon>. full_prog_eval_int n \<pi>2 \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>))"
  
          obtain inter_state
            where interm_for_\<pi>1: "full_prog_eval_int n \<pi>1 \<mu> inter_state"
              and interm_for_\<pi>2: "full_prog_eval_int n \<pi>2 inter_state \<nu>"
            using cur_assm
            by blast
  
          obtain par_inter_state
            where par_inter_state_cond: "(full_prog_eval_int n \<pi>1 \<omega> par_inter_state) \<and> fol_states_agree_on V inter_state par_inter_state"
            using interm_for_\<pi>1
            using cur_assm
            using \<pi>1_assm[of \<mu> \<omega> n inter_state]
            by blast
  
          then obtain par_fin_state
            where par_fin_state_cond: "(full_prog_eval_int n \<pi>2 par_inter_state par_fin_state) \<and> fol_states_agree_on V \<nu> par_fin_state"
            using cur_assm
            using interm_for_\<pi>2
            using \<pi>2_assm[of inter_state par_inter_state n \<nu>]
            by blast
  
          
  
          show "\<exists>\<upsilon>. (\<exists> \<nu>. full_prog_eval_int n \<pi>1 \<omega> \<nu> \<and> full_prog_eval_int n \<pi>2 \<nu> \<upsilon>) \<and> fol_states_agree_on V \<nu> \<upsilon>"
          proof (rule exI[where x=par_fin_state])
            have "(full_prog_eval_int n \<pi>1 \<omega> par_inter_state \<and> full_prog_eval_int n \<pi>2 par_inter_state par_fin_state) \<and>
                  fol_states_agree_on V \<nu> par_fin_state"
              using par_fin_state_cond par_inter_state_cond
              using full_prog_eval_int_n_combinable
              by (meson full_prog_eval_int_n_monotone nat_le_linear)
              
            thus"(\<exists>\<nu>. full_prog_eval_int n \<pi>1 \<omega> \<nu> \<and> full_prog_eval_int n \<pi>2 \<nu> par_fin_state) \<and>
                  fol_states_agree_on V \<nu> par_fin_state"
              by blast
          qed
        qed
      next
        case (CHOICE \<pi>1 \<pi>2)
        then show ?case
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps(4)
          unfolding full_prog_fv_syn.simps(4)
          by blast
      next
        case (LOOP \<pi>)
        then show ?case
        proof (intro impI)
          assume inductive_hyp: "(\<And>\<mu> \<omega> n \<nu>.
        (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int n \<pi> \<mu> \<nu> \<longrightarrow>
        (\<exists>\<upsilon>. full_prog_eval_int n \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>))"
          assume imp_assms: "(\<forall>v. full_prog_fv_syn (LOOP \<pi>) v \<longrightarrow> V v) \<and>
                              fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int n (LOOP \<pi>) \<mu> \<nu>"
          have "(\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v)"
            using imp_assms
            unfolding full_prog_fv_syn.simps
            by auto

          then have "n \<ge> 1"
            using imp_assms
            unfolding full_prog_eval_def
            using full_prog_eval_int.simps(5)[of n "(LOOP \<pi>)" \<mu> \<nu>]
            using linorder_not_le by force
            

          then have "\<And>\<mu> \<omega> \<nu>.
            (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int n (LOOP \<pi>) \<mu> \<nu> \<Longrightarrow>
            (\<exists>\<upsilon>. full_prog_eval_int n (LOOP \<pi>) \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
          proof (induct n rule: nat_induct_at_least[of 1])
            case base
            then show ?case
              unfolding full_prog_eval_int.simps(5)[of 1]
              unfolding full_prog_eval_int.simps(5)[of "(1-1)"]
              using fol_states_agree_on_def by auto
          next
            case (Suc N)
            then show ?case
            proof -
              assume suc_ind_hyp: "(\<And>\<mu> \<omega> \<nu>.
                      (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
                      fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int N (LOOP \<pi>) \<mu> \<nu> \<Longrightarrow>
                      \<exists>\<upsilon>. full_prog_eval_int N (LOOP \<pi>) \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
              assume "(\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int (Suc N) (LOOP \<pi>) \<mu> \<nu>"
              then have three_possible_cases: "(state_eval \<mu> = state_eval \<omega>) \<or> full_prog_eval_int (Suc N - 1) (SEQ \<pi> (LOOP \<pi>)) \<mu> \<nu> \<or> full_prog_eval_int (Suc N - 1) (LOOP \<pi>) \<mu> \<nu>"
                unfolding full_prog_eval_int.simps(5)[of "(Suc N)"]
                by (meson KATDynLog.full_prog_eval_int.simps(5) KATDynLog_axioms Suc.hyps(1) le_imp_less_Suc zero_less_diff)
              
              then show "\<exists>\<upsilon>. full_prog_eval_int (Suc N) (LOOP \<pi>) \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>"
                unfolding full_prog_eval_int.simps(5)[of "(Suc N)"]
              proof (cases "state_eval \<mu> = state_eval \<nu>")
                case True
                then show "\<exists>\<upsilon>. (if 0 < Suc N
                               then (state_eval \<omega> = state_eval \<upsilon>) \<or>
                                    full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<omega> \<upsilon> \<or> full_prog_eval_int (Suc N - 1) (\<pi>*) \<omega> \<upsilon>
                               else False) \<and>
                              fol_states_agree_on V \<nu> \<upsilon>"
                  using imp_assms
                  apply (intro exI[where x = "\<omega>"])
                  using \<open>(\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int (Suc N) (LOOP \<pi>) \<mu> \<nu>\<close>
                  by (simp add: fol_states_agree_on_def)
              next
                case False
                then show "\<exists>\<upsilon>. (if 0 < Suc N
                             then state_eval \<omega> = state_eval \<upsilon> \<or>
                                  full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<omega> \<upsilon> \<or> full_prog_eval_int (Suc N - 1) (\<pi>*) \<omega> \<upsilon>
                             else False) \<and>
                            fol_states_agree_on V \<nu> \<upsilon>"
                proof -
                  assume False_prems_1: "state_eval \<mu> \<noteq> state_eval \<nu>"
                  then show ?thesis
                  proof (cases "full_prog_eval_int (Suc N - 1) (LOOP \<pi>) \<mu> \<nu>")
                    case True
                    then show ?thesis
                      using suc_ind_hyp
                      by (metis Suc.prems diff_Suc_1 zero_less_Suc)
                  next
                    case False
                    then show ?thesis
                    proof -
                      assume "\<not> full_prog_eval_int (Suc N - 1) (\<pi>*) \<mu> \<nu>"
                      then have "full_prog_eval_int (Suc N - 1) (SEQ \<pi> (LOOP \<pi>)) \<mu> \<nu>"
                        using False_prems_1
                        using three_possible_cases
                        by (meson \<open>(\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int (Suc N) (\<pi>*) \<mu> \<nu>\<close> full_prog_eval_int.simps(5))

                      then have "\<exists>\<upsilon>. full_prog_eval_int (Suc N - 1) (SEQ \<pi> (LOOP \<pi>)) \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>"
                        unfolding full_prog_eval_int.simps(3)
                      proof -
                        assume "\<exists>\<nu>'. full_prog_eval_int (Suc N - 1) \<pi> \<mu> \<nu>' \<and> full_prog_eval_int (Suc N - 1) (LOOP \<pi>) \<nu>' \<nu>"
                        then obtain interm_state
                          where "full_prog_eval_int (Suc N - 1) \<pi> \<mu> interm_state"
                            and trans_to_final: "full_prog_eval_int (Suc N - 1) (LOOP \<pi>) interm_state \<nu>"
                          by blast

                        then obtain par_interm_state
                          where interm_trans: "full_prog_eval_int (Suc N - 1) \<pi> \<omega> par_interm_state"
                            and interm_agree: "fol_states_agree_on V interm_state par_interm_state"
                          using inductive_hyp[of \<mu> \<omega> "(Suc N -1)" interm_state]
                          using imp_assms
                          using \<open>\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v\<close>
                          using Suc.prems by blast

                        then obtain par_final_state
                          where final_trans: "full_prog_eval_int (Suc N - 1) (LOOP \<pi>) par_interm_state par_final_state"
                            and final_agree: "fol_states_agree_on V \<nu> par_final_state"
                          using trans_to_final
                          using suc_ind_hyp[of interm_state par_interm_state \<nu>]
                          using imp_assms
                          by (metis \<open>(\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval_int (Suc N) (LOOP \<pi>) \<mu> \<nu>\<close> diff_Suc_1)

                        show "\<exists>\<upsilon>. (\<exists>\<nu>. full_prog_eval_int (Suc N - 1) \<pi> \<omega> \<nu> \<and> full_prog_eval_int (Suc N - 1) (LOOP \<pi>) \<nu> \<upsilon>) \<and> fol_states_agree_on V \<nu> \<upsilon>"
                        proof (intro exI[where x=par_final_state], intro conjI)
                          show "\<exists>\<nu>. full_prog_eval_int (Suc N - 1) \<pi> \<omega> \<nu> \<and> full_prog_eval_int (Suc N - 1) (LOOP \<pi>) \<nu> par_final_state"
                            using interm_trans final_trans
                            by (intro exI[where x=par_interm_state],blast)

                          show "fol_states_agree_on V \<nu> par_final_state"
                            using final_agree
                            by simp
                        qed
                      qed
                      thus "\<exists>\<upsilon>. (if 0 < Suc N
                             then (state_eval \<omega> = state_eval \<upsilon>) \<or> full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<omega> \<upsilon> \<or> full_prog_eval_int (Suc N - 1) (\<pi>*) \<omega> \<upsilon>
                             else False) \<and>
                            fol_states_agree_on V \<nu> \<upsilon>"
                        by (meson zero_less_Suc)
                    qed
                  qed
                qed
              qed
            qed
          qed
          thus "\<exists>\<upsilon>. full_prog_eval_int n (LOOP \<pi>) \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>"
            using \<open>\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v\<close> imp_assms by blast
        qed
      qed
    qed

  thus "\<And>\<pi> V \<mu> \<omega> \<nu>.
         (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
      unfolding full_prog_eval_def
      by blast

    show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
    proof
      fix \<pi>
      have " \<forall>\<mu> \<omega> \<nu>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> ((\<exists> n . full_prog_eval_int n \<pi> \<mu> \<nu>) \<longleftrightarrow> (\<exists> n .full_prog_eval_int n \<pi> \<omega> \<nu>))"
        using full_prog_var_determinance_n
        by metis
  thus "\<forall>\<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
    unfolding full_prog_eval_def
    by meson
qed
qed

  show "\<And>\<pi>. finite (Collect (full_prog_fv_syn \<pi>))"
    using dynLogCore_instantiated
    using dynLogCore.prog_fv_finite[of "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"]
    by fastforce
  
  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
         (\<forall>v. full_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and> fol_states_agree_on V \<mu> \<omega> \<and> full_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. full_prog_eval \<pi> \<omega> \<upsilon> \<and> fol_states_agree_on V \<nu> \<upsilon>)"
  using dynLogCore_instantiated
  using dynLogCore.prog_fv_overapprox[of "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"]
  by blast

  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow> full_prog_eval \<pi> \<mu> = full_prog_eval \<pi> \<omega>"
    using dynLogCore_instantiated
    using dynLogCore.prog_var_determinance
    by blast
qed

(*sublocale kat_dl : dynLog
    "atom_eval" "atom_fv_syn" "state_eval" "full_prog_eval" "full_prog_fv_syn"
  by unfold_locales*)

lemma BV_overapprox:
  assumes "\<And> \<pi> v . dyn_prog_bv_sem \<pi> v \<Longrightarrow> BV \<pi> v"
  shows "kat_dl.dyn_prog_bv_sem \<pi> v \<Longrightarrow> full_dyn_prog_BV BV \<pi> v"
proof (induct \<pi>)
  case (KATPROG x)
  then show ?case
  by (metis assms dyn_prog_bv_sem.elims(3) full_dyn_prog_BV.simps(1) full_prog_eval_def full_prog_eval_int.simps(1) kat_dl.dyn_prog_bv_sem.elims(2))
next
  case (CHECK x)
  then show ?case
    unfolding kat_dl.dyn_prog_bv_sem.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding full_dyn_prog_BV.simps
    by force
next
  case (SEQ \<pi>1 \<pi>2)
  then show ?case
    unfolding kat_dl.dyn_prog_bv_sem.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding full_dyn_prog_BV.simps
    by force
next
  case (CHOICE \<pi>1 \<pi>2)
  then show ?case
    unfolding kat_dl.dyn_prog_bv_sem.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding full_dyn_prog_BV.simps
    by force
next
  case (LOOP \<pi>)
  then show ?case
    unfolding kat_dl.dyn_prog_bv_sem.simps
    unfolding full_prog_eval_def
  proof -
    assume ind_assm: "(\<exists>\<mu> \<omega>. (\<exists>n. full_prog_eval_int n \<pi> \<mu> \<omega>) \<and>
            state_eval \<mu> v \<noteq> state_eval \<omega> v \<Longrightarrow>
     full_dyn_prog_BV BV \<pi> v)"
    assume assm2: "\<exists>\<mu> \<omega>. (\<exists>n. full_prog_eval_int n (\<pi>*) \<mu> \<omega>) \<and>
           state_eval \<mu> v \<noteq> state_eval \<omega> v"
    have "\<And> N .\<exists>\<mu> \<omega>. full_prog_eval_int N (\<pi>*) \<mu> \<omega> \<and>
           state_eval \<mu> v \<noteq> state_eval \<omega> v \<Longrightarrow>
    full_dyn_prog_BV BV (\<pi>*) v"
    proof -
      fix N
      show "\<exists>\<mu> \<omega>. full_prog_eval_int N (\<pi>*) \<mu> \<omega> \<and>
           state_eval \<mu> v \<noteq> state_eval \<omega> v \<Longrightarrow>
              full_dyn_prog_BV BV (\<pi>*) v"
      proof (induct N)
        case 0
        then show ?case
          unfolding full_prog_eval_int.simps(5)[of 0]
          by simp
      next
        case (Suc N)
        then show ?case
          unfolding full_prog_eval_int.simps(5)[of "(Suc N)"]
        proof -
          assume "\<exists>\<mu> \<omega>. (if 0 < Suc N
            then state_eval \<mu> = state_eval \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<mu> \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>*) \<mu> \<omega>
            else False) \<and>
           state_eval \<mu> v \<noteq> state_eval \<omega> v"
          then obtain \<mu> \<omega> where mu_cases: "(if 0 < Suc N
            then state_eval \<mu> = state_eval \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<mu> \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>*) \<mu> \<omega>
            else False)"
                            and mu_omega_uneq: "state_eval \<mu> v \<noteq> state_eval \<omega> v"
            by blast
          have "(state_eval \<mu> = state_eval \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<mu> \<omega> \<or>
                 full_prog_eval_int (Suc N - 1) (\<pi>*) \<mu> \<omega>)"
            using mu_cases
            by argo
          then show "full_dyn_prog_BV BV (\<pi>*) v"
            unfolding full_dyn_prog_BV.simps
          proof (elim disjE)
            show "state_eval \<mu> = state_eval \<omega> \<Longrightarrow> full_dyn_prog_BV BV \<pi> v"
              using mu_omega_uneq
              by simp
            show "full_prog_eval_int (Suc N - 1) (\<pi>*) \<mu> \<omega> \<Longrightarrow> full_dyn_prog_BV BV \<pi> v"
              by (metis Suc.hyps diff_Suc_1 full_dyn_prog_BV.simps(5) mu_omega_uneq)
            show "full_prog_eval_int (Suc N - 1) (\<pi>;(\<pi>*)) \<mu> \<omega> \<Longrightarrow> full_dyn_prog_BV BV \<pi> v"
              unfolding full_prog_eval_int.simps(3)
              using Suc.hyps
              using ind_assm
              by (metis diff_Suc_1 full_dyn_prog_BV.simps(5) mu_omega_uneq)
          qed
        qed
      qed
    qed

    thus ?thesis
      using assm2
      by blast
  qed
qed

lemma dyn_axiom_test:
  fixes v :: "'var"
    and \<psi> :: "('atom,'var) fol_formula"
    and \<phi> :: "('atom,'var,('atom,'var,'prog) kat_prog) dyn_formula"
  shows "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (?(\<psi>)) \<rbrakk> \<phi>) \<Lleftarrow>\<Rrightarrow> ( (FOL \<psi>) \<Rrightarrow>\<phi>)"
proof -
  have dir1: "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (?(\<psi>)) \<rbrakk> \<phi>) \<Rrightarrow> ( (FOL \<psi>) \<Rrightarrow>\<phi>)"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by blast

  have dir2: "\<Turnstile>[kat_dl.dyn_eval] ( (FOL \<psi>) \<Rrightarrow>\<phi>) \<Rrightarrow> (\<lbrakk> (?(\<psi>)) \<rbrakk> \<phi>)"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding dyn_eval.simps
    unfolding full_prog_eval_def[of "(? \<psi>)"]
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    apply (simp,standard,intro impI)
    using kat_dl.dyn_differing_state_eval_due_to_vars by force

  show ?thesis
    using dir1 dir2
    by simp
qed

lemma dyn_axiom_seq:
  fixes v :: "'var"
    and \<pi>1 :: "('atom,'var,'prog) kat_prog"
    and \<pi>2 :: "('atom,'var,'prog) kat_prog"
    and \<phi> :: "('atom,'var,('atom,'var,'prog) kat_prog) dyn_formula"
  shows "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (\<pi>1;\<pi>2) \<rbrakk> \<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk> (\<pi>1)\<rbrakk>\<lbrakk>(\<pi>2) \<rbrakk> \<phi>)"
proof -
  have dir1: "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (\<pi>1;\<pi>2) \<rbrakk> \<phi>) \<Rrightarrow> (\<lbrakk> (\<pi>1)\<rbrakk>\<lbrakk>(\<pi>2) \<rbrakk> \<phi>)"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by (meson full_prog_eval_int_n_monotone linorder_le_cases)

  have dir2: "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (\<pi>1)\<rbrakk>\<lbrakk>(\<pi>2) \<rbrakk> \<phi>) \<Rrightarrow> (\<lbrakk> (\<pi>1;\<pi>2) \<rbrakk> \<phi>)"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by (meson full_prog_eval_int_n_monotone linorder_le_cases)

  show ?thesis
    using dir1 dir2
    by simp
qed

lemma dyn_axiom_choice:
  fixes v :: "'var"
    and \<pi>1 :: "('atom,'var,'prog) kat_prog"
    and \<pi>2 :: "('atom,'var,'prog) kat_prog"
    and \<phi> :: "('atom,'var,('atom,'var,'prog) kat_prog) dyn_formula"
  shows "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (\<pi>1 \<squnion> \<pi>2) \<rbrakk> \<phi>) \<Lleftarrow>\<Rrightarrow> ( (\<lbrakk>(\<pi>1)\<rbrakk>\<phi>) and (\<lbrakk>(\<pi>2)\<rbrakk>\<phi>) )"
proof -
  have dir1: "\<Turnstile>[kat_dl.dyn_eval] (\<lbrakk> (\<pi>1 \<squnion> \<pi>2) \<rbrakk> \<phi>) \<Rrightarrow> ( (\<lbrakk>(\<pi>1)\<rbrakk>\<phi>) and (\<lbrakk>(\<pi>2)\<rbrakk>\<phi>) )"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by blast

  have dir2: "\<Turnstile>[kat_dl.dyn_eval] ( (\<lbrakk>(\<pi>1)\<rbrakk>\<phi>) and (\<lbrakk>(\<pi>2)\<rbrakk>\<phi>) ) \<Rrightarrow> (\<lbrakk> (\<pi>1 \<squnion> \<pi>2) \<rbrakk> \<phi>)"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
    unfolding full_prog_eval_def
    unfolding full_prog_eval_int.simps
    unfolding dyn_eval.simps
    by blast

  show ?thesis
    using dir1 dir2
    by simp
qed

lemma dyn_axiom_star:
  "\<Turnstile>[kat_dl.dyn_eval] ((\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<phi> and \<lbrakk>(\<pi>1)\<rbrakk>\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>))"
proof -

  have dir1: "\<Turnstile>[kat_dl.dyn_eval] ((\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>) \<Rrightarrow> (\<phi> and \<lbrakk>(\<pi>1)\<rbrakk>\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>))"
  unfolding kat_dl.IMP_def
  unfolding theory_valid_def
  unfolding kat_dl.dyn_eval.simps
  proof (simp,standard)
    fix \<mu>
  
    have "(\<forall> \<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>) \<Longrightarrow>
           kat_dl.dyn_eval \<phi> \<mu> \<and>
           (\<forall>\<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>'))"
    proof (intro conjI)
      show "\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<mu>"
      proof -
        assume assm1: "\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
        have "full_prog_eval (\<pi>1*) \<mu> \<mu>"
          unfolding full_prog_eval_def
          apply (intro exI[where x="1"])
          unfolding full_prog_eval_int.simps(5)[of 1]
          by force
        thus "kat_dl.dyn_eval \<phi> \<mu>"
          using assm1
          by blast
      qed
  
      show "\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega> \<Longrightarrow>
          \<forall>\<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>')"
      proof (intro allI, intro impI,standard, intro impI)
        assume assm1: "\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
        fix \<omega>
        fix \<omega>'
        assume assm2: "full_prog_eval \<pi>1 \<mu> \<omega>"
        then obtain N1 where N1_cond: "full_prog_eval_int N1 \<pi>1 \<mu> \<omega>"
          unfolding full_prog_eval_def
          by blast
        assume assm3: "full_prog_eval (\<pi>1*) \<omega> \<omega>'"
        then obtain N2 where N2_cond: "full_prog_eval_int N2 (\<pi>1*) \<omega> \<omega>'"
          unfolding full_prog_eval_def
          by blast
  
        then obtain N where N_cond: "N \<ge> N1 \<and> N \<ge> N2"
          using nat_le_linear by blast
  
        have "full_prog_eval_int (Suc N) (\<pi>1*) \<mu> \<omega>'"
          unfolding full_prog_eval_int.simps(5)[of "(Suc N)"]
          unfolding full_prog_eval_int.simps(3)[of "(Suc N - 1)"]
        proof -
  
          have "(\<exists>\<nu>. full_prog_eval_int (Suc N - 1) \<pi>1 \<mu> \<nu> \<and> full_prog_eval_int (Suc N - 1) (\<pi>1*) \<nu> \<omega>')"
          proof (intro exI[where x="\<omega>"], intro conjI)
            show "full_prog_eval_int (Suc N - 1) \<pi>1 \<mu> \<omega>"
              using N1_cond N_cond full_prog_eval_int_n_monotone[of N1 \<pi>1 \<mu> \<omega> N]
              by force
  
            show "full_prog_eval_int (Suc N - 1) (\<pi>1*) \<omega> \<omega>'"
              using N2_cond N_cond full_prog_eval_int_n_monotone[of N2 "(\<pi>1*)" \<omega> \<omega>' N]
              using diff_Suc_1 by presburger
          qed
        
  
          thus "if 0 < Suc N
                then (state_eval \<mu>) = (state_eval \<omega>') \<or>
                     (\<exists>\<nu>. full_prog_eval_int (Suc N - 1) \<pi>1 \<mu> \<nu> \<and> full_prog_eval_int (Suc N - 1) (\<pi>1*) \<nu> \<omega>') \<or>
                     full_prog_eval_int (Suc N - 1) (\<pi>1*) \<mu> \<omega>'
                else False"
            by simp
        qed
  
        thus "kat_dl.dyn_eval \<phi> \<omega>'"
          using assm1
          unfolding full_prog_eval_def
          by blast
      qed
    qed
  
    thus "(\<exists>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<and> \<not> kat_dl.dyn_eval \<phi> \<omega>) \<or>
           kat_dl.dyn_eval \<phi> \<mu> \<and>
           (\<forall>\<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>'))"
      by blast
  qed

  have dir2: "\<Turnstile>[kat_dl.dyn_eval] ((\<phi> and \<lbrakk>(\<pi>1)\<rbrakk>\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>) \<Rrightarrow> (\<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>))"
    unfolding kat_dl.IMP_def
    unfolding theory_valid_def
    unfolding kat_dl.dyn_eval.simps
  proof (standard, simp, intro impI)
    fix \<mu>
    assume assm1: "kat_dl.dyn_eval \<phi> \<mu>"

    have "(\<forall> \<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<longrightarrow> (\<forall> \<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>')) \<longrightarrow>
         (\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>)"
    proof (standard, intro allI,intro impI)
      fix \<omega>
      assume assm2: "\<forall>\<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<longrightarrow> (\<forall>\<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>')"

      have "\<And> N . full_prog_eval_int N (\<pi>1*) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
      proof -
        fix N
        show "full_prog_eval_int N (\<pi>1*) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
        proof (induct N)
          case 0
          then show ?case
            unfolding full_prog_eval_int.simps(5)[of 0]
            by simp
        next
          case (Suc N)
          then show ?case
            unfolding full_prog_eval_int.simps(5)[of "(Suc N)"]
          proof -
            assume assm3: "(full_prog_eval_int N (\<pi>1*) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>)"
            have "((state_eval \<mu>) = (state_eval \<omega>) \<or> full_prog_eval_int (Suc N - 1) (\<pi>1;(\<pi>1*)) \<mu> \<omega> \<or> full_prog_eval_int (Suc N - 1) (\<pi>1*) \<mu> \<omega>)"
              using Suc.prems by auto
            thus "kat_dl.dyn_eval \<phi> \<omega>"
            proof (elim disjE)
              show "(state_eval \<mu>) = (state_eval \<omega>) \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
                using assm1
                using kat_dl.dyn_differing_state_eval_due_to_vars by force

              show "full_prog_eval_int (Suc N - 1) (\<pi>1*) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
                using assm3
                by force

              show "full_prog_eval_int (Suc N - 1) (\<pi>1;(\<pi>1*)) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
                unfolding full_prog_eval_int.simps(3)
              proof -
                assume "\<exists>\<nu>. full_prog_eval_int (Suc N - 1) \<pi>1 \<mu> \<nu> \<and> full_prog_eval_int (Suc N - 1) (\<pi>1*) \<nu> \<omega>"
                then obtain \<nu> where \<nu>_cond: "full_prog_eval_int (Suc N - 1) \<pi>1 \<mu> \<nu> \<and> full_prog_eval_int (Suc N - 1) (\<pi>1*) \<nu> \<omega>"
                  by blast

                have cond1: "full_prog_eval \<pi>1 \<mu> \<nu>"
                  using \<nu>_cond
                  unfolding full_prog_eval_def
                  by blast

                have cond2: "full_prog_eval (\<pi>1*) \<nu> \<omega>"
                  using \<nu>_cond
                  unfolding full_prog_eval_def
                  by blast

                show ?thesis
                  using cond1 cond2 assm2
                  by blast
              qed
            qed
          qed
        qed
      qed

      thus "full_prog_eval (\<pi>1*) \<mu> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
        unfolding full_prog_eval_def
        by blast
    qed
      

    thus "(\<exists>\<omega>. full_prog_eval \<pi>1 \<mu> \<omega> \<and> (\<exists>\<omega>'. full_prog_eval (\<pi>1*) \<omega> \<omega>' \<and> \<not> kat_dl.dyn_eval \<phi> \<omega>')) \<or>
         (\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>)"
      by blast
  qed

  show ?thesis
    using dir1 dir2
    by simp
qed

lemma loop_concat:
  assumes "full_prog_eval (\<pi>1 *) \<mu> \<sigma>"
      and "full_prog_eval (\<pi>1) \<sigma> \<nu>"
  shows "full_prog_eval (\<pi>1* ) \<mu> \<nu>"
proof -

  obtain N2 where N2_cond: "full_prog_eval_int N2 (\<pi>1 ) \<sigma> \<nu> \<and> N2 \<ge> 2" using assms
    unfolding full_prog_eval_def
    using full_prog_eval_int_n_monotone nat_le_linear by blast
  obtain N1 where N1_cond: "full_prog_eval_int N1 (\<pi>1* ) \<mu> \<sigma>" using assms
    unfolding full_prog_eval_def by blast

  then have "N1 \<ge> 1"
    using neq0_conv by fastforce

  then have "\<forall> s1 s2 s3 . full_prog_eval_int N1 (\<pi>1* ) s1 s2 \<and> full_prog_eval_int N2 (\<pi>1 ) s2 s3 \<longrightarrow> full_prog_eval_int (N1+N2) (\<pi>1* ) s1 s3"
  proof (induct N1)
    case 0
    then show ?case
      by simp
  next
    case (Suc N1)
    then show ?case
    proof (intro allI, intro impI)
      fix s1 s2 s3

      have ind_hyp: "\<forall>s1 s2 s3.
           full_prog_eval_int N1 (\<pi>1*) s1 s2 \<and>
           full_prog_eval_int N2 \<pi>1 s2 s3 \<longrightarrow>
           full_prog_eval_int (N1 + N2) (\<pi>1*) s1 s3"
        using Suc.hyps by auto

      have proof_details: "(state_eval s1 = state_eval s2 \<or>
        full_prog_eval_int (Suc N1 - 1) (\<pi>1;(\<pi>1* )) s1 s2 \<or>
        full_prog_eval_int (Suc N1 - 1) (\<pi>1*) s1 s2) \<and>
        full_prog_eval_int N2 \<pi>1 s2 s3
        \<Longrightarrow> full_prog_eval_int (Suc N1 + N2) (\<pi>1*) s1 s3"
      proof (elim conjE,elim disjE)
        show "full_prog_eval_int N2 \<pi>1 s2 s3 \<Longrightarrow>
                state_eval s1 = state_eval s2 \<Longrightarrow>
                full_prog_eval_int (Suc N1 + N2) (\<pi>1*) s1 s3"
        proof -
          assume assm1: "full_prog_eval_int N2 \<pi>1 s2 s3"
          assume assm2: "state_eval s1 = state_eval s2"
          then have "(\<forall>v. state_eval s1 v = state_eval s2 v)"
            by force
          then have "full_prog_eval_int N2 \<pi>1 s1 s3"
            using assm1
            using full_prog_var_determinance_n[of \<pi>1]
            unfolding full_prog_eval_def
            apply (elim allE[where x=N2])
            apply (erule allE[where x="s1"])
            apply (erule allE[where x="s2"])
            by simp
          thus "full_prog_eval_int (Suc N1 + N2) (\<pi>1* ) s1 s3"
            unfolding full_prog_eval_int.simps[of "(Suc N1 + N2)"]
            unfolding full_prog_eval_int.simps[of "(Suc N1 + N2 -1)"]
            using full_prog_eval_int_n_monotone[of N2 \<pi>1 s1 s3 "(Suc N1 + N2 - 1)"]
            using assm2 N2_cond
            by (metis Suc_1 Suc_le_D add_Suc diff_Suc_1 gr0_conv_Suc le_add2)
        qed

        show "full_prog_eval_int N2 \<pi>1 s2 s3 \<Longrightarrow>
                full_prog_eval_int (Suc N1 - 1) (\<pi>1*) s1 s2 \<Longrightarrow>
                full_prog_eval_int (Suc N1 + N2) (\<pi>1*) s1 s3"
          using ind_hyp
          by (metis Suc_n_not_le_n add_le_mono1 diff_Suc_1 full_prog_eval_int_n_monotone linorder_linear)

        show "full_prog_eval_int N2 \<pi>1 s2 s3 \<Longrightarrow>
          full_prog_eval_int (Suc N1 - 1) (\<pi>1;(\<pi>1* )) s1 s2 \<Longrightarrow>
          full_prog_eval_int (Suc N1 + N2) (\<pi>1*) s1 s3"
          using ind_hyp
          by (smt (verit, ccfv_SIG) add_Suc diff_Suc_1 full_prog_eval_int.simps(3) full_prog_eval_int.simps(5) full_prog_eval_int_n_monotone nat_le_iff_add zero_less_Suc)
      
      qed

      assume "full_prog_eval_int (Suc N1) (\<pi>1*) s1 s2 \<and>
       full_prog_eval_int N2 \<pi>1 s2 s3"
      thus "full_prog_eval_int (Suc N1 + N2) (\<pi>1*) s1 s3"
        unfolding full_prog_eval_int.simps[of "(Suc N1)"]
        using proof_details
        by simp
    qed
  qed
  thus "full_prog_eval (\<pi>1*) \<mu> \<nu>"
    using assms
    using N1_cond N2_cond full_prog_eval_def by blast
qed


lemma dyn_axiom_I:
  "\<Turnstile>[kat_dl.dyn_eval] ((\<lbrakk>((\<pi>1)*)\<rbrakk>(\<phi> \<Rrightarrow> \<lbrakk>\<pi>1\<rbrakk>\<phi>)) \<Rrightarrow> (\<phi> \<Rrightarrow> \<lbrakk>((\<pi>1)*)\<rbrakk>\<phi>))"
proof -
  have rephrased: "\<And>\<mu> .kat_dl.dyn_eval \<phi> \<mu> \<Longrightarrow>
         (\<forall>\<omega>. (full_prog_eval (\<pi>1*) \<mu> \<omega>) \<longrightarrow>
            (kat_dl.dyn_eval \<phi> \<omega> \<longrightarrow> (\<forall> \<nu>. full_prog_eval \<pi>1 \<omega> \<nu> \<longrightarrow> kat_dl.dyn_eval \<phi> \<nu>))
          )
        \<Longrightarrow> (\<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>)"
  proof -
    fix \<mu>
    assume holds_initially: "kat_dl.dyn_eval \<phi> \<mu>"
    assume inductive_argument: "(\<forall>\<omega>. (full_prog_eval (\<pi>1*) \<mu> \<omega>) \<longrightarrow>
                                  (kat_dl.dyn_eval \<phi> \<omega> \<longrightarrow> (\<forall> \<nu>. full_prog_eval \<pi>1 \<omega> \<nu> \<longrightarrow> kat_dl.dyn_eval \<phi> \<nu>))
                                )"

    have "\<forall> n \<sigma> \<omega>. ((full_prog_eval (\<pi>1*) \<mu> \<sigma>) \<and> (kat_dl.dyn_eval \<phi> \<sigma>) \<and> full_prog_eval_int n (\<pi>1*) \<sigma> \<omega>) \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
    proof
      fix n
      show "\<forall>\<sigma> \<omega>. ((full_prog_eval (\<pi>1*) \<mu> \<sigma>) \<and> (kat_dl.dyn_eval \<phi> \<sigma>) \<and> full_prog_eval_int n (\<pi>1*) \<sigma> \<omega>) \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
      proof (induct n)
        case 0
        then show ?case
          unfolding full_prog_eval_int.simps[of "0"]
          by simp
      next
        case (Suc n)
        then show ?case
        proof (intro allI, intro impI)
          fix \<sigma>
          fix \<omega>
          assume ind_hyp: "\<forall>\<sigma> \<omega>. (full_prog_eval (\<pi>1*) \<mu> \<sigma>) \<and> kat_dl.dyn_eval \<phi> \<sigma> \<and> full_prog_eval_int n (\<pi>1*) \<sigma> \<omega> \<longrightarrow>
                 kat_dl.dyn_eval \<phi> \<omega>"
          assume has_transition: "(full_prog_eval (\<pi>1*) \<mu> \<sigma>) \<and> kat_dl.dyn_eval \<phi> \<sigma> \<and> full_prog_eval_int (Suc n) (\<pi>1*) \<sigma> \<omega>"

          show "(full_prog_eval (\<pi>1*) \<mu> \<sigma>) \<and> kat_dl.dyn_eval \<phi> \<sigma> \<and> full_prog_eval_int (Suc n) (\<pi>1*) \<sigma> \<omega> \<Longrightarrow>
                  kat_dl.dyn_eval \<phi> \<omega>"
            unfolding full_prog_eval_int.simps[of "(Suc n)"]
          proof -

            have "state_eval \<sigma> = state_eval \<omega> \<or>
                   full_prog_eval_int (Suc n - 1) (\<pi>1;(\<pi>1*)) \<sigma> \<omega> \<or>
                   full_prog_eval_int (Suc n - 1) (\<pi>1*) \<sigma> \<omega>"
              using has_transition by auto

            thus "kat_dl.dyn_eval \<phi> \<omega>"
            proof (elim disjE)
              show "state_eval \<sigma> = state_eval \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
              using holds_initially
              using kat_dl.dyn_differing_state_eval_due_to_vars
              using has_transition by force

            show "full_prog_eval_int (Suc n - 1) (\<pi>1*) \<sigma> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
              using ind_hyp
              using has_transition
              by (metis diff_Suc_1)

            show "full_prog_eval_int (Suc n - 1) (\<pi>1;(\<pi>1*)) \<sigma> \<omega> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
              unfolding full_prog_eval_int.simps(3)
            proof -
              assume "\<exists>\<nu>. full_prog_eval_int (Suc n - 1) \<pi>1 \<sigma> \<nu> \<and>
                        full_prog_eval_int (Suc n - 1) (\<pi>1*) \<nu> \<omega>"
              then obtain \<nu> where one_step: "full_prog_eval_int (Suc n - 1) \<pi>1 \<sigma> \<nu>"
                              and loop_step: "full_prog_eval_int (Suc n - 1) (\<pi>1*) \<nu> \<omega>"
                by blast

              have \<nu>_loop_reachable: "full_prog_eval (\<pi>1*) \<sigma> \<nu>"
                using one_step
                by (metis full_prog_eval_def full_prog_eval_int.simps(3) full_prog_eval_int.simps(5) loop_step zero_less_Suc)

              then have \<nu>_reachable: "full_prog_eval (\<pi>1*) \<mu> \<nu>"
                using has_transition
                using loop_concat
                using full_prog_eval_def one_step by blast

              have \<nu>_sat_\<phi>: "kat_dl.dyn_eval \<phi> \<nu>"
                using inductive_argument holds_initially
                using one_step
                apply (elim allE[where x="\<sigma>"])
                using full_prog_eval_def
                using has_transition
                by blast

              show "kat_dl.dyn_eval \<phi> \<omega>"
                using \<nu>_reachable \<nu>_sat_\<phi> loop_step
                using ind_hyp
                by (metis diff_Suc_1)
            qed
          qed
        qed
      qed
    qed
  qed
  thus "kat_dl.dyn_eval \<phi> \<mu> \<Longrightarrow> \<forall>\<omega>. full_prog_eval (\<pi>1*) \<mu> \<omega> \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
      unfolding full_prog_eval_def[of "(\<pi>1*)"]
    proof (intro allI,intro impI)
      fix \<omega>
      assume rephrased: "\<forall>n \<sigma> \<omega>.
                (\<exists>n. full_prog_eval_int n (\<pi>1*) \<mu> \<sigma>) \<and>
                kat_dl.dyn_eval \<phi> \<sigma> \<and> full_prog_eval_int n (\<pi>1*) \<sigma> \<omega> \<longrightarrow>
                kat_dl.dyn_eval \<phi> \<omega>"
      assume "\<exists>n. full_prog_eval_int n (\<pi>1*) \<mu> \<omega>"
      then obtain N where "full_prog_eval_int N (\<pi>1*) \<mu> \<omega>" by blast

      thus "kat_dl.dyn_eval \<phi> \<mu> \<Longrightarrow> kat_dl.dyn_eval \<phi> \<omega>"
        using rephrased
        apply (elim allE[of _ N])
        apply (erule allE[where x=\<mu>])
        apply (erule allE[where x=\<omega>])
        by fastforce
    qed
  qed

  show ?thesis
    unfolding theory_valid_def
    unfolding kat_dl.IMP_def
    unfolding kat_dl.dyn_eval.simps
    apply (simp,intro allI, intro impI)
    using rephrased
    by blast
qed

fun translate :: "('atom, 'var, 'prog) dyn_formula \<Rightarrow>('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
  where
      "translate (FOL \<phi>) = (FOL \<phi>)"
    | "translate (\<phi> and \<psi>) = ((translate \<phi>) and (translate \<psi>))"
    | "translate (\<rceil> \<phi>) = (\<rceil> (translate \<phi>))"
    | "translate (\<bbbA> v . \<phi>) = (\<bbbA> v . (translate \<phi>))"
    | "translate (\<lbrakk>\<alpha>\<rbrakk>\<phi>) = (\<lbrakk>(KATPROG \<alpha>)\<rbrakk> (translate \<phi>))"

lemma dyn_axiom_RR:
  assumes "\<Turnstile>[dyn_eval] \<phi>"
  shows "\<Turnstile>[kat_dl.dyn_eval] (translate \<phi>)"
  using assms
proof -
  fix \<phi>
  have "\<And> \<mu> . ((dyn_eval \<phi> \<mu>) = (kat_dl.dyn_eval (translate \<phi>) \<mu>))"
  proof (induct \<phi>)
    case (FOL x)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding kat_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by simp
  next
    case (AND \<phi>1 \<phi>2)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding kat_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (NOT \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding kat_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (FOL_ALL x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding kat_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      by blast
  next
    case (BOX x1a \<phi>)
    then show ?case
      unfolding translate.simps
      unfolding theory_valid_def
      unfolding kat_dl.dyn_eval.simps
      unfolding dyn_eval.simps
      unfolding full_prog_eval_def
      unfolding full_prog_eval_int.simps
      by blast
  qed
  thus "\<Turnstile>[dyn_eval] \<phi> \<Longrightarrow> \<Turnstile>[kat_dl.dyn_eval] translate \<phi>"
    unfolding theory_valid_def
    by blast
qed

lemma dl_seq: "kat_dl.dyn_eval (\<lbrakk> (\<alpha> ; \<beta>) \<rbrakk> \<phi>) \<mu> = kat_dl.dyn_eval (\<lbrakk>\<alpha>\<rbrakk>(\<lbrakk>\<beta>\<rbrakk>\<phi>)) \<mu>"
proof -
  have "kat_dl.dyn_eval (\<lbrakk> (\<alpha>;\<beta>) \<rbrakk> \<phi>) \<mu> =
         (\<forall>s. full_prog_eval (\<alpha>;\<beta>) \<mu> s \<longrightarrow> kat_dl.dyn_eval \<phi> s)"
    by simp
  also have "... = (\<forall>s. (\<exists>t. full_prog_eval \<alpha> \<mu> t \<and> full_prog_eval \<beta> t s) \<longrightarrow> kat_dl.dyn_eval \<phi> s)"
    by (meson KATDynLog.full_prog_eval_int.simps(3) KATDynLog_axioms full_prog_eval_def full_prog_eval_int_n_monotone le_add2 nat_le_iff_add)
  also have "... = (\<forall>t. full_prog_eval \<alpha> \<mu> t \<longrightarrow> (\<forall>s. full_prog_eval \<beta> t s \<longrightarrow> kat_dl.dyn_eval \<phi> s))"
    by blast
  also have "... = kat_dl.dyn_eval (\<lbrakk> \<alpha> \<rbrakk> \<lbrakk> \<beta> \<rbrakk> \<phi>) \<mu>"
    by simp
  finally show ?thesis .
qed

lemma dia_is_ex:
  "kat_dl.dyn_eval (\<langle> \<pi> \<rangle> \<phi>) \<mu> = (\<exists>\<omega>. full_prog_eval \<pi> \<mu> \<omega> \<and> kat_dl.dyn_eval \<phi> \<omega>)"
  using kat_dl.DIAMOND_def by auto


fun REP :: "('a,'vr,'pr) kat_prog \<Rightarrow> nat \<Rightarrow> ('a,'vr,'pr) kat_prog" where
  "REP \<pi> (Suc n) = (\<pi> ; (REP \<pi> n))"
| "REP \<pi> 0 = (? FOLTRUE)"

lemma rep_is_kleene:
  assumes inrep: "full_prog_eval (REP \<pi> n) \<mu> \<omega>"
  shows "full_prog_eval (\<pi>*) \<mu> \<omega>"
proof -
  have "full_prog_eval (REP \<pi> n) \<mu> \<omega> \<Longrightarrow> full_prog_eval (\<pi>*) \<mu> \<omega>"
  proof (induct n arbitrary: \<mu>)
    case 0
    hence "state_eval \<mu> = state_eval \<omega>"
      using full_prog_eval_def by auto 
    hence "full_prog_eval_int 1 (\<pi>*) \<mu> \<omega>"
      by simp
    thus ?case
      using full_prog_eval_def by blast
  next
    case indhyp: (Suc n)
    then obtain \<nu> where nu: "full_prog_eval \<pi> \<mu> \<nu> \<and> full_prog_eval (REP \<pi> n) \<nu> \<omega> "
      using full_prog_eval_def by auto
    with indhyp have "full_prog_eval \<pi> \<mu> \<nu> \<and> full_prog_eval (\<pi>*) \<nu> \<omega>"
      by blast
    hence "full_prog_eval (\<pi> ; (\<pi>*)) \<mu> \<omega>"
      by (meson full_prog_eval_def full_prog_eval_int.simps(3) full_prog_eval_int_n_monotone nat_le_linear) 
    thus ?case
      by (metis add_eq_if diff_Suc_1 full_prog_eval_def full_prog_eval_int.simps(5) less_add_Suc1) 
  qed
  with inrep show ?thesis by blast
qed
    thm full_prog_eval_int.simps
lemma kleene_is_rep:
 assumes inkleene: "full_prog_eval (\<pi>*) \<mu> \<omega>"
  shows "\<exists>n. full_prog_eval (REP \<pi> n) \<mu> \<omega>"
proof -
  {
    fix n
    have "full_prog_eval_int n (\<pi>*) \<mu> \<omega> \<Longrightarrow> ?thesis"
    proof (induct n arbitrary: \<mu>)
      case 0
      then show ?case by auto
    next
      case indhyp: (Suc n)
      hence "state_eval \<mu> = state_eval \<omega> \<or>
          full_prog_eval_int n (\<pi>;(\<pi>*))\<mu> \<omega> \<or>
          full_prog_eval_int n (\<pi>*) \<mu> \<omega>" 
        using full_prog_eval_int.simps(5) by fastforce
      then show ?case
      proof (elim disjE)
        assume "state_eval \<mu> = state_eval \<omega>"
        thus ?case
          by (metis REP.simps(2) dyn_eval.simps(1) fol_true_valid full_prog_eval_def full_prog_eval_int.simps(2) theory_valid_def) 
      next
        assume "full_prog_eval_int n (\<pi>;(\<pi>*)) \<mu> \<omega>" 
        then obtain \<tau> where "full_prog_eval_int n \<pi> \<mu> \<tau> \<and> full_prog_eval_int n (\<pi>*) \<tau> \<omega>"
          using full_prog_eval_int.simps(3) by blast
        with indhyp obtain n' where "full_prog_eval \<pi> \<mu> \<tau> \<and> full_prog_eval (REP \<pi> n') \<tau> \<omega>"
          using full_prog_eval_def by blast
        hence "full_prog_eval (REP \<pi> (Suc n')) \<mu> \<omega>" using REP.simps
          by (smt (z3) full_prog_eval_def full_prog_eval_int.simps(3) full_prog_eval_int_n_monotone nat_le_linear)
        thus ?case by blast
      next
        assume "full_prog_eval_int n (\<pi>*) \<mu> \<omega>"
        with indhyp show ?case by simp
      qed
    qed
  }
  with inkleene show ?thesis
    using full_prog_eval_def by blast
qed

lemma kleene_rep_rewrite:
  "(full_prog_eval (\<pi>*) \<mu> \<omega>) = (\<exists>n. full_prog_eval (REP \<pi> n) \<mu> \<omega>)"
  using rep_is_kleene[of \<pi> _ \<mu> \<omega>] kleene_is_rep[of \<pi> \<mu> \<omega>]
  by blast

lemma full_prog_rewrite_seq:
  "full_prog_eval (\<alpha>;\<beta>) \<sigma> \<mu> = (\<exists> \<nu> . (full_prog_eval \<alpha> \<sigma> \<nu> \<and> full_prog_eval \<beta> \<nu> \<mu>))"
  unfolding full_prog_eval_def
  unfolding full_prog_eval_int.simps
  using full_prog_eval_int_n_monotone
  by (meson nat_le_linear)

lemma full_prog_rewrite_choice:
  "full_prog_eval (\<alpha> \<squnion> \<beta>) \<sigma> \<mu> = (full_prog_eval \<alpha> \<sigma> \<mu> \<or> full_prog_eval \<beta> \<sigma> \<mu>)"
  unfolding full_prog_eval_def
  unfolding full_prog_eval_int.simps
  using full_prog_eval_int_n_monotone
  by blast

end

end
