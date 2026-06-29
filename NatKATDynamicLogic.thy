theory NatKATDynamicLogic
  imports
    Main
    "KATDynamicLogic"
begin

subsubsection\<open>Inductive Expressivity\<close>
text\<open>
\label{subsubsec:lifting:nat-regular}
The proof rules established so far cannot reason about loops inside a
diamond modality.
To this end, we propose an additional proof rule which is formalized in
this file.
In contrast to the previously established proof rules, this axiom requires
additional assumptions on the underlying theory.
We formalize these assumptions in the locale below:
\<close>

definition is_nat_assignable :: "('st => 'vr => 'vl) => ('vl => nat) \<Rightarrow> 'vr \<Rightarrow> bool"
  where "is_nat_assignable eval val2nat v = (\<forall> n . (\<exists> \<mu> . (val2nat (eval \<mu> v)) = n ) )"

definition nat_assignable_vars :: "('st => 'vr => 'vl) => ('vl => nat) \<Rightarrow> 'vr set"
  where "nat_assignable_vars eval val2nat = (Collect (is_nat_assignable eval val2nat))"

locale nat_regular_lifting =
    regular_lifting atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> ('var + 'qfvar) \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> ('var + 'qfvar) \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> ('var + 'qfvar) \<Rightarrow> bool"
+
fixes val2nat :: "'val \<Rightarrow> nat"
  and nat_var :: "'var \<Rightarrow> bool"
  and plus_one_relation :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
  and eq_relation :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
  and positive_relation :: "'var \<Rightarrow> ('atom, 'var) fol_formula"
(*assumes infinite_nat_vars: "\<not> (finite (nat_assignable_vars state_eval val2nat))"*)
assumes nat_assignability: "\<forall> v . nat_var v \<longrightarrow> is_nat_assignable state_eval val2nat (Inl v)"
    and plus_one_sound: "\<forall> v1 v2 .
          (v1 \<noteq> v2) \<and>
          (nat_var v1) \<and>
          (nat_var v2)
          \<longrightarrow> (\<forall> \<mu> .
                dyn_eval (FOL (plus_one_relation v1 v2)) \<mu>
                \<longleftrightarrow>
                ((val2nat (state_eval \<mu> (Inl v2)))) = (val2nat (state_eval \<mu> (Inl v1)) + 1)
              )"
    and eq_sound: "\<forall> v1 v2 .
          (v1 \<noteq> v2) \<and>
          (nat_var v1) \<and>
          (nat_var v2)
          \<longrightarrow> (\<forall> \<mu> .
                dyn_eval (FOL (eq_relation v1 v2)) \<mu>
                \<longleftrightarrow>
                (val2nat (state_eval \<mu> (Inl v2))) = ((val2nat (state_eval \<mu> (Inl v1))))
              )"
    and positive_sound: "\<forall> v1 .
          (nat_var v1)
          \<longrightarrow> (\<forall> \<mu> .
                (dyn_eval (FOL (positive_relation v1)) \<mu>)
                \<longleftrightarrow>
                ((val2nat (state_eval \<mu> (Inl v1))) > 0)
              )"
begin

definition holds_for_n :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula \<Rightarrow> 'var \<Rightarrow> nat \<Rightarrow> 'state \<Rightarrow> bool"
  where "holds_for_n \<phi> v N \<mu> = (
    \<exists> \<omega> . (
      fol_equal_everywhere_but (Inl v) \<mu> \<omega> \<and> (N = val2nat (state_eval \<omega> (Inl v))) \<and>
       (kat_dl.dyn_eval \<phi> \<omega>)
  ))"

text\<open>
Under the assumptions formalized above, we can then prove the validity
of the following proof rule:
\<close>

lemma dyn_axiom_C:
  fixes \<phi> :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and \<pi> :: "('atom, 'var, 'prog) kat_prog"
    and v :: "'var"
    and w :: "'var"
  assumes "\<not> (full_prog_fv_syn \<pi> (Inl v)) \<and> \<not> (kat_dl.dyn_prog_bv_sem \<pi> (Inl v))"
      and "\<not> (full_prog_fv_syn \<pi> (Inl w)) \<and> \<not> (kat_dl.dyn_prog_bv_sem \<pi> (Inl w))"
      and "\<not> (kat_dl.dyn_FV \<phi> (Inl w))"
      and "nat_var v"
      and "nat_var w"
      and "v \<noteq> w"
    shows
  "\<Turnstile>[kat_dl.dyn_eval] (
      ( \<lbrakk>((\<pi>)*)\<rbrakk> (
        \<bbbA> v . (
          (((FOL (positive_relation v)) and \<phi>)
          \<Rrightarrow>
          (\<langle> \<pi> \<rangle> (
            \<bbbA> w . (
              (FOL (plus_one_relation w v))
              \<Rrightarrow>
              (
                \<bbbA> v .(
                  (FOL (eq_relation v w))
                  \<Rrightarrow>
                  \<phi>
                )
              )
            )
          ))
        ))
      ))
    \<Rrightarrow>
    (\<bbbA> v . (
      \<phi>
      \<Rrightarrow>
      (\<langle> \<pi>* \<rangle> (\<bbbE> v.
      ( (\<rceil>(FOL (positive_relation v))) and \<phi>)
      ))
    ))
  )"
  unfolding theory_valid_def
  apply simp
  unfolding kat_dl.dyn_eval.simps
  using assms
proof (simp, intro allI)
  fix \<pi>
  fix v w :: 'var
  fix \<mu>
  assume v_assms: "\<not> full_prog_fv_syn \<pi> (Inl v) \<and> \<not> kat_dl.dyn_prog_bv_sem \<pi> (Inl v)"
  then have strong_v_assms: "\<not> full_prog_fv_syn (\<pi>*) (Inl v) \<and> \<not> kat_dl.dyn_prog_bv_sem (\<pi>*) (Inl v)"
    unfolding full_prog_fv_syn.simps
  proof (intro conjI)
    show "\<not> full_prog_fv_syn \<pi> (Inl v) \<and> \<not> kat_dl.dyn_prog_bv_sem \<pi> (Inl v) \<Longrightarrow>
    \<not> full_prog_fv_syn \<pi> (Inl v)"
      by auto
    show "\<not> full_prog_fv_syn \<pi> (Inl v) \<and> \<not> kat_dl.dyn_prog_bv_sem \<pi> (Inl v) \<Longrightarrow> \<not> kat_dl.dyn_prog_bv_sem (\<pi>*) (Inl v)"
      unfolding kat_dl.dyn_prog_bv_sem.simps
      unfolding full_prog_eval_def[of "(\<pi>*)"]
    proof -
      assume not_bv_pi: "\<not> full_prog_fv_syn \<pi> (Inl v) \<and> (\<nexists>\<mu> \<omega>. full_prog_eval \<pi> \<mu> \<omega> \<and> state_eval \<mu> (Inl v) \<noteq> state_eval \<omega> (Inl v))"
      have "\<And> N . \<nexists>\<mu> \<omega>. (full_prog_eval_int N (\<pi>*) \<mu> \<omega>) \<and>
           state_eval \<mu> (Inl v) \<noteq> state_eval \<omega> (Inl v)"
      proof -
        fix N
        show "\<nexists>\<mu> \<omega>. (full_prog_eval_int N (\<pi>*) \<mu> \<omega>) \<and>
           state_eval \<mu> (Inl v) \<noteq> state_eval \<omega> (Inl v)"
        proof (induct N)
          case 0
          then show ?case
            unfolding full_prog_eval_int.simps[of "0"]
            by simp
        next
          case (Suc N)
          then show ?case
            unfolding full_prog_eval_int.simps[of "(Suc N)"]
            apply (simp del: full_prog_eval_int.simps)
            unfolding full_prog_eval_int.simps(3)
            using not_bv_pi
            by (metis full_prog_eval_def)
        qed
      qed
      thus "\<nexists>\<mu> \<omega>. (\<exists>n. full_prog_eval_int n (\<pi>*) \<mu> \<omega>) \<and>
           state_eval \<mu> (Inl v) \<noteq> state_eval \<omega> (Inl v)"
        by blast
    qed
  qed
        
      
  assume w_assms: "\<not> full_prog_fv_syn \<pi> (Inl w) \<and> \<not> kat_dl.dyn_prog_bv_sem \<pi> (Inl w)"
  assume \<phi>_assms: "\<not> kat_dl.dyn_FV \<phi> (Inl w)"
  assume v_nat_assignable: "nat_var v"
  (*then have v_nat_assignable: "v \<in> (nat_assignable_vars state_eval val2nat)"
    using nat_assignability
    by (simp add: nat_assignable_vars_def)*)
  assume w_nat_assignable: "nat_var w"
  (*then have w_nat_assignable: "w \<in> (nat_assignable_vars state_eval val2nat)"
    using nat_assignability
    by (simp add: nat_assignable_vars_def)*)
  assume v_w_distinct: "v \<noteq> w"
  have "kat_dl.dyn_eval ( \<lbrakk>((\<pi>)*)\<rbrakk> (
        \<bbbA> v . (
          (((FOL (positive_relation v)) and \<phi>)
          \<Rrightarrow>
          (\<langle> \<pi> \<rangle> (
            \<bbbA> w . (
              (FOL (plus_one_relation w v))
              \<Rrightarrow>
              (
                \<bbbA> v .(
                  (FOL (eq_relation v w))
                  \<Rrightarrow>
                  \<phi>
                )
              )
            )
          ))
        ))
      )) \<mu> \<Longrightarrow> kat_dl.dyn_eval (\<bbbA> v . (
      \<phi>
      \<Rrightarrow>
      (\<langle> \<pi>* \<rangle> (\<bbbE> v.
      ( (\<rceil>(FOL (positive_relation v))) and \<phi>)
      ))
    )) \<mu>"
  proof -
    let ?INSIDE_FML = "(
            \<bbbA> w . (
              (FOL (plus_one_relation w v))
              \<Rrightarrow>
              (
                \<bbbA> v .(
                  (FOL (eq_relation v w))
                  \<Rrightarrow>
                  \<phi>
                )
              )
            )
          )"
    let ?REACHABLE_FML = "(\<langle> \<pi> \<rangle> ?INSIDE_FML)"
    let ?INNER_FML = "(
        \<bbbA> v . (
          (((FOL (positive_relation v)) and \<phi>)
          \<Rrightarrow>
          ?REACHABLE_FML
        ))
      )"
    let ?ASSM_FML = "\<lbrakk>((\<pi>)*)\<rbrakk> ?INNER_FML"
    have holds_for_0_implications: "\<And> \<phi> \<omega> . holds_for_n \<phi> v 0 \<omega>
                  \<Longrightarrow> (\<exists>\<omega>'. fol_equal_everywhere_but (Inl v) \<omega> \<omega>' \<and>
                          \<not> fol_eval (positive_relation v) \<omega>' \<and> kat_dl.dyn_eval \<phi> \<omega>')"
      unfolding holds_for_n_def
      using positive_sound
      using v_nat_assignable
      by auto

    assume "kat_dl.dyn_eval (?ASSM_FML) \<mu>"
    then have assm_outer_all_quantified: "kat_dl.dyn_eval (\<bbbA> v . ?ASSM_FML) \<mu>"
      using kat_dl.dyn_hilbert_axiom_7[of ?ASSM_FML v]
      using v_assms
      by (meson kat_dl.dyn_FV.simps(4) kat_dl.dyn_FV.simps(5) kat_dl.dyn_FV_fml_sound kat_dl.dyn_eval.simps(4) kat_dl.dyn_fv_sem.elims(3) strong_v_assms)

    then have inductive_reformulation:
        "\<And> N \<omega> \<nu> .
          fol_equal_everywhere_but (Inl v) \<mu> \<omega> \<Longrightarrow>
          holds_for_n \<phi> v (Suc N) \<nu> \<Longrightarrow>
          full_prog_eval (\<pi>*) \<omega> \<nu> \<Longrightarrow>
            (\<exists> s1 . full_prog_eval \<pi> \<nu> s1 \<and> holds_for_n \<phi> v N s1)"
    proof -
      fix N \<omega> \<nu>
      assume \<nu>_reachable: "full_prog_eval (\<pi>*) \<omega> \<nu>"
      assume "fol_equal_everywhere_but (Inl v) \<mu> \<omega>"
      then have "kat_dl.dyn_eval (?ASSM_FML) \<omega>"
        using assm_outer_all_quantified
        using kat_dl.dyn_eval.simps(4) by blast
      then have \<nu>_sat: "kat_dl.dyn_eval (?INNER_FML) \<nu>"
        using \<nu>_reachable
        using kat_dl.dyn_eval.simps(5) by blast
      assume "holds_for_n \<phi> v (Suc N) \<nu>"
      then obtain \<nu>1 where \<nu>1_cond: "fol_equal_everywhere_but (Inl v) \<nu> \<nu>1 \<and> ((Suc N) = val2nat (state_eval \<nu>1 (Inl v))) \<and>
       (kat_dl.dyn_eval \<phi> \<nu>1)"
        unfolding holds_for_n_def by blast
      then have "kat_dl.dyn_eval ((FOL (positive_relation v)) and \<phi>) \<nu>1"
        using positive_sound
        using v_nat_assignable
        by simp
      then have "kat_dl.dyn_eval ?REACHABLE_FML \<nu>1"
        using \<nu>_sat
        using \<nu>1_cond
        by simp
      then obtain \<nu>2 where \<nu>2_cond: "full_prog_eval \<pi> \<nu>1 \<nu>2 \<and> kat_dl.dyn_eval ?INSIDE_FML \<nu>2"
        using kat_dl.DIAMOND_def by fastforce

      have plus_sound_v_w: "(\<forall>\<mu>. dyn_eval (FOL (plus_one_relation w v)) \<mu> =
             (val2nat (state_eval \<mu> (Inl v)) = (val2nat (state_eval \<mu> (Inl w))) + 1))"
        using plus_one_sound
        using v_nat_assignable w_nat_assignable v_w_distinct
        by presburger
      have eq_sound_v_w: "(\<forall>\<mu>. dyn_eval (FOL (eq_relation v w)) \<mu> =
             (val2nat (state_eval \<mu> (Inl w)) = val2nat (state_eval \<mu> (Inl v))))"
        using eq_sound
        using v_nat_assignable w_nat_assignable v_w_distinct
        by presburger

      have \<nu>2_Suc_N: "((Suc N) = val2nat (state_eval \<nu>2 (Inl v)))"
        using \<nu>1_cond \<nu>2_cond
        using v_assms
        unfolding kat_dl.dyn_prog_bv_sem.simps
        by metis
      then have \<nu>2_N_\<phi>_sat: "holds_for_n \<phi> v N \<nu>2"
        unfolding holds_for_n_def
        using \<nu>2_cond
        unfolding kat_dl.IMP_def
        unfolding kat_dl.dyn_eval.simps
        using plus_sound_v_w
        using eq_sound_v_w
      proof simp
        assume resolved_assm: "full_prog_eval \<pi> \<nu>1 \<nu>2 \<and>
                (\<forall>\<omega>. fol_equal_everywhere_but (Inl w) \<nu>2 \<omega> \<longrightarrow>
                      (val2nat (state_eval \<omega> (Inl v))) = Suc (val2nat (state_eval \<omega> (Inl w))) \<longrightarrow>
                      (\<forall>\<omega>'. val2nat (state_eval \<omega>' (Inl w)) = val2nat (state_eval \<omega>' (Inl v)) \<longrightarrow>
                             fol_equal_everywhere_but (Inl v) \<omega> \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>'))"
        obtain \<omega>1_pre where \<omega>1_pre_cond: "((val2nat (state_eval \<nu>2 (Inl v))) = Suc (val2nat (state_eval \<omega>1_pre (Inl w))))"
          using w_nat_assignable
          using nat_assignability
          by (metis \<nu>2_Suc_N is_nat_assignable_def)
        then obtain \<omega>1 where \<omega>1_cond: "\<forall> x . ((x \<in> {y . y = (Inl w)} \<longrightarrow> (state_eval \<omega>1_pre (Inl w)) = (state_eval \<omega>1 (Inl w))) \<and>
                                        (x \<notin> {y . y = (Inl w)} \<longrightarrow> (state_eval \<nu>2 x) = (state_eval \<omega>1 x)))"
          using state_space_convexity
          by (metis insert_iff singleton_conv)
        then have resolved_inner_asm: "(\<forall>\<omega>'. val2nat (state_eval \<omega>' (Inl w)) = val2nat (state_eval \<omega>' (Inl v)) \<longrightarrow>
                             fol_equal_everywhere_but (Inl v) \<omega>1 \<omega>' \<longrightarrow> kat_dl.dyn_eval \<phi> \<omega>')"
          using resolved_assm
          using \<open>(val2nat (state_eval \<nu>2 (Inl v))) = Suc (val2nat (state_eval \<omega>1_pre (Inl w)))\<close> fol_equal_everywhere_but_def fol_states_agree_on_def v_w_distinct by fastforce
        have \<omega>1_N: "N = val2nat (state_eval \<omega>1 (Inl w))"
          using \<nu>2_Suc_N
          using \<omega>1_cond \<omega>1_pre_cond
          by force
        obtain \<omega>2_pre where \<omega>2_pre_cond: "(val2nat (state_eval \<omega>1 (Inl w))) = val2nat (state_eval \<omega>2_pre (Inl v))"
          using w_nat_assignable v_nat_assignable
          using nat_assignability
          by (metis is_nat_assignable_def)
        then obtain \<omega>2 where \<omega>2_cond: "\<forall> x . ((x \<in> {y . y = (Inl v)} \<longrightarrow> (state_eval \<omega>2_pre x) = (state_eval \<omega>2 x)) \<and>
                                        (x \<notin> {y . y = (Inl v)} \<longrightarrow> (state_eval \<omega>1 x) = (state_eval \<omega>2 x)))"
          using state_space_convexity
          by metis
        then have \<omega>2_w_v_eq: "val2nat (state_eval \<omega>2 (Inl w)) = val2nat (state_eval \<omega>2 (Inl v))"
          using \<omega>2_pre_cond
          using v_w_distinct by auto
        then have \<omega>2_sat: "kat_dl.dyn_eval \<phi> \<omega>2"
          using resolved_inner_asm \<omega>2_cond
          by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def)
        then obtain \<omega>3 where \<omega>3_cond: "\<forall> x . ((x \<in> {y . y = (Inl w)} \<longrightarrow> (state_eval \<nu>2 x) = (state_eval \<omega>3 x)) \<and>
                                        (x \<notin> {y . y = (Inl w)} \<longrightarrow> (state_eval \<omega>2 x) = (state_eval \<omega>3 x)))"
          using state_space_convexity
          by metis
        then have "fol_states_agree_on (kat_dl.dyn_FV \<phi>) \<omega>2 \<omega>3"
          using \<phi>_assms
          using fol_states_agree_on_def by auto
        then have final_statement1: "kat_dl.dyn_eval \<phi> \<omega>3"
          using \<omega>2_sat
          using kat_dl.dyn_FV_coincidence kat_dl.dyn_FV_mirror_state_def by blast
        have "(\<forall> x . x \<noteq> (Inl w) \<longrightarrow> (state_eval \<omega>3 x) = (state_eval \<omega>2 x)) \<and>
              (\<forall> x . x \<noteq> (Inl v) \<longrightarrow> (state_eval \<omega>2 x) = (state_eval \<omega>1 x)) \<and>
              (\<forall> x . x \<noteq> (Inl w) \<longrightarrow> (state_eval \<omega>1 x) = (state_eval \<nu>2 x)) \<and>
              (\<forall> x . x = (Inl w) \<longrightarrow> (state_eval \<omega>3 x) = (state_eval \<nu>2 x))"
          apply (intro conjI)
          using \<omega>3_cond
           apply simp
          using \<omega>2_cond
           apply simp
          using \<omega>1_cond
          apply simp
          using \<omega>3_cond
          by simp
        then have final_statement2: "fol_equal_everywhere_but (Inl v) \<nu>2 \<omega>3"
          unfolding fol_equal_everywhere_but_def
          unfolding fol_states_agree_on_def
          by metis
        have final_statement3: "N = val2nat (state_eval \<omega>3 (Inl v))"
          using \<omega>3_cond \<omega>2_w_v_eq
          using v_w_distinct
          by (simp add: \<omega>1_N \<open>(\<forall>x. x \<noteq> (Inl w) \<longrightarrow> state_eval \<omega>3 x = state_eval \<omega>2 x) \<and> (\<forall>x. x \<noteq> (Inl v) \<longrightarrow> state_eval \<omega>2 x = state_eval \<omega>1 x) \<and> (\<forall>x. x \<noteq> (Inl w) \<longrightarrow> state_eval \<omega>1 x = state_eval \<nu>2 x) \<and> (\<forall>x. x = (Inl w) \<longrightarrow> state_eval \<omega>3 x = state_eval \<nu>2 x)\<close>)

        show "\<exists>\<omega>. fol_equal_everywhere_but (Inl v) \<nu>2 \<omega> \<and> N = val2nat (state_eval \<omega> (Inl v)) \<and> kat_dl.dyn_eval \<phi> \<omega>"
          apply (intro exI[of _ \<omega>3])
          using final_statement1 final_statement2 final_statement3
          by simp
      qed

      let ?V1 = "(\<lambda> x . x \<noteq> (Inl v))"
      let ?V2 = "(\<lambda> x . x = (Inl v))"
      have "fol_states_agree_on ?V1 \<nu>1 \<nu>"
        using \<nu>1_cond
        using v_assms
        unfolding fol_states_agree_on_def
        using fol_equal_everywhere_but_def fol_states_agree_on_def by fastforce
      then have "\<exists>\<omega>2. full_prog_eval \<pi> \<nu> \<omega>2 \<and> fol_equal_everywhere_but (Inl v) \<nu>2 \<omega>2"
        using \<nu>2_cond
        using kat_dl.dyn_prog_fv_sem_coincidence[of \<pi> \<nu>1 \<nu>2 ?V1 \<nu> ?V2]
        using v_assms
        unfolding fol_equal_everywhere_but_def
        by (metis (mono_tags, lifting) kat_dl.prog_fv_overapprox)
      then obtain \<nu>2_par where \<nu>2_par_cond: "full_prog_eval \<pi> \<nu> \<nu>2_par \<and> fol_equal_everywhere_but (Inl v) \<nu>2 \<nu>2_par"
        by blast
      then have "holds_for_n \<phi> v N \<nu>2_par"
        using \<nu>2_N_\<phi>_sat
        unfolding holds_for_n_def
        by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def)

      thus "\<exists>s1. full_prog_eval \<pi> \<nu> s1 \<and> holds_for_n \<phi> v N s1"
        using \<nu>2_par_cond 
        by (intro exI[of _ \<nu>2_par],simp)
    qed

    show "kat_dl.dyn_eval (\<bbbA> v . (
      \<phi>
      \<Rrightarrow>
      (\<langle> \<pi>* \<rangle> (\<bbbE> v.
      ( (\<rceil>(FOL (positive_relation v))) and \<phi>)
      ))
    )) \<mu>"
      unfolding kat_dl.IMP_def
      unfolding kat_dl.dyn_eval.simps
    proof (simp, intro allI, intro impI)
      fix \<omega>
      assume \<mu>_\<omega>_trans: "fol_equal_everywhere_but (Inl v) \<mu> \<omega>"

      have inductive_argument: "\<And> N \<nu> .
          full_prog_eval (\<pi>*) \<omega> \<nu> \<Longrightarrow>
          holds_for_n \<phi> v N \<nu> \<Longrightarrow>
          \<exists>\<omega>F. (full_prog_eval (\<pi>*) \<nu> \<omega>F) \<and> holds_for_n \<phi> v 0 \<omega>F"
      proof -
        fix N
        show "\<And> \<nu> . full_prog_eval (\<pi>*) \<omega> \<nu> \<Longrightarrow> holds_for_n \<phi> v N \<nu> \<Longrightarrow> \<exists>\<omega>F. (full_prog_eval (\<pi>*) \<nu> \<omega>F) \<and> holds_for_n \<phi> v 0 \<omega>F"
        proof (induct N)
          case 0
          then show ?case
            unfolding full_prog_eval_def
            by (metis full_prog_eval_int.simps(5))
        next
          case (Suc N)
          then show ?case
          proof -
            fix \<nu>
            assume ind_hyp: "(\<And>\<nu>. full_prog_eval (\<pi>*) \<omega> \<nu> \<Longrightarrow> holds_for_n \<phi> v N \<nu> \<Longrightarrow> \<exists>\<omega>F. full_prog_eval (\<pi>*) \<nu> \<omega>F \<and> holds_for_n \<phi> v 0 \<omega>F)"
            assume \<nu>_reachable: "full_prog_eval (\<pi>*) \<omega> \<nu>"
            assume \<phi>_sat_for_SucN: "holds_for_n \<phi> v (Suc N) \<nu>"

            have "\<exists>\<omega>F. (full_prog_eval (\<pi>;(\<pi>*)) \<nu> \<omega>F  \<and>
                          holds_for_n \<phi> v 0 \<omega>F)"
              unfolding full_prog_eval_def
              unfolding full_prog_eval_int.simps(3)
            proof-
              obtain s1 where s1_cond: "full_prog_eval \<pi> \<nu> s1 \<and>
                               holds_for_n \<phi> v N s1"
                using \<phi>_sat_for_SucN
                using \<nu>_reachable
                using inductive_reformulation
                using \<mu>_\<omega>_trans
                by blast
              have "full_prog_eval (\<pi>*) \<omega> s1"
                using s1_cond
                using \<nu>_reachable
                using full_prog_eval_def loop_concat by blast
              then obtain s2 where s2_cond: "full_prog_eval (\<pi>*) s1 s2 \<and>
                                    holds_for_n \<phi> v 0 s2"
                using s1_cond
                using ind_hyp[of s1]
                using Suc_eq_plus1 by presburger

              show "\<exists>\<omega>F. (\<exists>n s1. full_prog_eval_int n \<pi> \<nu> s1 \<and> full_prog_eval_int n (\<pi>*) s1 \<omega>F) \<and>
                      holds_for_n \<phi> v 0 \<omega>F"
                apply (intro exI[of _ s2], intro conjI)
                using s1_cond s2_cond
                unfolding full_prog_eval_def
                using full_prog_eval_int_n_monotone
                 apply (meson linorder_linear)
                  using s2_cond
                  by simp
              qed
    

              thus "\<exists>\<omega>F. full_prog_eval (\<pi>*) \<nu> \<omega>F \<and> holds_for_n \<phi> v 0 \<omega>F"
                unfolding full_prog_eval_def
                using full_prog_eval_int.simps(5)
                by (metis diff_Suc_1 zero_less_Suc)
          qed
        qed
      qed
    
      assume \<omega>_\<phi>_sat: "kat_dl.dyn_eval \<phi> \<omega>"
      obtain N where "N = val2nat (state_eval \<omega> (Inl v))" by blast
      then have "holds_for_n \<phi> v N \<omega>"
        unfolding holds_for_n_def
        using \<omega>_\<phi>_sat
        using fol_equal_everywhere_but_def fol_states_agree_on_def by blast
      then have "\<exists> \<omega>F . full_prog_eval ((\<pi>)*) \<omega> \<omega>F \<and> holds_for_n \<phi> v 0 \<omega>F"
        unfolding full_prog_eval_def
        using inductive_argument[of \<omega> N]
        unfolding full_prog_eval_def
        by (metis full_prog_eval_int.simps(5) zero_less_one)

      thus "kat_dl.dyn_eval (\<langle> \<pi>* \<rangle> \<rceil> \<bbbA> v . \<rceil> (\<rceil> FOL (positive_relation v) and \<phi>)) \<omega>"
        unfolding kat_dl.DIAMOND_def
        unfolding kat_dl.dyn_eval.simps
        apply (simp del: full_prog_eval_int.simps)
        using holds_for_0_implications
        by blast
    qed
  qed

  thus "(\<exists>\<omega>. full_prog_eval (\<pi>*) \<mu> \<omega> \<and>
              (\<exists>\<omega>'. fol_equal_everywhere_but (Inl v) \<omega> \<omega>' \<and>
                     kat_dl.dyn_eval \<phi> \<omega>' \<and>
                     fol_eval (positive_relation v) \<omega>' \<and>
                     \<not> kat_dl.dyn_eval
                         (\<langle> \<pi> \<rangle> \<bbbA> w . \<rceil> (FOL (plus_one_relation w v) and
   \<rceil> \<bbbA> v . \<rceil> (FOL (eq_relation v w) and \<rceil> \<phi>)))
                         \<omega>')) \<or>
         (\<forall>\<omega>. kat_dl.dyn_eval \<phi> \<omega> \<longrightarrow>
               fol_equal_everywhere_but (Inl v) \<mu> \<omega> \<longrightarrow>
               kat_dl.dyn_eval
                (\<langle> \<pi>* \<rangle> \<rceil> \<bbbA> v . \<rceil> (\<rceil> FOL (positive_relation v) and \<phi>)) \<omega>)"
    apply simp
    unfolding kat_dl.dyn_eval.simps
    by blast
  qed

end

end