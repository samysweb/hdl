theory DifferentialDL
  imports
    Main
    "Heterogeneous_Dynamic_Logic.DynamicLogic"
    Differential_Dynamic_Logic.Differential_Dynamic_Logic
begin

context ids begin
(* ('a::finite, 'b::finite, 'c::finite) interp) *)

type_synonym ('a, 'b, 'c) dl_state = "('a, 'b, 'c) interp * ('c state)"
type_synonym ('a, 'b, 'c) dl_var = "((('a + 'b + 'c) + ('c + 'c)))"
type_synonym ('a, 'b, 'c) dl_val = "((('c Rvec \<Rightarrow> real) + ('c state set \<Rightarrow> 'c state set) + ( ('c Rvec \<Rightarrow> bool) * (('c state * 'c state) set) * ('c simple_state \<Rightarrow> 'c simple_state) * ('c set) )) + real)"

datatype ('a, 'b, 'c) dl_atom = 
  AGeq "('a, 'c) trm" "('a, 'c) trm"
  | AProp 'c "'c \<Rightarrow> ('a, 'c) trm" 

fun dl_atom2formula :: "('a, 'b, 'c) dl_atom \<Rightarrow> ('a, 'b, 'c) formula"
  where
    "dl_atom2formula (AGeq t1 t2) = (Geq t1 t2)"
  | "dl_atom2formula (AProp x y) = (Prop x y)"

fun dl_atom_eval :: "('a::finite, 'b::finite, 'c::finite) dl_atom \<Rightarrow> ('a, 'b, 'c) dl_state => bool"
  where "dl_atom_eval a (I,\<mu>) = (\<mu> \<in> (fml_sem I (dl_atom2formula a)))"

fun dl_atom_fv :: "('a::finite, 'b::finite, 'c::finite) dl_atom \<Rightarrow> ('a,'b,'c) dl_var \<Rightarrow> bool"
  where
    "dl_atom_fv a (Inr v) = ((\<not>fsafe (dl_atom2formula a)) \<or> (v \<in> (FVF (dl_atom2formula a))))"
  | "dl_atom_fv a (Inl v) = ((\<not>fsafe (dl_atom2formula a)) \<or> (v \<in> (SIGF (dl_atom2formula a))))"

fun dl_state_eval :: "('a::finite, 'b::finite, 'c::finite) dl_state => ('a,'b,'c) dl_var  \<Rightarrow> ('a, 'b, 'c) dl_val"
  where
    "dl_state_eval (I, \<mu>) (Inr (Inl v)) = (Inr ((fst \<mu>) $ v))"
  | "dl_state_eval (I, \<mu>) (Inr (Inr v)) = (Inr ((snd \<mu>) $ v))"
  | "dl_state_eval (I, \<mu>) (Inl (Inl v)) = (Inl (Inl (Functions I v)))"
  | "dl_state_eval (I, \<mu>) (Inl (Inr (Inl v))) = (Inl (Inr (Inl (Contexts I v))))"
  | "dl_state_eval (I, \<mu>) (Inl (Inr (Inr v))) = (Inl (Inr (Inr (
    Predicates I v, Programs I v, ODEs I v, ODEBV I v
  ))))"

fun dl_prog_fv :: "('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('a,'b,'c) dl_var \<Rightarrow> bool"
  where
    "dl_prog_fv \<pi> (Inr v) = ((\<not>hpsafe \<pi>) \<or> (v \<in> (FVP \<pi>)))"
  | "dl_prog_fv \<pi> (Inl v) = ((\<not>hpsafe \<pi>) \<or> (v \<in> (SIGP \<pi>)))"

definition dl_prog_eval :: "('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('a, 'b, 'c) dl_state \<Rightarrow> ('a, 'b, 'c) dl_state \<Rightarrow> bool"
  where
    "dl_prog_eval \<pi> s1 s2 = (((fst s1)=(fst s2)) \<and> ((snd s1,snd s2) \<in> (prog_sem (fst s1) \<pi>)))"

fun dl_prog_bv ::  "('a::finite, 'b::finite, 'c::finite) hp \<Rightarrow> ('a,'b,'c) dl_var \<Rightarrow> bool"
  where
    "dl_prog_bv \<pi> (Inl v) = False"
  | "dl_prog_bv \<pi> (Inr v) = ((\<not>hpsafe \<pi>) \<or> (v \<in> BVP \<pi>))"

lemma state_extensionality:
  assumes "\<forall>v. dl_state_eval s1 v = dl_state_eval s2 v"
  shows "s1=s2"
proof -
  obtain I where I_cond: "I = fst s1" by blast
  obtain \<mu> where \<mu>_cond: "\<mu> = snd s1" by blast
  obtain J where J_cond: "J = fst s2" by blast
  obtain \<omega> where \<omega>_cond: "\<omega> = snd s2" by blast
  
  have all_eq1: "\<forall>v. dl_state_eval (I,\<mu>) v = dl_state_eval (J,\<omega>) v"
    using I_cond \<mu>_cond J_cond \<omega>_cond assms
    by force
  have all_eq2: "\<forall>v. dl_state_eval (I,\<mu>) v = dl_state_eval (J,\<omega>) v"
    using I_cond \<mu>_cond J_cond \<omega>_cond assms
    by force
  have state_equiv: "\<mu> = \<omega>"
  proof -
    have all_eq_1_1:
      "(\<forall>v. dl_state_eval (I, \<mu>) (Inr (Inl v)) = dl_state_eval (J, \<omega>) (Inr (Inl v)))"
      using all_eq1 by blast
    have all_eq_1_2:
      "(\<forall>v. dl_state_eval (I, \<mu>) (Inr (Inr v)) = dl_state_eval (J, \<omega>) (Inr (Inr v)))"
      using all_eq1 by blast
    thus "\<mu> = \<omega>"
      using all_eq_1_1 all_eq_1_2
      unfolding dl_state_eval.simps
      by (simp add: prod_eqI vec_eq_iff)
  qed
  have interp_eq: "I = J"
  proof -
    have "(\<forall>v. dl_state_eval (I, \<mu>) (Inl (Inl v)) = dl_state_eval (J, \<omega>) (Inl (Inl v)))"
      using all_eq2 by blast
    then have all_eq_2_1: "Functions I = Functions J"
      unfolding dl_state_eval.simps
      apply simp
      by presburger 
    have
      "(\<forall>v. dl_state_eval (I, \<mu>) (Inl (Inr (Inl v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inl v))))"
      using all_eq2 by blast
    then have all_eq_2_2_2: "Contexts I = Contexts J"
      unfolding dl_state_eval.simps
      apply simp
      by presburger 
    have
      "(\<forall>v. dl_state_eval (I, \<mu>) (Inl (Inr (Inr v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inr v))))"
      using all_eq2 by blast
    then have all_eq_2_2_1: "Predicates I = Predicates J \<and> Programs I = Programs J \<and> ODEs I = ODEs J \<and> ODEBV I = ODEBV J"
      unfolding dl_state_eval.simps
      apply simp
      by presburger 
    thus "I = J"
      using all_eq_2_1 all_eq_2_2_1 all_eq_2_2_2
      unfolding dl_state_eval.simps
      by simp
  qed
  thus "s1=s2"
    using state_equiv
    using I_cond \<mu>_cond J_cond \<omega>_cond
    using prod_eqI by blast
qed


interpretation dl_fol_core :
  folCore "dl_atom_eval" dl_atom_fv "dl_state_eval"
proof
  show "\<And>a. finite (Collect (dl_atom_fv a))"
    by simp

  show "\<And> (a :: ('a, 'b, 'c) dl_atom) (s1 :: ('a,'b,'c) dl_state) (s2 :: ('a,'b,'c) dl_state).
       fol_states_agree_on_gen (dl_state_eval) (dl_atom_fv a) s1 s2 \<Longrightarrow>
       dl_atom_eval a s1 = dl_atom_eval a s2"
    unfolding fol_states_agree_on_gen_def
    unfolding dl_atom_eval.simps
  proof -
    fix a :: "('a, 'b, 'c) dl_atom"
    fix s1 :: "('a,'b,'c) dl_state"
    fix s2 :: "('a,'b,'c) dl_state"

    obtain I where split_cond1: "I = fst s1" by blast
    obtain J where split_cond2: "J = fst s2" by blast
    obtain \<mu> where split_cond3: "\<mu> = snd s1" by blast
    obtain \<omega> where split_cond4: "\<omega> = snd s2" by blast

    have  "\<forall>v. dl_atom_fv a v \<longrightarrow> dl_state_eval (I,\<mu>) v = dl_state_eval (J,\<omega>) v \<Longrightarrow>
       dl_atom_eval a (I,\<mu>) = dl_atom_eval a (J,\<omega>)"
    proof (induct a)
      case (AGeq x1 x2)
      then show ?case
        unfolding dl_atom_eval.simps
        unfolding dl_atom2formula.simps
      proof -
        have Iagreement: "Iagree I I (SIGF (Geq x1 x2))"
          using Iagree_refl by blast
        assume state_eq: "\<forall>v. dl_atom_fv (AGeq x1 x2) v \<longrightarrow>
          dl_state_eval (I, \<mu>) v = dl_state_eval (J, \<omega>) v"
        then have state_eq_1: "\<forall>v. dl_atom_fv (AGeq x1 x2) (Inr v) \<longrightarrow>
          dl_state_eval (I, \<mu>) (Inr v) = dl_state_eval (J, \<omega>) (Inr v)"
          by force
        have state_eq_1_1:
            "(\<forall>v. dl_atom_fv (AGeq x1 x2) (Inr (Inl v)) \<longrightarrow>
              dl_state_eval (I, \<mu>) (Inr (Inl v)) = dl_state_eval (J, \<omega>) (Inr (Inl v)))"
          using state_eq_1 by blast
        have state_eq_1_2:
            "(\<forall>v. dl_atom_fv (AGeq x1 x2) (Inr (Inr v)) \<longrightarrow>
              dl_state_eval (I, \<mu>) (Inr (Inr v)) = dl_state_eval (J, \<omega>) (Inr (Inr v)))"
          using state_eq_1 by blast
        have state_eq_2: "\<forall>v. dl_atom_fv (AGeq x1 x2) (Inl v) \<longrightarrow>
          dl_state_eval (I, \<mu>) (Inl v) = dl_state_eval (J, \<omega>) (Inl v)"
          using state_eq by force
        have agreement: "Vagree \<mu> \<omega> (FVF (Geq x1 x2))"
          unfolding Vagree_def
          using state_eq_1_1 state_eq_1_2
          unfolding dl_atom_fv.simps
          unfolding dl_state_eval.simps
          unfolding dl_atom2formula.simps
          by simp          
        show "(\<mu> \<in> fml_sem I (Geq x1 x2)) = (\<omega> \<in> fml_sem J (Geq x1 x2))"
        proof (cases "fsafe (Geq x1 x2)")
          case True
          then show ?thesis
          proof -

              have Iagreement: "Iagree I J (SIGF (Geq x1 x2))"
                using state_eq_2
                unfolding Iagree_def
                unfolding dl_atom_fv.simps
                unfolding dl_atom2formula.simps
                using True
              proof (intro ballI, intro conjI)
                fix i :: "('a + 'b + 'c)"
                assume i_in_SIGF: "i \<in> SIGF (Geq x1 x2)"
                have "\<forall>v. (Inl v) \<in> SIGF (dl_atom2formula (AGeq x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inl v)) = dl_state_eval (J, \<omega>) (Inl (Inl v))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  by fastforce
                thus "\<forall>x. i = Inl x \<longrightarrow> Functions I x = Functions J x"
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                have "\<forall>v. (Inr (Inl v)) \<in> SIGF (dl_atom2formula (AGeq x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inr (Inl v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inl v)))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  by fastforce
                thus "\<forall>x. i = (Inr (Inl x)) \<longrightarrow> Contexts I x = Contexts J x"
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                have third_case: "\<forall>v. (Inr (Inr v)) \<in> SIGF (dl_atom2formula (AGeq x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inr (Inr v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inr v)))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  by fastforce

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Predicates I x = Predicates J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Programs I x = Programs J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEs I x = ODEs J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEBV I x = ODEBV J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto
              qed
          
            show ?thesis
              using Coincidence.ids.coincidence_formula[of vid1 vid2 vid3 fid1 fid2 fid3 pid1 pid2 pid3 pid4 "(Geq x1 x2)" I J \<mu> \<omega>]
              using ids_axioms
              using agreement Iagreement
              using True
              by simp
          qed
          next
          case False
          then show ?thesis
            using state_extensionality[of "(I, \<mu>)"]
            using state_eq
            using False
            by (metis dl_atom2formula.simps(1) dl_atom_fv.elims(3) fsafe_Geq_simps prod.exhaust_sel split_cond1 split_cond2 split_cond3 split_cond4)
        qed
      qed
    next
      case (AProp x1 x2)then show ?case
        unfolding dl_atom_eval.simps
        unfolding dl_atom2formula.simps
      proof -
        have Iagreement: "Iagree I I (SIGF (Prop x1 x2))"
          using Iagree_refl by blast
        assume state_eq: "\<forall>v. dl_atom_fv (AProp x1 x2) v \<longrightarrow>
          dl_state_eval (I, \<mu>) v = dl_state_eval (J, \<omega>) v"
        then have state_eq_1: "\<forall>v. dl_atom_fv (AProp x1 x2) (Inr v) \<longrightarrow>
          dl_state_eval (I, \<mu>) (Inr v) = dl_state_eval (J, \<omega>) (Inr v)"
          by force
        have state_eq_1_1:
            "(\<forall>v. dl_atom_fv (AProp x1 x2) (Inr (Inl v)) \<longrightarrow>
              dl_state_eval (I, \<mu>) (Inr (Inl v)) = dl_state_eval (J, \<omega>) (Inr (Inl v)))"
          using state_eq_1 by blast
        have state_eq_1_2:
            "(\<forall>v. dl_atom_fv (AProp x1 x2) (Inr (Inr v)) \<longrightarrow>
              dl_state_eval (I, \<mu>) (Inr (Inr v)) = dl_state_eval (J, \<omega>) (Inr (Inr v)))"
          using state_eq_1 by blast
        have state_eq_2: "\<forall>v. dl_atom_fv (AProp x1 x2) (Inl v) \<longrightarrow>
          dl_state_eval (I, \<mu>) (Inl v) = dl_state_eval (J, \<omega>) (Inl v)"
          using state_eq by force
        have agreement: "Vagree \<mu> \<omega> (FVF (Prop x1 x2))"
          unfolding Vagree_def
          using state_eq_1_1 state_eq_1_2
          unfolding dl_atom_fv.simps
          unfolding dl_state_eval.simps
          unfolding dl_atom2formula.simps
          by simp          
        show "(\<mu> \<in> fml_sem I (Prop x1 x2)) = (\<omega> \<in> fml_sem J (Prop x1 x2))"
        proof (cases "fsafe (Prop x1 x2)")
          case True
          then show ?thesis
          proof -

              have Iagreement: "Iagree I J (SIGF (Prop x1 x2))"
                using state_eq_2
                unfolding Iagree_def
                unfolding dl_atom_fv.simps
                unfolding dl_atom2formula.simps
                using True
              proof (intro ballI, intro conjI)
                fix i :: "('a + 'b + 'c)"
                assume i_in_SIGF: "i \<in> SIGF (Prop x1 x2)"
                have "\<forall>v. (Inl v) \<in> SIGF (dl_atom2formula (AProp x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inl v)) = dl_state_eval (J, \<omega>) (Inl (Inl v))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  unfolding dl_atom2formula.simps
                proof (intro allI,intro impI)
                  fix v
                  show "\<forall>v. \<not> fsafe ($\<phi> x1 x2) \<or> v \<in> SIGF ($\<phi> x1 x2) \<longrightarrow>
                             dl_state_eval (I, \<mu>) (Inl v) =
                             dl_state_eval (J, \<omega>) (Inl v) \<Longrightarrow>
                         Inl v \<in> SIGF ($\<phi> x1 x2) \<Longrightarrow>
                         dl_state_eval (I, \<mu>) (Inl (Inl v)) =
                         dl_state_eval (J, \<omega>) (Inl (Inl v))"
                    apply (erule allE[of _ "(Inl v)"])
                    apply (erule impE)
                     apply simp
                    by simp
                qed
                thus "\<forall>x. i = Inl x \<longrightarrow> Functions I x = Functions J x"
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                have "\<forall>v. (Inr (Inl v)) \<in> SIGF (dl_atom2formula (AProp x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inr (Inl v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inl v)))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  by fastforce
                thus "\<forall>x. i = (Inr (Inl x)) \<longrightarrow> Contexts I x = Contexts J x"
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                have third_case: "\<forall>v. (Inr (Inr v)) \<in> SIGF (dl_atom2formula (AProp x1 x2)) \<longrightarrow>
        dl_state_eval (I, \<mu>) (Inl (Inr (Inr v))) = dl_state_eval (J, \<omega>) (Inl (Inr (Inr v)))"
                  using state_eq_2
                  unfolding dl_atom_fv.simps
                  by fastforce

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Predicates I x = Predicates J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Programs I x = Programs J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEs I x = ODEs J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto

                show "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEBV I x = ODEBV J x"
                  using third_case
                  unfolding dl_atom_fv.simps
                  using True
                  unfolding dl_state_eval.simps
                  using i_in_SIGF
                  by auto
              qed
          
              show ?thesis
                using Coincidence.ids.coincidence_formula[of vid1 vid2 vid3 fid1 fid2 fid3 pid1 pid2 pid3 pid4 "(Prop x1 x2)" I J \<mu> \<omega>]
                using ids_axioms
                using agreement Iagreement
                using True
                by simp
            qed
          next
          case False
          then show ?thesis
            using state_extensionality[of "(I, \<mu>)" "(J,\<omega>)"]
            using state_eq
            using False
            by (metis dl_atom2formula.simps(2) dl_atom_fv.elims(3) fsafe_Prop_simps prod.exhaust_sel split_cond1 split_cond2 split_cond3 split_cond4)
        qed
      qed
    qed
    thus "\<forall>v. dl_atom_fv a v \<longrightarrow> dl_state_eval s1 v = dl_state_eval s2 v \<Longrightarrow>
       dl_atom_eval a s1 = dl_atom_eval a s2"
      using  split_cond1 split_cond2 split_cond3 split_cond4
      by auto
  qed
  show "\<forall> (s1::('a,'b,'c) dl_state) (s2::('a,'b,'c) dl_state) V.
       \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval s2 v) \<and>
               (v \<notin> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval s1 v)"
  proof (intro allI)
    fix s1 :: "('a,'b,'c) dl_state"
    fix s2 :: "('a,'b,'c) dl_state"
    fix V :: "(('a, 'b, 'c) dl_var) set"
    obtain I where I_cond: "I = fst s1" by blast
    obtain \<mu> where \<mu>_cond: "\<mu> = snd s1" by blast
    obtain J where J_cond: "J = fst s2" by blast
    obtain \<omega> where \<omega>_cond: "\<omega> = snd s2" by blast

    obtain \<mu>1 where \<mu>1_cond: "\<mu>1 = fst \<mu>" by blast
    obtain \<mu>2 where \<mu>2_cond: "\<mu>2 = snd \<mu>" by blast
    obtain \<omega>1 where \<omega>1_cond: "\<omega>1 = fst \<omega>" by blast
    obtain \<omega>2 where \<omega>2_cond: "\<omega>2 = snd \<omega>" by blast

    let ?\<nu>1 = "vec_lambda (\<lambda> v :: 'c . if ((Inr (Inl v)) \<in> V) then (\<omega>1 $ v) else (\<mu>1 $ v))"
    let ?\<nu>2 = "vec_lambda (\<lambda> v :: 'c . if ((Inr (Inr v)) \<in> V) then (\<omega>2 $ v) else (\<mu>2 $ v))"
    let ?\<nu> = "(?\<nu>1,?\<nu>2)"

    let ?Functions = "(\<lambda> v :: 'a . if ((Inl (Inl v)) \<in> V) then (Functions J v) else (Functions I v))"
    let ?Contexts = "(\<lambda> v :: 'b . if ((Inl (Inr (Inl v))) \<in> V) then (Contexts J v) else (Contexts I v))"
    let ?Predicates = "(\<lambda> v :: 'c . if ((Inl (Inr (Inr v))) \<in> V) then (Predicates J v) else (Predicates I v))"
    let ?Programs = "(\<lambda> v :: 'c . if ((Inl (Inr (Inr v))) \<in> V) then (Programs J v) else (Programs I v))"
    let ?ODEs = "(\<lambda> v :: 'c . if ((Inl (Inr (Inr v))) \<in> V) then (ODEs J v) else (ODEs I v))"
    let ?ODEBV = "(\<lambda> v :: 'c . if ((Inl (Inr (Inr v))) \<in> V) then (ODEBV J v) else (ODEBV I v))"

    define K :: "('a,'b,'c) interp" where
      K_cond: "K = \<lparr> Functions=?Functions, Predicates=?Predicates, Contexts=?Contexts, Programs=?Programs, ODEs=?ODEs, ODEBV=?ODEBV\<rparr>"
    

    have "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval (J,(\<omega>1,\<omega>2)) v) \<and>
               (v \<notin> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval (I,(\<mu>1,\<mu>2)) v)"
    proof (intro exI[where x="(K,?\<nu>)"],intro allI)
      fix v
      show "(v \<in> V \<longrightarrow> dl_state_eval (K,?\<nu>) v = dl_state_eval (J,(\<omega>1,\<omega>2)) v) \<and>
         (v \<notin> V \<longrightarrow> dl_state_eval (K,?\<nu>) v = dl_state_eval (I,(\<mu>1,\<mu>2)) v)"
      proof (induct v)
        case (Inl a)
        then show ?case
        proof (induct a)
          case (Inl a)
          then show ?case
            unfolding dl_state_eval.simps
            using K_cond
            by simp
        next
          case (Inr b)
          then show ?case
          proof (induct b)
            case (Inl a)
            then show ?case
            unfolding dl_state_eval.simps
            using K_cond
            by simp
          next
            case (Inr b)
            then show ?case
            unfolding dl_state_eval.simps
            using K_cond
            by simp
          qed
        qed
      next
        case (Inr b)
        then show ?case
        proof (induct b)
          case (Inl a)
          then show ?case
            unfolding dl_state_eval.simps
            using K_cond
            by simp
        next
          case (Inr b)
          then show ?case
            unfolding dl_state_eval.simps
            by simp
        qed
      qed
    qed

    thus "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval s2 v) \<and>
               (v \<notin> V \<longrightarrow> dl_state_eval \<nu> v = dl_state_eval s1 v)"
      using I_cond J_cond
      using \<mu>_cond \<omega>_cond
      using \<mu>1_cond \<mu>2_cond \<omega>1_cond \<omega>2_cond
      by auto
  qed
qed

interpretation dl_dyn_core :
  dynamic_theory "dl_atom_eval" dl_atom_fv "dl_state_eval" dl_prog_eval dl_prog_fv
proof
  show "\<And>\<pi>. finite (Collect (dl_prog_fv \<pi>))"
    by auto

  show "\<And>\<pi> (V::(('a,'b,'c) dl_var) \<Rightarrow> bool) s1 s2 s3.
       (\<forall>v. dl_prog_fv \<pi> v \<longrightarrow> V v) \<and>
       dl_fol_core.fol_states_agree_on V s1 s2 \<and> dl_prog_eval \<pi> s1 s3 \<longrightarrow>
       (\<exists>\<upsilon>. dl_prog_eval \<pi> s2 \<upsilon> \<and> dl_fol_core.fol_states_agree_on V s3 \<upsilon>)"
  proof (intro impI)
    fix \<pi> :: "('a,'b,'c) hp"
    fix V :: "(('a,'b,'c) dl_var) \<Rightarrow> bool"
    fix s1 :: "('a,'b,'c) dl_state"
    fix s2 :: "('a,'b,'c) dl_state"
    fix s3 :: "('a,'b,'c) dl_state"
    assume all_assms: "(\<forall>v. dl_prog_fv \<pi> v \<longrightarrow> V v) \<and>
       dl_fol_core.fol_states_agree_on V s1 s2 \<and> dl_prog_eval \<pi> s1 s3"

    then have V_superset: "(\<forall>v. dl_prog_fv \<pi> v \<longrightarrow> V v)"
      by auto

    let ?I = "fst s1"
    let ?\<mu> = "snd s1"
    let ?J = "fst s2"
    let ?\<omega> = "snd s2"
    let ?\<nu> = "snd s3"
    let ?V_all = "(Collect V)"
    let ?V_var = "{v . (Inr v) \<in> ?V_all}"

    have Iagree_1_3: "Iagree ?I (fst s3) (SIGP \<pi>)"
      using all_assms
      unfolding dl_prog_eval_def
      by (simp add: Iagree_refl)

    have states_agree: "dl_fol_core.fol_states_agree_on V (?I,?\<mu>) (?J,?\<omega>)"
      using all_assms by force

    then have coincidence_cond1: "Iagree ?I ?J (SIGP \<pi>)"
      unfolding Iagree_def
      unfolding dl_atom_fv.simps
      unfolding dl_atom2formula.simps
    proof (intro ballI, intro conjI)
      fix i :: "('a + 'b + 'c)"
      assume i_in_SIGP: "i \<in> SIGP \<pi>"

      have "\<forall>v. (Inl v) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inl v)) = dl_state_eval (?J, ?\<omega>) (Inl (Inl v))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inl x) \<longrightarrow> Functions ?I x = Functions ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto

      have "\<forall>v. (Inr (Inl v)) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inr (Inl v))) = dl_state_eval (?J, ?\<omega>) (Inl (Inr (Inl v)))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inr (Inl x)) \<longrightarrow> Contexts ?I x = Contexts ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto

      have "\<forall>v. (Inr (Inr v)) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inr (Inr v))) = dl_state_eval (?J, ?\<omega>) (Inl (Inr (Inr v)))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Predicates ?I x = Predicates ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto

      have "\<forall>v. (Inr (Inr v)) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inr (Inr v))) = dl_state_eval (?J, ?\<omega>) (Inl (Inr (Inr v)))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> Programs ?I x = Programs ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto

      have "\<forall>v. (Inr (Inr v)) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inr (Inr v))) = dl_state_eval (?J, ?\<omega>) (Inl (Inr (Inr v)))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEs ?I x = ODEs ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto

      have "\<forall>v. (Inr (Inr v)) \<in> SIGP \<pi> \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inl (Inr (Inr v))) = dl_state_eval (?J, ?\<omega>) (Inl (Inr (Inr v)))"
        using states_agree
        unfolding dl_fol_core.fol_states_agree_on_def
        using V_superset
        unfolding dl_atom_fv.simps
        by fastforce
      thus "\<forall>x. i = (Inr (Inr x)) \<longrightarrow> ODEBV ?I x = ODEBV ?J x"
        unfolding dl_atom_fv.simps
        unfolding dl_state_eval.simps
        using i_in_SIGP
        by auto
    qed

    have "\<forall>v. v \<in> ?V_var \<longrightarrow>
        dl_state_eval (?I, ?\<mu>) (Inr v) = dl_state_eval (?J, ?\<omega>) (Inr v)"
      using states_agree
      unfolding dl_fol_core.fol_states_agree_on_def
      using V_superset
      unfolding dl_atom_fv.simps
      by fastforce

    then have coincidence_cond2: "Vagree (snd s1) (snd s2) {v. Inr v \<in> Collect V}"
      using dl_state_eval.simps(1,2)
      unfolding Vagree_def
      by (metis (mono_tags, lifting) Inr_inject)
      
    have coincidence_cond3: "FVP \<pi> \<subseteq> ?V_var"
      using V_superset
      using dl_prog_fv.simps(1)
      by blast

    have coincidence_cond4: "(?\<mu>, ?\<nu>) \<in> (prog_sem ?I \<pi>)"
      using all_assms
      unfolding dl_prog_eval_def
      by auto

    have almost_coincidence: "hpsafe \<pi> \<Longrightarrow> (\<exists>\<mu>'. (?\<omega>, \<mu>') \<in> prog_sem ?J \<pi> \<and>
            Vagree ?\<nu> \<mu>' (MBV \<pi> \<union> ?V_var))"
      using coincidence_hp[of \<pi> ?I ?J ?\<mu> ?\<omega> ?V_var ?\<nu>]
      using coincidence_cond1 coincidence_cond2
      using coincidence_cond3 coincidence_cond4
      by simp

    show "(\<exists>\<upsilon>. dl_prog_eval \<pi> s2 \<upsilon> \<and> dl_fol_core.fol_states_agree_on V s3 \<upsilon>)"
    proof (cases "hpsafe \<pi>")
      case True
      then show ?thesis
      proof -
        have "(\<exists>\<mu>'. (?\<omega>, \<mu>') \<in> prog_sem ?J \<pi> \<and>
                Vagree ?\<nu> \<mu>' (MBV \<pi> \<union> ?V_var))"
          using almost_coincidence True
          by simp

        then obtain \<nu> where \<nu>_cond: "(?\<omega>, \<nu>) \<in> prog_sem ?J \<pi> \<and>
                Vagree ?\<nu> \<nu> (MBV \<pi> \<union> ?V_var)" by blast

        show "\<exists>\<upsilon>. dl_prog_eval \<pi> s2 \<upsilon> \<and> dl_fol_core.fol_states_agree_on V s3 \<upsilon>"
        proof (intro exI[where x="(?J,\<nu>)"],intro conjI)
          show has_trans: "dl_prog_eval \<pi> s2 (fst s2, \<nu>)"
            unfolding dl_prog_eval_def
            using \<nu>_cond
            by simp

          have "dl_fol_core.fol_states_agree_on V (fst s3, ?\<nu>) (fst s2, \<nu>)"
            unfolding dl_fol_core.fol_states_agree_on_def
          proof
            fix v :: "('a,'b,'c) dl_var"
            show "V v \<longrightarrow> dl_state_eval (fst s3, snd s3) v = dl_state_eval (fst s2, \<nu>) v"
            proof (induct v)
              case (Inl a)
              then show ?case
              proof (induct a)
                case (Inl a)
                then show ?case
                  unfolding dl_state_eval.simps
                  using coincidence_cond1
                  using Iagree_1_3
                  by (metis (no_types, lifting) all_assms dl_fol_core.fol_states_agree_on_def dl_prog_eval_def dl_state_eval.simps(3) surjective_pairing)
              next
                case (Inr b)
                then show ?case
                proof (induct b)
                  case (Inl a)
                  then show ?case
                  unfolding dl_state_eval.simps
                  using coincidence_cond1
                  using Iagree_1_3
                  by (metis (no_types, lifting) all_assms dl_fol_core.fol_states_agree_on_def dl_prog_eval_def dl_state_eval.simps(4) surjective_pairing)
                next
                  case (Inr b)
                  then show ?case
                  unfolding dl_state_eval.simps
                  using coincidence_cond1
                  using Iagree_1_3
                  by (metis (no_types, lifting) all_assms dl_fol_core.fol_states_agree_on_def dl_prog_eval_def dl_state_eval.simps(5) surjective_pairing)
                qed
              qed
            next
              case (Inr b)
              then show ?case
              proof (induct b)
                case (Inl a)
                then show ?case
                  unfolding dl_state_eval.simps
                  using \<nu>_cond
                  by (simp add: Vagree_def)
              next
                case (Inr b)
                then show ?case
                  unfolding dl_state_eval.simps
                  using \<nu>_cond
                  by (simp add: Vagree_def)
              qed
            qed
          qed

          thus "dl_fol_core.fol_states_agree_on V s3 (fst s2, \<nu>)"
            by simp
        qed
      qed
    next
      case False
      then show ?thesis
      proof -
        have "\<forall>v. dl_state_eval s1 v = dl_state_eval s2 v"
          using all_assms
          unfolding dl_fol_core.fol_states_agree_on_def
          using False
          by (metis dl_prog_fv.elims(3))
        then have "s1=s2"
          using state_extensionality by blast
        thus "\<exists>\<upsilon>. dl_prog_eval \<pi> s2 \<upsilon> \<and> dl_fol_core.fol_states_agree_on V s3 \<upsilon>"
          apply (intro exI[where x=s3])
          using all_assms
          using dl_fol_core.fol_states_agree_on_def by blast
      qed
    qed
  qed

  show "\<forall>\<pi> \<mu> \<omega>.
       (\<forall>v. dl_state_eval \<mu> v = dl_state_eval \<omega> v) \<longrightarrow>
       dl_prog_eval \<pi> \<mu> = dl_prog_eval \<pi> \<omega>"
    using state_extensionality
    by blast
qed

(* This proof is taken from the
Differential Dynamic Logic formalization in the AFP,
but we removed the good_interp assumption as it's not necessary *)
lemma bound_effect_generalized:
  fixes I::"('a::finite,'b::finite,'c::finite) interp"
  shows "\<And>\<nu> :: ('c) state. \<And>\<omega> ::('c) state. hpsafe \<alpha> \<Longrightarrow> (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (- (BVP \<alpha>))"
proof (induct rule: hp_induct)
  case Var then show "?case" 
    using agree_nil Compl_UNIV_eq BVP.simps(1) by fastforce
next
  case Test then show "?case"
    by auto(simp add: agree_refl Compl_UNIV_eq Vagree_def)
next
  case (Choice a b \<nu> \<omega>)
  assume IH1:"\<And>\<nu>'. \<And>\<omega>'. hpsafe a \<Longrightarrow>((\<nu>', \<omega>') \<in> prog_sem I a \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP a))"
  assume IH2:"\<And>\<nu>'. \<And>\<omega>'. hpsafe b \<Longrightarrow>((\<nu>', \<omega>') \<in> prog_sem I b \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP b))"
  assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (a \<union>\<union> b)"
  assume safe:"hpsafe (Choice a b)"
  from safe have safes:"hpsafe a" "hpsafe b" by (auto dest: hpsafe.cases)
  have sems:"(\<nu>, \<omega>) \<in> prog_sem I (a) \<or> (\<nu>, \<omega>) \<in> prog_sem I (b)" using sem by auto
  have agrees:"Vagree \<nu> \<omega> (- BVP a) \<or> Vagree \<nu> \<omega> (- BVP b)" using IH1 IH2 sems safes by blast
  have sub1:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
  have sub2:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
  have res:"Vagree \<nu> \<omega> (- BVP a \<inter> - BVP b)" using agrees sub1 sub2 agree_supset by blast
  then show "?case" by auto
next
  case (Compose a b \<nu> \<omega>) 
  assume IH1:"\<And>\<nu>'. \<And>\<omega>'. hpsafe a \<Longrightarrow> (\<nu>', \<omega>') \<in> prog_sem I a \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP a)"
  assume IH2:"\<And>\<nu>'. \<And>\<omega>'. hpsafe b \<Longrightarrow> (\<nu>', \<omega>') \<in> prog_sem I b \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP b)"
  assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (a ;; b)"
  assume safe:"hpsafe (a ;; b)"
  from safe have safes:"hpsafe a" "hpsafe b" by (auto dest: hpsafe.cases)  
  then show "?case" 
    using agree_trans IH1 IH2 sem safes by fastforce
next
  fix ODE::"('a,'c) ODE" and P::"('a,'b,'c) formula" and \<nu> \<omega>
  assume safe:"hpsafe (EvolveODE ODE P)"
  from safe have osafe:"osafe ODE" and fsafe:"fsafe P" by (auto dest: hpsafe.cases)
  show "(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P) \<Longrightarrow> Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))"
  proof -
    assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P)"
    from sem have agree:"Vagree \<nu> \<omega> (- BVO ODE)"
      apply(simp only: prog_sem.simps(8) mem_Collect_eq osafe fsafe)
      apply(erule exE)+
    proof -
      fix \<nu>' sol t  
      assume assm:
        "(\<nu>, \<omega>) = (\<nu>', mk_v I ODE \<nu>' (sol t)) \<and>
         0 \<le> t \<and>
         (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu>' x \<in> fml_sem I P} \<and>  (sol 0) = (fst \<nu>')"
      have semBV:"-BVO ODE \<subseteq> -semBV I ODE"
        by(induction ODE, auto)
      from assm have "Vagree \<omega> \<nu> (- BVO ODE)" using mk_v_agree[of I ODE \<nu> "(sol t)"] 
        using agree_sub[OF semBV] by auto
      thus  "Vagree \<nu> \<omega> (- BVO ODE)" by (rule agree_comm)
    qed 
    thus "Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))" by auto
  qed
next
  case (Star a \<nu> \<omega>) then
  have IH:"(\<And>\<nu> \<omega>. hpsafe a \<Longrightarrow> (\<nu>, \<omega>) \<in> prog_sem I a \<Longrightarrow> Vagree \<nu> \<omega> (- BVP a))"
    and safe:"hpsafe a**"
    and sem:"(\<nu>, \<omega>) \<in> prog_sem I a**"
    by auto
  from safe have asafe:"hpsafe a" by (auto dest: hpsafe.cases)
  show "Vagree \<nu> \<omega> (- BVP a**)" 
    using sem apply (simp only: prog_sem.simps)
    apply (erule converse_rtrancl_induct)
     subgoal by(rule agree_refl)
    subgoal for y z using IH[of y z, OF asafe] sem by (auto simp add: Vagree_def)
    done
qed (auto simp add: Vagree_def)

end

end