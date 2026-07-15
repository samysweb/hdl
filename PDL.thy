section\<open>Instantiations\<close>
text\<open>
We now demonstrate the utility of our theory, by providing concrete instantiations.
In addition to the two instantiations presented here,
we also have an instantiation for the AFP formalization of
differential dynamic logic~\cite{Differential_Dynamic_Logic-AFP}.
For sake of modularity of this Isabelle session,
we extracted this instantiation to its own session.
\<close>
subsection\<open>Propositional Dynamic Logic\<close>
text\<open>
\label{subsec:inst:pdl}
TODO: Update
\<close>
theory PDL
  imports
    Main
    DynamicLogicCore
    DynamicLogic
    HavocDynamicLogic
    KATDynamicLogic
    KATRewriting
begin

(* PDL does not have first-order variables *)
datatype pdl_atom_var = singleton_var

type_synonym 'ap pdl_var = "pdl_atom_var + 'ap"

type_synonym ('atom, 'ap) pdl_universe = "('atom \<Rightarrow> bool) + (('atom set \<times> 'atom set) \<Rightarrow> bool)"

type_synonym ('atom, 'ap) pdl_state = "((pdl_atom_var \<Rightarrow> ('atom \<Rightarrow> bool)) \<times> ('ap \<Rightarrow> ('atom set \<times> 'atom set) \<Rightarrow> bool))"

fun pdl_var_eval :: "('atom, 'ap) pdl_state \<Rightarrow> 'ap pdl_var \<Rightarrow> ('atom, 'ap) pdl_universe"
  where
    "pdl_var_eval \<omega> (Inl singleton_var) = (Inl ((fst \<omega>) singleton_var))"
   | "pdl_var_eval \<omega> (Inr prog) = (Inr ((snd \<omega>) prog))"

fun pdl_atom_eval :: "'atom \<Rightarrow> (('atom, 'ap) pdl_state) \<Rightarrow> bool"
  where "pdl_atom_eval a \<omega> = (((fst \<omega>) singleton_var) a)"

fun pdl_atom_set :: "(('atom, 'ap) pdl_state) \<Rightarrow> 'atom set"
  where "pdl_atom_set \<omega> = { (a :: 'atom) . (pdl_atom_eval a \<omega>) }"

fun pdl_prog_eval :: "'ap \<Rightarrow> (('atom, 'ap) pdl_state) \<Rightarrow> (('atom, 'ap) pdl_state) \<Rightarrow> bool"
  where
    "pdl_prog_eval prog \<mu> \<omega> = (
      (fol_equal_everywhere_but_gen pdl_var_eval (Inl singleton_var) \<mu> \<omega>)
      \<and>
      ((snd \<mu>) prog ((pdl_atom_set \<mu>),(pdl_atom_set \<omega>)))
    )"

fun pdl_fv_syn :: "'atom \<Rightarrow> 'ap pdl_var \<Rightarrow> bool"
  where
    "pdl_fv_syn a (Inl singleton_var) = True"
  | "pdl_fv_syn a (Inr x) = False"


interpretation pdlFOL : folCore
  pdl_atom_eval pdl_fv_syn pdl_var_eval
proof
  fix a :: 'atom
  show "finite (Collect (pdl_fv_syn a))"
  proof -
    have subset: "(Collect (pdl_fv_syn a)) \<subseteq> { (Inl singleton_var) }"
      apply auto
      subgoal for x
      proof (induct x)
        case (Inl a)
        then show ?case
        proof (induct a)
          case singleton_var
          then show ?case
            unfolding pdl_fv_syn.simps
            by simp
        qed
      next
        case (Inr b)
        then show ?case
          unfolding pdl_fv_syn.simps
          by simp
      qed.
    have sup_fin: "finite { (Inl singleton_var) }"
      by simp
    thus "finite (Collect (pdl_fv_syn a))"
      using subset
      using finite_subset by blast
  qed

      
  
    show "\<And>a \<mu> \<omega>. fol_states_agree_on_gen pdl_var_eval (pdl_fv_syn a) \<mu> \<omega> \<Longrightarrow> pdl_atom_eval a \<mu> = pdl_atom_eval a \<omega>"
      unfolding fol_states_agree_on_gen_def
      using pdl_fv_syn.simps
      by fastforce

    show "\<forall> (\<omega> :: ('atom, 'ap) pdl_state) \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<omega> v)"
      apply (rule allI, rule allI, rule allI)
    proof -
      fix \<omega> :: "('atom, 'ap) pdl_state"
      fix \<mu> :: "('atom, 'ap) pdl_state"
      fix V :: "('ap pdl_var) set"
      obtain \<omega>1 where h\<omega>1: "\<omega>1 = (fst \<omega>)"
        by simp
      obtain \<omega>2 :: "('ap \<Rightarrow> ('atom set \<times> 'atom set) \<Rightarrow> bool)" where h\<omega>2: "\<omega>2 = (snd \<omega>)"
        by simp
      obtain \<mu>1 where h\<mu>1: "\<mu>1 = (fst \<mu>)"
        by simp
      obtain \<mu>2 :: "('ap \<Rightarrow> ('atom set \<times> 'atom set) \<Rightarrow> bool)" where h\<mu>2: "\<mu>2 = (snd \<mu>)"
        by simp
      obtain V1 :: "pdl_atom_var set" where hV1: "V1 = { x . ((Inl x) \<in> V) }"
        by simp
      obtain V2 :: "'ap set" where hV2: "V2 = { x . ((Inr x) \<in> V) }"
        by simp

      obtain \<nu>1 where h\<nu>1: "\<forall>v. (v \<in> V1 \<longrightarrow> \<nu>1 v = \<mu>1 v) \<and> (v \<notin> V1 \<longrightarrow> \<nu>1 v = \<omega>1 v)"
        by (metis pdl_atom_var.exhaust)

      have ex_\<nu>2: "\<exists>\<nu>2 :: ('ap \<Rightarrow> ('atom set \<times> 'atom set) \<Rightarrow> bool).
                      \<forall>v. (v \<in> V2 \<longrightarrow> \<nu>2 v = \<mu>2 v) \<and> (v \<notin> V2 \<longrightarrow> \<nu>2 v = \<omega>2 v)"
        by (rule exI[where x = "\<lambda>v. if v \<in> V2 then \<mu>2 v else \<omega>2 v"], simp)
      then obtain \<nu>2 :: "('ap \<Rightarrow> ('atom set \<times> 'atom set) \<Rightarrow> bool)"
        where h\<nu>2: "\<forall>v. (v \<in> V2 \<longrightarrow> \<nu>2 v = \<mu>2 v) \<and> (v \<notin> V2 \<longrightarrow> \<nu>2 v = \<omega>2 v)"
        by blast

      define \<nu>0 :: "('atom, 'ap) pdl_state" where \<nu>0_def: "\<nu>0 \<equiv> (\<nu>1, \<nu>2)"

      have \<nu>1_eq: "fst \<nu>0 = \<nu>1" and \<nu>2_eq: "snd \<nu>0 = \<nu>2"
        unfolding \<nu>0_def by simp_all

      have pdl_var_eval_Inl: "\<And>\<sigma> x. pdl_var_eval \<sigma> (Inl x) = Inl ((fst \<sigma>) x)"
        by (metis pdl_atom_var.exhaust pdl_var_eval.simps(1))

      show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<omega> v)"
      proof (intro exI[where x = \<nu>0] allI)
        fix v :: "'ap pdl_var"
        show "(v \<in> V \<longrightarrow> pdl_var_eval \<nu>0 v = pdl_var_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> pdl_var_eval \<nu>0 v = pdl_var_eval \<omega> v)"
        proof (cases v)
          case (Inl x)
          show ?thesis
          proof (intro conjI impI)
            assume "v \<in> V"
            with Inl have "x \<in> V1"
              using hV1 by force
            with h\<nu>1 have key: "\<nu>1 x = \<mu>1 x"
              by auto
            show "pdl_var_eval \<nu>0 v = pdl_var_eval \<mu> v"
              unfolding Inl
              by (simp add: pdl_var_eval_Inl \<nu>1_eq h\<mu>1 key)
          next
            assume "v \<notin> V"
            with Inl have "x \<notin> V1"
              using hV1 by force
            with h\<nu>1 have key: "\<nu>1 x = \<omega>1 x"
              by auto
            show "pdl_var_eval \<nu>0 v = pdl_var_eval \<omega> v"
              unfolding Inl
              by (simp add: pdl_var_eval_Inl \<nu>1_eq h\<omega>1 key)
          qed
        next
          case (Inr p)
          show ?thesis
          proof (intro conjI impI)
            assume "v \<in> V"
            with Inr have "p \<in> V2"
              using hV2 by force
            with h\<nu>2 have key: "\<nu>2 p = \<mu>2 p"
              by auto
            show "pdl_var_eval \<nu>0 v = pdl_var_eval \<mu> v"
              unfolding Inr
              by (simp add: pdl_var_eval.simps(2) \<nu>2_eq h\<mu>2 key)
          next
            assume "v \<notin> V"
            with Inr have "p \<notin> V2"
              using hV2 by force
            with h\<nu>2 have key: "\<nu>2 p = \<omega>2 p"
              by auto
            show "pdl_var_eval \<nu>0 v = pdl_var_eval \<omega> v"
              unfolding Inr
              by (simp add: pdl_var_eval.simps(2) \<nu>2_eq h\<omega>2 key)
          qed
        qed
      qed
    qed
qed


fun pdl_prog_fv_syn :: "'ap \<Rightarrow> 'ap pdl_var \<Rightarrow> bool"
  where
    "pdl_prog_fv_syn \<alpha> (Inl x) = True"
  | "pdl_prog_fv_syn \<alpha> (Inr y) = (\<alpha> = y)"



interpretation pdlDLFull : dynamic_theory
    "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
proof
  show "\<And>\<pi>. finite (Collect (pdl_prog_fv_syn \<pi>))"
    proof -
    fix \<pi> :: 'ap
    have subset: "(Collect (pdl_prog_fv_syn \<pi>)) \<subseteq> { (Inl singleton_var), (Inr \<pi>) }"
      apply auto
      subgoal for x
      proof (induct x)
        case (Inl a)
        then show ?case
          by (cases a) simp
      next
        case (Inr b)
        then show ?case
          unfolding pdl_prog_fv_syn.simps
          by simp
      qed.
    have sup_fin: "finite { (Inl singleton_var), (Inr \<pi>) }"
      by simp
    thus "finite (Collect (pdl_prog_fv_syn \<pi>))"
      using subset
      using finite_subset by blast
  qed

  show "\<And>(\<pi> :: 'ap) (V :: 'ap pdl_var \<Rightarrow> bool) \<mu> \<omega> \<nu>.
       (\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       folCore.fol_states_agree_on pdl_var_eval V \<mu> \<omega> \<and> pdl_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. pdl_prog_eval \<pi> \<omega> \<upsilon> \<and> folCore.fol_states_agree_on pdl_var_eval V \<nu> \<upsilon>)"
  proof
    fix \<pi> :: 'ap
    fix V :: "'ap pdl_var \<Rightarrow> bool"
    fix \<mu> \<omega> \<nu> :: "('atom, 'ap) pdl_state"
    assume asm: "(\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
                 folCore.fol_states_agree_on pdl_var_eval V \<mu> \<omega> \<and> pdl_prog_eval \<pi> \<mu> \<nu>"
    have fv_sub: "\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v"
      using asm by auto
    have agree_\<mu>\<omega>: "folCore.fol_states_agree_on pdl_var_eval V \<mu> \<omega>"
      using asm by auto
    have eval_\<mu>\<nu>: "pdl_prog_eval \<pi> \<mu> \<nu>"
      using asm by auto

    have V_singleton: "V (Inl singleton_var)"
      using fv_sub by fastforce
    have V_prog: "V (Inr \<pi>)"
      using fv_sub by fastforce

    have agree_atoms: "fst \<mu> singleton_var = fst \<omega> singleton_var"
      using agree_\<mu>\<omega>[unfolded folCore.fol_states_agree_on_def] V_singleton
      unfolding pdlFOL.fol_states_agree_on_def
      by auto
    have agree_prog: "snd \<mu> \<pi> = snd \<omega> \<pi>"
      using agree_\<mu>\<omega>[unfolded folCore.fol_states_agree_on_def] V_prog
      unfolding pdlFOL.fol_states_agree_on_def
      by auto

    have atom_set_eq: "pdl_atom_set \<mu> = pdl_atom_set \<omega>"
      unfolding pdl_atom_set.simps pdl_atom_eval.simps
      using agree_atoms
      by simp

    from eval_\<mu>\<nu> have eq_everywhere: "fol_equal_everywhere_but_gen pdl_var_eval (Inl singleton_var) \<mu> \<nu>"
      and trans: "(snd \<mu>) \<pi> ((pdl_atom_set \<mu>),(pdl_atom_set \<nu>))"
      by simp_all

    have snd_const: "\<And>p. snd \<mu> p = snd \<nu> p"
    proof -
      fix p :: 'ap
      have "pdl_var_eval \<mu> (Inr p) = pdl_var_eval \<nu> (Inr p)"
        using eq_everywhere 
        unfolding fol_equal_everywhere_but_gen_def
        unfolding fol_states_agree_on_gen_def
        unfolding pdl_var_eval.simps
        by auto
      then show "snd \<mu> p = snd \<nu> p"
        by simp
    qed

    define \<upsilon> :: "('atom, 'ap) pdl_state" where \<upsilon>_def: "\<upsilon> \<equiv> (fst \<nu>, snd \<omega>)"

    have \<upsilon>1_eq: "fst \<upsilon> = fst \<nu>" and \<upsilon>2_eq: "snd \<upsilon> = snd \<omega>"
      unfolding \<upsilon>_def by simp_all

    have atom_set_\<upsilon>\<nu>: "pdl_atom_set \<upsilon> = pdl_atom_set \<nu>"
      unfolding pdl_atom_set.simps pdl_atom_eval.simps
      using \<upsilon>1_eq
      by simp

    have step1: "fol_equal_everywhere_but_gen pdl_var_eval (Inl singleton_var) \<omega> \<upsilon>"
    proof (unfold fol_equal_everywhere_but_gen_def fol_states_agree_on_gen_def, intro allI impI)
      fix w :: "'ap pdl_var"
      assume "w \<noteq> Inl singleton_var"
      then obtain p where w_eq: "w = Inr p"
        by (metis pdl_atom_var.exhaust sum.exhaust)
      show "pdl_var_eval \<omega> w = pdl_var_eval \<upsilon> w"
        unfolding w_eq
        using \<upsilon>2_eq
        by simp
    qed

    have step2: "(snd \<omega>) \<pi> ((pdl_atom_set \<omega>),(pdl_atom_set \<upsilon>))"
      unfolding atom_set_\<upsilon>\<nu>
      using agree_prog atom_set_eq trans
      by simp

    have eval_\<omega>\<upsilon>: "pdl_prog_eval \<pi> \<omega> \<upsilon>"
      using step1 step2
      by simp

    have agree_\<nu>\<upsilon>: "folCore.fol_states_agree_on pdl_var_eval V \<nu> \<upsilon>"
      unfolding folCore.fol_states_agree_on_def pdlFOL.fol_states_agree_on_def
    proof (intro allI impI)
      fix w :: "'ap pdl_var"
      assume Vw: "V w"
      show "pdl_var_eval \<nu> w = pdl_var_eval \<upsilon> w"
      proof (cases w)
        case (Inl x)
        then have x_eq: "x = singleton_var"
          by (cases x) simp
        with Inl show ?thesis
          using \<upsilon>1_eq by simp
      next
        case (Inr p)
        then have Vp: "V (Inr p)"
          using Vw by simp
        then have "pdl_var_eval \<mu> (Inr p) = pdl_var_eval \<omega> (Inr p)"
          using agree_\<mu>\<omega>[unfolded folCore.fol_states_agree_on_def]
          unfolding pdlFOL.fol_states_agree_on_def
          by auto
        then have h1: "snd \<mu> p = snd \<omega> p"
          by simp
        have h2: "snd \<nu> p = snd \<mu> p"
          using snd_const by simp
        have h3: "snd \<upsilon> p = snd \<omega> p"
          using \<upsilon>2_eq by simp
        have "snd \<nu> p = snd \<upsilon> p"
          using h1 h2 h3 by simp
        with Inr show ?thesis
          by simp
      qed
    qed

    show "\<exists>\<upsilon>. pdl_prog_eval \<pi> \<omega> \<upsilon> \<and> folCore.fol_states_agree_on pdl_var_eval V \<nu> \<upsilon>"
    proof (intro exI[where x = \<upsilon>] conjI)
      show "pdl_prog_eval \<pi> \<omega> \<upsilon>" by (rule eval_\<omega>\<upsilon>)
      show "folCore.fol_states_agree_on pdl_var_eval V \<nu> \<upsilon>" by (rule agree_\<nu>\<upsilon>)
    qed
  qed

  show " \<forall>\<pi> \<mu> \<omega>. (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v) \<longrightarrow> pdl_prog_eval \<pi> \<mu> = pdl_prog_eval \<pi> \<omega>"
    using pdl_var_eval.simps
    proof (intro allI impI)
    fix \<pi> :: 'ap
    fix \<mu> \<omega> :: "('atom, 'ap) pdl_state"
    assume agree: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v"
    have fst_eq: "fst \<mu> = fst \<omega>"
    proof
      fix x :: pdl_atom_var
      show "fst \<mu> x = fst \<omega> x"
      proof (cases x)
        case singleton_var
        have "pdl_var_eval \<mu> (Inl singleton_var) = pdl_var_eval \<omega> (Inl singleton_var)"
          using agree
          using pdl_var_eval.simps
          by blast
        then show ?thesis
          unfolding singleton_var
          by simp
      qed
    qed
    have snd_eq: "snd \<mu> = snd \<omega>"
    proof
      fix p :: 'ap
      have "pdl_var_eval \<mu> (Inr p) = pdl_var_eval \<omega> (Inr p)"
        using agree
        using pdl_var_eval.simps
        by blast
      then show "snd \<mu> p = snd \<omega> p"
        by simp
    qed
    have state_eq: "\<mu> = \<omega>"
      using fst_eq snd_eq by (metis prod.collapse)
    then show "pdl_prog_eval \<pi> \<mu> = pdl_prog_eval \<pi> \<omega>"
      by simp
  qed
    
qed

interpretation regular_pdl :
  regular_lifting "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
  unfolding regular_lifting_def
    using pdlDLFull.dynamic_theory_axioms
    by blast

interpretation regular_pdl_kat :
KleeneDynLog "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
  proof
    have pdl_state_eq_of_agree:
      "\<And>(\<sigma>::('atom,'ap) pdl_state) \<tau>. (\<forall>v. pdl_var_eval \<sigma> v = pdl_var_eval \<tau> v) \<Longrightarrow> \<sigma> = \<tau>"
    proof -
      fix \<sigma> \<tau> :: "('atom, 'ap) pdl_state"
      assume assms: "\<forall>v. pdl_var_eval \<sigma> v = pdl_var_eval \<tau> v"
      have fst_eq: "fst \<sigma> = fst \<tau>"
      proof
        fix x :: pdl_atom_var
        show "fst \<sigma> x = fst \<tau> x"
        proof (cases x)
          case singleton_var
          have h: "pdl_var_eval \<sigma> (Inl singleton_var) = pdl_var_eval \<tau> (Inl singleton_var)"
            using assms
            by blast
          show ?thesis
            unfolding singleton_var
            using h[unfolded pdl_var_eval.simps]
            by simp
        qed
      qed
      have snd_eq: "snd \<sigma> = snd \<tau>"
      proof
        fix p :: 'ap
        have h: "pdl_var_eval \<sigma> (Inr p) = pdl_var_eval \<tau> (Inr p)"
          using assms
          by blast
        show "snd \<sigma> p = snd \<tau> p"
          using h[unfolded pdl_var_eval.simps]
          by simp
      qed
      show "\<sigma> = \<tau>"
        using fst_eq snd_eq by (metis prod.collapse)
    qed

    show "\<forall>\<pi> \<mu> \<omega> \<mu>' \<omega>'.
           (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and> pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v) \<longrightarrow>
           pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
    proof (intro allI impI)
      fix \<pi> :: 'ap
      fix \<mu> \<omega> \<mu>' \<omega>' :: "('atom, 'ap) pdl_state"
      assume agree: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and> pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v"
      have agree1: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v"
        using agree by auto
      have agree2: "\<forall>v. pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v"
        using agree by auto
      have state_eq1: "\<mu> = \<omega>"
        using pdl_state_eq_of_agree[OF agree1] .
      have state_eq2: "\<mu>' = \<omega>'"
        using pdl_state_eq_of_agree[OF agree2] .
      show "pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
        using state_eq1 state_eq2
        by simp
    qed
  qed

end