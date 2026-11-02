section\<open>Heterogeneous Dynamic Theories\<close>
text\<open>
\label{sec:heterogeneous}
We now present our formalization of \emph{combination} of dynamic theories
and its associated proof rules.
A combined theory consists of two independent dynamic theories
and a first-order core that can formalize statements about the \emph{crossproduct}
of the two state spaces.
Based on this, we first define a simple heterogeneous dynamic theory
and then its \emph{lifted} variant which inherits havoc and regular program closure.
\<close>

theory HeterogeneousDynamicLogic
  imports
    Main
    "DynamicLogic"
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "NatKATDynamicLogic"
begin

datatype ('at1,'at2,'atc) het_atom =
  ATOM1 "'at1" | ATOM2 "'at2" | ATOMC "'atc"

datatype ('pr1,'pr2) het_prog =
  PROG1 "'pr1" | PROG2 "'pr2"

definition common_atom_eval :: "('st1\<Rightarrow>'vr1\<Rightarrow>'vl1) \<Rightarrow> ('st2\<Rightarrow>'vr2\<Rightarrow>'vl2) \<Rightarrow> ('st1 \<times> 'st2) \<Rightarrow> ('vr1+'vr2) \<Rightarrow> ('vl1+'vl2)"
  where "common_atom_eval eval1 eval2 \<mu> = (map_sum (eval1 (fst \<mu>)) (eval2 (snd \<mu>)))"

locale HeterogeneousDynLog =
fixes atom_eval1 :: "'atom1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and atom_fv_syn1 :: "'atom1 \<Rightarrow> 'var1 \<Rightarrow> bool"
  and state_eval1 :: "'state1 \<Rightarrow> 'var1 \<Rightarrow> 'val1"
  and prog_eval1 :: "'prog1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and dyn_prog_FV1 :: "'prog1 \<Rightarrow> 'var1 \<Rightarrow> bool"

fixes atom_eval2 :: "'atom2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and atom_fv_syn2 :: "'atom2 \<Rightarrow> 'var2 \<Rightarrow> bool"
  and state_eval2 :: "'state2 \<Rightarrow> 'var2 \<Rightarrow> 'val2"
  and prog_eval2 :: "'prog2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and dyn_prog_FV2 :: "'prog2 \<Rightarrow> 'var2 \<Rightarrow> bool"

fixes atom_eval_comm :: "'atom_comm \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> bool"
  and atom_fv_syn_comm :: "'atom_comm \<Rightarrow> ('var1 + 'var2) \<Rightarrow> bool"

  assumes dynamic_theory1: "dynamic_theory atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1"
  assumes dynamic_theory2: "dynamic_theory atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2"
  assumes colCoreComm: "folCore atom_eval_comm atom_fv_syn_comm (common_atom_eval state_eval1 state_eval2)"
begin

sublocale dyn_log_1 : dynamic_theory atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
  using dynamic_theory1 by auto

sublocale dyn_log_2 : dynamic_theory atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
  using dynamic_theory2 by auto

sublocale fol_core_comm : folCore atom_eval_comm atom_fv_syn_comm "(common_atom_eval state_eval1 state_eval2)"
  using colCoreComm by auto

subsection\<open>Semantics\<close>
text\<open>
We begin by defining the evaluation of heterogeneous atoms and their free variables:
\<close>

fun het_atom_eval :: "('atom1,'atom2,'atom_comm) het_atom \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> bool"
  where
    "het_atom_eval (ATOM1 a) \<mu> = atom_eval1 a (fst \<mu>)"
  | "het_atom_eval (ATOM2 a) \<mu> = atom_eval2 a (snd \<mu>)"
  | "het_atom_eval (ATOMC a) \<mu> = atom_eval_comm a \<mu>"

fun het_atom_fv_syn :: "('atom1,'atom2,'atom_comm) het_atom \<Rightarrow> ('var1 + 'var2) \<Rightarrow> bool"
  where
    "het_atom_fv_syn (ATOM1 a) (Inl v) = atom_fv_syn1 a v"
  | "het_atom_fv_syn (ATOM1 a) (Inr v) = False"
  | "het_atom_fv_syn (ATOM2 a) (Inl v) = False"
  | "het_atom_fv_syn (ATOM2 a) (Inr v) = atom_fv_syn2 a v"
  | "het_atom_fv_syn (ATOMC a) v = atom_fv_syn_comm a v"

text\<open>
Similarly, we define the evaluation of variables which are mapped back to their
respective state space:\<close>

definition het_state_eval :: "('state1 \<times> 'state2) \<Rightarrow> ('var1+'var2) \<Rightarrow> ('val1+'val2)"
  where [simp]: "het_state_eval = (common_atom_eval state_eval1 state_eval2)"

text\<open>
In the same fashion,
programs are then evaluated w.r.t. their underlying dynamic theory.
A program's free/bound variables are also given by their underlying theories:
\<close>

fun het_prog_eval :: "('prog1,'prog2) het_prog \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> bool"
  where
    "het_prog_eval (PROG1 \<pi>) (\<mu>1,\<mu>2) (\<omega>1,\<omega>2) = ((prog_eval1 \<pi> \<mu>1 \<omega>1) \<and> ((state_eval2 \<mu>2) = (state_eval2 \<omega>2)))"
  | "het_prog_eval (PROG2 \<pi>) (\<mu>1,\<mu>2) (\<omega>1,\<omega>2) = (((state_eval1 \<mu>1) = (state_eval1 \<omega>1)) \<and> (prog_eval2 \<pi> \<mu>2 \<omega>2))"

fun het_dyn_prog_FV :: "('prog1,'prog2) het_prog \<Rightarrow>  ('var1+'var2) \<Rightarrow> bool"
  where
    "het_dyn_prog_FV (PROG1 \<pi>) (Inl v) = dyn_prog_FV1 \<pi> v"
  | "het_dyn_prog_FV (PROG1 \<pi>) (Inr v) = False"
  | "het_dyn_prog_FV (PROG2 \<pi>) (Inl v) = False"
  | "het_dyn_prog_FV (PROG2 \<pi>) (Inr v) = dyn_prog_FV2 \<pi> v"

fun het_dyn_prog_BV :: "('prog1 \<Rightarrow> 'var1 \<Rightarrow> bool) \<Rightarrow> ('prog2 \<Rightarrow> 'var2 \<Rightarrow> bool) \<Rightarrow>('prog1,'prog2) het_prog \<Rightarrow>  ('var1+'var2) \<Rightarrow> bool"
  where
    "het_dyn_prog_BV BV1 BV2 (PROG1 \<pi>) (Inl v) = BV1 \<pi> v"
  | "het_dyn_prog_BV BV1 BV2 (PROG1 \<pi>) (Inr v) = False"
  | "het_dyn_prog_BV BV1 BV2 (PROG2 \<pi>) (Inl v) = False"
  | "het_dyn_prog_BV BV1 BV2 (PROG2 \<pi>) (Inr v) = BV2 \<pi> v"

subsection\<open>Simple Heterogeneous Dynamic Theory\<close>
text\<open>
We now want to prove that the resulting constructs again form a dynamic
theory win which we can reason about programs from both theories.
To this end, we begin by proving that our heterogeneous atoms can be used to construct
a (heterogeneous) first-order logic core:
\<close>

interpretation het_fol :
    folCore het_atom_eval het_atom_fv_syn het_state_eval
proof
  show "\<And>a. finite (Collect (het_atom_fv_syn a))"
  proof -
    fix a

    let ?set_split = "(\<lambda> a . ({w . \<exists> v . (w = (Inl v) \<and> (het_atom_fv_syn a (Inl v)))} \<union> {w . \<exists> v . (w = (Inr v) \<and> (het_atom_fv_syn a (Inr v)))}))"

    have split_superset: "\<And> b . {v. het_atom_fv_syn b v} \<subseteq> ?set_split b"
      using het_atom_fv_syn.elims(2)
      proof -
        fix b
        obtain vv :: "'var1 + 'var2 \<Rightarrow> 'var2" and vva :: "'var1 + 'var2 \<Rightarrow> 'var1" where
          "\<forall>s. s = Inr (vv s) \<or> s = Inl (vva s)"
          by (metis (no_types) obj_sumE)
        then have "Collect (het_atom_fv_syn b) \<subseteq> {s. (\<exists>v. s = Inr v \<and> het_atom_fv_syn b s) \<or> (\<exists>v. s = Inl v \<and> het_atom_fv_syn b s)}"
          by blast
        then show "{v. het_atom_fv_syn b v} \<subseteq> ?set_split b"
          by blast
      qed

    show "finite (Collect (het_atom_fv_syn a))"
    proof (induct a)
      case (ATOM1 x)
      then show ?case
      proof -
        have "finite (?set_split (ATOM1 x))"
          unfolding het_atom_fv_syn.simps
          using dyn_log_1.fv_finite[of x]
          by simp
        thus "finite {a. het_atom_fv_syn (ATOM1 x) a}"
          using split_superset
          by (meson rev_finite_subset)
      qed
    next
      case (ATOM2 x)
      then show ?case
      proof -
        have "finite (?set_split (ATOM2 x))"
          unfolding het_atom_fv_syn.simps
          using dyn_log_2.fv_finite[of x]
          by simp
        thus "finite {a. het_atom_fv_syn (ATOM2 x) a}"
          using split_superset
          by (meson rev_finite_subset)
      qed
    next
      case (ATOMC x)
      then show ?case
      proof -
        show "finite {a. het_atom_fv_syn (ATOMC x) a}"
          unfolding het_atom_fv_syn.simps 
          using fol_core_comm.fv_finite[of x]
          by simp
      qed
    qed
  qed

  show "\<And>a \<mu> \<omega>.
         fol_states_agree_on_gen het_state_eval (het_atom_fv_syn a) \<mu> \<omega> \<Longrightarrow>
         het_atom_eval a \<mu> = het_atom_eval a \<omega>"
  proof -
    fix a \<mu> \<omega>
    show "fol_states_agree_on_gen het_state_eval (het_atom_fv_syn a) \<mu> \<omega> \<Longrightarrow>
           het_atom_eval a \<mu> = het_atom_eval a \<omega>"
    proof (induct a)
      case (ATOM1 x)
      then show ?case
        using dyn_log_1.fv_overapprox[of "x" "(fst \<mu>)" "(fst \<omega>)"]
        unfolding fol_states_agree_on_gen_def
        using het_atom_fv_syn.simps(1,2)
        unfolding het_state_eval_def
        unfolding common_atom_eval_def
        unfolding het_atom_eval.simps
        by (metis map_sum.simps(1) sum.inject(1))
    next
      case (ATOM2 x)
      then show ?case
        using dyn_log_2.fv_overapprox[of "x" "(snd \<mu>)" "(snd \<omega>)"]
        unfolding fol_states_agree_on_gen_def
        using het_atom_fv_syn.simps(3,4)
        unfolding het_state_eval_def
        unfolding common_atom_eval_def
        unfolding het_atom_eval.simps
        by (metis map_sum.simps(2) sum.inject(2))
    next
      case (ATOMC x)
      then show ?case
        using fol_core_comm.fv_overapprox[of x \<mu> \<omega>]
        unfolding fol_states_agree_on_gen_def
        unfolding het_atom_fv_syn.simps(5)
        by simp
    qed
  qed

  show "\<forall>\<omega> \<mu> V.
       \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> het_state_eval \<nu> v = het_state_eval \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> het_state_eval \<nu> v = het_state_eval \<omega> v)"
  proof (intro allI)
    fix \<omega> \<mu> V
    show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> het_state_eval \<nu> v = het_state_eval \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> het_state_eval \<nu> v = het_state_eval \<omega> v)"
    proof -

      let ?V1 = "{ v . (Inl v) \<in> V}"
      let ?V2 = "{ v . (Inr v) \<in> V}"

      obtain \<nu>1 where \<nu>1_cond: "\<forall>v. (v \<in> ?V1 \<longrightarrow> state_eval1 \<nu>1 v = state_eval1 (fst \<mu>) v) \<and>
                           (v \<notin> ?V1 \<longrightarrow> state_eval1 \<nu>1 v = state_eval1 (fst \<omega>) v)"
        using dyn_log_1.state_space_convexity
        by presburger

      obtain \<nu>2 where \<nu>2_cond: "\<forall>v. (v \<in> ?V2 \<longrightarrow> state_eval2 \<nu>2 v = state_eval2 (snd \<mu>) v) \<and>
                           (v \<notin> ?V2 \<longrightarrow> state_eval2 \<nu>2 v = state_eval2 (snd \<omega>) v)"
        using dyn_log_2.state_space_convexity
        by presburger

      show ?thesis
        using \<nu>1_cond \<nu>2_cond
        apply (intro exI[where x="(\<nu>1,\<nu>2)"])
        unfolding het_state_eval_def
        unfolding common_atom_eval_def
        by (metis (no_types, lifting) fst_conv map_sum.simps(1) map_sum.simps(2) mem_Collect_eq old.sum.exhaust snd_conv)
    qed
  qed
qed

sublocale het_fol :
    folCore het_atom_eval het_atom_fv_syn het_state_eval
  using het_fol.folCore_axioms by blast

text\<open>
We now show that combing our heterogeneous first-order core with our definition
of heterogeneous programs yields a dynamic theory:
\<close>

interpretation het_dl :
    dynamic_theory het_atom_eval het_atom_fv_syn het_state_eval het_prog_eval het_dyn_prog_FV
proof
  show "\<And>\<pi>. finite (Collect (het_dyn_prog_FV \<pi>))"
  proof -
    fix \<pi>

    let ?set_split = "(\<lambda> a . ({w . \<exists> v . (w = (Inl v) \<and> (het_dyn_prog_FV a (Inl v)))} \<union> {w . \<exists> v . (w = (Inr v) \<and> (het_dyn_prog_FV a (Inr v)))}))"

    have split_superset: "\<And> b . {v. het_dyn_prog_FV b v} \<subseteq> ?set_split b"
      using het_atom_fv_syn.elims(2)
      proof -
        fix b
        obtain vv :: "'var1 + 'var2 \<Rightarrow> 'var2" and vva :: "'var1 + 'var2 \<Rightarrow> 'var1" where
          "\<forall>s. s = Inr (vv s) \<or> s = Inl (vva s)"
          by (metis (no_types) obj_sumE)
        then have "Collect (het_dyn_prog_FV b) \<subseteq> {s. (\<exists>v. s = Inr v \<and> het_dyn_prog_FV b s) \<or> (\<exists>v. s = Inl v \<and> het_dyn_prog_FV b s)}"
          by blast
        then show "{v. het_dyn_prog_FV b v} \<subseteq> ?set_split b"
          by blast
      qed

    show "finite (Collect (het_dyn_prog_FV \<pi>))"
    proof (induct \<pi>)
      case (PROG1 x)
      then show ?case
      proof -
        have "finite (?set_split (PROG1 x))"
          unfolding het_atom_fv_syn.simps
          using dyn_log_1.prog_fv_finite[of x]
          by simp
        thus "finite {a. het_dyn_prog_FV (PROG1 x) a}"
          using split_superset
          by (meson rev_finite_subset)
      qed      
    next
      case (PROG2 x)
      then show ?case
      proof -
        have "finite (?set_split (PROG2 x))"
          unfolding het_atom_fv_syn.simps
          using dyn_log_2.prog_fv_finite[of x]
          by simp
        thus "finite {a. het_dyn_prog_FV (PROG2 x) a}"
          using split_superset
          by (meson rev_finite_subset)
      qed
    qed
  qed

  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
         (\<forall>v. het_dyn_prog_FV \<pi> v \<longrightarrow> V v) \<and>
         folCore.fol_states_agree_on het_state_eval V \<mu> \<omega> \<and> het_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. het_prog_eval \<pi> \<omega> \<upsilon> \<and> folCore.fol_states_agree_on het_state_eval V \<nu> \<upsilon>)"
  proof
    fix \<pi> V \<mu> \<omega> \<nu>
    have "\<forall> \<mu>1 \<mu>2 \<omega>1 \<omega>2 \<nu>1 \<nu>2 .
            ((\<forall>v. het_dyn_prog_FV \<pi> v \<longrightarrow> V v) \<and> het_fol.fol_states_agree_on V (\<mu>1,\<mu>2) (\<omega>1,\<omega>2) \<and> het_prog_eval \<pi> (\<mu>1,\<mu>2) (\<nu>1,\<nu>2) \<longrightarrow>
             (\<exists>\<upsilon>1 \<upsilon>2. het_prog_eval \<pi> (\<omega>1,\<omega>2) (\<upsilon>1,\<upsilon>2) \<and> het_fol.fol_states_agree_on V (\<nu>1,\<nu>2) (\<upsilon>1,\<upsilon>2)))"
    proof (induct \<pi>)
      case (PROG1 x)
      then show ?case
        unfolding het_prog_eval.simps
      proof (standard, intro allI, intro impI)
        fix \<mu>1 \<mu>2 \<omega>1 \<omega>2 \<nu>1 \<nu>2

        obtain V1 where V1_cond: "\<forall> w . V1 w \<longleftrightarrow> (V (Inl w))"
          by fastforce

        obtain V2 where V2_cond: "\<forall> w . V2 w \<longleftrightarrow> (V (Inr w))"
          by fastforce

        assume local_assms: "(\<forall>v. het_dyn_prog_FV (PROG1 x) v \<longrightarrow> V v) \<and>
                 het_fol.fol_states_agree_on V (\<mu>1, \<mu>2) (\<omega>1, \<omega>2) \<and>
                 prog_eval1 x \<mu>1 \<nu>1 \<and> state_eval2 \<mu>2 = state_eval2 \<nu>2"

        then have state2_eq: "dyn_log_2.fol_states_agree_on V2 \<nu>2 \<omega>2"
          unfolding het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def common_atom_eval_def
          using V2_cond dyn_log_2.fol_states_agree_on_def by auto

        have all_v1_cond: "(\<forall>v. dyn_prog_FV1 x v \<longrightarrow> V1 v)"
          using local_assms
          using het_dyn_prog_FV.simps(1,2)
          using V1_cond
          by blast

        have eq_everywhere_but_1: "dyn_log_1.fol_states_agree_on V1 \<mu>1 \<omega>1"
          using local_assms
          unfolding  het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def
          unfolding common_atom_eval_def
          unfolding dyn_log_1.fol_states_agree_on_def
          using V1_cond
          by fastforce

        then have "\<exists>\<upsilon>1.
                (prog_eval1 x \<omega>1 \<upsilon>1) \<and>
                dyn_log_1.fol_states_agree_on V1 \<nu>1 \<upsilon>1"
          using dyn_log_1.prog_fv_overapprox
          using all_v1_cond
          using local_assms
          by blast

        then obtain \<upsilon>1_fixed where \<upsilon>1_fixed_cond: "(prog_eval1 x \<omega>1 \<upsilon>1_fixed) \<and>
                dyn_log_1.fol_states_agree_on V1 \<nu>1 \<upsilon>1_fixed"
          by blast
          

        show "\<exists>\<upsilon>1 \<upsilon>2.
                (prog_eval1 x \<omega>1 \<upsilon>1 \<and> state_eval2 \<omega>2 = state_eval2 \<upsilon>2) \<and>
                het_fol.fol_states_agree_on V (\<nu>1, \<nu>2) (\<upsilon>1, \<upsilon>2)"
          apply (intro exI[where x=\<upsilon>1_fixed],intro exI[where x=\<omega>2])
          unfolding het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def common_atom_eval_def
          using \<upsilon>1_fixed_cond
          using state2_eq
          using V1_cond V2_cond
          by (metis (no_types, lifting) dyn_log_1.fol_states_agree_on_def dyn_log_2.fol_states_agree_on_def fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)
      qed
    next
      case (PROG2 x)
      then show ?case
        unfolding het_prog_eval.simps
      proof (standard, intro allI, intro impI)
        fix \<mu>1 \<mu>2 \<omega>1 \<omega>2 \<nu>1 \<nu>2

        obtain V1 where V1_cond: "\<forall> w . V1 w \<longleftrightarrow> (V (Inl w))"
          by fastforce

        obtain V2 where V2_cond: "\<forall> w . V2 w \<longleftrightarrow> (V (Inr w))"
          by fastforce

        assume local_assms: "(\<forall>v. het_dyn_prog_FV (PROG2 x) v \<longrightarrow> V v) \<and>
                 het_fol.fol_states_agree_on V (\<mu>1, \<mu>2) (\<omega>1, \<omega>2) \<and>
                 state_eval1 \<mu>1 = state_eval1 \<nu>1 \<and> prog_eval2 x \<mu>2 \<nu>2"

        then have state1_eq: "dyn_log_1.fol_states_agree_on V1 \<nu>1 \<omega>1"
          unfolding het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def common_atom_eval_def
          using dyn_log_1.fol_states_agree_on_def
          using V1_cond by auto

        have all_v2_cond: "(\<forall>v. dyn_prog_FV2 x v \<longrightarrow> V2 v)"
          using local_assms
          using het_dyn_prog_FV.simps(3,4)
          using V2_cond
          by blast

        have eq_everywhere_but_2: "dyn_log_2.fol_states_agree_on V2 \<mu>2 \<omega>2"
          using local_assms
          unfolding  het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def
          unfolding common_atom_eval_def
          unfolding dyn_log_2.fol_states_agree_on_def
          using V2_cond
          by fastforce

        then have "\<exists>\<upsilon>2.
                (prog_eval2 x \<omega>2 \<upsilon>2) \<and>
                dyn_log_2.fol_states_agree_on V2 \<nu>2 \<upsilon>2"
          using dyn_log_2.prog_fv_overapprox
          using all_v2_cond
          using local_assms
          by blast

        then obtain \<upsilon>2_fixed where \<upsilon>2_fixed_cond: "(prog_eval2 x \<omega>2 \<upsilon>2_fixed) \<and>
                dyn_log_2.fol_states_agree_on V2 \<nu>2 \<upsilon>2_fixed"
          by blast

        show "\<exists>\<upsilon>1 \<upsilon>2.
                (state_eval1 \<omega>1 = state_eval1 \<upsilon>1 \<and> prog_eval2 x \<omega>2 \<upsilon>2) \<and>
                het_fol.fol_states_agree_on V (\<nu>1, \<nu>2) (\<upsilon>1, \<upsilon>2)"
          apply (intro exI[where x=\<omega>1],intro exI[where x=\<upsilon>2_fixed])
          unfolding het_fol.fol_states_agree_on_def
          unfolding het_state_eval_def common_atom_eval_def
          using \<upsilon>2_fixed_cond
          using state1_eq
          using V1_cond V2_cond
          by (metis (no_types, lifting) dyn_log_1.fol_states_agree_on_def dyn_log_2.fol_states_agree_on_def fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)
      qed
    qed
    thus "(\<forall>v. het_dyn_prog_FV \<pi> v \<longrightarrow> V v) \<and> het_fol.fol_states_agree_on V \<mu> \<omega> \<and> het_prog_eval \<pi> \<mu> \<nu> \<Longrightarrow>
       \<exists>\<upsilon>. het_prog_eval \<pi> \<omega> \<upsilon> \<and> het_fol.fol_states_agree_on V \<nu> \<upsilon>"
      by (metis old.prod.exhaust)
  qed

  show "\<forall>\<pi> \<mu> \<omega>. (\<forall>v. het_state_eval \<mu> v = het_state_eval \<omega> v) \<longrightarrow> het_prog_eval \<pi> \<mu> = het_prog_eval \<pi> \<omega>"
  proof (intro allI)
    fix \<pi> \<mu> \<omega>
    have "\<forall> \<mu>1 \<mu>2 \<omega>1 \<omega>2 .
            (\<forall>v. het_state_eval (\<mu>1,\<mu>2) v = het_state_eval (\<omega>1,\<omega>2) v) \<longrightarrow> het_prog_eval \<pi> (\<mu>1,\<mu>2) = het_prog_eval \<pi> (\<omega>1,\<omega>2)"
    proof (induct \<pi>)
      case (PROG1 x)
      then show ?case
      proof (intro allI,intro impI)
        fix \<mu>1 \<mu>2 \<omega>1 \<omega>2
        assume eval_assm: "\<forall>v. het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<omega>1, \<omega>2) v"
        have eval1_eq: "\<forall>v. state_eval1 \<mu>1 v = state_eval1 \<omega>1 v"
          using eval_assm
          unfolding het_state_eval_def common_atom_eval_def
          by (simp,metis map_sum.simps(1) sum.inject(1))

        
        have eval2_eq: "\<forall>v. state_eval2 \<mu>2 v = state_eval2 \<omega>2 v"
          using eval_assm
          unfolding het_state_eval_def common_atom_eval_def
          by (simp,metis map_sum.simps(2) sum.inject(2))

        have "\<forall> \<nu>1 \<nu>2 . het_prog_eval (PROG1 x) (\<mu>1, \<mu>2) (\<nu>1,\<nu>2) = het_prog_eval (PROG1 x) (\<omega>1, \<omega>2) (\<nu>1,\<nu>2)"
          unfolding het_prog_eval.simps
          using eval1_eq eval2_eq
          using dyn_log_1.prog_var_determinance
          by (metis ext)

        thus "het_prog_eval (PROG1 x) (\<mu>1, \<mu>2) = het_prog_eval (PROG1 x) (\<omega>1, \<omega>2)"
          by fastforce 
      qed
    next
      case (PROG2 x)
      then show ?case
      proof (intro allI,intro impI)
        fix \<mu>1 \<mu>2 \<omega>1 \<omega>2
        assume eval_assm: "\<forall>v. het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<omega>1, \<omega>2) v"
        have eval1_eq: "\<forall>v. state_eval1 \<mu>1 v = state_eval1 \<omega>1 v"
          using eval_assm
          unfolding het_state_eval_def common_atom_eval_def
          by (simp,metis map_sum.simps(1) sum.inject(1))

        
        have eval2_eq: "\<forall>v. state_eval2 \<mu>2 v = state_eval2 \<omega>2 v"
          using eval_assm
          unfolding het_state_eval_def common_atom_eval_def
          by (simp,metis map_sum.simps(2) sum.inject(2))

        have "\<forall> \<nu>1 \<nu>2 . het_prog_eval (PROG2 x) (\<mu>1, \<mu>2) (\<nu>1,\<nu>2) = het_prog_eval (PROG2 x) (\<omega>1, \<omega>2) (\<nu>1,\<nu>2)"
          unfolding het_prog_eval.simps
          using eval1_eq eval2_eq
          using dyn_log_2.prog_var_determinance
          by (metis ext)

        thus "het_prog_eval (PROG2 x) (\<mu>1, \<mu>2) = het_prog_eval (PROG2 x) (\<omega>1, \<omega>2)"
          by fastforce 
      qed
    qed
    thus "(\<forall>v. het_state_eval \<mu> v = het_state_eval \<omega> v) \<longrightarrow> het_prog_eval \<pi> \<mu> = het_prog_eval \<pi> \<omega>"
      by (metis old.prod.exhaust)
  qed
qed

sublocale het_dl:
    dynamic_theory het_atom_eval het_atom_fv_syn het_state_eval het_prog_eval het_dyn_prog_FV
  using het_dl.dynamic_theory_axioms by blast


lemma BV_overapprox:
  assumes "\<And> \<pi> v . dyn_log_1.dyn_prog_bv_sem \<pi> v \<Longrightarrow> BV1 \<pi> v"
      and "\<And> \<pi> v . dyn_log_2.dyn_prog_bv_sem \<pi> v \<Longrightarrow> BV2 \<pi> v"
    shows "het_dl.dyn_prog_bv_sem \<pi> v \<Longrightarrow> het_dyn_prog_BV BV1 BV2 \<pi> v"
proof (induct \<pi>)
  case (PROG1 x)
  then show ?case
  proof (induct v)
    case (Inl a)
    then show ?case
      unfolding het_dyn_prog_BV.simps
      using assms
      unfolding het_dl.dyn_prog_bv_sem.simps
      unfolding dyn_log_1.dyn_prog_bv_sem.simps
      unfolding het_prog_eval.simps
      by (smt (verit, best) common_atom_eval_def fst_conv het_prog.inject(1) het_prog_eval.elims(2) het_state_eval_def map_sum.simps(1))
  next
    case (Inr b)
    then show ?case
      unfolding het_dyn_prog_BV.simps
      using assms
      unfolding het_dl.dyn_prog_bv_sem.simps
      unfolding dyn_log_1.dyn_prog_bv_sem.simps
      unfolding het_prog_eval.simps
      by (metis common_atom_eval_def het_prog_eval.simps(1) het_state_eval_def map_sum.simps(2) split_pairs)
  qed
next
  case (PROG2 x)
  then show ?case
  proof (induct v)
    case (Inl a)
    then show ?case
      unfolding het_dyn_prog_BV.simps
      using assms
      unfolding het_dl.dyn_prog_bv_sem.simps
      unfolding dyn_log_2.dyn_prog_bv_sem.simps
      unfolding het_prog_eval.simps
      by (smt (verit, ccfv_SIG) common_atom_eval_def fst_conv het_prog_eval.elims(2) het_prog_eval.simps(2) het_state_eval_def map_sum.simps(1))
  next
    case (Inr b)
    then show ?case
      unfolding het_dyn_prog_BV.simps
      using assms
      unfolding het_dl.dyn_prog_bv_sem.simps
      unfolding dyn_log_2.dyn_prog_bv_sem.simps
      unfolding het_prog_eval.simps
      by (simp add: common_atom_eval_def)
  qed
qed

subsection\<open>Full Heterogeneous Dynamic Theories\<close>
text\<open>
We have now established that our heterogeneous atoms and programs
form a dynamic theory.
Based of this knowledge, we \emph{lift} the dynamic theory to support havoc
and regular programs:
\<close>

interpretation het_dl_havoc : 
    havoc_lifting het_atom_eval het_atom_fv_syn het_state_eval het_prog_eval het_dyn_prog_FV
  using havoc_lifting_def het_dl.dynamic_theory_axioms by blast

sublocale hdl_havoc:
    havoc_lifting het_atom_eval het_atom_fv_syn het_state_eval het_prog_eval het_dyn_prog_FV
  using het_dl_havoc.havoc_lifting_axioms by blast

interpretation het_dl_kat :
    regular_lifting  "het_atom_eval" "het_atom_fv_syn" "het_state_eval" "het_dl_havoc.full_prog_eval" "het_dl_havoc.full_prog_FV"
  using regular_lifting_def het_dl_havoc.havoc_dl.dynamic_theory_axioms by blast

sublocale hdl_kat:
    regular_lifting  "het_atom_eval" "het_atom_fv_syn" "het_state_eval" "het_dl_havoc.full_prog_eval" "het_dl_havoc.full_prog_FV"
  using het_dl_kat.regular_lifting_axioms by force

subsection\<open>Proof Rules\<close>
text\<open>
The main objective of heterogeneous dynamic theories,
is to \emph{reuse} proof results established for individual theories
to reason about combined systems.
To this end, we ``only'' introduce two additional heterogenous dynamic theories:
A rule to lift results from dynamic theory 0 and a rule to lift
results from dynamic theory 1.
\<close>

paragraph\<open>Purity.\<close>
text\<open>
To formalize these rules, we first define what it means to be ``pure'' for a
formula in heterogeneous dynamic logic:
\<close>

fun is_het_prog_pure :: "nat \<Rightarrow> ('prog1, 'prog2) het_prog \<Rightarrow> bool"
  where
    "is_het_prog_pure i (PROG1 \<pi>) = (i=0)"
  | "is_het_prog_pure i (PROG2 \<pi>) = (i=1)"

fun is_havoc_prog_pure :: "nat \<Rightarrow> (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog \<Rightarrow> bool"
  where
    "is_havoc_prog_pure i (HPROG \<pi>) = (is_het_prog_pure i \<pi>)"
  | "is_havoc_prog_pure i \<pi> = False"

fun is_kat_prog_pure :: "nat \<Rightarrow> (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog \<Rightarrow> bool"
  where
    "is_kat_prog_pure i (KATPROG \<pi>) = (is_havoc_prog_pure i \<pi>)"
  | "is_kat_prog_pure i \<pi> = False"

fun is_atom_pure :: "nat \<Rightarrow> ('atom1,'atom2,'atom_comm) het_atom \<Rightarrow> bool"
  where
    "is_atom_pure i (ATOM1 a) = (i=0)"
  | "is_atom_pure i (ATOM2 a) = (i=1)"
  | "is_atom_pure i (ATOMC a) = False"

fun is_fol_pure :: "nat \<Rightarrow> (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2
                    ) fol_formula \<Rightarrow> bool"
  where
    "is_fol_pure i (ATOM a) = (is_atom_pure i a)"
  | "is_fol_pure i (\<phi> foland \<psi>) = ((is_fol_pure i \<phi>) \<and> (is_fol_pure i \<psi>))"
  | "is_fol_pure i (folnot \<phi>) = is_fol_pure i \<phi>"
  | "is_fol_pure i (folall (Inl v) \<phi>) = ((i=0) \<and> (is_fol_pure i \<phi>))"
  | "is_fol_pure i (folall (Inr v) \<phi>) = ((i=1) \<and> (is_fol_pure i \<phi>))"

fun is_fml_pure :: "nat \<Rightarrow> (
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog
                  ) dyn_formula \<Rightarrow> bool"
  where
    "is_fml_pure i (FOL \<phi>) = is_fol_pure i \<phi>"
  | "is_fml_pure i (AND \<phi> \<psi>) = ((is_fml_pure i \<phi>) \<and> (is_fml_pure i \<psi>))"
  | "is_fml_pure i (NOT \<phi>) = is_fml_pure i \<phi>"
  | "is_fml_pure i (FOL_ALL (Inl v) \<phi>) = ((i=0) \<and> (is_fml_pure i \<phi>))"
  | "is_fml_pure i (FOL_ALL (Inr v) \<phi>) = ((i=1) \<and> (is_fml_pure i \<phi>))"
  | "is_fml_pure i (BOX \<pi> \<phi>) = ((is_kat_prog_pure i \<pi>) \<and> (is_fml_pure i \<phi>))"


fun is_fml_pure_simple :: "nat \<Rightarrow> (
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      ('prog1, 'prog2) het_prog
                  ) dyn_formula \<Rightarrow> bool"
  where
    "is_fml_pure_simple i (FOL \<phi>) = is_fol_pure i \<phi>"
  | "is_fml_pure_simple i (AND \<phi> \<psi>) = ((is_fml_pure_simple i \<phi>) \<and> (is_fml_pure_simple i \<psi>))"
  | "is_fml_pure_simple i (NOT \<phi>) = is_fml_pure_simple i \<phi>"
  | "is_fml_pure_simple i (FOL_ALL (Inl v) \<phi>) = ((i=0) \<and> (is_fml_pure_simple i \<phi>))"
  | "is_fml_pure_simple i (FOL_ALL (Inr v) \<phi>) = ((i=1) \<and> (is_fml_pure_simple i \<phi>))"
  | "is_fml_pure_simple i (BOX \<pi> \<phi>) = ((is_het_prog_pure i \<pi>) \<and> (is_fml_pure_simple i \<phi>))"

fun fol_purify_1 :: "(
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2
                    ) fol_formula \<Rightarrow> (
                        'atom1,
                        'var1
                    ) fol_formula"
  where
    "fol_purify_1 (ATOM (ATOM1 a)) = (ATOM a)"
  | "fol_purify_1 (ATOM b) = undefined"
  | "fol_purify_1 (\<phi> foland \<psi>) = ((fol_purify_1 \<phi>) foland (fol_purify_1 \<psi>))"
  | "fol_purify_1 (folnot \<phi>) = (folnot (fol_purify_1 \<phi>))"
  | "fol_purify_1 (folall (Inl v) \<phi>) = (folall v (fol_purify_1 \<phi>))"
  | "fol_purify_1 (folall (Inr v) \<phi>) = undefined"

fun fol_heterify_1 :: "(
                        'atom1,
                        'var1
                    ) fol_formula \<Rightarrow> (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2
                    ) fol_formula"
  where
    "fol_heterify_1 (ATOM a) = (ATOM (ATOM1 a))"
  | "fol_heterify_1 (\<phi> foland \<psi>) = ((fol_heterify_1 \<phi>) foland (fol_heterify_1 \<psi>))"
  | "fol_heterify_1 (folnot \<phi>) = (folnot (fol_heterify_1 \<phi>))"
  | "fol_heterify_1 (folall v \<phi>) = (folall (Inl v) (fol_heterify_1 \<phi>))"

fun fol_heterify_2 :: "(
                        'atom2,
                        'var2
                    ) fol_formula \<Rightarrow> (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2
                    ) fol_formula"
  where
    "fol_heterify_2 (ATOM a) = (ATOM (ATOM2 a))"
  | "fol_heterify_2 (\<phi> foland \<psi>) = ((fol_heterify_2 \<phi>) foland (fol_heterify_2 \<psi>))"
  | "fol_heterify_2 (folnot \<phi>) = (folnot (fol_heterify_2 \<phi>))"
  | "fol_heterify_2 (folall v \<phi>) = (folall (Inr v) (fol_heterify_2 \<phi>))"

fun prog_purify_simple_1 :: "('prog1, 'prog2) het_prog
                         \<Rightarrow> 'prog1"
  where
    "prog_purify_simple_1 (PROG1 \<pi>) = \<pi>"
  | "prog_purify_simple_1 \<pi> = undefined"

fun prog_purify_1 :: "(
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog \<Rightarrow> 'prog1"
  where
    "prog_purify_1 (KATPROG (HPROG (PROG1 \<pi>))) = \<pi>"
  | "prog_purify_1 \<pi> = undefined"

fun fml_purify_1 :: "(
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog
                  ) dyn_formula \<Rightarrow> ('atom1,'var1,'prog1) dyn_formula"
  where
    "fml_purify_1 (FOL \<phi>) = (FOL (fol_purify_1 \<phi>))"
  | "fml_purify_1 (AND \<phi> \<psi>) = (AND (fml_purify_1 \<phi>) (fml_purify_1 \<psi>))"
  | "fml_purify_1 (NOT \<phi>) = (NOT (fml_purify_1 \<phi>))"
  | "fml_purify_1 (FOL_ALL (Inl v) \<phi>) = (FOL_ALL v (fml_purify_1 \<phi>))"
  | "fml_purify_1 (FOL_ALL (Inr v) \<phi>) = undefined"
  | "fml_purify_1 (BOX \<pi> \<phi>) = (BOX (prog_purify_1 \<pi>) (fml_purify_1 \<phi>))"

fun fml_purify_simple_1 :: "(
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      ('prog1, 'prog2) het_prog
                  ) dyn_formula \<Rightarrow> ('atom1,'var1,'prog1) dyn_formula"
  where
    "fml_purify_simple_1 (FOL \<phi>) = (FOL (fol_purify_1 \<phi>))"
  | "fml_purify_simple_1 (AND \<phi> \<psi>) = (AND (fml_purify_simple_1 \<phi>) (fml_purify_simple_1 \<psi>))"
  | "fml_purify_simple_1 (NOT \<phi>) = (NOT (fml_purify_simple_1 \<phi>))"
  | "fml_purify_simple_1 (FOL_ALL (Inl v) \<phi>) = (FOL_ALL v (fml_purify_simple_1 \<phi>))"
  | "fml_purify_simple_1 (FOL_ALL (Inr v) \<phi>) = undefined"
  | "fml_purify_simple_1 (BOX \<pi> \<phi>) = (BOX (prog_purify_simple_1 \<pi>) (fml_purify_simple_1 \<phi>))"

fun fol_purify_2 :: "(
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2
                    ) fol_formula \<Rightarrow> (
                        'atom2,
                        'var2
                    ) fol_formula"
  where
    "fol_purify_2 (ATOM (ATOM2 a)) = (ATOM a)"
  | "fol_purify_2 (ATOM b) = undefined"
  | "fol_purify_2 (\<phi> foland \<psi>) = ((fol_purify_2 \<phi>) foland (fol_purify_2 \<psi>))"
  | "fol_purify_2 (folnot \<phi>) = (folnot (fol_purify_2 \<phi>))"
  | "fol_purify_2 (folall (Inr v) \<phi>) = (folall v (fol_purify_2 \<phi>))"
  | "fol_purify_2 (folall (Inl v) \<phi>) = undefined"

fun prog_purify_2 :: "(
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog \<Rightarrow> 'prog2"
  where
    "prog_purify_2 (KATPROG (HPROG (PROG2 \<pi>))) = \<pi>"
  | "prog_purify_2 \<pi> = undefined"

fun prog_purify_simple_2 :: "('prog1, 'prog2) het_prog
                         \<Rightarrow> 'prog2"
  where
    "prog_purify_simple_2 (PROG2 \<pi>) = \<pi>"
  | "prog_purify_simple_2 \<pi> = undefined"

fun fml_purify_2 :: "(
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      (
                        ('atom1, 'atom2, 'atom_comm) het_atom,
                        'var1 + 'var2,
                        (
                          ('atom1, 'atom2, 'atom_comm) het_atom,
                          'var1 + 'var2,
                          ('prog1, 'prog2) het_prog
                        ) havoc_prog
                      ) kat_prog
                  ) dyn_formula \<Rightarrow> ('atom2,'var2,'prog2) dyn_formula"
  where
    "fml_purify_2 (FOL \<phi>) = (FOL (fol_purify_2 \<phi>))"
  | "fml_purify_2 (AND \<phi> \<psi>) = (AND (fml_purify_2 \<phi>) (fml_purify_2 \<psi>))"
  | "fml_purify_2 (NOT \<phi>) = (NOT (fml_purify_2 \<phi>))"
  | "fml_purify_2 (FOL_ALL (Inr v) \<phi>) = (FOL_ALL v (fml_purify_2 \<phi>))"
  | "fml_purify_2 (FOL_ALL (Inl v) \<phi>) = undefined"
  | "fml_purify_2 (BOX \<pi> \<phi>) = (BOX (prog_purify_2 \<pi>) (fml_purify_2 \<phi>))"

fun fml_purify_simple_2 :: "(
                      ('atom1, 'atom2, 'atom_comm) het_atom,
                      'var1 + 'var2,
                      ('prog1, 'prog2) het_prog
                  ) dyn_formula \<Rightarrow> ('atom2,'var2,'prog2) dyn_formula"
  where
    "fml_purify_simple_2 (FOL \<phi>) = (FOL (fol_purify_2 \<phi>))"
  | "fml_purify_simple_2 (AND \<phi> \<psi>) = (AND (fml_purify_simple_2 \<phi>) (fml_purify_simple_2 \<psi>))"
  | "fml_purify_simple_2 (NOT \<phi>) = (NOT (fml_purify_simple_2 \<phi>))"
  | "fml_purify_simple_2 (FOL_ALL (Inr v) \<phi>) = (FOL_ALL v (fml_purify_simple_2 \<phi>))"
  | "fml_purify_simple_2 (FOL_ALL (Inl v) \<phi>) = undefined"
  | "fml_purify_simple_2 (BOX \<pi> \<phi>) = (BOX (prog_purify_simple_2 \<pi>) (fml_purify_simple_2 \<phi>))"

lemma purify_heterify_inverse:
  "(fol_purify_1 (fol_heterify_1 P)) = P"
proof (induct P)
  case (ATOM x)
  then show ?case
    unfolding fol_heterify_1.simps
    unfolding fol_purify_1.simps
    by simp
next
  case (AND P1 P2)
  then show ?case
    unfolding fol_heterify_1.simps
    unfolding fol_purify_1.simps
    by simp
next
  case (NOT P)
  then show ?case
    unfolding fol_heterify_1.simps
    unfolding fol_purify_1.simps
    by simp
next
  case (FOL_ALL x1a P)
  then show ?case
    unfolding fol_heterify_1.simps
    unfolding fol_purify_1.simps
    by simp
qed

paragraph\<open>Semantic Implications\<close>
text\<open>Based on the purity definition above, we can show the semantic implications
of purity of a formula w.r.t. dynamic theory 0/1:
A formula holds in the individual theory iff it holds for all adjoined states:
\<close>

lemma dyn_het_simple_equiv_0:
  assumes "is_fml_pure_simple 0 \<phi>"
  shows "((dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) s1) \<longrightarrow>
           (\<forall> s2 . (het_dl.dyn_eval \<phi> (s1,s2)))) \<and>
          ((\<forall> s2 . (het_dl.dyn_eval \<phi> (s1,s2))) \<longrightarrow>
           (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) s1))"
proof -
  have reformulatation: "\<And> \<phi> \<mu> .  is_fml_pure_simple 0 \<phi> \<Longrightarrow> 
        ((dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>)) \<longrightarrow>
         (het_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>)))"
  proof -
    fix \<phi>
    show "\<And> \<mu> .  is_fml_pure_simple 0 \<phi> \<Longrightarrow> 
        ((dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>)) \<longrightarrow>
         (het_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>)))"
    proof (induct \<phi>)
      case (FOL \<psi>)

      have "is_fol_pure 0 \<psi>"
        using FOL by auto

      then have "\<And> \<mu> . (dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>) \<longrightarrow>
     het_fol.fol_eval \<psi> \<mu>) \<and>
    (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
     dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>))"
        proof (induct \<psi>)
          case (ATOM x)
          then show ?case
          proof (induct x)
            case (ATOM1 x)
            then show ?case
              unfolding fol_purify_1.simps
              unfolding dyn_log_1.fol_eval.simps
              unfolding het_fol.fol_eval.simps
              unfolding het_atom_eval.simps
              by simp
          next
            case (ATOM2 x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by linarith
          next
            case (ATOMC x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by simp
          qed
        next
          case (AND \<psi>1 \<psi>2)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_1.simps
          unfolding dyn_log_1.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          by simp
        next
          case (NOT \<psi>)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_1.simps
          unfolding dyn_log_1.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          unfolding is_fol_pure.simps
          by blast
        next
          case (FOL_ALL x1a \<psi>)
          assume fol_pure: "is_fol_pure 0 (folall x1a \<psi>)"
          then show ?case
          proof (induct x1a)
            case (Inl a)
            assume fol_inl_pure: "is_fol_pure 0 (folall Inl a \<psi>)"
              have outer_ind_hyp: "(\<And>\<mu>. is_fol_pure 0 \<psi> \<Longrightarrow>
                   (dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>) \<longrightarrow>
                    het_fol.fol_eval \<psi> \<mu>) \<and>
                   (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
                    dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>)))"
                using FOL_ALL.hyps by blast
            then show ?case
              unfolding is_fml_pure.simps
              unfolding fol_purify_1.simps
              unfolding dyn_log_1.fol_eval.simps
              unfolding het_fol.fol_eval.simps
            proof (intro conjI)
              show "(\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                            dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_dl1: "\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                           dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>"
                assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega>"
                then have "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) (fst \<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_1.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_1.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by fastforce
    
                then show "het_fol.fol_eval \<psi> \<omega>"
                  using sat_in_dl1
                  apply (elim allE[of _ "(fst \<omega>)"])
                  using outer_ind_hyp[of "\<omega>"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by blast
              qed
              show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                            dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_hdl: "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
                assume omega_hyp: "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega>"
                then have "het_fol.fol_equal_everywhere_but (Inl a) \<mu> (\<omega>,(snd \<mu>))"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_1.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_1.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by (metis fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)
    
                then show "dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>"
                  using sat_in_hdl
                  apply (elim allE[of _ "(\<omega>, snd \<mu>)"])
                  using outer_ind_hyp[of "(\<omega>, snd \<mu>)"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by force
              qed
            qed
          next
            case (Inr b)
            then show ?case
              unfolding is_fol_pure.simps
              by linarith
          qed
        qed
      thus ?case
        unfolding fml_purify_simple_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by blast
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        unfolding fml_purify_simple_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        unfolding is_fml_pure_simple.simps
        unfolding fml_purify_simple_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by blast
    next
      case (FOL_ALL x1a \<phi>)
      assume fol_pure: "is_fml_pure_simple 0 (\<bbbA> x1a . \<phi>)"
      then show ?case
      proof (induct x1a)
        case (Inl a)
        assume fol_inl_pure: "is_fml_pure_simple 0 (\<bbbA> Inl a . \<phi>)"
          have outer_ind_hyp: "\<And> \<mu> . is_fml_pure_simple 0 \<phi> \<Longrightarrow>
                (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>) \<longrightarrow>
                 het_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>))"
            using FOL_ALL.hyps by blast
        then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_simple_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl.dyn_eval.simps
        proof (intro conjI)
          show "(\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                        dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                        het_dl.dyn_eval \<phi> \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_dl1: "\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
             dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>"
            assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega>"
            then have "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) (fst \<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_1.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_1.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by fastforce

            then show "het_dl.dyn_eval \<phi> \<omega>"
              using sat_in_dl1
              apply (elim allE[of _ "(fst \<omega>)"])
              using outer_ind_hyp[of "\<omega>"]
              using fol_inl_pure
              unfolding is_fml_pure_simple.simps
              by blast
          qed
          show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                        het_dl.dyn_eval \<phi> \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                        dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_hdl: "\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
             het_dl.dyn_eval \<phi> \<omega>"
            assume omega_hyp: "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega>"
            then have "het_fol.fol_equal_everywhere_but (Inl a) \<mu> (\<omega>,(snd \<mu>))"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_1.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_1.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by (metis fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)

            then show "dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>"
              using sat_in_hdl
              apply (elim allE[of _ "(\<omega>, snd \<mu>)"])
              using outer_ind_hyp[of "(\<omega>, snd \<mu>)"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by force
          qed
        qed
      next
        case (Inr b)
        then show ?case
          unfolding is_fml_pure_simple.simps
          by linarith
      qed
    next
      case (BOX x1a \<phi>)
      then show ?case
      proof (induct x1a)
        have outer_ind_hyp: "\<And> \<mu> . is_fml_pure_simple 0 \<phi> \<Longrightarrow>
                (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>) \<longrightarrow>
                 het_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>))"
          using BOX.hyps by blast
          case (PROG1 x)
            then show ?case
              unfolding fml_purify_simple_1.simps prog_purify_simple_1.simps
            proof (intro conjI)
              assume ind_hyp: "(\<And>\<mu>. is_fml_pure_simple 0 \<phi> \<Longrightarrow>
                    (dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>) \<longrightarrow>
                     het_dl.dyn_eval \<phi> \<mu>) \<and>
                    (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                     dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) (fst \<mu>)))"
              assume prog_pure: "is_fml_pure_simple 0 (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>)"
              show "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) (fst \<mu>) \<longrightarrow>
                      het_dl.dyn_eval (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>) \<mu>"
              proof (intro impI)
                let ?\<mu>1 = "(fst \<mu>)"
                let ?\<mu>2 = "(snd \<mu>)"

                assume "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) ?\<mu>1"
                then have "\<forall>\<omega>1 \<omega>2. (prog_eval1 x (fst \<mu>) \<omega>1 \<and>
                  state_eval2 (snd \<mu>) = state_eval2 \<omega>2) \<longrightarrow> het_dl.dyn_eval \<phi> (\<omega>1,\<omega>2)"
                  proof (intro allI,intro impI)
                    fix \<omega>1 \<omega>2
                    show "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) (fst \<mu>) \<Longrightarrow>
                           (prog_eval1 x (fst \<mu>) \<omega>1 \<and>
                                state_eval2 (snd \<mu>) = state_eval2 \<omega>2) \<Longrightarrow>
                           het_dl.dyn_eval \<phi> (\<omega>1, \<omega>2)"
                    unfolding dyn_log_1.dyn_eval.simps
                    apply (elim allE[of _ \<omega>1])
                    using ind_hyp[of "(\<omega>1,\<omega>2)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by simp
                qed
                thus "het_dl.dyn_eval (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>) \<mu>"
                  unfolding het_dl.dyn_eval.simps
                  by (metis HeterogeneousDynLog.het_prog_eval.simps(1) HeterogeneousDynLog_axioms
                      prod.exhaust_sel)
              qed
              show "het_dl.dyn_eval (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>) \<mu>
                    \<longrightarrow> dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) (fst \<mu>)"
              proof (intro impI)
                let ?\<mu>1 = "(fst \<mu>)"
                let ?\<mu>2 = "(snd \<mu>)"
                assume "het_dl.dyn_eval (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>) \<mu>"
                then have sat_in_het: "het_dl.dyn_eval (\<lbrakk> (PROG1 x) \<rbrakk> \<phi>) (?\<mu>1,?\<mu>2)"
                  by force
                have "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) (fst \<mu>)"
                  unfolding dyn_log_1.dyn_eval.simps
                proof (intro allI, intro impI)
                  fix \<omega>
                  let ?\<omega>2 = "(snd \<mu>)"
                  have "prog_eval1 x (fst \<mu>) \<omega> \<Longrightarrow>
                    (prog_eval1 x (fst \<mu>) \<omega> \<and> state_eval2 (snd \<mu>) = state_eval2 ?\<omega>2) \<longrightarrow>
                    het_dl.dyn_eval \<phi> (\<omega>, ?\<omega>2) \<Longrightarrow>
                    dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>"
                    using ind_hyp[of "(\<omega>,?\<omega>2)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by auto
                  thus "prog_eval1 x (fst \<mu>) \<omega> \<Longrightarrow> dyn_log_1.dyn_eval (fml_purify_simple_1 \<phi>) \<omega>"
                    using sat_in_het
                    unfolding het_dl.dyn_eval.simps
                    apply (elim allE[of _ "(\<omega>,?\<omega>2)"])
                    unfolding het_dl_kat.full_prog_eval_def
                    unfolding het_dl_kat.full_prog_eval_int.simps
                    unfolding het_dl_havoc.full_prog_eval.simps
                    unfolding het_prog_eval.simps
                    by blast
                qed
                thus "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_1 \<phi>) (fst \<mu>)"
                  by simp
              qed
            qed
          next
            case (PROG2 x)
            then show ?case
              unfolding is_fml_pure_simple.simps
              unfolding is_het_prog_pure.simps
              by linarith
          qed
        qed
      qed
  show ?thesis
    using assms
    using reformulatation
    by auto
qed


lemma dyn_het_simple_equiv_1:
  assumes "is_fml_pure_simple 1 \<phi>"
  shows "((dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) s2) \<longrightarrow>
           (\<forall> s1 . (het_dl.dyn_eval \<phi> (s1,s2)))) \<and>
          ((\<forall> s1 . (het_dl.dyn_eval \<phi> (s1,s2))) \<longrightarrow>
           (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) s2))"
proof -
  have reformulatation: "\<And> \<phi> \<mu> .  is_fml_pure_simple 1 \<phi> \<Longrightarrow> 
        ((dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>)) \<longrightarrow>
         (het_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>)))"
  proof -
    fix \<phi>
    show "\<And> \<mu> .  is_fml_pure_simple 1 \<phi> \<Longrightarrow> 
        ((dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>)) \<longrightarrow>
         (het_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>)))"
    proof (induct \<phi>)
      case (FOL \<psi>)

      have "is_fol_pure 1 \<psi>"
        using FOL by auto

      then have "\<And> \<mu> . (dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>) \<longrightarrow>
     het_fol.fol_eval \<psi> \<mu>) \<and>
    (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
     dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>))"
        proof (induct \<psi>)
          case (ATOM x)
          then show ?case
          proof (induct x)
            case (ATOM2 x)
            then show ?case
              unfolding fol_purify_2.simps
              unfolding dyn_log_2.fol_eval.simps
              unfolding het_fol.fol_eval.simps
              unfolding het_atom_eval.simps
              by simp
          next
            case (ATOM1 x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by linarith
          next
            case (ATOMC x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by simp
          qed
        next
          case (AND \<psi>1 \<psi>2)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_2.simps
          unfolding dyn_log_2.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          by simp
        next
          case (NOT \<psi>)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_2.simps
          unfolding dyn_log_2.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          unfolding is_fol_pure.simps
          by blast
        next
          case (FOL_ALL x1a \<psi>)
          assume fol_pure: "is_fol_pure 1 (folall x1a \<psi>)"
          then show ?case
          proof (induct x1a)
            case (Inr a)
            assume fol_inl_pure: "is_fol_pure 1 (folall Inr a \<psi>)"
              have outer_ind_hyp: "(\<And>\<mu>. is_fol_pure 1 \<psi> \<Longrightarrow>
                   (dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>) \<longrightarrow>
                    het_fol.fol_eval \<psi> \<mu>) \<and>
                   (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
                    dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>)))"
                using FOL_ALL.hyps by blast
            then show ?case
              unfolding is_fml_pure.simps
              unfolding fol_purify_2.simps
              unfolding dyn_log_2.fol_eval.simps
              unfolding het_fol.fol_eval.simps
            proof (intro conjI)
              show "(\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                            dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_dl1: "\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                           dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>"
                assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega>"
                then have "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) (snd \<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_2.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_2.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by fastforce
    
                then show "het_fol.fol_eval \<psi> \<omega>"
                  using sat_in_dl1
                  apply (elim allE[of _ "(snd \<omega>)"])
                  using outer_ind_hyp[of "\<omega>"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by blast
              qed
              show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                            dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_hdl: "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
                assume omega_hyp: "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega>"
                then have "het_fol.fol_equal_everywhere_but (Inr a) \<mu> ((fst \<mu>),\<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_2.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_2.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by (metis snd_conv map_sum.simps(1) map_sum.simps(2) fst_conv sumE)
    
                then show "dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>"
                  using sat_in_hdl
                  apply (elim allE[of _ "(fst \<mu>, \<omega>)"])
                  using outer_ind_hyp[of "(fst \<mu>, \<omega>)"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by force
              qed
            qed
          next
            case (Inl b)
            then show ?case
              unfolding is_fol_pure.simps
              by linarith
          qed
        qed
      thus ?case
        unfolding fml_purify_simple_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by blast
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        unfolding fml_purify_simple_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        unfolding is_fml_pure_simple.simps
        unfolding fml_purify_simple_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl.dyn_eval.simps
        by blast
    next
      case (FOL_ALL x1a \<phi>)
      assume fol_pure: "is_fml_pure_simple 1 (\<bbbA> x1a . \<phi>)"
      then show ?case
      proof (induct x1a)
        case (Inr a)
        assume fol_inl_pure: "is_fml_pure_simple 1 (\<bbbA> Inr a . \<phi>)"
          have outer_ind_hyp: "\<And> \<mu> . is_fml_pure_simple 1 \<phi> \<Longrightarrow>
                (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>) \<longrightarrow>
                 het_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>))"
            using FOL_ALL.hyps by blast
        then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_simple_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl.dyn_eval.simps
        proof (intro conjI)
          show "(\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                        dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                        het_dl.dyn_eval \<phi> \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_dl1: "\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
             dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>"
            assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega>"
            then have "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) (snd \<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_2.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_2.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by fastforce

            then show "het_dl.dyn_eval \<phi> \<omega>"
              using sat_in_dl1
              apply (elim allE[of _ "(snd \<omega>)"])
              using outer_ind_hyp[of "\<omega>"]
              using fol_inl_pure
              unfolding is_fml_pure_simple.simps
              by blast
          qed
          show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                        het_dl.dyn_eval \<phi> \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                        dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_hdl: "\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
             het_dl.dyn_eval \<phi> \<omega>"
            assume omega_hyp: "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega>"
            then have "het_fol.fol_equal_everywhere_but (Inr a) \<mu> ((fst \<mu>),\<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_2.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_2.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by (metis snd_conv map_sum.simps(1) map_sum.simps(2) fst_conv sumE)

            then show "dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>"
              using sat_in_hdl
              apply (elim allE[of _ "(fst \<mu>,\<omega>)"])
              using outer_ind_hyp[of "(fst \<mu>,\<omega>)"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by force
          qed
        qed
      next
        case (Inl b)
        then show ?case
          unfolding is_fml_pure_simple.simps
          by linarith
      qed
    next
      case (BOX x1a \<phi>)
      then show ?case
      proof (induct x1a)
        have outer_ind_hyp: "\<And> \<mu> . is_fml_pure_simple 1 \<phi> \<Longrightarrow>
                (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>) \<longrightarrow>
                 het_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>))"
          using BOX.hyps by blast
          case (PROG2 x)
            then show ?case
              unfolding fml_purify_simple_2.simps prog_purify_simple_2.simps
            proof (intro conjI)
              assume ind_hyp: "(\<And>\<mu>. is_fml_pure_simple 1 \<phi> \<Longrightarrow>
                    (dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>) \<longrightarrow>
                     het_dl.dyn_eval \<phi> \<mu>) \<and>
                    (het_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                     dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) (snd \<mu>)))"
              assume prog_pure: "is_fml_pure_simple 1 (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>)"
              show "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) (snd \<mu>) \<longrightarrow>
                      het_dl.dyn_eval (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>) \<mu>"
              proof (intro impI)
                let ?\<mu>1 = "(snd \<mu>)"
                let ?\<mu>2 = "(fst \<mu>)"

                assume "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) ?\<mu>1"
                then have "\<forall>\<omega>1 \<omega>2. (prog_eval2 x (snd \<mu>) \<omega>1 \<and>
                  state_eval1 (fst \<mu>) = state_eval1 \<omega>2) \<longrightarrow> het_dl.dyn_eval \<phi> (\<omega>2,\<omega>1)"
                  proof (intro allI,intro impI)
                    fix \<omega>1 \<omega>2
                    show "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) (snd \<mu>) \<Longrightarrow>
                           (prog_eval2 x (snd \<mu>) \<omega>1 \<and>
                                state_eval1 (fst \<mu>) = state_eval1 \<omega>2) \<Longrightarrow>
                           het_dl.dyn_eval \<phi> (\<omega>2,\<omega>1)"
                    unfolding dyn_log_2.dyn_eval.simps
                    apply (elim allE[of _ \<omega>1])
                    using ind_hyp[of "(\<omega>2,\<omega>1)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by simp
                qed
                thus "het_dl.dyn_eval (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>) \<mu>"
                  unfolding het_dl.dyn_eval.simps
                  by (metis HeterogeneousDynLog.het_prog_eval.simps(2) HeterogeneousDynLog_axioms
                      prod.exhaust_sel)
              qed
              show "het_dl.dyn_eval (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>) \<mu>
                    \<longrightarrow> dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) (snd \<mu>)"
              proof (intro impI)
                let ?\<mu>1 = "(snd \<mu>)"
                let ?\<mu>2 = "(fst \<mu>)"
                assume "het_dl.dyn_eval (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>) \<mu>"
                then have sat_in_het: "het_dl.dyn_eval (\<lbrakk> (PROG2 x) \<rbrakk> \<phi>) (?\<mu>2,?\<mu>1)"
                  by force
                have "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) (snd \<mu>)"
                  unfolding dyn_log_2.dyn_eval.simps
                proof (intro allI, intro impI)
                  fix \<omega>
                  let ?\<omega>2 = "(fst \<mu>)"
                  have "prog_eval2 x (snd \<mu>) \<omega> \<Longrightarrow>
                    (prog_eval2 x (snd \<mu>) \<omega> \<and> state_eval1 (fst \<mu>) = state_eval1 ?\<omega>2) \<longrightarrow>
                    het_dl.dyn_eval \<phi> (?\<omega>2,\<omega>) \<Longrightarrow>
                    dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>"
                    using ind_hyp[of "(?\<omega>2,\<omega>)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by auto
                  thus "prog_eval2 x (snd \<mu>) \<omega> \<Longrightarrow> dyn_log_2.dyn_eval (fml_purify_simple_2 \<phi>) \<omega>"
                    using sat_in_het
                    unfolding het_dl.dyn_eval.simps
                    apply (elim allE[of _ "(?\<omega>2,\<omega>)"])
                    unfolding het_dl_kat.full_prog_eval_def
                    unfolding het_dl_kat.full_prog_eval_int.simps
                    unfolding het_dl_havoc.full_prog_eval.simps
                    unfolding het_prog_eval.simps
                    by blast
                qed
                thus "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_simple_2 \<phi>) (snd \<mu>)"
                  by simp
              qed
            qed
          next
            case (PROG1 x)
            then show ?case
              unfolding is_fml_pure_simple.simps
              unfolding is_het_prog_pure.simps
              by linarith
          qed
        qed
      qed
  show ?thesis
    using assms
    using reformulatation
    by auto
qed

lemma dyn_het_equiv_0:
  assumes "is_fml_pure 0 \<phi>"
  shows "((dyn_log_1.dyn_eval (fml_purify_1 \<phi>) s1) \<longrightarrow>
           (\<forall> s2 . (het_dl_kat.kat_dl.dyn_eval \<phi> (s1,s2)))) \<and>
          ((\<forall> s2 . (het_dl_kat.kat_dl.dyn_eval \<phi> (s1,s2))) \<longrightarrow>
           (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) s1))"
proof -
  have reformulatation: "\<And> \<phi> \<mu> .  is_fml_pure 0 \<phi> \<Longrightarrow> 
        ((dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>)) \<longrightarrow>
         (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>)))"
  proof -
    fix \<phi>
    show "\<And> \<mu> .  is_fml_pure 0 \<phi> \<Longrightarrow> 
        ((dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>)) \<longrightarrow>
         (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>)))"
    proof (induct \<phi>)
      case (FOL \<psi>)

      have "is_fol_pure 0 \<psi>"
        using FOL by auto

      then have "\<And> \<mu> . (dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>) \<longrightarrow>
     het_fol.fol_eval \<psi> \<mu>) \<and>
    (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
     dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>))"
        proof (induct \<psi>)
          case (ATOM x)
          then show ?case
          proof (induct x)
            case (ATOM1 x)
            then show ?case
              unfolding fol_purify_1.simps
              unfolding dyn_log_1.fol_eval.simps
              unfolding het_fol.fol_eval.simps
              unfolding het_atom_eval.simps
              by simp
          next
            case (ATOM2 x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by linarith
          next
            case (ATOMC x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by simp
          qed
        next
          case (AND \<psi>1 \<psi>2)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_1.simps
          unfolding dyn_log_1.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          by simp
        next
          case (NOT \<psi>)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_1.simps
          unfolding dyn_log_1.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          unfolding is_fol_pure.simps
          by blast
        next
          case (FOL_ALL x1a \<psi>)
          assume fol_pure: "is_fol_pure 0 (folall x1a \<psi>)"
          then show ?case
          proof (induct x1a)
            case (Inl a)
            assume fol_inl_pure: "is_fol_pure 0 (folall Inl a \<psi>)"
              have outer_ind_hyp: "(\<And>\<mu>. is_fol_pure 0 \<psi> \<Longrightarrow>
                   (dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>) \<longrightarrow>
                    het_fol.fol_eval \<psi> \<mu>) \<and>
                   (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
                    dyn_log_1.fol_eval (fol_purify_1 \<psi>) (fst \<mu>)))"
                using FOL_ALL.hyps by blast
            then show ?case
              unfolding is_fml_pure.simps
              unfolding fol_purify_1.simps
              unfolding dyn_log_1.fol_eval.simps
              unfolding het_fol.fol_eval.simps
            proof (intro conjI)
              show "(\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                            dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_dl1: "\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                           dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>"
                assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega>"
                then have "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) (fst \<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_1.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_1.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by fastforce
    
                then show "het_fol.fol_eval \<psi> \<omega>"
                  using sat_in_dl1
                  apply (elim allE[of _ "(fst \<omega>)"])
                  using outer_ind_hyp[of "\<omega>"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by blast
              qed
              show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                            dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_hdl: "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
                assume omega_hyp: "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega>"
                then have "het_fol.fol_equal_everywhere_but (Inl a) \<mu> (\<omega>,(snd \<mu>))"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_1.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_1.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by (metis fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)
    
                then show "dyn_log_1.fol_eval (fol_purify_1 \<psi>) \<omega>"
                  using sat_in_hdl
                  apply (elim allE[of _ "(\<omega>, snd \<mu>)"])
                  using outer_ind_hyp[of "(\<omega>, snd \<mu>)"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by force
              qed
            qed
          next
            case (Inr b)
            then show ?case
              unfolding is_fol_pure.simps
              by linarith
          qed
        qed
      thus ?case
        unfolding fml_purify_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by blast
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        unfolding is_fml_pure.simps
        unfolding fml_purify_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        unfolding is_fml_pure.simps
        unfolding fml_purify_1.simps
        unfolding dyn_log_1.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by blast
    next
      case (FOL_ALL x1a \<phi>)
      assume fol_pure: "is_fml_pure 0 (\<bbbA> x1a . \<phi>)"
      then show ?case
      proof (induct x1a)
        case (Inl a)
        assume fol_inl_pure: "is_fml_pure 0 (\<bbbA> Inl a . \<phi>)"
          have outer_ind_hyp: "\<And> \<mu> . is_fml_pure 0 \<phi> \<Longrightarrow>
                (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>) \<longrightarrow>
                 het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>))"
            using FOL_ALL.hyps by blast
        then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_1.simps
          unfolding dyn_log_1.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
        proof (intro conjI)
          show "(\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                        dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                        het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_dl1: "\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
             dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>"
            assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega>"
            then have "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) (fst \<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_1.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_1.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by fastforce

            then show "het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>"
              using sat_in_dl1
              apply (elim allE[of _ "(fst \<omega>)"])
              using outer_ind_hyp[of "\<omega>"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by blast
          qed
          show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
                        het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega> \<longrightarrow>
                        dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_hdl: "\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl a) \<mu> \<omega> \<longrightarrow>
             het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>"
            assume omega_hyp: "dyn_log_1.fol_equal_everywhere_but a (fst \<mu>) \<omega>"
            then have "het_fol.fol_equal_everywhere_but (Inl a) \<mu> (\<omega>,(snd \<mu>))"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_1.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_1.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by (metis fst_conv map_sum.simps(1) map_sum.simps(2) snd_conv sumE)

            then show "dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>"
              using sat_in_hdl
              apply (elim allE[of _ "(\<omega>, snd \<mu>)"])
              using outer_ind_hyp[of "(\<omega>, snd \<mu>)"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by force
          qed
        qed
      next
        case (Inr b)
        then show ?case
          unfolding is_fml_pure.simps
          by linarith
      qed
    next
      case (BOX x1a \<phi>)
      then show ?case
      proof (induct x1a)
        have outer_ind_hyp: "\<And> \<mu> . is_fml_pure 0 \<phi> \<Longrightarrow>
                (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>) \<longrightarrow>
                 het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>))"
          using BOX.hyps by blast
        case (KATPROG x)
        then show ?case
        proof (induct x)
          case (HPROG x)
          then show ?case
          proof (induct x)
            case (PROG1 x)
            then show ?case
              unfolding fml_purify_1.simps
              unfolding prog_purify_1.simps
            proof (intro conjI)
              assume ind_hyp: "(\<And>\<mu>. is_fml_pure 0 \<phi> \<Longrightarrow>
                    (dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>) \<longrightarrow>
                     het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                    (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                     dyn_log_1.dyn_eval (fml_purify_1 \<phi>) (fst \<mu>)))"
              assume prog_pure: "is_fml_pure 0 (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>)"
              show "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) (fst \<mu>) \<longrightarrow>
                      het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>) \<mu>"
              proof (intro impI)
                let ?\<mu>1 = "(fst \<mu>)"
                let ?\<mu>2 = "(snd \<mu>)"

                assume "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) ?\<mu>1"
                then have "\<forall>\<omega>1 \<omega>2. (\<exists>n. prog_eval1 x (fst \<mu>) \<omega>1 \<and>
                  state_eval2 (snd \<mu>) = state_eval2 \<omega>2) \<longrightarrow> het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>1,\<omega>2)"
                  proof (intro allI,intro impI)
                    fix \<omega>1 \<omega>2
                    show "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) (fst \<mu>) \<Longrightarrow>
                           (\<exists>n. prog_eval1 x (fst \<mu>) \<omega>1 \<and>
                                state_eval2 (snd \<mu>) = state_eval2 \<omega>2) \<Longrightarrow>
                           het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>1, \<omega>2)"
                    unfolding dyn_log_1.dyn_eval.simps
                    apply (elim allE[of _ \<omega>1])
                    using ind_hyp[of "(\<omega>1,\<omega>2)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by simp
                 qed
                  
  
                then have "\<forall>\<omega>1 \<omega>2. het_dl_kat.full_prog_eval (KATPROG (HPROG (PROG1 x))) (?\<mu>1,?\<mu>2) (\<omega>1,\<omega>2) \<longrightarrow>
                             het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>1,\<omega>2)"
                  apply (intro allI)
                  unfolding het_prog_eval.simps
                  unfolding dyn_log_1.dyn_eval.simps
                  unfolding het_dl_kat.full_prog_eval_def
                  unfolding het_dl_kat.full_prog_eval_int.simps
                  unfolding het_dl_havoc.full_prog_eval.simps
                  unfolding het_prog_eval.simps
                  by auto
                thus "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>) \<mu>"
                  unfolding het_dl_kat.kat_dl.dyn_eval.simps
                  by force
              qed
              show "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>) \<mu>
                    \<longrightarrow> dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) (fst \<mu>)"
              proof (intro impI)
                let ?\<mu>1 = "(fst \<mu>)"
                let ?\<mu>2 = "(snd \<mu>)"
                assume "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>) \<mu>"
                then have sat_in_het: "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG1 x)) \<rbrakk> \<phi>) (?\<mu>1,?\<mu>2)"
                  by force
                have "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) (fst \<mu>)"
                  unfolding dyn_log_1.dyn_eval.simps
                proof (intro allI, intro impI)
                  fix \<omega>
                  let ?\<omega>2 = "(snd \<mu>)"
                  have "prog_eval1 x (fst \<mu>) \<omega> \<Longrightarrow>
                    (\<exists>n. prog_eval1 x (fst \<mu>) \<omega> \<and> state_eval2 (snd \<mu>) = state_eval2 ?\<omega>2) \<longrightarrow>
                    het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>, ?\<omega>2) \<Longrightarrow>
                    dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>"
                    using ind_hyp[of "(\<omega>,?\<omega>2)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by auto
                  thus " prog_eval1 x (fst \<mu>) \<omega> \<Longrightarrow> dyn_log_1.dyn_eval (fml_purify_1 \<phi>) \<omega>"
                    using sat_in_het
                    unfolding het_dl_kat.kat_dl.dyn_eval.simps
                    apply (elim allE[of _ "(\<omega>,?\<omega>2)"])
                    unfolding het_dl_kat.full_prog_eval_def
                    unfolding het_dl_kat.full_prog_eval_int.simps
                    unfolding het_dl_havoc.full_prog_eval.simps
                    unfolding het_prog_eval.simps
                    by blast
                qed
                thus "dyn_log_1.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_1 \<phi>) (fst \<mu>)"
                  by simp
              qed
            qed
          next
            case (PROG2 x)
            then show ?case
              unfolding is_fml_pure.simps
              unfolding is_kat_prog_pure.simps
              unfolding is_havoc_prog_pure.simps
              unfolding is_het_prog_pure.simps
              by linarith
          qed
        next
          case (HAVOC x)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          unfolding is_havoc_prog_pure.simps
          by blast
        qed
      next
        case (CHECK x)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (SEQ x1a1 x1a2)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (CHOICE x1a1 x1a2)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (LOOP x1a)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by simp
      qed
    qed
  qed

  show ?thesis
    using assms
    using reformulatation
    by auto
qed

lemma dyn_het_equiv_1:
  assumes "is_fml_pure 1 \<phi>"
  shows "((dyn_log_2.dyn_eval (fml_purify_2 \<phi>) s2) \<longrightarrow>
           (\<forall> s1 . (het_dl_kat.kat_dl.dyn_eval \<phi> (s1,s2)))) \<and>
          ((\<forall> s1 . (het_dl_kat.kat_dl.dyn_eval \<phi> (s1,s2))) \<longrightarrow>
           (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) s2))"
proof -
  have reformulatation: "\<And> \<phi> \<mu> .  is_fml_pure 1 \<phi> \<Longrightarrow> 
        ((dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>)) \<longrightarrow>
         (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>)))"
      proof -
    fix \<phi>
    show "\<And> \<mu> .  is_fml_pure 1 \<phi> \<Longrightarrow> 
        ((dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>)) \<longrightarrow>
         (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>)) \<and>
        ((het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<longrightarrow>
         (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>)))"
    proof (induct \<phi>)
      case (FOL \<psi>)

      have "is_fol_pure 1 \<psi>"
        using FOL by auto

      then have "\<And> \<mu> . (dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>) \<longrightarrow>
     het_fol.fol_eval \<psi> \<mu>) \<and>
    (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
     dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>))"
        proof (induct \<psi>)
          case (ATOM x)
          then show ?case
          proof (induct x)
            case (ATOM2 x)
            then show ?case
              unfolding fol_purify_2.simps
              unfolding dyn_log_2.fol_eval.simps
              unfolding het_fol.fol_eval.simps
              unfolding het_atom_eval.simps
              by simp
          next
            case (ATOM1 x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by linarith
          next
            case (ATOMC x)
            then show ?case
              unfolding is_fol_pure.simps
              unfolding is_atom_pure.simps
              by simp
          qed
        next
          case (AND \<psi>1 \<psi>2)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_2.simps
          unfolding dyn_log_2.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          by simp
        next
          case (NOT \<psi>)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
          unfolding fol_purify_2.simps
          unfolding dyn_log_2.fol_eval.simps
          unfolding het_fol.fol_eval.simps
          unfolding is_fol_pure.simps
          by blast
        next
          case (FOL_ALL x1a \<psi>)
          assume fol_pure: "is_fol_pure 1 (folall x1a \<psi>)"
          then show ?case
          proof (induct x1a)
            case (Inr a)
            assume fol_inl_pure: "is_fol_pure 1 (folall Inr a \<psi>)"
              have outer_ind_hyp: "(\<And>\<mu>. is_fol_pure 1 \<psi> \<Longrightarrow>
                   (dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>) \<longrightarrow>
                    het_fol.fol_eval \<psi> \<mu>) \<and>
                   (het_fol.fol_eval \<psi> \<mu> \<longrightarrow>
                    dyn_log_2.fol_eval (fol_purify_2 \<psi>) (snd \<mu>)))"
                using FOL_ALL.hyps by blast
            then show ?case
              unfolding is_fml_pure.simps
              unfolding fol_purify_2.simps
              unfolding dyn_log_2.fol_eval.simps
              unfolding het_fol.fol_eval.simps
            proof (intro conjI)
              show "(\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                            dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_dl1: "\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                           dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>"
                assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega>"
                then have "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) (snd \<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_2.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_2.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by fastforce
    
                then show "het_fol.fol_eval \<psi> \<omega>"
                  using sat_in_dl1
                  apply (elim allE[of _ "(snd \<omega>)"])
                  using outer_ind_hyp[of "\<omega>"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by blast
              qed
              show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>) \<longrightarrow>
                      (\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                            dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>)"
              proof (intro impI,intro allI,intro impI)
                fix \<omega>
                assume sat_in_hdl: "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                            het_fol.fol_eval \<psi> \<omega>)"
                assume omega_hyp: "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega>"
                then have "het_fol.fol_equal_everywhere_but (Inr a) \<mu> ((fst \<mu>),\<omega>)"
                  unfolding het_fol.fol_equal_everywhere_but_def
                  unfolding dyn_log_2.fol_equal_everywhere_but_def
                  unfolding het_fol.fol_states_agree_on_def
                  unfolding dyn_log_2.fol_states_agree_on_def
                  unfolding het_state_eval_def
                  unfolding common_atom_eval_def
                  by (metis snd_conv map_sum.simps(1) map_sum.simps(2) fst_conv sumE)
    
                then show "dyn_log_2.fol_eval (fol_purify_2 \<psi>) \<omega>"
                  using sat_in_hdl
                  apply (elim allE[of _ "(fst \<mu>, \<omega>)"])
                  using outer_ind_hyp[of "(fst \<mu>, \<omega>)"]
                  using fol_inl_pure
                  unfolding is_fol_pure.simps
                  by force
              qed
            qed
          next
            case (Inl b)
            then show ?case
              unfolding is_fol_pure.simps
              by linarith
          qed
        qed
      thus ?case
        unfolding fml_purify_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by blast
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        unfolding is_fml_pure.simps
        unfolding fml_purify_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        unfolding is_fml_pure.simps
        unfolding fml_purify_2.simps
        unfolding dyn_log_2.dyn_eval.simps
        unfolding het_dl_kat.kat_dl.dyn_eval.simps
        by blast
    next
      case (FOL_ALL x1a \<phi>)
      assume fol_pure: "is_fml_pure 1 (\<bbbA> x1a . \<phi>)"
      then show ?case
      proof (induct x1a)
        case (Inr a)
        assume fol_inl_pure: "is_fml_pure 1 (\<bbbA> Inr a . \<phi>)"
          have outer_ind_hyp: "\<And> \<mu> . is_fml_pure 1 \<phi> \<Longrightarrow>
                (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>) \<longrightarrow>
                 het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>))"
            using FOL_ALL.hyps by blast
        then show ?case
          unfolding is_fml_pure.simps
          unfolding fml_purify_2.simps
          unfolding dyn_log_2.dyn_eval.simps
          unfolding het_dl_kat.kat_dl.dyn_eval.simps
        proof (intro conjI)
          show "(\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                        dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                        het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_dl1: "\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
             dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>"
            assume omega_hyp: "het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega>"
            then have "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) (snd \<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_2.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_2.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by fastforce

            then show "het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>"
              using sat_in_dl1
              apply (elim allE[of _ "(snd \<omega>)"])
              using outer_ind_hyp[of "\<omega>"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by blast
          qed
          show "(\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
                        het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>) \<longrightarrow>
                  (\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega> \<longrightarrow>
                        dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>)"
          proof (intro impI,intro allI,intro impI)
            fix \<omega>
            assume sat_in_hdl: "\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr a) \<mu> \<omega> \<longrightarrow>
             het_dl_kat.kat_dl.dyn_eval \<phi> \<omega>"
            assume omega_hyp: "dyn_log_2.fol_equal_everywhere_but a (snd \<mu>) \<omega>"
            then have "het_fol.fol_equal_everywhere_but (Inr a) \<mu> ((fst \<mu>),\<omega>)"
              unfolding het_fol.fol_equal_everywhere_but_def
              unfolding dyn_log_2.fol_equal_everywhere_but_def
              unfolding het_fol.fol_states_agree_on_def
              unfolding dyn_log_2.fol_states_agree_on_def
              unfolding het_state_eval_def
              unfolding common_atom_eval_def
              by (metis snd_conv map_sum.simps(1) map_sum.simps(2) fst_conv sumE)

            then show "dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>"
              using sat_in_hdl
              apply (elim allE[of _ "(fst \<mu>, \<omega>)"])
              using outer_ind_hyp[of "(fst \<mu>, \<omega>)"]
              using fol_inl_pure
              unfolding is_fml_pure.simps
              by force
          qed
        qed
      next
        case (Inl b)
        then show ?case
          unfolding is_fml_pure.simps
          by linarith
      qed
    next
      case (BOX x1a \<phi>)
      then show ?case
      proof (induct x1a)
        have outer_ind_hyp: "\<And> \<mu> . is_fml_pure 1 \<phi> \<Longrightarrow>
                (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>) \<longrightarrow>
                 het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                 dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>))"
          using BOX.hyps by blast
        case (KATPROG x)
        then show ?case
        proof (induct x)
          case (HPROG x)
          then show ?case
          proof (induct x)
            case (PROG2 x)
            then show ?case
              unfolding fml_purify_2.simps
              unfolding prog_purify_2.simps
            proof (intro conjI)
              assume ind_hyp: "(\<And>\<mu>. is_fml_pure 1 \<phi> \<Longrightarrow>
                    (dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>) \<longrightarrow>
                     het_dl_kat.kat_dl.dyn_eval \<phi> \<mu>) \<and>
                    (het_dl_kat.kat_dl.dyn_eval \<phi> \<mu> \<longrightarrow>
                     dyn_log_2.dyn_eval (fml_purify_2 \<phi>) (snd \<mu>)))"
              assume prog_pure: "is_fml_pure 1 (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>)"
              show "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) (snd \<mu>) \<longrightarrow>
                      het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>) \<mu>"
              proof (intro impI)
                let ?\<mu>1 = "(snd \<mu>)"
                let ?\<mu>2 = "(fst \<mu>)"

                assume "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) ?\<mu>1"
                then have "\<forall>\<omega>1 \<omega>2. (\<exists>n. prog_eval2 x (snd \<mu>) \<omega>1 \<and>
                  state_eval1 (fst \<mu>) = state_eval1 \<omega>2) \<longrightarrow> het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>2,\<omega>1)"
                  proof (intro allI,intro impI)
                    fix \<omega>1 \<omega>2
                    show "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) (snd \<mu>) \<Longrightarrow>
                           (\<exists>n. prog_eval2 x (snd \<mu>) \<omega>1 \<and>
                                state_eval1 (fst \<mu>) = state_eval1 \<omega>2) \<Longrightarrow>
                           het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>2,\<omega>1)"
                    unfolding dyn_log_2.dyn_eval.simps
                    apply (elim allE[of _ \<omega>1])
                    using ind_hyp[of "(\<omega>2,\<omega>1)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by simp
                 qed
                  
  
                then have "\<forall>\<omega>1 \<omega>2. het_dl_kat.full_prog_eval (KATPROG (HPROG (PROG2 x))) (?\<mu>2,?\<mu>1) (\<omega>2,\<omega>1) \<longrightarrow>
                             het_dl_kat.kat_dl.dyn_eval \<phi> (\<omega>2,\<omega>1)"
                  apply (intro allI)
                  unfolding het_prog_eval.simps
                  unfolding dyn_log_2.dyn_eval.simps
                  unfolding het_dl_kat.full_prog_eval_def
                  unfolding het_dl_kat.full_prog_eval_int.simps
                  unfolding het_dl_havoc.full_prog_eval.simps
                  unfolding het_prog_eval.simps
                  by auto
                thus "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>) \<mu>"
                  unfolding het_dl_kat.kat_dl.dyn_eval.simps
                  by force
              qed
              show "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>) \<mu>
                    \<longrightarrow> dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) (snd \<mu>)"
              proof (intro impI)
                let ?\<mu>1 = "(snd \<mu>)"
                let ?\<mu>2 = "(fst \<mu>)"
                assume "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>) \<mu>"
                then have sat_in_het: "het_dl_kat.kat_dl.dyn_eval (\<lbrakk> KATPROG (HPROG (PROG2 x)) \<rbrakk> \<phi>) (?\<mu>2,?\<mu>1)"
                  by force
                have "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) (snd \<mu>)"
                  unfolding dyn_log_2.dyn_eval.simps
                proof (intro allI, intro impI)
                  fix \<omega>
                  let ?\<omega>2 = "(fst \<mu>)"
                  have "prog_eval2 x (snd \<mu>) \<omega> \<Longrightarrow>
                    (\<exists>n. prog_eval2 x (snd \<mu>) \<omega> \<and> state_eval1 (fst \<mu>) = state_eval1 ?\<omega>2) \<longrightarrow>
                    het_dl_kat.kat_dl.dyn_eval \<phi> (?\<omega>2,\<omega>) \<Longrightarrow>
                    dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>"
                    using ind_hyp[of "(?\<omega>2,\<omega>)"]
                    using prog_pure
                    unfolding is_fml_pure.simps
                    by auto
                  thus " prog_eval2 x (snd \<mu>) \<omega> \<Longrightarrow> dyn_log_2.dyn_eval (fml_purify_2 \<phi>) \<omega>"
                    using sat_in_het
                    unfolding het_dl_kat.kat_dl.dyn_eval.simps
                    apply (elim allE[of _ "(?\<omega>2,\<omega>)"])
                    unfolding het_dl_kat.full_prog_eval_def
                    unfolding het_dl_kat.full_prog_eval_int.simps
                    unfolding het_dl_havoc.full_prog_eval.simps
                    unfolding het_prog_eval.simps
                    by fastforce
                qed
                thus "dyn_log_2.dyn_eval (\<lbrakk> x \<rbrakk> fml_purify_2 \<phi>) (snd \<mu>)"
                  by simp
              qed
            qed
          next
            case (PROG1 x)
            then show ?case
              unfolding is_fml_pure.simps
              unfolding is_kat_prog_pure.simps
              unfolding is_havoc_prog_pure.simps
              unfolding is_het_prog_pure.simps
              by linarith
          qed
        next
          case (HAVOC x)
          then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          unfolding is_havoc_prog_pure.simps
          by blast
        qed
      next
        case (CHECK x)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (SEQ x1a1 x1a2)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (CHOICE x1a1 x1a2)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by blast
      next
        case (LOOP x1a)
        then show ?case
          unfolding is_fml_pure.simps
          unfolding is_kat_prog_pure.simps
          by simp
      qed
    qed
  qed

  show ?thesis
    using assms
    using reformulatation
    by auto
qed

paragraph\<open>Proof Rules.\<close>
text\<open>
The observations from above yield the following proof rules:
\<close>

lemma dyn_axiom_R0:
  assumes "is_fml_pure 0 \<phi>"
      and "\<Turnstile>[dyn_log_1.dyn_eval] (fml_purify_1 \<phi>)"
    shows "\<Turnstile>[het_dl_kat.kat_dl.dyn_eval] \<phi>"
  using assms
  unfolding theory_valid_def
  using dyn_het_equiv_0[of \<phi>]
  by auto

lemma dyn_axiom_R1:
  assumes "is_fml_pure 1 \<phi>"
      and "\<Turnstile>[dyn_log_2.dyn_eval] (fml_purify_2 \<phi>)"
    shows "\<Turnstile>[het_dl_kat.kat_dl.dyn_eval] \<phi>"
  using assms
  unfolding theory_valid_def
  using dyn_het_equiv_1[of \<phi>]
  by auto

lemma dyn_axiom_simple_R0:
  assumes "is_fml_pure_simple 0 \<phi>"
      and "\<Turnstile>[dyn_log_1.dyn_eval] (fml_purify_simple_1 \<phi>)"
    shows "\<Turnstile>[het_dl.dyn_eval] \<phi>"
  using assms
  unfolding theory_valid_def
  using dyn_het_simple_equiv_0[of \<phi>]
  by auto


lemma dyn_axiom_simple_R1:
  assumes "is_fml_pure_simple 1 \<phi>"
      and "\<Turnstile>[dyn_log_2.dyn_eval] (fml_purify_simple_2 \<phi>)"
    shows "\<Turnstile>[het_dl.dyn_eval] \<phi>"
  using assms
  unfolding theory_valid_def
  using dyn_het_simple_equiv_1[of \<phi>]
  by auto

subsubsection\<open>Inductive Expressivity\<close>
text\<open>
We now show that inductive expressivity from individual dynamic theories
can also be lifted to the heterogeneous level.
This allows us to also use the loop convergence axiom for the heterogeneous
theory:
\<close>

fun val_nat_ext1 :: "('val1 \<Rightarrow> nat) \<Rightarrow> 'val1 + 'val2 \<Rightarrow> nat"
  where
    "val_nat_ext1 v2n (Inl v) = (v2n v)"
  | "val_nat_ext1 v2n (Inr v) = 0"

fun nat_var_ext1 :: "('var1 \<Rightarrow> bool) \<Rightarrow> 'var1 + 'var2 \<Rightarrow> bool"
  where 
    "nat_var_ext1 nv (Inl v) = (nv v)"
  | "nat_var_ext1 nv (Inr v) = False"

fun plus_one_ext1 :: "('var1 \<Rightarrow> 'var1 \<Rightarrow> ('atom1, 'var1) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                          \<Rightarrow> 'var1 + 'var2
                             \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                                 'var1 + 'var2) fol_formula"
  where
    "plus_one_ext1 po (Inl v) (Inl w) = (fol_heterify_1 (po v w))"
  | "plus_one_ext1 po v w = (folnot FOLTRUE)"

fun eq_ext1 :: "('var1 \<Rightarrow> 'var1 \<Rightarrow> ('atom1, 'var1) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                          \<Rightarrow> 'var1 + 'var2
                             \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                                 'var1 + 'var2) fol_formula"
  where
    "eq_ext1 eq (Inl v) (Inl w) = (fol_heterify_1 (eq v w))"
  | "eq_ext1 eq v w = (folnot FOLTRUE)"

fun positive_ext1 :: "('var1 \<Rightarrow> ('atom1, 'var1) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                           \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                               'var1 + 'var2) fol_formula"
  where
    "positive_ext1 pos (Inl v) = (fol_heterify_1 (pos v))"
  | "positive_ext1 pos v = (folnot FOLTRUE)"

fun val_nat_ext2 :: "('val2 \<Rightarrow> nat) \<Rightarrow> 'val1 + 'val2 \<Rightarrow> nat"
  where
    "val_nat_ext2 v2n (Inr v) = (v2n v)"
  | "val_nat_ext2 v2n (Inl v) = 0"

fun nat_var_ext2 :: "('var2 \<Rightarrow> bool) \<Rightarrow> 'var1 + 'var2 \<Rightarrow> bool"
  where 
    "nat_var_ext2 nv (Inr v) = (nv v)"
  | "nat_var_ext2 nv (Inl v) = False"

fun plus_one_ext2 :: "('var2 \<Rightarrow> 'var2 \<Rightarrow> ('atom2, 'var2) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                          \<Rightarrow> 'var1 + 'var2
                             \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                                 'var1 + 'var2) fol_formula"
  where
    "plus_one_ext2 po (Inr v) (Inr w) = (fol_heterify_2 (po v w))"
  | "plus_one_ext2 po v w = (folnot FOLTRUE)"

fun eq_ext2 :: "('var2 \<Rightarrow> 'var2 \<Rightarrow> ('atom2, 'var2) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                          \<Rightarrow> 'var1 + 'var2
                             \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                                 'var1 + 'var2) fol_formula"
  where
    "eq_ext2 eq (Inr v) (Inr w) = (fol_heterify_2 (eq v w))"
  | "eq_ext2 eq v w = (folnot FOLTRUE)"

fun positive_ext2 :: "('var2 \<Rightarrow> ('atom2, 'var2) fol_formula)
                       \<Rightarrow> 'var1 + 'var2
                           \<Rightarrow> (('atom1, 'atom2, 'atom_comm) het_atom,
                               'var1 + 'var2) fol_formula"
  where
    "positive_ext2 pos (Inr v) = (fol_heterify_2 (pos v))"
  | "positive_ext2 pos v = (folnot FOLTRUE)"

lemma heterify1_coincidence:
  "\<And>\<mu>1 \<mu>2 . (dyn_log_1.dyn_eval (FOL F)) \<mu>1 = (het_dl_havoc.havoc_dl.dyn_eval
     (FOL (fol_heterify_1 F))) (\<mu>1,\<mu>2)"
proof (induct F)
  case (ATOM x)
  then show ?case
    unfolding dyn_log_1.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_1.fol_eval.simps
    unfolding fol_heterify_1.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (AND F1 F2)
  then show ?case
    unfolding dyn_log_1.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_1.fol_eval.simps
    unfolding fol_heterify_1.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (NOT F)
  then show ?case
    unfolding dyn_log_1.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_1.fol_eval.simps
    unfolding fol_heterify_1.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (FOL_ALL x1a F)
  assume ind_assm: "\<And> \<mu>1 \<mu>2 . dyn_log_1.dyn_eval (FOL F) \<mu>1 =
  het_dl_havoc.havoc_dl.dyn_eval (FOL (fol_heterify_1 F)) (\<mu>1, \<mu>2)"
  then show ?case
    unfolding dyn_log_1.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_1.fol_eval.simps
    unfolding fol_heterify_1.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
  proof
    have dir1: "(\<forall>\<omega>1. dyn_log_1.fol_equal_everywhere_but x1a \<mu>1 \<omega>1 \<longrightarrow>
          dyn_log_1.fol_eval F \<omega>1) \<Longrightarrow>
    (\<forall>\<omega>1. het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<mu>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_1 F) (\<omega>1,\<mu>2))"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding dyn_log_1.fol_equal_everywhere_but_def
    unfolding dyn_log_1.fol_states_agree_on_def
    apply (intro allI, intro impI)
    using ind_assm
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps(1)[of "(fol_heterify_1 F)"]
    by (metis common_atom_eval_def dyn_log_1.dyn_eval.simps(1) fst_conv het_state_eval_def map_sum.simps(1) sum.sel(1))
  have dir2: "(\<forall>\<omega>1. het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<mu>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_1 F) (\<omega>1,\<mu>2)) \<Longrightarrow> 
        (\<forall>\<omega>1. dyn_log_1.fol_equal_everywhere_but x1a \<mu>1 \<omega>1 \<longrightarrow>
          dyn_log_1.fol_eval F \<omega>1)"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding dyn_log_1.fol_equal_everywhere_but_def
    unfolding dyn_log_1.fol_states_agree_on_def
    apply (intro allI, intro impI)
  proof -
    fix \<omega>1
    assume almost_eq_assm: "\<forall>v. v \<noteq> x1a \<longrightarrow> state_eval1 \<mu>1 v = state_eval1 \<omega>1 v"
    assume "\<forall>\<omega>1. (\<forall>v. v \<noteq> Inl x1a \<longrightarrow>
                    het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<omega>1, \<mu>2) v) \<longrightarrow>
               het_fol.fol_eval (fol_heterify_1 F) (\<omega>1, \<mu>2)"
    then have "(\<forall>v. v \<noteq> Inl x1a \<longrightarrow>
                    het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<omega>1, \<mu>2) v) \<longrightarrow>
               het_fol.fol_eval (fol_heterify_1 F) (\<omega>1, \<mu>2)"
      by blast
    thus "dyn_log_1.fol_eval F \<omega>1"
      using almost_eq_assm
      using ind_assm[of \<omega>1 \<mu>2]
      unfolding het_dl_havoc.havoc_dl.dyn_eval.simps(1)[of "(fol_heterify_1 F)"]
      unfolding dyn_log_1.dyn_eval.simps
      unfolding het_state_eval_def
      unfolding common_atom_eval_def
      apply simp
      by (metis (no_types, lifting) map_sum.simps(1) map_sum.simps(2) sumE)
  qed
  have "\<And> \<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow> (state_eval2 \<mu>2)=(state_eval2 \<omega>2)"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding het_state_eval_def
    unfolding common_atom_eval_def
  proof (intro impI)
    fix \<omega>1 \<omega>2
    assume "(\<forall>v. v \<noteq> Inl x1a \<longrightarrow>
            map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
             v =
            map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
             v)"
    then have "\<And> v . map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
             (Inr v) =
            map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
             (Inr v)"
    proof -
      fix v
      assume "\<forall>v. v \<noteq> Inl x1a \<longrightarrow>
             map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
              v =
             map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
              v"
      thus "map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
             (Inr v) =
            map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
             (Inr v)"
        apply (elim allE[of _ "(Inr v)"])
        by simp
    qed
    then have "\<And> v . state_eval2 \<mu>2 v = state_eval2 \<omega>2 v"
      by fastforce
    thus "state_eval2 \<mu>2 = state_eval2 \<omega>2"
      by blast
  qed
  then have helper: "\<And> \<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow> het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<mu>2)"
    by (smt (verit, ccfv_threshold) common_atom_eval_def fst_conv het_fol.fol_equal_everywhere_but_def het_fol.fol_states_agree_on_def het_state_eval_def snd_conv)
  have dir1_final: "(\<forall>\<omega>1. dyn_log_1.fol_equal_everywhere_but x1a \<mu>1 \<omega>1 \<longrightarrow>
          dyn_log_1.fol_eval F \<omega>1) \<Longrightarrow>
    (\<forall>\<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_1 F) (\<omega>1,\<omega>2))"
    using dir1
    apply (intro allI, intro impI)
    using helper
    by (meson het_dl_havoc.havoc_dl.dyn_eval.simps(1) ind_assm)
  have dir2_final: "(\<forall>\<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_1 F) (\<omega>1,\<omega>2)) \<Longrightarrow> (\<forall>\<omega>1. dyn_log_1.fol_equal_everywhere_but x1a \<mu>1 \<omega>1 \<longrightarrow>
          dyn_log_1.fol_eval F \<omega>1)"
    using dir2
    apply (intro allI, intro impI)
    using helper
    by (meson het_dl_havoc.havoc_dl.dyn_eval.simps(1) ind_assm)

  show "(\<forall>\<omega>. dyn_log_1.fol_equal_everywhere_but x1a \<mu>1 \<omega> \<longrightarrow>
          dyn_log_1.fol_eval F \<omega>) =
    (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inl x1a) (\<mu>1, \<mu>2) \<omega> \<longrightarrow>
          het_fol.fol_eval (fol_heterify_1 F) \<omega>)"
    using dir1_final dir2_final
    by fastforce
  qed
qed

lemma heterify2_coincidence:
  "\<And>\<mu>1 \<mu>2 . (dyn_log_2.dyn_eval (FOL F)) \<mu>2 = (het_dl_havoc.havoc_dl.dyn_eval
     (FOL (fol_heterify_2 F))) (\<mu>1,\<mu>2)"
proof (induct F)
  case (ATOM x)
  then show ?case
    unfolding dyn_log_2.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_2.fol_eval.simps
    unfolding fol_heterify_2.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (AND F1 F2)
  then show ?case
    unfolding dyn_log_2.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_2.fol_eval.simps
    unfolding fol_heterify_2.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (NOT F)
  then show ?case
    unfolding dyn_log_2.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_2.fol_eval.simps
    unfolding fol_heterify_2.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
    by simp
next
  case (FOL_ALL x1a F)
  assume ind_assm: "\<And> \<mu>1 \<mu>2 . dyn_log_2.dyn_eval (FOL F) \<mu>2 =
  het_dl_havoc.havoc_dl.dyn_eval (FOL (fol_heterify_2 F)) (\<mu>1, \<mu>2)"
  then show ?case
    unfolding dyn_log_2.dyn_eval.simps
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps
    unfolding dyn_log_2.fol_eval.simps
    unfolding fol_heterify_2.simps
    unfolding het_fol.fol_eval.simps
    unfolding het_atom_eval.simps
  proof
    have dir1: "(\<forall>\<omega>2. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega>2 \<longrightarrow>
          dyn_log_2.fol_eval F \<omega>2) \<Longrightarrow>
    (\<forall>\<omega>2. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<mu>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_2 F) (\<mu>1,\<omega>2))"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding dyn_log_2.fol_equal_everywhere_but_def
    unfolding dyn_log_2.fol_states_agree_on_def
    apply (intro allI, intro impI)
    using ind_assm
    unfolding het_dl_havoc.havoc_dl.dyn_eval.simps(1)[of "(fol_heterify_2 F)"]
    unfolding dyn_log_2.dyn_eval.simps
    by (metis common_atom_eval_def het_state_eval_def map_sum.simps(2) snd_conv sum.inject(2))
  have dir2: "(\<forall>\<omega>2. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<mu>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_2 F) (\<mu>1,\<omega>2)) \<Longrightarrow> 
        (\<forall>\<omega>2. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega>2 \<longrightarrow>
          dyn_log_2.fol_eval F \<omega>2)"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding dyn_log_2.fol_equal_everywhere_but_def
    unfolding dyn_log_2.fol_states_agree_on_def
    apply (intro allI, intro impI)
  proof -
    fix \<omega>2
    assume almost_eq_assm: "\<forall>v. v \<noteq> x1a \<longrightarrow> state_eval2 \<mu>2 v = state_eval2 \<omega>2 v"
    assume "\<forall>\<omega>2. (\<forall>v. v \<noteq> Inr x1a \<longrightarrow>
                    het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<mu>1, \<omega>2) v) \<longrightarrow>
               het_fol.fol_eval (fol_heterify_2 F) (\<mu>1, \<omega>2)"
    then have "(\<forall>v. v \<noteq> Inr x1a \<longrightarrow>
                    het_state_eval (\<mu>1, \<mu>2) v = het_state_eval (\<mu>1, \<omega>2) v) \<longrightarrow>
               het_fol.fol_eval (fol_heterify_2 F) (\<mu>1, \<omega>2)"
      by blast
    thus "dyn_log_2.fol_eval F \<omega>2"
      using almost_eq_assm
      using ind_assm[of \<omega>2 \<mu>1]
      unfolding het_dl_havoc.havoc_dl.dyn_eval.simps(1)[of "(fol_heterify_2 F)"]
      unfolding dyn_log_2.dyn_eval.simps
      unfolding het_state_eval_def
      unfolding common_atom_eval_def
      apply simp
      by (smt (verit, best) map_sum.simps(1) map_sum.simps(2) old.sum.exhaust)
  qed
  have "\<And> \<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow> (state_eval1 \<mu>1)=(state_eval1 \<omega>1)"
    unfolding  het_fol.fol_equal_everywhere_but_def
    unfolding het_fol.fol_states_agree_on_def
    unfolding het_state_eval_def
    unfolding common_atom_eval_def
  proof (intro impI)
    fix \<omega>1 \<omega>2
    assume "(\<forall>v. v \<noteq> Inr x1a \<longrightarrow>
           map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
            v =
           map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
            v)"
    then have "\<And> v . map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
             (Inl v) =
            map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
             (Inl v)"
    proof -
      fix v
      assume "\<forall>v. v \<noteq> Inr x1a \<longrightarrow>
             map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
              v =
             map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
              v"
      thus "map_sum (state_eval1 (fst (\<mu>1, \<mu>2))) (state_eval2 (snd (\<mu>1, \<mu>2)))
             (Inl v) =
            map_sum (state_eval1 (fst (\<omega>1, \<omega>2))) (state_eval2 (snd (\<omega>1, \<omega>2)))
             (Inl v)"
        apply (elim allE[of _ "(Inl v)"])
        by simp
    qed
    then have "\<And> v . state_eval1 \<mu>1 v = state_eval1 \<omega>1 v"
      by fastforce
    thus "state_eval1 \<mu>1 = state_eval1 \<omega>1"
      by blast
  qed
  then have helper: "\<And> \<omega>1 \<omega>2 . het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow> het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<mu>2)"
    by (smt (verit, ccfv_threshold) common_atom_eval_def fst_conv het_fol.fol_equal_everywhere_but_def het_fol.fol_states_agree_on_def het_state_eval_def snd_conv)
  have dir1_final: "(\<forall>\<omega>2. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega>2 \<longrightarrow>
          dyn_log_2.fol_eval F \<omega>2) \<Longrightarrow>
    (\<forall>\<omega>1 \<omega>2. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_2 F) (\<omega>1,\<omega>2))"
  proof (intro allI, intro impI)
    fix \<omega>1 \<omega>2
    assume "het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1, \<omega>2)"
    then have modified: "het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<mu>2)"
      using helper
      by blast
    assume "\<forall>\<omega>2. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega>2 \<longrightarrow>
             dyn_log_2.fol_eval F \<omega>2"
    thus "het_fol.fol_eval (fol_heterify_2 F) (\<omega>1, \<omega>2)"
      using dir1 modified
      by (smt (verit, best) \<open>\<And>\<omega>2 \<omega>1. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1, \<omega>2) \<longrightarrow> state_eval1 \<mu>1 = state_eval1 \<omega>1\<close> \<open>het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1, \<omega>2)\<close> common_atom_eval_def fst_conv het_dl_havoc.havoc_dl.dyn_eval.simps(1) het_fol.fol_equal_everywhere_but_def het_fol.fol_states_agree_on_def het_state_eval_def ind_assm snd_conv)
  qed
    
  have dir2_final: "(\<forall>\<omega>1 \<omega>2. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) (\<omega>1,\<omega>2) \<longrightarrow>
          het_fol.fol_eval (fol_heterify_2 F) (\<omega>1,\<omega>2)) \<Longrightarrow> 
        (\<forall>\<omega>2. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega>2 \<longrightarrow>
          dyn_log_2.fol_eval F \<omega>2)"
    using dir2
    apply (intro allI, intro impI)
    using helper
    by (meson het_dl_havoc.havoc_dl.dyn_eval.simps(1) ind_assm)

  show "(\<forall>\<omega>. dyn_log_2.fol_equal_everywhere_but x1a \<mu>2 \<omega> \<longrightarrow>
          dyn_log_2.fol_eval F \<omega>) =
    (\<forall>\<omega>. het_fol.fol_equal_everywhere_but (Inr x1a) (\<mu>1, \<mu>2) \<omega> \<longrightarrow>
          het_fol.fol_eval (fol_heterify_2 F) \<omega>)"
    using dir1_final dir2_final
    by fastforce
  qed
qed

lemma inductively_expressive_1:
  assumes nat_kat1: "nat_regular_lifting atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1 val2nat nat_var plus_one_relation eq_relation positive_relation"
  shows "nat_regular_lifting het_atom_eval het_atom_fv_syn het_state_eval het_dl_havoc.full_prog_eval het_dl_havoc.full_prog_FV (val_nat_ext1 val2nat) (nat_var_ext1 nat_var) (plus_one_ext1 plus_one_relation) (eq_ext1 eq_relation) (positive_ext1 positive_relation)"
proof

  show "\<forall>v. nat_var_ext1 nat_var v \<longrightarrow>
        is_nat_assignable het_state_eval (val_nat_ext1 val2nat) v"
  proof (intro allI, intro impI)
    fix v
    show "nat_var_ext1 nat_var v \<Longrightarrow>
         is_nat_assignable het_state_eval (val_nat_ext1 val2nat) v"
    proof (induct v)
      case (Inl a)
      then show ?case
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.nat_assignability[of atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (simp add: common_atom_eval_def is_nat_assignable_def)
    next
      case (Inr b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and> nat_var_ext1 nat_var v1 \<and> nat_var_ext1 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
              (FOL (plus_one_ext1 plus_one_relation v1 v2)) \<mu> =
             (val_nat_ext1 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext1 val2nat (het_state_eval \<mu> v1) + 1))"
  proof (intro allI)
    fix v1 v2
    show "v1 \<noteq> v2 \<and> nat_var_ext1 nat_var v1 \<and> nat_var_ext1 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
              (FOL (plus_one_ext1 plus_one_relation v1 v2)) \<mu> =
             (val_nat_ext1 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext1 val2nat (het_state_eval \<mu> v1) + 1))"
    proof (induct v1)
      case (Inl a)
      then show ?case
      proof (induct v2)
        case (Inl a)
        then show ?case 
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.plus_one_sound[of atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis (no_types, lifting) common_atom_eval_def dyn_log_1.dyn_eval.simps(1) fst_conv het_state_eval_def heterify1_coincidence map_sum.simps(1) val_nat_ext1.simps(1))
      next
        case (Inr b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
      qed
    next
      case (Inr b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and> nat_var_ext1 nat_var v1 \<and> nat_var_ext1 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval (FOL (eq_ext1 eq_relation v1 v2))
              \<mu> =
             (val_nat_ext1 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext1 val2nat (het_state_eval \<mu> v1)))"
  proof (intro allI)
    fix v1 v2
    show "v1 \<noteq> v2 \<and> nat_var_ext1 nat_var v1 \<and> nat_var_ext1 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval (FOL (eq_ext1 eq_relation v1 v2))
              \<mu> =
             (val_nat_ext1 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext1 val2nat (het_state_eval \<mu> v1)))"
    proof (induct v1)
      case (Inl a)
      then show ?case
      proof (induct v2)
        case (Inl a)
        then show ?case 
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.eq_sound[of atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis (no_types, lifting) common_atom_eval_def dyn_log_1.dyn_eval.simps(1) fst_conv het_state_eval_def heterify1_coincidence map_sum.simps(1) val_nat_ext1.simps(1))
      next
        case (Inr b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
      qed
    next
      case (Inr b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1. nat_var_ext1 nat_var v1 \<longrightarrow>
         (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
                (FOL (positive_ext1 positive_relation v1)) \<mu> =
               (0 < val_nat_ext1 val2nat (het_state_eval \<mu> v1)))"
  proof (intro allI)
    fix v1
    show "nat_var_ext1 nat_var v1 \<longrightarrow>
         (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
                (FOL (positive_ext1 positive_relation v1)) \<mu> =
               (0 < val_nat_ext1 val2nat (het_state_eval \<mu> v1)))"
    proof (induct v1)
      case (Inl a)
      then show ?case
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.positive_sound[of atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis (no_types, lifting) common_atom_eval_def dyn_log_1.dyn_eval.simps(1) fst_conv het_state_eval_def heterify1_coincidence map_sum.simps(1) val_nat_ext1.simps(1))
      next
        case (Inr b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed
qed

lemma inductively_expressive_2:
  assumes nat_kat1: "nat_regular_lifting atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2 val2nat nat_var plus_one_relation eq_relation positive_relation"
  shows "nat_regular_lifting het_atom_eval het_atom_fv_syn het_state_eval het_dl_havoc.full_prog_eval het_dl_havoc.full_prog_FV (val_nat_ext2 val2nat) (nat_var_ext2 nat_var) (plus_one_ext2 plus_one_relation) (eq_ext2 eq_relation) (positive_ext2 positive_relation)"
proof

  show "\<forall>v. nat_var_ext2 nat_var v \<longrightarrow>
        is_nat_assignable het_state_eval (val_nat_ext2 val2nat) v"
  proof (intro allI, intro impI)
    fix v
    show "nat_var_ext2 nat_var v \<Longrightarrow>
         is_nat_assignable het_state_eval (val_nat_ext2 val2nat) v"
    proof (induct v)
      case (Inr a)
      then show ?case
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.nat_assignability[of atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (simp add: common_atom_eval_def is_nat_assignable_def)
    next
      case (Inl b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and> nat_var_ext2 nat_var v1 \<and> nat_var_ext2 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
              (FOL (plus_one_ext2 plus_one_relation v1 v2)) \<mu> =
             (val_nat_ext2 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext2 val2nat (het_state_eval \<mu> v1) + 1))"
  proof (intro allI)
    fix v1 v2
    show "v1 \<noteq> v2 \<and> nat_var_ext2 nat_var v1 \<and> nat_var_ext2 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
              (FOL (plus_one_ext2 plus_one_relation v1 v2)) \<mu> =
             (val_nat_ext2 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext2 val2nat (het_state_eval \<mu> v1) + 1))"
    proof (induct v1)
      case (Inr a)
      then show ?case
      proof (induct v2)
        case (Inr a)
        then show ?case 
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.plus_one_sound[of atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis common_atom_eval_def dyn_log_2.dyn_eval.simps(1) het_state_eval_def heterify2_coincidence map_sum.simps(2) split_pairs val_nat_ext2.simps(1))
      next
        case (Inl b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
      qed
    next
      case (Inl b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and> nat_var_ext2 nat_var v1 \<and> nat_var_ext2 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval (FOL (eq_ext2 eq_relation v1 v2))
              \<mu> =
             (val_nat_ext2 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext2 val2nat (het_state_eval \<mu> v1)))"
  proof (intro allI)
    fix v1 v2
    show "v1 \<noteq> v2 \<and> nat_var_ext2 nat_var v1 \<and> nat_var_ext2 nat_var v2 \<longrightarrow>
       (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval (FOL (eq_ext2 eq_relation v1 v2))
              \<mu> =
             (val_nat_ext2 val2nat (het_state_eval \<mu> v2) =
              val_nat_ext2 val2nat (het_state_eval \<mu> v1)))"
    proof (induct v1)
      case (Inr a)
      then show ?case
      proof (induct v2)
        case (Inr a)
        then show ?case 
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.eq_sound[of atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis common_atom_eval_def dyn_log_2.dyn_eval.simps(1) het_state_eval_def heterify2_coincidence map_sum.simps(2) split_pairs val_nat_ext2.simps(1))
      next
        case (Inl b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
      qed
    next
      case (Inl b)
      then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed

  show "\<forall>v1. nat_var_ext2 nat_var v1 \<longrightarrow>
         (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
                (FOL (positive_ext2 positive_relation v1)) \<mu> =
               (0 < val_nat_ext2 val2nat (het_state_eval \<mu> v1)))"
  proof (intro allI)
    fix v1
    show "nat_var_ext2 nat_var v1 \<longrightarrow>
         (\<forall>\<mu>. het_dl_havoc.havoc_dl.dyn_eval
                (FOL (positive_ext2 positive_relation v1)) \<mu> =
               (0 < val_nat_ext2 val2nat (het_state_eval \<mu> v1)))"
    proof (induct v1)
      case (Inr a)
      then show ?case
        unfolding nat_var_ext1.simps
        using nat_kat1
        using nat_regular_lifting.positive_sound[of atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
         val2nat nat_var plus_one_relation eq_relation positive_relation]
        apply simp
        by (metis common_atom_eval_def dyn_log_2.dyn_eval.simps(1) het_state_eval_def heterify2_coincidence map_sum.simps(2) split_pairs val_nat_ext2.simps(1))
      next
        case (Inl b)
        then show ?case
        unfolding nat_var_ext1.simps
        by simp
    qed
  qed
qed

(*lemma test:
  assumes "\<Turnstile>[het_dl_kat.kat_dl.dyn_eval] \<phi>"
  shows "\<Turnstile>[het_dl_kat.kat_dl.dyn_eval] \<lbrakk> \<pi> \<rbrakk> \<phi>"
  using het_dl_kat.kat_dl.dyn_axiom_G
  using assms
  by simp*)
end

end