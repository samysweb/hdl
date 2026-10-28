section\<open>Instantiations\<close>
text\<open>
We now demonstrate the utility of our theory, by providing concrete instantiations.
To this end, I first want to define dynamic logics with a (fixed) interpretation.
The fixed interpretation can \emph{vary} by state, but is \emph{fixed} across
all program transitions. This allows modelling notions such as, e.g.,
rigid functions.
\<close>
subsection\<open>Dynamic Logics with Interpretation\<close>
theory InterpDL
  imports
    Main
    DynamicLogicCore
    DynamicLogic
    DynamicLogicProof
    HavocDynamicLogic
    KATDynamicLogic
    KATRewriting
begin

datatype idl_internal_var =
     IdlInterpVar

instance idl_internal_var :: finite
proof
  have "x = IdlInterpVar" for x :: idl_internal_var
    by (cases x) auto
  hence "(UNIV :: idl_internal_var set) = {IdlInterpVar}"
    by auto
  thus "finite (UNIV :: idl_internal_var set)"
    by (metis finite.insertI infinite_imp_nonempty)
qed

datatype 'var idl_var =
    InternalVar idl_internal_var
    | ExternalVar 'var

datatype ('val,'interp) idl_val =
    InternalVal 'interp
  | ExternalVal 'val


datatype ('interp, 'state) idl_state =
  IdlState  (interp_var  : "'interp")
            (other_var : "'state")

fun idl_internal_get_state :: "
  ('interp, 'state) idl_state
  \<Rightarrow> 'state"
  where "idl_internal_get_state \<omega> = (other_var \<omega>)"

fun idl_internal_get_interp :: "
  ('interp, 'state) idl_state
  \<Rightarrow> 'interp"
  where "idl_internal_get_interp \<omega> = (interp_var \<omega>)"

locale interp_fol_core =
  fixes atom_eval :: "'atom \<Rightarrow> 'interp \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  assumes fv_finite: "finite (Collect (atom_fv_syn a))"
      and fv_overapprox: "(fol_states_agree_on_gen state_eval (atom_fv_syn (a::'atom)) (\<mu>::'state) (\<omega>::'state)) \<Longrightarrow> (atom_eval a I \<mu>) = (atom_eval a I \<omega>)"
      and state_space_convexity:
          "\<forall> \<omega> :: 'state . \<forall> \<mu>  :: 'state . \<forall> V :: 'var set . (
            (\<exists> \<nu>  :: 'state . (
              (\<forall> v . 
              (v \<in> V \<longrightarrow> ((state_eval \<nu>) v) = ((state_eval \<mu>) v)) \<and>
              (v \<notin> V \<longrightarrow> ((state_eval \<nu>) v) = ((state_eval \<omega>) v))))))"
begin

fun idl_atom_eval_full :: "'atom \<Rightarrow> ('interp, 'state) idl_state \<Rightarrow> bool"
  where "idl_atom_eval_full a (IdlState I \<omega>) = atom_eval a I \<omega>"

fun idl_atom_fv_syn_full :: "'atom \<Rightarrow> 'var idl_var \<Rightarrow> bool"
  where
    "idl_atom_fv_syn_full a (InternalVar x) = True"
  | "idl_atom_fv_syn_full a (ExternalVar x) = atom_fv_syn a x"

fun idl_state_eval_full :: "
    ('interp, 'state) idl_state \<Rightarrow>
    'var idl_var \<Rightarrow>
    ('val,'interp) idl_val"
  where
    "idl_state_eval_full \<mu> (InternalVar x) =
      InternalVal (idl_internal_get_interp \<mu>)"
  | "idl_state_eval_full \<mu> (ExternalVar x) =
      (let
        \<omega> = (idl_internal_get_state \<mu>)
      in ExternalVal (state_eval \<omega> x))"

sublocale fc: folCore idl_atom_eval_full idl_atom_fv_syn_full idl_state_eval_full
proof
  show "\<And>a. finite (Collect (idl_atom_fv_syn_full a))"
  proof -
    fix a
    have fact1: "(Collect (idl_atom_fv_syn_full a))
            =
          ({ y . \<exists> x . y=(ExternalVar x) \<and> (x \<in> (Collect (atom_fv_syn a))) }
          \<union>
          { y. \<exists> x . y=(InternalVar x) })"
    by (smt (verit, best) Collect_cong Un_def idl_atom_fv_syn_full.elims(1)
        idl_atom_fv_syn_full.simps(1) idl_var.inject(2) mem_Collect_eq)

    have fact2: "finite { y. \<exists> x . y=(InternalVar x) }"
    proof -
      have "{y. \<exists>x. y = InternalVar x} = range InternalVar"
        by auto
      thus ?thesis
        by (metis finite_UNIV finite_imageI)
    qed

    have "finite ({ y . \<exists> x . y=(ExternalVar x) \<and> (x \<in> (Collect (atom_fv_syn a))) })"
      using fv_finite
      by auto

    thus "finite (Collect (idl_atom_fv_syn_full a))"
      using fact1 fact2
      by auto
  qed
  show "\<And>a \<mu> \<omega>.
       fol_states_agree_on_gen idl_state_eval_full (idl_atom_fv_syn_full a) \<mu> \<omega> \<Longrightarrow>
       idl_atom_eval_full a \<mu> = idl_atom_eval_full a \<omega>"
    unfolding fol_states_agree_on_gen_def
  proof -
    fix a \<mu> \<omega>
    assume assm1: "\<forall>v. idl_atom_fv_syn_full a v \<longrightarrow>
           idl_state_eval_full \<mu> v = idl_state_eval_full \<omega> v"
    then have fact1: "fol_states_agree_on_gen state_eval (atom_fv_syn a) (idl_internal_get_state \<mu>) (idl_internal_get_state \<omega>)"
      by (metis (mono_tags, lifting) fol_states_agree_on_gen_def
          idl_atom_fv_syn_full.simps(2) idl_state_eval_full.simps(2)
          idl_val.inject(2))
    have fact2: "interp_var \<mu> = interp_var \<omega>"
      using assm1
      apply (rule allE[where x="InternalVar IdlInterpVar"])
      unfolding idl_atom_fv_syn_full.simps
      unfolding idl_state_eval_full.simps
      unfolding idl_internal_get_interp.simps
      by (metis (lifting) ext
          idl_val.inject(1))
    show "idl_atom_eval_full a \<mu> = idl_atom_eval_full a \<omega>"
      using fact1 fact2 fv_overapprox
      by (metis idl_atom_eval_full.simps idl_internal_get_state.elims
          idl_state.collapse)
  qed
  show "\<forall>\<omega> \<mu> V.
       \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> idl_state_eval_full \<nu> v = idl_state_eval_full \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> idl_state_eval_full \<nu> v = idl_state_eval_full \<omega> v)"
  proof (intro allI)
    fix \<omega> \<mu> :: "('interp, 'state) idl_state"
    fix V
    obtain s :: "'state" where s:
      "\<forall>v. (v \<in> {x. ExternalVar x \<in> V} \<longrightarrow> state_eval s v = state_eval (other_var \<mu>) v) \<and>
           (v \<notin> {x. ExternalVar x \<in> V} \<longrightarrow> state_eval s v = state_eval (other_var \<omega>) v)"
      using state_space_convexity
      by presburger
    define I where "I = (if InternalVar IdlInterpVar \<in> V then interp_var \<mu> else interp_var \<omega>)"
    let ?\<nu> = "IdlState I s"
    have "(v \<in> V \<longrightarrow> idl_state_eval_full ?\<nu> v = idl_state_eval_full \<mu> v) \<and>
          (v \<notin> V \<longrightarrow> idl_state_eval_full ?\<nu> v = idl_state_eval_full \<omega> v)" for v
    proof (cases v)
      case (InternalVar x)
      then show ?thesis by (cases x) (auto simp: I_def)
    next
      case (ExternalVar x)
      then show ?thesis using s by (auto simp: Let_def)
    qed
    then show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> idl_state_eval_full \<nu> v = idl_state_eval_full \<mu> v) \<and>
                       (v \<notin> V \<longrightarrow> idl_state_eval_full \<nu> v = idl_state_eval_full \<omega> v)"
      by blast
  qed
qed
end

locale interp_dynamic_theory =
 interp_fol_core atom_eval atom_fv_syn state_eval
    for (* this is necessary because we need matching type variables *)
      atom_eval :: "'atom \<Rightarrow> 'interp \<Rightarrow> 'state \<Rightarrow> bool"
      and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
      and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  +
  fixes prog_eval :: "'prog \<Rightarrow> 'interp \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
  assumes prog_fv_finite: "finite (Collect (dyn_prog_FV \<pi>))"
        and prog_fv_overapprox:
        "\<And> \<pi> I V \<mu> \<omega> \<nu> . ((\<forall> v . ((dyn_prog_FV \<pi> v) \<longrightarrow> (V v))) \<and> fol_states_agree_on_gen state_eval V \<mu> \<omega> \<and> prog_eval \<pi> I \<mu> \<nu>) \<longrightarrow> (\<exists> \<upsilon> . prog_eval \<pi> I \<omega> \<upsilon> \<and> fol_states_agree_on_gen state_eval V \<nu> \<upsilon>)"
        and prog_var_determinance:
          "\<forall> \<pi> I \<mu> \<omega> . ((\<forall> v. ((state_eval \<mu>) v = (state_eval \<omega>) v)) \<longrightarrow> prog_eval \<pi> I \<mu> = prog_eval \<pi> I \<omega>)"
begin

fun idl_prog_eval_full :: "
  'prog \<Rightarrow>
  ('interp, 'state) idl_state \<Rightarrow> 
  ('interp, 'state) idl_state \<Rightarrow> bool"
  where "idl_prog_eval_full \<pi> (IdlState I \<mu>) (IdlState J \<omega>) =
          ((prog_eval \<pi> I \<mu> \<omega>) \<and> I=J)"

fun idl_prog_fv_syn_full :: "'prog \<Rightarrow> 'var idl_var \<Rightarrow> bool"
  where
    "idl_prog_fv_syn_full \<pi> (InternalVar x) = True"
  | "idl_prog_fv_syn_full \<pi> (ExternalVar x) = dyn_prog_FV \<pi> x"

sublocale dt: dynamic_theory
                idl_atom_eval_full idl_atom_fv_syn_full idl_state_eval_full
                idl_prog_eval_full idl_prog_fv_syn_full
proof
  show "\<And>a. finite (Collect (idl_prog_fv_syn_full a))"
  proof -
    fix a
    have fact1: "(Collect (idl_prog_fv_syn_full a))
            =
          ({ y . \<exists> x . y=(ExternalVar x) \<and> (x \<in> (Collect (dyn_prog_FV a))) }
          \<union>
          { y. \<exists> x . y=(InternalVar x) })"
      by (smt (verit, best) Collect_cong Un_def idl_prog_fv_syn_full.elims(1)
          idl_prog_fv_syn_full.simps(1) idl_var.inject(2) mem_Collect_eq) 

    have fact2: "finite { y. \<exists> x . y=(InternalVar x) }"
    proof -
      have "{y. \<exists>x. y = InternalVar x} = range InternalVar"
        by auto
      thus ?thesis
        by (metis finite_UNIV finite_imageI)
    qed

    have "finite ({ y . \<exists> x . y=(ExternalVar x) \<and> (x \<in> (Collect (dyn_prog_FV a))) })"
      using prog_fv_finite
      by auto

    thus "finite (Collect (idl_prog_fv_syn_full a))"
      using fact1 fact2
      by auto
  qed
  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
         (\<forall>v. idl_prog_fv_syn_full \<pi> v \<longrightarrow> V v) \<and>
         fc.fol_states_agree_on V \<mu> \<omega> \<and> idl_prog_eval_full \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. idl_prog_eval_full \<pi> \<omega> \<upsilon> \<and> fc.fol_states_agree_on V \<nu> \<upsilon>)"
  proof (intro impI, elim conjE)
    fix \<pi> V \<mu> \<omega> \<nu>
    assume fv: "\<forall>v. idl_prog_fv_syn_full \<pi> v \<longrightarrow> V v"
       and agree: "fc.fol_states_agree_on V \<mu> \<omega>"
       and run: "idl_prog_eval_full \<pi> \<mu> \<nu>"
    note defs = fc.fol_states_agree_on_def fol_states_agree_on_gen_def
    obtain I \<mu>s where \<mu>: "\<mu> = IdlState I \<mu>s" by (cases \<mu>)
    obtain K \<omega>s where \<omega>: "\<omega> = IdlState K \<omega>s" by (cases \<omega>)
    obtain J \<nu>s where \<nu>: "\<nu> = IdlState J \<nu>s" by (cases \<nu>)
    from run have run': "prog_eval \<pi> I \<mu>s \<nu>s" and IJ: "I = J"
      using \<mu> \<nu> apply auto[1]
      using \<mu> \<nu> run by fastforce
    have Vint: "V (InternalVar IdlInterpVar)"
      using fv[rule_format, of "InternalVar IdlInterpVar"] by simp
    have agree': "\<forall>v. V v \<longrightarrow> idl_state_eval_full \<mu> v = idl_state_eval_full \<omega> v"
      using agree by (simp add: defs)
    have IK: "I = K"
      using agree'[rule_format, OF Vint] by (simp add: \<mu> \<omega>)
    define V' where "V' = (\<lambda>x. V (ExternalVar x))"
    have fv': "\<forall>v. dyn_prog_FV \<pi> v \<longrightarrow> V' v"
      unfolding V'_def using fv by (metis idl_prog_fv_syn_full.simps(2))
    have agree_s: "fol_states_agree_on_gen state_eval V' \<mu>s \<omega>s"
      unfolding fol_states_agree_on_gen_def V'_def
    proof (intro allI impI)
      fix v assume "V (ExternalVar v)"
      from agree'[rule_format, OF this] show "state_eval \<mu>s v = state_eval \<omega>s v"
        by (simp add: \<mu> \<omega> Let_def)
    qed
    obtain \<upsilon>s where run2: "prog_eval \<pi> I \<omega>s \<upsilon>s"
                and agree2: "fol_states_agree_on_gen state_eval V' \<nu>s \<upsilon>s"
      using prog_fv_overapprox[of \<pi> V' \<mu>s \<omega>s I \<nu>s]  fv' agree_s run'
      by blast
    let ?\<upsilon> = "IdlState I \<upsilon>s"
    have "idl_prog_eval_full \<pi> \<omega> ?\<upsilon>"
      using run2 IK by (simp add: \<omega>)
    moreover have "fc.fol_states_agree_on V \<nu> ?\<upsilon>"
      unfolding defs
    proof (intro allI impI)
      fix v assume "V v"
      show "idl_state_eval_full \<nu> v = idl_state_eval_full ?\<upsilon> v"
      proof (cases v)
        case (InternalVar x)
        then show ?thesis using IJ by (simp add: \<nu>)
      next
        case (ExternalVar x)
        with \<open>V v\<close> have "V' x" by (simp add: V'_def)
        with agree2 have "state_eval \<nu>s x = state_eval \<upsilon>s x"
          by (simp add: fol_states_agree_on_gen_def)
        with ExternalVar show ?thesis by (simp add: \<nu> Let_def)
      qed
    qed
    ultimately show "\<exists>\<upsilon>. idl_prog_eval_full \<pi> \<omega> \<upsilon> \<and> fc.fol_states_agree_on V \<nu> \<upsilon>"
      by blast
  qed
  show " \<forall>\<pi> \<mu> \<omega>.
       (\<forall>v. idl_state_eval_full \<mu> v = idl_state_eval_full \<omega> v) \<longrightarrow>
       idl_prog_eval_full \<pi> \<mu> = idl_prog_eval_full \<pi> \<omega>"
  proof (intro allI impI)
    fix \<pi> \<mu> \<omega>
    assume agree: "\<forall>v. idl_state_eval_full \<mu> v = idl_state_eval_full \<omega> v"
    obtain I \<mu>s where \<mu>: "\<mu> = IdlState I \<mu>s" by (cases \<mu>)
    obtain K \<omega>s where \<omega>: "\<omega> = IdlState K \<omega>s" by (cases \<omega>)
    have IK: "I = K"
      using agree[rule_format, of "InternalVar IdlInterpVar"] by (simp add: \<mu> \<omega>)
    have "\<forall>v. state_eval \<mu>s v = state_eval \<omega>s v"
    proof
      fix v
      from agree[rule_format, of "ExternalVar v"]
      show "state_eval \<mu>s v = state_eval \<omega>s v" by (simp add: \<mu> \<omega> Let_def)
    qed
    hence pe: "prog_eval \<pi> I \<mu>s = prog_eval \<pi> I \<omega>s"
      using prog_var_determinance by blast
    show "idl_prog_eval_full \<pi> \<mu> = idl_prog_eval_full \<pi> \<omega>"
    proof (rule ext)
      fix \<nu>
      show "idl_prog_eval_full \<pi> \<mu> \<nu> = idl_prog_eval_full \<pi> \<omega> \<nu>"
        by (cases \<nu>) (simp add: \<mu> \<omega> IK[symmetric] pe)
    qed
  qed
qed

end
end
