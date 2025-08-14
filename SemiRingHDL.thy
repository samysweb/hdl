theory SemiRingHDL
  imports
    Main
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "NatKATDynamicLogic"
    "SemiRingFOL"
    "SemiRingDL"
    "HeterogeneousDynamicLogic"
begin


type_synonym semiringhfol_var = "string + string"

datatype ('semiringhfol_val :: ordered_semiring) semiringhfol_term =
  Const 'semiringhfol_val
  | Var "semiringhfol_var"
  | Add "'semiringhfol_val semiringhfol_term" "'semiringhfol_val semiringhfol_term"
  | Mul "'semiringhfol_val semiringhfol_term" "'semiringhfol_val semiringhfol_term"

datatype ('semiringhfol_val :: ordered_semiring) semiringhfol_atom =
  Eq "'semiringhfol_val semiringhfol_term" "'semiringhfol_val semiringhfol_term"
  | Less "'semiringhfol_val semiringhfol_term" "'semiringhfol_val semiringhfol_term"

fun semiringhfol_TermEval :: "('semiringhfol_val :: ordered_semiring) semiringhfol_term \<Rightarrow> (((semiringfol_var, 'semiringhfol_val) fol_state)*((semiringfol_var, 'semiringhfol_val) fol_state)) \<Rightarrow> 'semiringhfol_val"
  where
    "semiringhfol_TermEval (Const n) \<mu> = n"
  | "semiringhfol_TermEval (Var (Inl v)) \<mu> = ((fst \<mu>) v)"
  | "semiringhfol_TermEval (Var (Inr v)) \<mu> = ((snd \<mu>) v)"
  | "semiringhfol_TermEval (Add a b) \<mu> = (semiringhfol_TermEval a \<mu>) + (semiringhfol_TermEval b \<mu>)"
  | "semiringhfol_TermEval (Mul a b) \<mu> = (semiringhfol_TermEval a \<mu>) * (semiringhfol_TermEval b \<mu>)"

fun semiringhfol_AtomEval :: "('semiringhfol_val :: ordered_semiring) semiringhfol_atom \<Rightarrow> (((semiringfol_var, 'semiringhfol_val) fol_state)*((semiringfol_var, 'semiringhfol_val) fol_state)) \<Rightarrow> bool"
  where
    "semiringhfol_AtomEval (Eq a b) \<mu> = ((semiringhfol_TermEval a \<mu>) = (semiringhfol_TermEval b \<mu>))"
  | "semiringhfol_AtomEval (Less a b) \<mu> = ((semiringhfol_TermEval a \<mu>) < (semiringhfol_TermEval b \<mu>))"

fun semiringhfol_TermFVSyn :: "('semiringhfol_val :: ordered_semiring) semiringhfol_term \<Rightarrow> semiringhfol_var \<Rightarrow> bool"
  where
    "semiringhfol_TermFVSyn (Const n) v = False"
  | "semiringhfol_TermFVSyn (Var w) v = (v=w)"
  | "semiringhfol_TermFVSyn (Add a b) v = ((semiringhfol_TermFVSyn a v) \<or> (semiringhfol_TermFVSyn b v))"
  | "semiringhfol_TermFVSyn (Mul a b) v = ((semiringhfol_TermFVSyn a v) \<or> (semiringhfol_TermFVSyn b v))"

fun semiringhfol_AtomFVSyn :: "('semiringhfol_val :: ordered_semiring) semiringhfol_atom \<Rightarrow> semiringhfol_var \<Rightarrow> bool"
  where
    "semiringhfol_AtomFVSyn (Eq a b) v = ((semiringhfol_TermFVSyn a v) \<or> (semiringhfol_TermFVSyn b v))"
  | "semiringhfol_AtomFVSyn (Less a b) v = ((semiringhfol_TermFVSyn a v) \<or> (semiringhfol_TermFVSyn b v))"


(* Sanity check: semiring DL + semiring DL *)
interpretation semiring_hdl:
  HeterogeneousDynamicLogic.HeterogeneousDynLog
    "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV
    "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV
    semiringhfol_AtomEval semiringhfol_AtomFVSyn
proof
  fix a :: "('semiringhfol_val :: ordered_semiring) semiringhfol_atom"
  fix \<mu> :: "(semiringfol_var \<Rightarrow> ('semiringhfol_val :: ordered_semiring))*(semiringfol_var \<Rightarrow> ('semiringhfol_val :: ordered_semiring))"
  fix \<omega> :: "(semiringfol_var \<Rightarrow> ('semiringhfol_val :: ordered_semiring))*(semiringfol_var \<Rightarrow> ('semiringhfol_val :: ordered_semiring))"

  show "finite (Collect (semiringhfol_AtomFVSyn a))"
  proof -
    have termFV_finite: "\<And> (t :: ('semiringhfol_val :: ordered_semiring) semiringhfol_term) .finite (Collect (semiringhfol_TermFVSyn t))"
    proof -
      fix t :: "('semiringhfol_val :: ordered_semiring) semiringhfol_term"
      show "finite (Collect (semiringhfol_TermFVSyn t))"
      proof (induct t)
        case (Const x)
        then show ?case by auto
      next
        case (Var x)
        then show ?case by auto
      next
        case (Add t1 t2)
        then show ?case by auto
      next
        case (Mul t1 t2)
        then show ?case by auto
      qed
    qed

    thus "finite (Collect (semiringhfol_AtomFVSyn a))"
    proof (induct a)
      case (Eq x1 x2)
      then show ?case
        unfolding semiringhfol_AtomFVSyn.simps
        by auto
    next
      case (Less x1 x2)
      then show ?case
        unfolding semiringhfol_AtomFVSyn.simps
        by auto
    qed
  qed

  have "\<And> t .fol_states_agree_on_gen (common_atom_eval state_id state_id)
        (semiringhfol_TermFVSyn t) \<mu> \<omega> \<Longrightarrow>
       semiringhfol_TermEval t \<mu> = semiringhfol_TermEval t \<omega>"
  proof -
      fix t :: "('semiringhfol_val :: ordered_semiring) semiringhfol_term"
      show "fol_states_agree_on_gen (common_atom_eval state_id state_id)
        (semiringhfol_TermFVSyn t) \<mu> \<omega> \<Longrightarrow>
       semiringhfol_TermEval t \<mu> = semiringhfol_TermEval t \<omega>"
      proof (induct t)
        case (Const x)
        then show ?case by auto
      next
        case (Var x)
        then show ?case
          unfolding fol_states_agree_on_gen_def
          unfolding common_atom_eval_def
          unfolding semiringhfol_TermFVSyn.simps
          proof (induct x)
            case (Inl a)
            then show ?case
              unfolding semiringhfol_TermEval.simps
              by auto
          next
            case (Inr b)
            then show ?case
              unfolding semiringhfol_TermEval.simps
              by auto
          qed
      next
        case (Add t1 t2)
        then show ?case by auto
      next
        case (Mul t1 t2)
        then show ?case by auto
      qed
    qed

  thus "fol_states_agree_on_gen (common_atom_eval state_id state_id)
        (semiringhfol_AtomFVSyn a) \<mu> \<omega> \<Longrightarrow>
       semiringhfol_AtomEval a \<mu> = semiringhfol_AtomEval a \<omega>"
  proof (induct a)
    case (Eq x1 x2)
    then show ?case
      by simp
  next
    case (Less x1 x2)
    then show ?case
      by simp
  qed

  show "\<forall>\<omega> \<mu> V.
           \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow>
                    common_atom_eval state_id state_id \<nu> v =
                    common_atom_eval state_id state_id \<mu> v) \<and>
                   (v \<notin> V \<longrightarrow>
                    common_atom_eval state_id state_id \<nu> v =
                    common_atom_eval state_id state_id \<omega> v)"
  proof (intro allI)
    fix \<omega>
    fix \<mu>
    fix V :: "(string + string) set"

    let ?Vl = "{v . (Inl v) \<in> V}"
    let ?Vr = "{v . (Inr v) \<in> V}"

    let ?S = "((\<lambda> v . if v \<in> ?Vl then ((fst \<mu>) v) else ((fst \<omega>) v)), (\<lambda> v . if v \<in> ?Vr then ((snd \<mu>) v) else ((snd \<omega>) v)))"

    show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow>
                common_atom_eval state_id state_id \<nu> v =
                common_atom_eval state_id state_id \<mu> v) \<and>
               (v \<notin> V \<longrightarrow>
                common_atom_eval state_id state_id \<nu> v =
                common_atom_eval state_id state_id \<omega> v)"
    proof (intro exI[where x= "?S"], intro allI)
      fix v
      show "(v \<in> V \<longrightarrow>
                common_atom_eval state_id state_id ?S v =
                common_atom_eval state_id state_id \<mu> v) \<and>
               (v \<notin> V \<longrightarrow>
                common_atom_eval state_id state_id ?S v =
                common_atom_eval state_id state_id \<omega> v)"
      proof (induct v)
        case (Inl a)
        then show ?case
          unfolding common_atom_eval_def
          by simp
      next
        case (Inr b)
        then show ?case
          unfolding common_atom_eval_def
          by simp
      qed
    qed
  qed
qed
end