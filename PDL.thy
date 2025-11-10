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
datatype pdl_var = singleton_var

type_synonym 'atom pdl_state = "(pdl_var \<Rightarrow> ('atom \<Rightarrow> bool))"

fun pdl_atom_eval :: "'atom \<Rightarrow> ('atom pdl_state) \<Rightarrow> bool"
  where "pdl_atom_eval a \<omega> = ((\<omega> singleton_var) a)"

(* Trivial of course... *)
(* Should also be possible to make this False?*)
fun pdl_fv_syn :: "'atom \<Rightarrow> pdl_var \<Rightarrow> bool"
  where "pdl_fv_syn a singleton_var = True"
(*interpretation pdlDLCore
  : dynLogCore
    "pdl_atom_eval" "pdl_prog_eval"*)

definition state_id :: "'atom pdl_state \<Rightarrow> 'atom pdl_state"
  where [simp]: "state_id = id"

interpretation pdlFOL : folCore
  pdl_atom_eval pdl_fv_syn state_id
proof
    show "\<And>a. finite (Collect (pdl_fv_syn a))"
      by (metis (full_types) List.finite_set UNIV_I finite_insert insert_iff pdl_var.exhaust subsetI subset_antisym)
  
    show "\<And>a \<mu> \<omega>. fol_states_agree_on_gen state_id (pdl_fv_syn a) \<mu> \<omega> \<Longrightarrow> pdl_atom_eval a \<mu> = pdl_atom_eval a \<omega>"
      by (simp)

    show "\<forall>\<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_id \<nu> v = state_id \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_id \<nu> v = state_id \<omega> v)"
      by (metis pdl_var.exhaust)
  qed

datatype 'ap pdl_prog =
    Atomic "'ap"
    | Seq     "'ap pdl_prog" "'ap pdl_prog"
    | Choice  "'ap pdl_prog" "'ap pdl_prog"
    | Check   "('ap, pdl_var) fol_formula"
    | Repeat  "'ap pdl_prog"

(* use rtrancl (rel (\<rho> \<pi>))) instead *)
fun pdl_prog_eval_internal  :: "('atom \<Rightarrow> 'atom pdl_state \<Rightarrow> 'atom pdl_state \<Rightarrow> bool) \<Rightarrow> Nat.nat \<Rightarrow> 'atom pdl_prog \<Rightarrow> 'atom pdl_state \<Rightarrow> 'atom pdl_state \<Rightarrow> bool"
  where
    "pdl_prog_eval_internal I n (Atomic \<alpha>) \<mu> \<omega> = I \<alpha> \<mu> \<omega>"
  | "pdl_prog_eval_internal I n (Seq \<alpha> \<beta>) \<mu> \<omega> = (\<exists> \<nu> . (pdl_prog_eval_internal I n \<alpha> \<mu> \<nu>) \<and> (pdl_prog_eval_internal I n \<alpha> \<nu> \<omega>))"
  | "pdl_prog_eval_internal I n (Choice \<alpha> \<beta>) \<mu> \<omega> = ((pdl_prog_eval_internal I n \<alpha> \<mu> \<omega>) \<or> (pdl_prog_eval_internal I n \<beta> \<mu> \<omega>))"
  | "pdl_prog_eval_internal I n (Check \<phi>) \<mu> \<omega> = (pdlFOL.fol_eval \<phi> \<mu> \<and> \<mu>=\<omega>)"
  | "pdl_prog_eval_internal I n (Repeat \<alpha>) \<mu> \<omega> = (if n>0 then (\<mu>=\<omega> \<or> (pdl_prog_eval_internal I (n-1) (Seq \<alpha> (Repeat \<alpha>) ) \<mu> \<omega>)) else False)"
      

fun pdl_prog_eval :: "('atom \<Rightarrow> 'atom pdl_state \<Rightarrow> 'atom pdl_state \<Rightarrow> bool) \<Rightarrow> 'atom pdl_prog \<Rightarrow> 'atom pdl_state \<Rightarrow> 'atom pdl_state \<Rightarrow> bool"
  where
    "pdl_prog_eval I \<alpha> \<mu> \<omega> = (\<exists> n . (pdl_prog_eval_internal I n \<alpha> \<mu> \<omega>))"



definition pdl_prog_fv_syn :: "'atom pdl_prog \<Rightarrow> pdl_var \<Rightarrow> bool"
  where "pdl_prog_fv_syn \<alpha> x = True"

definition pdl_prog_bv_syn :: "'atom pdl_prog \<Rightarrow> pdl_var \<Rightarrow> bool"
  where "pdl_prog_bv_syn \<alpha> x = True"



interpretation pdlDL : dynLogCore
    "pdl_atom_eval" "pdl_fv_syn" "state_id"
    "(pdl_prog_eval I)" "pdl_prog_fv_syn"
proof
  show "\<And>\<pi>. finite (Collect (pdl_prog_fv_syn \<pi>))"
    by (metis (full_types) finite.emptyI finite_insert insert_iff pdl_var.exhaust rev_finite_subset subsetI)

  show "\<And>\<pi> V \<mu> \<omega> \<nu>.
       (\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       folCore.fol_states_agree_on state_id V \<mu> \<omega> \<and> pdl_prog_eval I \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. pdl_prog_eval I \<pi> \<omega> \<upsilon> \<and> folCore.fol_states_agree_on state_id V \<nu> \<upsilon>)"
    unfolding pdl_prog_fv_syn_def
    unfolding folCore.fol_states_agree_on_def
  proof (intro impI)
    fix \<pi> V \<mu> \<omega> \<nu>
    assume assms: "(\<forall>v. True \<longrightarrow> V v) \<and> folCore.fol_states_agree_on state_id V \<mu> \<omega> \<and> pdl_prog_eval I \<pi> \<mu> \<nu>"
    then have "V=(\<lambda> v . True)"
      by blast
    then have "folCore.fol_states_agree_on state_id (\<lambda> v . True) \<mu> \<omega>"
      using assms by blast
    then have "\<forall> v . \<mu> v = \<omega> v"
      using pdlFOL.fol_states_agree_on_def[of "(\<lambda>v. True)" \<mu> \<omega>]
      by auto
    
    thus "\<exists>\<upsilon>. pdl_prog_eval I \<pi> \<omega> \<upsilon> \<and> folCore.fol_states_agree_on state_id V \<nu> \<upsilon>"
      apply (intro exI[where x=\<nu>])
      unfolding pdlFOL.fol_states_agree_on_def
      using assms by presburger
  qed

  show " \<forall>\<pi> \<mu> \<omega>. (\<forall>v. state_id \<mu> v = state_id \<omega> v) \<longrightarrow> pdl_prog_eval I \<pi> \<mu> = pdl_prog_eval I \<pi> \<omega>"
    unfolding state_id_def id_def
    by presburger
qed

interpretation pdlDLFull : dynLog
    "pdl_atom_eval" "pdl_fv_syn" "state_id"
    "pdl_prog_eval I" "pdl_prog_fv_syn" (*"pdl_prog_bv_syn"*)
  by standard
(*  show "\<And>\<pi> v. pdlDL.dyn_prog_bv_sem \<pi> v \<Longrightarrow> pdl_prog_bv_syn \<pi> v"
    unfolding pdl_prog_bv_syn_def
    by simp
qed*)

interpretation regular_pdl :
  KATDynLog "pdl_atom_eval" "pdl_fv_syn" "state_id"
    "pdl_prog_eval I" "pdl_prog_fv_syn"
  unfolding KATDynLog_def
    using pdlDLFull.dynLog_axioms
    by blast

interpretation regular_pdl_kat :
KleeneDynLog "pdl_atom_eval" "pdl_fv_syn" "state_id"
    "pdl_prog_eval I" "pdl_prog_fv_syn"
  apply standard
  unfolding state_id_def id_def
  by presburger
end