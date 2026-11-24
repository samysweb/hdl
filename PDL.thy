subsection\<open>Propositional Dynamic Logic\<close>
text\<open>
\label{subsec:inst:pdl}
\<close>
theory PDL
  imports
    Main
    DynamicLogicCore
    DynamicLogic
    DynamicLogicProof
    HavocDynamicLogic
    KATDynamicLogic
    KATRewriting
    InterpDL
begin
(*
locale interp_dynamic_theory =
 interp_fol_core atom_eval atom_fv_syn state_eval
    for (* this is necessary because we need matching type variables *)
      atom_eval :: "'atom \<Rightarrow> 'interp \<Rightarrow> 'state \<Rightarrow> bool"
      and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
      and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  +
  fixes prog_eval :: "'prog \<Rightarrow> 'interp \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"*)

datatype pdl_var = SingletonVar

datatype ('atom,'prog,'state) pdl_interp =
  PdlInterp (atom_eval: "'atom \<Rightarrow> 'state \<Rightarrow> bool")
            (prog_eval: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool")


fun pdl_var_eval :: "'state \<Rightarrow> pdl_var \<Rightarrow> 'state"
  where
    "pdl_var_eval \<omega> x = \<omega>"

fun pdl_atom_eval :: "'atom \<Rightarrow> ('atom,'prog,'state) pdl_interp \<Rightarrow> 'state \<Rightarrow> bool"
  where "pdl_atom_eval a I \<omega> = ((atom_eval I) a \<omega>)"

fun pdl_prog_eval :: "'prog \<Rightarrow> ('atom,'prog,'state) pdl_interp \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
  where
    "pdl_prog_eval prog I \<mu> \<omega> = ((prog_eval I) prog \<mu> \<omega>)"

fun pdl_fv_syn :: "'atom \<Rightarrow> pdl_var \<Rightarrow> bool"
  where
    "pdl_fv_syn a x = True"


interpretation pdlFOL : interp_fol_core
  pdl_atom_eval pdl_fv_syn pdl_var_eval
proof
  fix a :: 'atom
  show "finite (Collect (pdl_fv_syn a))"
  proof -
    have fact1: "(Collect (pdl_fv_syn a)) \<subseteq> { SingletonVar }"
      using pdl_var.exhaust by blast
    have "finite { SingletonVar }"
      by auto
    then show ?thesis
      using fact1
      using rev_finite_subset by blast
  qed
  
    show "\<And>a \<mu> \<omega> I.
       fol_states_agree_on_gen pdl_var_eval (pdl_fv_syn a) \<mu> \<omega> \<Longrightarrow>
       pdl_atom_eval a I \<mu> = pdl_atom_eval a I \<omega>"
      unfolding pdl_atom_eval.simps
      unfolding fol_states_agree_on_gen_def
      unfolding pdl_fv_syn.simps
      unfolding pdl_var_eval.simps
      by blast

    show " \<forall>\<omega> \<mu> V.
             \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<mu> v) \<and>
                     (v \<notin> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<omega> v)"
      by (metis pdl_var.exhaust)
  qed

fun pdl_prog_fv_syn :: "'prog \<Rightarrow> pdl_var \<Rightarrow> bool"
  where
    "pdl_prog_fv_syn p x = True"

interpretation pdlDLFull : interp_dynamic_theory
    "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
proof
  show "\<And>\<pi>. finite (Collect (pdl_prog_fv_syn \<pi>))"
  proof -
    fix \<pi> :: 'prog
    have fact1: "(Collect (pdl_prog_fv_syn \<pi>)) \<subseteq> { SingletonVar }"
      using pdl_var.exhaust by blast
    have "finite { SingletonVar }"
      by auto
    then show "finite (Collect (pdl_prog_fv_syn \<pi>))"
      using fact1
      using rev_finite_subset by blast
  qed
  show "\<And>\<pi> I V \<mu> \<omega> \<nu>.
       (\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       fol_states_agree_on_gen pdl_var_eval V \<mu> \<omega> \<and> pdl_prog_eval \<pi> I \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. pdl_prog_eval \<pi> I \<omega> \<upsilon> \<and> fol_states_agree_on_gen pdl_var_eval V \<nu> \<upsilon>)"
    unfolding pdl_prog_fv_syn.simps
    unfolding fol_states_agree_on_gen_def
    unfolding pdl_var_eval.simps
    unfolding pdl_prog_eval.simps
    by auto

  show "\<forall>\<pi> I \<mu> \<omega>.
       (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v) \<longrightarrow>
       pdl_prog_eval \<pi> I \<mu> = pdl_prog_eval \<pi> I \<omega>"
    unfolding pdl_var_eval.simps
    unfolding pdl_prog_eval.simps
    by auto
qed

interpretation regular_pdl :
  regular_lifting
    "pdlFOL.idl_atom_eval_full"
    "pdlFOL.idl_atom_fv_syn_full"
    "pdlFOL.idl_state_eval_full"
    "pdlDLFull.idl_prog_eval_full"
    "pdlDLFull.idl_prog_fv_syn_full"
  unfolding regular_lifting_def
    using pdlDLFull.dt.dynamic_theory_axioms
    by blast

(*interpretation regular_pdl_kat :
KleeneDynLog
    "pdlFOL.idl_atom_eval_full"
    "pdlFOL.idl_atom_fv_syn_full"
    "pdlFOL.idl_state_eval_full"
    "pdlDLFull.idl_prog_eval_full"
    "pdlDLFull.idl_prog_fv_syn_full"
proof
  show "\<forall>\<pi> \<mu> \<omega> \<mu>' \<omega>'.
       (\<forall>v. pdlFOL.idl_state_eval_full \<mu> v = pdlFOL.idl_state_eval_full \<omega> v \<and>
            pdlFOL.idl_state_eval_full \<mu>' v = pdlFOL.idl_state_eval_full \<omega>' v) \<longrightarrow>
       pdlDLFull.idl_prog_eval_full \<pi> \<mu> \<mu>' = pdlDLFull.idl_prog_eval_full \<pi> \<omega> \<omega>'"
    sledgehammer
proof (intro allI, intro impI)
    fix \<pi> :: 'prog
    fix \<mu> \<omega> \<mu>' \<omega>' :: "('atom, 'prog, 'state) pdl_state"
    assume "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and>
           pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v"
    then have all_eq: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v"
      by blast
    have fact1: "fol_equal_everywhere_but_gen pdl_var_eval StateVar \<mu>
            =
          fol_equal_everywhere_but_gen pdl_var_eval StateVar \<omega>"
      using all_eq
      unfolding fol_equal_everywhere_but_gen_def fol_states_agree_on_gen_def
      by presburger

    have fact2: "\<And> \<omega>' . prog_eval \<omega>' \<pi> (state_id \<mu> singleton_var) = prog_eval \<omega>' \<pi> (state_id \<omega> singleton_var)"
      unfolding prog_eval_def state_id_def
      using all_eq
      by (metis pdl_universe.inject(1) pdl_var_eval.simps(1) state_id_def)

    show "pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
      unfolding pdl_prog_eval.simps
      unfolding fact1 fact2
      by (smt (verit, ccfv_threshold)
          \<open>\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and> pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v\<close>
          fol_equal_everywhere_but_gen_def fol_states_agree_on_gen_def
          pdl_universe.inject(1,3) pdl_var_eval.simps(1,3))
  qed
qed*)

(*declare [[show_types]]
declare [[show_sorts]]
*)
  

text\<open>Fix EV so that all theorems below evaluate w.r.t. the same PDL state space \<close>
context
  fixes ev :: "('atom, pdl_var idl_var, 'prog) dyn_formula
                \<Rightarrow> (('atom,'prog,'state) pdl_interp, 'state) idl_state \<Rightarrow> bool"
  fixes EV :: "('atom, pdl_var idl_var,
                ('atom, pdl_var idl_var, 'prog) kat_prog) dyn_formula
               \<Rightarrow> (('atom,'prog,'state) pdl_interp, 'state) idl_state \<Rightarrow> bool"
  assumes ev_def: "ev = pdlDLFull.dt.dyn_eval"
  assumes EV_def: "EV = regular_pdl.kat_dl.dyn_eval"
begin

lemma test0:
  assumes "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL X) (FOL Y))"
      and "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL Y) (FOL Z))"
    shows "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL X) (FOL Z))"
  using assms
  unfolding EV_def
  using regular_pdl.kat_dl.dt_prop_imp_trans
  by blast
  

lemma test1:
  assumes "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL X) (\<lbrakk> (KATPROG P) \<rbrakk> (FOL Y)))"
  assumes "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL Y) (\<lbrakk> (KATPROG Q) \<rbrakk> ((FOL Y) and (FOL Z))))"
  shows "\<Turnstile>[EV]
              (PDL.regular_pdl.kat_dl.IMP (FOL X) (\<lbrakk> ((KATPROG P);(KATPROG Q)) \<rbrakk> ((FOL Y) and (FOL Z))))"
proof -
  have "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL X) (\<lbrakk> (KATPROG P)\<rbrakk>(\<lbrakk>(KATPROG Q) \<rbrakk> (FOL Y and FOL Z))))"
    using assms
    unfolding EV_def
    using regular_pdl.kat_dl.dt_box_MRimp
    by blast

  then show "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP (FOL X) (\<lbrakk> (KATPROG P;KATPROG Q) \<rbrakk> (FOL Y and FOL Z)))"
    unfolding EV_def
    by (metis regular_pdl.dyn_axiom_seq regular_pdl.kat_dl.EQUIV_def
        regular_pdl.kat_dl.dt_prop_imp_trans
        regular_pdl.kat_dl.dyn_hilbert_axiom_conj_e2
        regular_pdl.kat_dl.dyn_hilbert_mp)
qed


lemma test12:
  assumes "\<Turnstile>[ev]
              ((FOL X) \<Rrightarrow> \<lbrakk> P \<rbrakk> (FOL Y))"
  assumes "\<Turnstile>[ev] ((FOL Y) \<Rrightarrow> \<lbrakk> Q \<rbrakk> ((FOL Y) and (FOL Z)))"
  shows "\<Turnstile>[EV]
              (PDL.regular_pdl.kat_dl.IMP
              (FOL X) (\<lbrakk> ((KATPROG P);(KATPROG Q)) \<rbrakk> ((FOL Y) and (FOL Z))))"
proof -
  have fact1: "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP
                      (FOL X) (\<lbrakk> (KATPROG P) \<rbrakk> (FOL Y)))"
    using assms(1)
    using regular_pdl.dyn_axiom_RR[
        where \<phi>="((FOL X) \<Rrightarrow> \<lbrakk> P \<rbrakk> (FOL Y))"]
    unfolding pdlDLFull.dt.IMP_def pdlDLFull.dt.OR_def
    unfolding regular_pdl.translate.simps
    unfolding regular_pdl.kat_dl.IMP_def regular_pdl.kat_dl.OR_def
    unfolding EV_def ev_def
    by blast
  
  have fact2: "\<Turnstile>[EV] (PDL.regular_pdl.kat_dl.IMP
                        (FOL Y) (\<lbrakk> (KATPROG Q) \<rbrakk> ((FOL Y) and (FOL Z))))"
    using assms(2)
    using regular_pdl.dyn_axiom_RR[
        where \<phi>="((FOL Y) \<Rrightarrow> \<lbrakk> Q \<rbrakk> ((FOL Y) and (FOL Z)))"]
    unfolding pdlDLFull.dt.IMP_def pdlDLFull.dt.OR_def
    unfolding regular_pdl.translate.simps
    unfolding regular_pdl.kat_dl.IMP_def regular_pdl.kat_dl.OR_def
    unfolding EV_def ev_def
    by blast
  show ?thesis
    using fact1 fact2 test1
    by blast
qed

end
end
