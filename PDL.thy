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
    DynamicLogicProof
    HavocDynamicLogic
    KATDynamicLogic
    KATRewriting
begin

(* PDL does not have first-order variables *)
datatype pdl_atom_var = singleton_var

datatype ('atom,'prog) pdl_var =
     StateVar
   | AtomVar 'atom
   | ProgVar 'prog

datatype 'state pdl_universe =
    PdlStateId 'state
  | PdlStateAtomVal "'state \<Rightarrow> bool"
  | PdlStateProgVal "'state \<Rightarrow> 'state \<Rightarrow> bool"


datatype ('atom, 'prog, 'state) pdl_state =
  PdlState  (state_id  : "(pdl_atom_var \<Rightarrow> 'state)")
            (atom_eval : "'atom \<Rightarrow> ('state \<Rightarrow> bool)")
            (prog_eval : "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool")



fun pdl_var_eval :: "('atom, 'prog, 'state) pdl_state \<Rightarrow> ('atom,'prog) pdl_var \<Rightarrow> ('state) pdl_universe"
  where
    "pdl_var_eval \<omega> StateVar = PdlStateId ((state_id \<omega>) singleton_var)"
  | "pdl_var_eval \<omega> (AtomVar a) = PdlStateAtomVal ((atom_eval \<omega>) a)"
  | "pdl_var_eval \<omega> (ProgVar p) = PdlStateProgVal ((prog_eval \<omega>) p)"

fun pdl_atom_eval :: "'atom \<Rightarrow> ('atom, 'prog, 'state) pdl_state \<Rightarrow> bool"
  where "pdl_atom_eval a \<omega> = ((atom_eval \<omega>) a)  ((state_id \<omega>) singleton_var)"

fun pdl_prog_eval :: "'prog \<Rightarrow> ('atom, 'prog, 'state) pdl_state \<Rightarrow> ('atom, 'prog, 'state) pdl_state \<Rightarrow> bool"
  where
    "pdl_prog_eval prog \<mu> \<omega> = (
      (fol_equal_everywhere_but_gen pdl_var_eval StateVar \<mu> \<omega>)
      \<and>
      (prog_eval \<omega>) prog ((state_id \<mu>) singleton_var) ((state_id \<omega>) singleton_var)
    )"

fun pdl_fv_syn :: "'atom \<Rightarrow> ('atom,'prog) pdl_var \<Rightarrow> bool"
  where
    "pdl_fv_syn a StateVar = True"
  | "pdl_fv_syn a (AtomVar b) = (a=b)"
  | "pdl_fv_syn a x = False"


interpretation pdlFOL : folCore
  pdl_atom_eval pdl_fv_syn pdl_var_eval
proof
  fix a :: 'atom
  show "finite (Collect (pdl_fv_syn a))"
  proof -
    have subset: "(Collect (pdl_fv_syn a)) \<subseteq> { StateVar, (AtomVar a) }"
      apply auto
      subgoal for x
      proof (cases x)
        case StateVar
        assume "x \<noteq> StateVar"
        then show ?thesis
          using StateVar by blast
      next
        case (AtomVar x2)
        assume "pdl_fv_syn a x"
        then show ?thesis
          by (simp add: AtomVar)
      next
        case (ProgVar x3)
        assume "pdl_fv_syn a x"
        then show ?thesis
          by (simp add: ProgVar)
      qed.
    have sup_fin: "finite { StateVar }"
      by simp
    thus "finite (Collect (pdl_fv_syn a))"
      using subset
      using finite_subset by blast
  qed

      
  
    show "\<And>a \<mu> \<omega>. fol_states_agree_on_gen pdl_var_eval (pdl_fv_syn a) \<mu> \<omega> \<Longrightarrow> pdl_atom_eval a \<mu> = pdl_atom_eval a \<omega>"
      unfolding fol_states_agree_on_gen_def
      unfolding pdl_atom_eval.simps
      using pdl_fv_syn.simps
      by (metis pdl_universe.inject(1,2) pdl_var_eval.simps(1,2))

    show "\<forall> (\<omega> :: ('atom, 'prog, 'state) pdl_state) \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<omega> v)"
    proof (intro allI)
      fix \<omega> :: "('atom, 'prog, 'state) pdl_state"
      fix \<mu> :: "('atom, 'prog, 'state) pdl_state"
      fix V :: "('atom,'prog) pdl_var set"

      obtain \<nu>_state where \<nu>_state_cond: "\<nu>_state = (if (StateVar \<in> V)
                                        then (state_id \<mu>)
                                        else (state_id \<omega>))"
        by simp
      obtain \<nu>_atom where \<nu>_atom_cond: "\<And> a. \<nu>_atom a = (if ((AtomVar a) \<in> V)
                                        then (atom_eval \<mu> a)
                                        else (atom_eval \<omega> a))"
        by simp
      obtain \<nu>_prog where \<nu>_prog_cond: "\<And> p. \<nu>_prog p = (if ((ProgVar p) \<in> V)
                                        then (prog_eval \<mu> p)
                                        else (prog_eval \<omega> p))"
        by simp

      show "\<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<mu> v) \<and>
               (v \<notin> V \<longrightarrow> pdl_var_eval \<nu> v = pdl_var_eval \<omega> v)"
        apply (rule exI[where x = "(PdlState \<nu>_state \<nu>_atom \<nu>_prog)"],intro allI)
        subgoal for v
        proof (cases v)
          case StateVar
          then show ?thesis
            unfolding StateVar
            unfolding pdl_var_eval.simps
            by (simp add: \<nu>_state_cond)
        next
          case (AtomVar x2)
          then show ?thesis
            unfolding AtomVar
            unfolding pdl_var_eval.simps
            by (simp add: \<nu>_atom_cond)
        next
          case (ProgVar x3)
          then show ?thesis
            unfolding ProgVar
            unfolding pdl_var_eval.simps
            by (simp add: \<nu>_prog_cond)
        qed.
    qed
  qed


fun pdl_prog_fv_syn :: "'prog \<Rightarrow> ('atom,'prog) pdl_var \<Rightarrow> bool"
  where
    "pdl_prog_fv_syn a StateVar = True"
  | "pdl_prog_fv_syn a (ProgVar b) = (a=b)"
  | "pdl_prog_fv_syn a x = False"



interpretation pdlDLFull : dynamic_theory
    "pdl_atom_eval" "pdl_fv_syn" "pdl_var_eval"
    "pdl_prog_eval" "pdl_prog_fv_syn"
proof
  show "\<And>\<pi>. finite (Collect (pdl_prog_fv_syn \<pi>))"
    proof -
    fix \<pi> :: 'prog
    have subset: "(Collect (pdl_prog_fv_syn \<pi>)) \<subseteq> { StateVar, (ProgVar \<pi>) }"
      apply auto
      subgoal for x
      proof (cases x)
        case StateVar
        assume "x \<noteq> StateVar"
        then show ?thesis
          using StateVar by blast
      next
        case (AtomVar x2)
        assume "pdl_prog_fv_syn \<pi> x"
        then show ?thesis
          by (simp add: AtomVar)
      next
        case (ProgVar x3)
        assume "pdl_prog_fv_syn \<pi> x"
        then show ?thesis
          by (simp add: ProgVar)
      qed.
    have sup_fin: "finite { (Inl singleton_var), (Inr \<pi>) }"
      by simp
    thus "finite (Collect (pdl_prog_fv_syn \<pi>))"
      using subset
      using finite_subset by blast
  qed

  show "\<And>(\<pi> :: 'prog) (V :: ('atom,'prog) pdl_var \<Rightarrow> bool) \<mu> \<omega> \<nu>.
       (\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
       pdlFOL.fol_states_agree_on V \<mu> \<omega> \<and> pdl_prog_eval \<pi> \<mu> \<nu> \<longrightarrow>
       (\<exists>\<upsilon>. pdl_prog_eval \<pi> \<omega> \<upsilon> \<and> pdlFOL.fol_states_agree_on V \<nu> \<upsilon>)"
  proof
    fix \<pi> :: 'prog
    fix V :: "('atom,'prog) pdl_var \<Rightarrow> bool"
    fix \<mu> \<omega> \<nu> :: "('atom, 'prog, 'state) pdl_state"
    assume asm: "(\<forall>v. pdl_prog_fv_syn \<pi> v \<longrightarrow> V v) \<and>
                 folCore.fol_states_agree_on pdl_var_eval V \<mu> \<omega> \<and> pdl_prog_eval \<pi> \<mu> \<nu>"

    obtain \<upsilon> where \<upsilon>_cond1: "\<And> x . V x \<Longrightarrow> ((pdl_var_eval \<upsilon> x) = (pdl_var_eval \<nu> x))"
               and \<upsilon>_cond2: "\<And> x . \<not>(V x) \<Longrightarrow> ((pdl_var_eval \<upsilon> x) = (pdl_var_eval \<omega> x))"
      using pdlFOL.state_space_convexity
      by (metis mem_Collect_eq)

    have VStateVarCond: "V StateVar" "V (ProgVar \<pi>)"
       apply (simp add: asm)
      by (simp add: asm)
    
    then have fact1: "(state_id \<omega>) = (state_id \<mu>)"
      using asm
      by (metis ext[of "state_id \<mu>" "state_id \<omega>"]
          folCore.fol_states_agree_on_def[of pdl_atom_eval pdl_fv_syn pdl_var_eval V \<mu> \<omega>]
          pdlFOL.folCore_axioms pdl_atom_var.exhaust
          pdl_universe.inject(1)[of "state_id \<mu> singleton_var"
            "state_id \<omega> singleton_var"]
          pdl_var_eval.simps(1)[of \<omega>] pdl_var_eval.simps(1)[of \<mu>])

    have fact2: "pdlFOL.fol_states_agree_on V \<nu> \<upsilon>"
      unfolding pdlFOL.fol_states_agree_on_def
      using \<upsilon>_cond1
      by presburger

    have fact3: "(state_id \<upsilon>) = (state_id \<nu>)"
      using \<upsilon>_cond1[of StateVar] VStateVarCond
      unfolding pdl_var_eval.simps
      by (metis (lifting) ext pdl_atom_var.exhaust pdl_universe.inject(1))

    have fact4: "(prog_eval \<upsilon> \<pi>) = (prog_eval \<nu> \<pi>)"
      using \<upsilon>_cond1[of "(ProgVar \<pi>)"] VStateVarCond
      unfolding prog_eval_def pdl_var_eval.simps
      by simp

    show "\<exists>\<upsilon>. pdl_prog_eval \<pi> \<omega> \<upsilon> \<and> pdlFOL.fol_states_agree_on V \<nu> \<upsilon>"
      unfolding pdl_prog_eval.simps
    proof (intro exI[where x=\<upsilon>], intro conjI)
      show "fol_equal_everywhere_but_gen pdl_var_eval StateVar \<omega> \<upsilon>"
        apply (simp add: dyn_sem, intro allI)
        subgoal for v
        proof (cases "V v")
          case True
          then show ?thesis
            unfolding \<upsilon>_cond1[OF True]
          proof (intro impI)
            assume notstatevar: "v \<noteq> StateVar"
            assume "V v"
            then have "pdl_var_eval \<omega> v = pdl_var_eval \<mu> v"
              using asm
              by (simp add: pdlFOL.fol_states_agree_on_def)
            also have "pdl_var_eval \<mu> v = pdl_var_eval \<nu> v"
              using notstatevar
              using asm
              unfolding pdl_prog_eval.simps
              by (simp add: dyn_sem)
            finally show "pdl_var_eval \<omega> v = pdl_var_eval \<nu> v"
              by blast
          qed
        next
          case False
          then show ?thesis
            using \<upsilon>_cond2
            by presburger
        qed.

      show "prog_eval \<upsilon> \<pi> (state_id \<omega> singleton_var) (state_id \<upsilon> singleton_var)"
        unfolding fact1
        unfolding fact3
        using asm
        unfolding pdl_prog_eval.simps
        unfolding fact4
        by simp
    
      show "pdlFOL.fol_states_agree_on V \<nu> \<upsilon>"
        by (simp add: dyn_sem fact2)
    qed
  qed

  show " \<forall>\<pi> \<mu> \<omega>. (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v) \<longrightarrow> pdl_prog_eval \<pi> \<mu> = pdl_prog_eval \<pi> \<omega>"
  proof (intro allI, intro impI)
    fix \<pi> :: 'prog
    fix \<mu> \<omega> :: "('atom, 'prog, 'state) pdl_state"
    assume all_eq: "\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v"
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

    show "pdl_prog_eval \<pi> \<mu> = pdl_prog_eval \<pi> \<omega>"
      unfolding pdl_prog_eval.simps
      using fact1 fact2
      by metis
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
  show "\<forall>\<pi> \<mu> \<omega> \<mu>' \<omega>'.
       (\<forall>v. pdl_var_eval \<mu> v = pdl_var_eval \<omega> v \<and>
            pdl_var_eval \<mu>' v = pdl_var_eval \<omega>' v) \<longrightarrow>
       pdl_prog_eval \<pi> \<mu> \<mu>' = pdl_prog_eval \<pi> \<omega> \<omega>'"
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
qed

(*declare [[show_types]]
declare [[show_sorts]]
*)


text\<open>Fix EV so that all theorems below evaluate w.r.t. the same PDL state space \<close>
context
  fixes ev :: "('atom,
                ('atom,'prog) pdl_var,
                'prog) dyn_formula
               \<Rightarrow> ('atom,'prog,'state) pdl_state \<Rightarrow> bool"
  fixes EV :: "('atom,
                ('atom,'prog) pdl_var,
                ('atom,('atom,'prog) pdl_var,'prog) kat_prog) dyn_formula
               \<Rightarrow> ('atom,'prog,'state) pdl_state \<Rightarrow> bool"
  assumes ev_def: "ev = pdlDLFull.dyn_eval"
  assumes EV_def: "EV = regular_pdl.kat_dl.dyn_eval"
begin

lemma test0:
  assumes "\<Turnstile>[EV] (FOL X) \<Rrightarrow> (FOL Y)"
      and "\<Turnstile>[EV] (FOL Y) \<Rrightarrow> (FOL Z)"
    shows "\<Turnstile>[EV] (FOL X) \<Rrightarrow> (FOL Z)"
  using assms
  unfolding EV_def
  using regular_pdl.kat_dl.dt_prop_imp_trans
  by blast
  

lemma test1:
  assumes "\<Turnstile>[EV] ((FOL X) \<Rrightarrow> \<lbrakk> (KATPROG P) \<rbrakk> (FOL Y))"
  assumes "\<Turnstile>[EV] ((FOL Y) \<Rrightarrow> \<lbrakk> (KATPROG Q) \<rbrakk> ((FOL Y) and (FOL Z)))"
  shows "\<Turnstile>[EV]
              ((FOL X) \<Rrightarrow> \<lbrakk> ((KATPROG P);(KATPROG Q)) \<rbrakk> ((FOL Y) and (FOL Z)))"
proof -
  have "\<Turnstile>[EV] FOL X \<Rrightarrow> \<lbrakk> (KATPROG P)\<rbrakk>(\<lbrakk>(KATPROG Q) \<rbrakk> (FOL Y and FOL Z))"
    using assms
    unfolding EV_def
    using regular_pdl.kat_dl.dt_box_MRimp
    by blast

  then show "\<Turnstile>[EV] FOL X \<Rrightarrow> \<lbrakk> (KATPROG P;KATPROG Q) \<rbrakk> (FOL Y and FOL Z)"
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
              ((FOL X) \<Rrightarrow> \<lbrakk> ((KATPROG P);(KATPROG Q)) \<rbrakk> ((FOL Y) and (FOL Z)))"
proof -
  have fact1: "\<Turnstile>[EV] ((FOL X) \<Rrightarrow> \<lbrakk> (KATPROG P) \<rbrakk> (FOL Y))"
    using assms(1)
    using regular_pdl.dyn_axiom_RR[
        where \<phi>="((FOL X) \<Rrightarrow> \<lbrakk> P \<rbrakk> (FOL Y))"]
    unfolding pdlDLFull.IMP_def pdlDLFull.OR_def
    unfolding regular_pdl.translate.simps
    unfolding regular_pdl.kat_dl.IMP_def regular_pdl.kat_dl.OR_def
    unfolding EV_def ev_def
    by blast
  
  have fact2: "\<Turnstile>[EV] ((FOL Y) \<Rrightarrow> \<lbrakk> (KATPROG Q) \<rbrakk> ((FOL Y) and (FOL Z)))"
    using assms(2)
    using regular_pdl.dyn_axiom_RR[
        where \<phi>="((FOL Y) \<Rrightarrow> \<lbrakk> Q \<rbrakk> ((FOL Y) and (FOL Z)))"]
    unfolding pdlDLFull.IMP_def pdlDLFull.OR_def
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
