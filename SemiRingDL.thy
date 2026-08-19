subsubsection\<open>Dynamic Theory\<close>
text\<open>
We then define the dynamic theory which manipulates
variables with ordered semi-ring values.
\<close>

theory SemiRingDL
  imports
    Main
    "SemiRingFOL"
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "NatKATDynamicLogic"
    "KATRewriting"
begin

declare [[coercion_enabled]]

type_synonym ('semiring_var, 'semiringfol_val) semiringfol_state = "'semiring_var \<Rightarrow> 'semiringfol_val"

datatype ('semiring_var, 'semiringfol_val :: ordered_semiring) semiring_prog =
  ASSIGN "'semiring_var" "('semiring_var,'semiringfol_val) semiringfol_term"

notation ASSIGN ("_:=_" 20)

fun semiring_prog_eval :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiring_prog \<Rightarrow> ('semiring_var,'semiringfol_val) semiringfol_state \<Rightarrow> ('semiring_var,'semiringfol_val) semiringfol_state \<Rightarrow> bool"
  where "semiring_prog_eval (ASSIGN v t) \<mu> \<omega> =
          (semiring_folCore.fol_equal_everywhere_but v \<mu> \<omega> \<and> (\<omega> v = semiringfol_TermEval t \<mu>))"

fun semiring_prog_fv :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiring_prog \<Rightarrow> 'semiring_var \<Rightarrow> bool"
  where "(semiring_prog_fv (ASSIGN v t) w) = semiringfol_TermFVSyn t w"

fun semiring_prog_bv :: "('semiring_var,'semiringfol_val :: ordered_semiring) semiring_prog \<Rightarrow> 'semiring_var \<Rightarrow> bool"
  where "(semiring_prog_bv (ASSIGN v t) w) = (v=w)"

fun semiringfol_ProgramEval_flex
    :: "('semiring_state \<Rightarrow> 'semiring_var \<Rightarrow> 'semiringfol_val) \<Rightarrow>
        ('semiring_var,'semiringfol_val :: ordered_semiring) semiring_prog \<Rightarrow>
        'semiring_state \<Rightarrow>
        'semiring_state \<Rightarrow>
        bool"
    where "semiringfol_ProgramEval_flex state_eval p \<mu> \<omega> = semiring_prog_eval p (state_eval \<mu>) (state_eval \<omega>)"

lemma semiring_dyn_theory_via:
  fixes state_eval :: "'semiring_state \<Rightarrow> 'semiring_var \<Rightarrow> 'semiringfol_val :: ordered_semiring"
  assumes semiring_state_space_convexity: "\<forall> \<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_eval \<nu> v = state_eval \<mu> v) \<and> (v \<notin> V \<longrightarrow> state_eval \<nu> v = state_eval \<omega> v)"
  shows "dynamic_theory (semiringfol_AtomEval_flex state_eval) semiringfol_AtomFVSyn state_eval (semiringfol_ProgramEval_flex state_eval) semiring_prog_fv"
proof -

  have folCore_fact: "folCore (semiringfol_AtomEval_flex state_eval) semiringfol_AtomFVSyn state_eval"
    using assms semiring_folCore_via[of state_eval]
    by auto

  show ?thesis
    proof
      show "\<And>a. finite (Collect (semiringfol_AtomFVSyn a))"
        using folCore_fact
        using semiring_folCore.fv_finite by blast
  
      show " \<And>a \<mu> \<omega>.
         fol_states_agree_on_gen state_eval (semiringfol_AtomFVSyn a) \<mu> \<omega> \<Longrightarrow>
         semiringfol_AtomEval_flex state_eval a \<mu> =
         semiringfol_AtomEval_flex state_eval a \<omega>"
        using folCore_fact
        by (simp add: folCore_def)
  
      show convexity: "\<forall>\<omega> \<mu> V.
         \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> state_eval \<nu> v = state_eval \<mu> v) \<and>
                 (v \<notin> V \<longrightarrow> state_eval \<nu> v = state_eval \<omega> v)"
        using folCore_fact
        by (simp add: folCore_def)
  
   show "\<And>\<pi>. finite (Collect (semiring_prog_fv \<pi>))"
      by (metis Collect_mono_iff rev_finite_subset semiring_folCore.fv_finite semiring_prog.exhaust semiring_prog_fv.simps semiringfol_AtomFVSyn.simps(2))
  
   show "\<And>\<pi> V \<mu> \<omega> \<nu>.
         (\<forall>v. semiring_prog_fv \<pi> v \<longrightarrow> V v) \<and>
         folCore.fol_states_agree_on state_eval V \<mu> \<omega> \<and>
         semiringfol_ProgramEval_flex state_eval \<pi> \<mu> \<nu> \<longrightarrow>
         (\<exists>\<upsilon>. semiringfol_ProgramEval_flex state_eval \<pi> \<omega> \<upsilon> \<and>
              folCore.fol_states_agree_on state_eval V \<nu> \<upsilon>)"
     proof-
       fix \<pi> V \<mu> \<omega> \<nu>
       show "(\<forall>v. semiring_prog_fv \<pi> v \<longrightarrow> V v) \<and>
           folCore.fol_states_agree_on state_eval V \<mu> \<omega> \<and>
           semiringfol_ProgramEval_flex state_eval \<pi> \<mu> \<nu> \<longrightarrow>
           (\<exists>\<upsilon>. semiringfol_ProgramEval_flex state_eval \<pi> \<omega> \<upsilon> \<and>
                folCore.fol_states_agree_on state_eval V \<nu> \<upsilon>)"
       proof (intro impI,induct \<pi>)
         case (ASSIGN x1a x2a)
         then show ?case
         proof -
           assume "(\<forall>v. semiring_prog_fv (x1a:=x2a) v \<longrightarrow> V v) \<and>
                  folCore.fol_states_agree_on state_eval V \<mu> \<omega> \<and>
                  semiringfol_ProgramEval_flex state_eval (x1a:=x2a) \<mu> \<nu>"
    
           then have term_eq: "semiringfol_TermEval x2a (state_eval \<mu>) = semiringfol_TermEval x2a (state_eval \<omega>)"
             unfolding semiring_prog_fv.simps
             using fv_term_overapprox[of x2a state_eval \<mu> \<omega>]
             by (smt (verit, best) ASSIGN folCore.fol_states_agree_on_def folCore_fact
                 fol_states_agree_on_gen_def id_apply semiring_prog_fv.simps)
    
           obtain \<upsilon> where \<upsilon>_cond: "((state_eval \<upsilon>) x1a) = ((state_eval \<nu>) x1a) \<and>
                  (\<forall> v . v \<noteq> x1a \<longrightarrow> (((state_eval \<upsilon>) v) = (state_eval \<omega>) v))"
             using convexity[rule_format, of "{x1a}" \<nu> \<omega>]
             apply simp
             by auto
    
           show "\<exists>\<upsilon>. (semiringfol_ProgramEval_flex state_eval (x1a:=x2a) \<omega> \<upsilon> \<and>
                    folCore.fol_states_agree_on state_eval V \<nu> \<upsilon>)"
           apply (intro exI[where x="\<upsilon>"])
           using \<upsilon>_cond
           unfolding semiringfol_ProgramEval_flex.simps
           using folCore_fact
           by (smt (verit, ccfv_SIG) ASSIGN folCore.fol_states_agree_on_def id_def
               semiring_folCore.fol_equal_everywhere_but_def
               semiring_folCore.fol_states_agree_on_def semiring_prog_eval.simps
               semiringfol_ProgramEval_flex.elims(2) state_id_def term_eq)
       qed
     qed
    qed
  
  
    show "\<forall>\<pi> \<mu> \<omega>.
         (\<forall>v. state_eval \<mu> v = state_eval \<omega> v) \<longrightarrow>
         semiringfol_ProgramEval_flex state_eval \<pi> \<mu> =
         semiringfol_ProgramEval_flex state_eval \<pi> \<omega>"
      unfolding semiringfol_ProgramEval_flex.simps
      by presburger
  qed
qed

interpretation semiring_dl :
  dynamic_theory semiringfol_AtomEval semiringfol_AtomFVSyn state_id semiring_prog_eval semiring_prog_fv
  using state_id_convex
  using semiring_dyn_theory_via[of state_id]
  unfolding semiringfol_AtomEval_flex.simps
  unfolding semiringfol_ProgramEval_flex.simps
  unfolding state_id_def id_def
  by auto

interpretation semiring_dl_havoc :
  havoc_lifting "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_prog_eval semiring_prog_fv
  by standard

declare [[coercion "HPROG ::
    ('a,'b) semiring_prog \<Rightarrow>
    (('a,'b) semiringfol_atom, char list, ('a,'b) semiring_prog) havoc_prog"]]

text\<open>
With the definitions above we can then lift the dynamic theory to the full
regular closure:
\<close>

interpretation semiring_dl_full :
  regular_lifting "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV
  using regular_lifting_def semiring_dl_havoc.havoc_dl.dynamic_theory_axioms by blast

thm semiring_dl_full.kat_dl.dynamic_theory_axioms

declare [[coercion "KPROG :: 
    (('a,'b) semiringfol_atom, char list,
     ('a,'b) semiring_prog) havoc_prog \<Rightarrow>
    (('a,'b) semiringfol_atom, char list,
    (('a,'b) semiringfol_atom, char list,
     ('a,'b) semiring_prog) havoc_prog) kat_prog"]]

thm semiring_dl_full.dyn_axiom_I

paragraph\<open>Inductive Expressivity for Natural Numbers\<close>
text\<open>
If we restrict valuations to natural numbers, we can prove
that the resulting dynamic theory is inductively expressive.
\<close>

definition Varn :: "'semiring_var \<Rightarrow> ('semiring_var, nat) semiringfol_term"
  where "Varn v = (Var v)"

definition ATOMn :: "('semiring_var, nat) semiringfol_atom \<Rightarrow> (('semiring_var, nat) semiringfol_atom, 'semiring_var) fol_formula"
  where "ATOMn a = (ATOM a)"

fun val2nat :: "nat \<Rightarrow> nat"
  where "val2nat n = id n"

fun plus_one_relation :: "'semiring_var \<Rightarrow> 'semiring_var \<Rightarrow> ((('semiring_var,nat) semiringfol_atom), 'semiring_var) fol_formula"
  where "plus_one_relation v w = (ATOMn (Eq (Varn w) (Add (Varn v) (Const 1))))"

fun eq_relation :: "'semiring_var \<Rightarrow> 'semiring_var \<Rightarrow> ((('semiring_var,nat) semiringfol_atom), 'semiring_var) fol_formula"
  where "eq_relation v w = (ATOMn (Eq (Varn v) (Varn w)))"

fun positive_relation :: "'semiring_var \<Rightarrow> ((('semiring_var,nat) semiringfol_atom), 'semiring_var) fol_formula"
  where "positive_relation v = (ATOMn (Less (Const 0) (Varn v)))"

interpretation semiring_dl_full_nat:
  nat_regular_lifting "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV "val2nat" "(\<lambda> v . True)" "plus_one_relation" "eq_relation" "positive_relation"
proof

    show "\<forall>v. True \<longrightarrow> is_nat_assignable state_id val2nat v"
      unfolding is_nat_assignable_def
      unfolding state_id_def
      unfolding val2nat.simps
      unfolding id_def
      by force

    show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and>
       True \<and>
       True \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (plus_one_relation v1 v2)) \<mu> =
             ((val2nat (state_id \<mu> v2)) = (val2nat (state_id \<mu> v1)) + 1))"
    proof -
      have "\<forall>v1 v2. v1 \<noteq> v2 \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (plus_one_relation v1 v2)) \<mu> =
             (val2nat (state_id \<mu> v2) = (val2nat (state_id \<mu> v1)) + 1))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding plus_one_relation.simps
        unfolding ATOMn_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding Varn_def
        unfolding semiringfol_TermEval.simps
        unfolding val2nat.simps
        unfolding id_def
        unfolding state_id_def
        unfolding id_def
        by force
      thus ?thesis
        by auto
    qed

    show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and>
       True \<and>
       True \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (eq_relation v1 v2)) \<mu> =
             (val2nat (state_id \<mu> v2) = val2nat (state_id \<mu> v1)))"
    proof -
      have "\<forall> v1 v2 .
              v1 \<noteq> v2\<longrightarrow>
               (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (eq_relation v1 v2)) \<mu> =
                     (val2nat (state_id \<mu> v2) = val2nat (state_id \<mu> v1)))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding eq_relation.simps
        unfolding ATOMn_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding Varn_def
        unfolding semiringfol_TermEval.simps
        unfolding val2nat.simps
        unfolding id_def
        unfolding state_id_def
        unfolding id_def
        by force

      thus ?thesis
        by auto
    qed

    show "\<forall>v1. True \<longrightarrow>
         (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (positive_relation v1)) \<mu> =
               (0 < val2nat (state_id \<mu> v1)))"
    proof -
      have "\<forall>v1. (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (positive_relation v1)) \<mu> =
               (0 < val2nat (state_id \<mu> v1)))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding positive_relation.simps
        unfolding ATOMn_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding Varn_def
        unfolding semiringfol_TermEval.simps
        unfolding val2nat.simps
        unfolding id_def
        unfolding state_id_def
        unfolding id_def
        by force

      thus ?thesis
        by auto
    qed
  qed

paragraph\<open>Inductive Expressivity for Integers\<close>
text\<open>
Similarly, we can prove inductive expressivity for integers.
\<close>

definition VarI :: "'semiring_var \<Rightarrow> ('semiring_var, int) semiringfol_term"
  where "VarI v = (Var v)"

definition ATOMI :: "('semiring_var, int) semiringfol_atom \<Rightarrow> (('semiring_var, int) semiringfol_atom, 'semiring_var) fol_formula"
  where "ATOMI a = (ATOM a)"

fun val2natI :: "int \<Rightarrow> nat"
  where "val2natI n = (nat n)"

fun plus_one_relationI :: "'semiring_var \<Rightarrow> 'semiring_var \<Rightarrow> (('semiring_var, int) semiringfol_atom, 'semiring_var) fol_formula"
  where "plus_one_relationI v w =
      (folnot ((folnot ((ATOMI (Less (VarI v) (Const (0::int)))) foland ((ATOMI (Eq (VarI w) (Const 1)))))) foland
      (folnot ((folnot (ATOMI (Less (VarI v) (Const (0::int))))) foland (ATOMI (Eq (VarI w) (Add (VarI v) (Const 1))))))))"

fun eq_relationI :: "'semiring_var \<Rightarrow> 'semiring_var \<Rightarrow> (('semiring_var, int) semiringfol_atom, 'semiring_var) fol_formula"
  where "eq_relationI v w =(folnot
           ((folnot (ATOMI (Eq (VarI v) (VarI w)))) foland
           (folnot ((ATOMI (Less (VarI v) (Const 1))) foland (ATOMI (Less (VarI w) (Const 1))))))
          )"

fun positive_relationI :: "'semiring_var \<Rightarrow> (('semiring_var, int) semiringfol_atom, 'semiring_var) fol_formula"
  where "positive_relationI v = (ATOMI (Less (Const 0) (VarI v)))"

interpretation semiring_dl_full_nat_int:
  nat_regular_lifting "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV "val2natI" "(\<lambda> v . True)" "plus_one_relationI" "eq_relationI" "positive_relationI"
proof

    show "\<forall>v. True \<longrightarrow> is_nat_assignable state_id val2natI v"
      unfolding is_nat_assignable_def
      unfolding state_id_def
      unfolding val2natI.simps
      unfolding id_def
      by (meson nat_int)

    show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and>
       True \<and>
       True \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (plus_one_relationI v1 v2)) \<mu> =
             ((val2natI (state_id \<mu> v2)) = (val2natI (state_id \<mu> v1)) + 1))"
    proof -
      have "\<forall>v1 v2. v1 \<noteq> v2 \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (plus_one_relationI v1 v2)) \<mu> =
             (val2natI (state_id \<mu> v2) = (val2natI (state_id \<mu> v1)) + 1))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding plus_one_relationI.simps
        unfolding ATOMI_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding VarI_def
        unfolding semiringfol_TermEval.simps
        unfolding val2natI.simps
        unfolding id_def
        unfolding state_id_def
        by auto
      thus ?thesis
        by auto
    qed

    show "\<forall>v1 v2.
       v1 \<noteq> v2 \<and>
       True \<and>
       True \<longrightarrow>
       (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (eq_relationI v1 v2)) \<mu> =
             (val2natI (state_id \<mu> v2) = val2natI (state_id \<mu> v1)))"
    proof -
      have "\<forall> v1 v2 .
              v1 \<noteq> v2\<longrightarrow>
               (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (eq_relationI v1 v2)) \<mu> =
                     (val2natI (state_id \<mu> v2) = val2natI (state_id \<mu> v1)))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding eq_relationI.simps
        unfolding ATOMI_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding VarI_def
        unfolding semiringfol_TermEval.simps
        unfolding val2natI.simps
        unfolding id_def
        unfolding state_id_def
        unfolding id_def
        by force

      thus ?thesis
        by auto
    qed

    show "\<forall>v1. True \<longrightarrow>
         (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (positive_relationI v1)) \<mu> =
               (0 < val2natI (state_id \<mu> v1)))"
    proof -
      have "\<forall>v1. (\<forall>\<mu>. semiring_dl_havoc.havoc_dl.dyn_eval (FOL (positive_relationI v1)) \<mu> =
               (0 < val2natI (state_id \<mu> v1)))"
        unfolding semiring_dl_havoc.havoc_dl.dyn_eval.simps
        unfolding positive_relationI.simps
        unfolding ATOMI_def
        unfolding semiring_folCore.fol_eval.simps
        unfolding semiringfol_AtomEval.simps
        unfolding VarI_def
        unfolding semiringfol_TermEval.simps
        unfolding val2natI.simps
        unfolding id_def
        unfolding state_id_def
        unfolding id_def
        by force

      thus ?thesis
        by auto
    qed
  qed

interpretation kleene_dyn_log:
  KleeneDynLog "semiringfol_AtomEval" "semiringfol_AtomFVSyn" state_id semiring_dl_havoc.full_prog_eval semiring_dl_havoc.full_prog_FV
  apply standard
    unfolding state_id_def unfolding id_def
    by presburger

fun semiring_eq :: "'semiring_var \<Rightarrow> 'semiring_var \<Rightarrow> (('semiring_var, 'semiringfol_val :: ordered_semiring) semiringfol_atom,'semiring_var) fol_formula"
  where "semiring_eq v w = (ATOM (Eq (Var v) (Var w)))"

interpretation semiring_dl_eq:
  dynamic_theory_eq semiringfol_AtomEval semiringfol_AtomFVSyn state_id semiring_prog_eval semiring_prog_fv semiring_eq
  apply standard
  unfolding semiring_dl.dyn_eval.simps
  unfolding semiring_eq.simps
  unfolding semiring_folCore.fol_eval.simps
  unfolding semiringfol_AtomEval.simps
  unfolding semiringfol_TermEval.simps
  unfolding state_id_def
  by fastforce


end