section\<open>Heterogeneous Rewriting\<close>
text\<open>
If one of the two dynamic theories combined in a dynamic theory is 
a \emph{regularly lifted dynamic theory},
we can rewrite single-theory sequential composition, nondeterministic choice and loops
to their \emph{heterogeneous} counterparts.
\<close>

theory HeterogeneousRewriting
  imports
    Main
    "DynamicLogic"
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "HeterogeneousDynamicLogic"
    "DLRewriting"
    "KATRewriting"
begin


locale HeterogeneousRewriting =
regular_lifting atom_eval1 atom_fv_syn1 state_eval1 prog_eval1 dyn_prog_FV1
+
HeterogeneousDynLog
  atom_eval1 atom_fv_syn1 state_eval1
  "(regular_lifting.full_prog_eval atom_eval1 state_eval1 prog_eval1)"
  "(regular_lifting.full_prog_fv_syn atom_fv_syn1 dyn_prog_FV1)"
  atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
  atom_eval_comm atom_fv_syn_comm
for atom_eval1 :: "'atom1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and atom_fv_syn1 :: "'atom1 \<Rightarrow> 'var1 \<Rightarrow> bool"
  and state_eval1 :: "'state1 \<Rightarrow> 'var1 \<Rightarrow> 'val1"
  and prog_eval1 :: "'prog1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and dyn_prog_FV1 :: "'prog1 \<Rightarrow> 'var1 \<Rightarrow> bool"

  and atom_eval2 :: "'atom2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and atom_fv_syn2 :: "'atom2 \<Rightarrow> 'var2 \<Rightarrow> bool"
  and state_eval2 :: "'state2 \<Rightarrow> 'var2 \<Rightarrow> 'val2"
  and prog_eval2 :: "'prog2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and dyn_prog_FV2 :: "'prog2 \<Rightarrow> 'var2 \<Rightarrow> bool"

  and atom_eval_comm :: "'atom_comm \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> bool"
  and atom_fv_syn_comm :: "'atom_comm \<Rightarrow> ('var1 + 'var2) \<Rightarrow> bool"
begin

sublocale hdl:
  HeterogeneousDynLog
  atom_eval1 atom_fv_syn1 state_eval1 
  "(regular_lifting.full_prog_eval atom_eval1 state_eval1 prog_eval1)"
  "(regular_lifting.full_prog_fv_syn atom_fv_syn1 dyn_prog_FV1)"
  atom_eval2 atom_fv_syn2 state_eval2 prog_eval2 dyn_prog_FV2
  atom_eval_comm atom_fv_syn_comm
  using HeterogeneousDynLog_axioms by force

notation hdl_kat.kat_dl.progRefine ("_ \<le> _" [190, 190] 190)

notation hdl_kat.kat_dl.progEquiv ("_ \<rightleftharpoons> _ " [200, 200] 200)

lemma choice_rewrite:
  fixes \<alpha> \<beta> :: "('atom1, 'var1, 'prog1) kat_prog"
  shows "(KATPROG (HPROG (PROG1 (\<alpha>\<squnion>\<beta>)))) \<rightleftharpoons> ((KATPROG (HPROG (PROG1 \<alpha>)))\<squnion>(KATPROG (HPROG (PROG1 \<beta>))))"
    unfolding
      hdl_kat.kat_dl.progEquiv_def
      hdl_kat.kat_dl.progRefine_def
    unfolding
      hdl_kat.full_prog_eval_def
      hdl_kat.full_prog_eval_int.simps
      hdl_havoc.full_prog_eval.simps
    apply (intro conjI, intro allI, intro impI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply hypsubst
      unfolding het_prog_eval.simps
      unfolding full_prog_eval_def
      unfolding full_prog_eval_int.simps
      by blast
    apply (intro allI, intro impI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply hypsubst
      unfolding het_prog_eval.simps
      unfolding full_prog_eval_def
      unfolding full_prog_eval_int.simps
      by blast.

lemma seq_rewrite:
  fixes \<alpha> \<beta> :: "('atom1, 'var1, 'prog1) kat_prog"
  shows "(KATPROG (HPROG (PROG1 (\<alpha> ; \<beta>)))) \<rightleftharpoons> ((KATPROG (HPROG (PROG1 \<alpha>))) ; (KATPROG (HPROG (PROG1 \<beta>))))"
    unfolding
      hdl_kat.kat_dl.progEquiv_def
      hdl_kat.kat_dl.progRefine_def
    unfolding
      hdl_kat.full_prog_eval_def
      hdl_kat.full_prog_eval_int.simps
      hdl_havoc.full_prog_eval.simps
    apply (intro conjI, intro allI, intro impI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply hypsubst
      subgoal for a b aa ba
      proof -
        assume "\<exists>n. het_prog_eval (PROG1 (\<alpha>;\<beta>)) (a, b) (aa, ba)"
        then have "\<exists>n \<nu> \<nu>'. het_prog_eval (PROG1 \<alpha>) (a, b) (\<nu>,\<nu>') \<and>
               het_prog_eval (PROG1 \<beta>) (\<nu>,\<nu>') (aa, ba)"
        unfolding het_prog_eval.simps
        unfolding full_prog_eval_def
        unfolding full_prog_eval_int.simps
        apply simp
        by blast
      thus ?thesis
        by simp
    qed.

  apply (intro allI, intro impI)
  apply (elim exE)
    subgoal for \<sigma> \<mu> _ \<nu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply (cases \<nu>)
      apply hypsubst
      unfolding het_prog_eval.simps
      unfolding full_prog_eval_def
      unfolding full_prog_eval_int.simps
      apply simp
      by (meson full_prog_eval_int_n_monotone nat_le_linear).

lemma check_rewrite:
  fixes P :: "('atom1, 'var1) fol_formula"
  shows "(KATPROG (HPROG (PROG1 (? P)))) \<rightleftharpoons> ( ? (fol_heterify_1 P))"
    unfolding
      hdl_kat.kat_dl.progEquiv_def
      hdl_kat.kat_dl.progRefine_def
    unfolding
      hdl_kat.full_prog_eval_def
      hdl_kat.full_prog_eval_int.simps
    apply (intro conjI, intro allI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply hypsubst
      unfolding
        hdl_havoc.full_prog_eval.simps
        het_prog_eval.simps
      unfolding hdl_havoc.havoc_dl.dyn_eval.simps
      unfolding full_prog_eval_def full_prog_eval_int.simps
      unfolding dyn_eval.simps
      using dyn_het_equiv_0[of "(FOL (fol_heterify_1 P))"]
      unfolding fml_purify_1.simps
      unfolding kat_dl.dyn_eval.simps hdl_kat.kat_dl.dyn_eval.simps
      unfolding purify_heterify_inverse
      by (metis common_atom_eval_def fst_conv hdl_havoc.havoc_dl.dyn_eval.simps(1) het_state_eval_def heterify1_coincidence kat_dl.dyn_eval.simps(1) snd_conv)
    apply (intro allI) 
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>)
      apply (cases \<mu>)
      apply hypsubst
      unfolding
        hdl_havoc.full_prog_eval.simps
        het_prog_eval.simps
      unfolding hdl_havoc.havoc_dl.dyn_eval.simps
      unfolding full_prog_eval_def full_prog_eval_int.simps
      unfolding dyn_eval.simps
      using dyn_het_equiv_0[of "(FOL (fol_heterify_1 P))"]
      unfolding fml_purify_1.simps
      unfolding kat_dl.dyn_eval.simps hdl_kat.kat_dl.dyn_eval.simps
      unfolding purify_heterify_inverse
      by (metis (no_types, lifting) dyn_eval.simps(1) full_prog_eval_def full_prog_eval_int.simps(2) hdl_havoc.havoc_dl.dyn_eval.simps(1) het_dl.prog_var_determinance het_prog_eval.simps(1) heterify1_coincidence kat_dl.dyn_eval.simps(1)).

lemma loop_rewrite:
  fixes \<alpha> :: "('atom1, 'var1, 'prog1) kat_prog"
  shows "(KATPROG (HPROG (PROG1 ( ((\<alpha>)* ))))) \<rightleftharpoons> ((KATPROG (HPROG (PROG1 \<alpha>)))* )"
    unfolding
      hdl_kat.kat_dl.progEquiv_def
      hdl_kat.kat_dl.progRefine_def
    apply (subst (0 4) hdl_kat.full_prog_eval_def)
    unfolding hdl_kat.full_prog_eval_int.simps
    unfolding hdl_havoc.full_prog_eval.simps
    apply (intro conjI)
     apply (intro allI, intro impI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>, cases \<mu>)
      apply hypsubst
      unfolding het_prog_eval.simps
      unfolding kleene_rep_rewrite hdl_kat.kleene_rep_rewrite
      apply (elim exE, elim conjE, elim exE)
      subgoal for a b aa ba _ n
        apply (intro exI[where x=n])
      proof (induct n arbitrary: \<sigma> \<mu> a b aa ba)
        case 0
        then show ?case
          unfolding hdl_kat.REP.simps
          unfolding hdl_kat.full_prog_eval_def
          unfolding hdl_kat.full_prog_eval_int.simps
          unfolding hdl_havoc.havoc_dl.dyn_eval.simps
          unfolding FOLTRUE_def
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps dyn_eval.simps
          by (metis FOLTRUE_def common_atom_eval_def fst_conv het_fol.fol_true_valid het_state_eval_def snd_conv theory_valid_def)
      next
        case (Suc n)
        show ?case
          using Suc.prems
          unfolding hdl_kat.REP.simps
          unfolding hdl_kat.full_prog_eval_def hdl_kat.full_prog_eval_int.simps
          unfolding hdl_havoc.full_prog_eval.simps
          unfolding full_prog_eval_def[of "(\<alpha>;hdl_kat.REP \<alpha> n)"] full_prog_eval_int.simps
          apply (elim exE)
          subgoal for m \<nu>
            using Suc.hyps[of "(aa,ba)" aa ba "(\<nu>,ba)" \<nu> ba]
            unfolding hdl_kat.full_prog_eval_def[of "(hdl_kat.REP (KATPROG (HPROG (PROG1 \<alpha>))) n)"]
          unfolding full_prog_eval_def[of "(hdl_kat.REP \<alpha> n)"]
          apply (simp del: het_state_eval_def)
          using full_prog_eval_def by blast.
      qed.
     apply (intro allI, intro impI)
    subgoal for \<sigma> \<mu>
      apply (cases \<sigma>, cases \<mu>)
      apply hypsubst
      unfolding het_prog_eval.simps
      unfolding kleene_rep_rewrite hdl_kat.kleene_rep_rewrite
      apply (elim exE)
      subgoal for a b aa ba n
        apply (intro exI[where x=n])
        apply (intro conjI)
        apply (intro exI[where x=n])
      proof (induct n arbitrary: \<sigma> \<mu> a b aa ba)
        case 0
        then show ?case
          unfolding hdl_kat.REP.simps
          unfolding hdl_kat.full_prog_eval_def
          unfolding hdl_kat.full_prog_eval_int.simps
          unfolding hdl_havoc.havoc_dl.dyn_eval.simps
          unfolding FOLTRUE_def
          unfolding full_prog_eval_def
          unfolding full_prog_eval_int.simps dyn_eval.simps
          by (metis FOLTRUE_def dyn_eval.simps(1) fol_true_valid full_prog_eval_def full_prog_eval_int.simps(2) het_dl.prog_var_determinance het_prog_eval.simps(1) theory_valid_def)
      next
        case (Suc n)
        show ?case
          using Suc.prems
          unfolding hdl_kat.REP.simps
          unfolding hdl_kat.full_prog_eval_def hdl_kat.full_prog_eval_int.simps
          unfolding hdl_havoc.full_prog_eval.simps
          unfolding full_prog_eval_def[of "(\<alpha>;hdl_kat.REP \<alpha> n)"] full_prog_eval_int.simps
          apply (elim exE)
          subgoal for m \<nu>
            apply (cases \<nu>)
            apply hypsubst
            subgoal for a b
            using Suc.hyps[of "(aa,ba)" aa ba "(a,b)" "a" "b"]
            unfolding hdl_kat.full_prog_eval_def[of "(hdl_kat.REP (KATPROG (HPROG (PROG1 \<alpha>))) n)"]
          unfolding full_prog_eval_def[of "(hdl_kat.REP \<alpha> n)"]
          apply (simp del: het_state_eval_def)
          by (meson full_prog_eval_def full_prog_eval_int_n_monotone nat_le_linear)
        .
      .
  next
    show "\<mu> = (aa, ba) \<Longrightarrow>
    \<sigma> = (a, b) \<Longrightarrow>
    hdl_kat.full_prog_eval (hdl_kat.REP (KATPROG (HPROG (PROG1 \<alpha>))) n) (a, b)
     (aa, ba) \<Longrightarrow>
    state_eval2 b = state_eval2 ba"
    proof (induct n arbitrary: \<mu> aa ba \<sigma> a b)
      case 0
      then show ?case
        unfolding hdl_kat.REP.simps
        unfolding hdl_kat.full_prog_eval_def
        unfolding hdl_kat.full_prog_eval_int.simps
        by (metis (no_types, opaque_lifting) HeterogeneousDynLog.het_prog_eval.simps(1) HeterogeneousDynLog_axioms check_rewrite dynamic_theory.dyn_eval.simps(1) fol_eval.simps(3) hdl_havoc.full_prog_eval.simps(1) hdl_kat.full_prog_eval_def hdl_kat.full_prog_eval_int.simps(1) hdl_kat.full_prog_eval_int.simps(2) hdl_kat.kat_dl.progEquivSimplification heterify1_coincidence kat_dl.dynamic_theory_axioms)
    next
      case (Suc n)
      show ?case
        using Suc.prems
        unfolding hdl_kat.REP.simps
        unfolding
          hdl_kat.full_prog_eval_def
          hdl_kat.full_prog_eval_int.simps
        unfolding hdl_havoc.full_prog_eval.simps
        apply (elim exE)
        subgoal for n \<nu>
          apply (cases \<nu>)
          apply hypsubst
          unfolding het_prog_eval.simps
          subgoal for a b
            using Suc.hyps[of "(a,b)" a b "(aa,ba)" aa ba]
            apply (simp del: het_state_eval_def)
            by (meson Suc.hyps hdl_kat.full_prog_eval_def)
          .
        .
    qed
  qed.
  .
end

locale FullHeterogeneousRewriting =
  HeterogeneousDynamicLogic.HeterogeneousDynLog atom_eval1 atom_fv_syn1 state_eval1
      prog_eval1 dyn_prog_FV1 atom_eval2 atom_fv_syn2 state_eval2
      prog_eval2 dyn_prog_FV2 atom_eval_comm atom_fv_syn_comm

  for atom_eval1 :: "'atom1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and atom_fv_syn1 :: "'atom1 \<Rightarrow> 'var1 \<Rightarrow> bool"
  and state_eval1 :: "'state1 \<Rightarrow> 'var1 \<Rightarrow> 'val1"
  and prog_eval1 :: "'prog1 \<Rightarrow> 'state1 \<Rightarrow> 'state1 \<Rightarrow> bool"
  and dyn_prog_FV1 :: "'prog1 \<Rightarrow> 'var1 \<Rightarrow> bool"

  and atom_eval2 :: "'atom2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and atom_fv_syn2 :: "'atom2 \<Rightarrow> 'var2 \<Rightarrow> bool"
  and state_eval2 :: "'state2 \<Rightarrow> 'var2 \<Rightarrow> 'val2"
  and prog_eval2 :: "'prog2 \<Rightarrow> 'state2 \<Rightarrow> 'state2 \<Rightarrow> bool"
  and dyn_prog_FV2 :: "'prog2 \<Rightarrow> 'var2 \<Rightarrow> bool"

  and atom_eval_comm :: "'atom_comm \<Rightarrow> ('state1 \<times> 'state2) \<Rightarrow> bool"
  and atom_fv_syn_comm :: "'atom_comm \<Rightarrow> ('var1 + 'var2) \<Rightarrow> bool"
+
assumes strong_extensionality1:
    "\<forall> \<pi> \<mu> \<omega> \<mu>' \<omega>' . ((\<forall> v. (((state_eval1 \<mu>) v = (state_eval1 \<omega>) v) \<and> ((state_eval1 \<mu>') v = (state_eval1 \<omega>') v))) \<longrightarrow> prog_eval1 \<pi> \<mu> \<mu>' = prog_eval1 \<pi> \<omega> \<omega>')"
and strong_extensionality2:
    "\<forall> \<pi> \<mu> \<omega> \<mu>' \<omega>' . ((\<forall> v. (((state_eval2 \<mu>) v = (state_eval2 \<omega>) v) \<and> ((state_eval2 \<mu>') v = (state_eval2 \<omega>') v))) \<longrightarrow> prog_eval2 \<pi> \<mu> \<mu>' = prog_eval2 \<pi> \<omega> \<omega>')"
begin

(*
sublocale hdl:
  HeterogeneousDynamicLogic.HeterogeneousDynLog atom_eval1 atom_fv_syn1 state_eval1
      prog_eval1 dyn_prog_FV1 atom_eval2 atom_fv_syn2 state_eval2
      prog_eval2 dyn_prog_FV2 atom_eval_comm atom_fv_syn_comm
  using HeterogeneousDynLog_axioms by blast
*)
sublocale kat_rewriting: KleeneDynLog  "het_atom_eval" "het_atom_fv_syn" "het_state_eval" "hdl_havoc.full_prog_eval" "hdl_havoc.full_prog_FV"
  unfolding KleeneDynLog_def
  apply (intro conjI)
  using hdl_kat.regular_lifting_axioms
   apply simp
  unfolding KleeneDynLog_axioms_def
  apply (intro allI, intro impI)
  subgoal for \<pi> \<mu> \<omega> \<mu>' \<omega>'
  proof (induct \<pi>)
    case (HPROG x)
    then show ?case
    proof (induct x)
      case (PROG1 x)
      then show ?case
        unfolding hdl_havoc.full_prog_eval.simps
        apply (cases \<mu>, cases \<mu>', cases \<omega>, cases \<omega>')
        apply (hypsubst)
        subgoal for a b aa ba ab bb ac bc
      proof -
        assume assm: "\<forall>v. het_state_eval (a, b) v = het_state_eval (ab, bb) v \<and>
        het_state_eval (aa, ba) v = het_state_eval (ac, bc) v"
        have fact1: "\<forall>v. het_state_eval (a, b) (Inl v) = het_state_eval (ab, bb) (Inl v) \<and>
        het_state_eval (aa, ba) (Inl v) = het_state_eval (ac, bc) (Inl v)"
          using assm by blast
        have fact2: "\<forall>v. het_state_eval (a, b) (Inr v) = het_state_eval (ab, bb) (Inr v) \<and>
        het_state_eval (aa, ba) (Inr v) = het_state_eval (ac, bc) (Inr v)"
          using assm by blast
        show ?thesis          
        using strong_extensionality1
        unfolding het_prog_eval.simps
        using fact1 fact2
        apply (simp add: common_atom_eval_def)
        apply (elim allE[where x=x], erule allE[where x=a], erule allE[where x=ab], erule allE[where x=aa], erule allE[where x=ac])
        by presburger
    qed.
    next
      case (PROG2 x)
      then show ?case
        unfolding hdl_havoc.full_prog_eval.simps
        apply (cases \<mu>, cases \<mu>', cases \<omega>, cases \<omega>')
        apply (hypsubst)
        subgoal for a b aa ba ab bb ac bc
      proof -
        assume assm: "\<forall>v. het_state_eval (a, b) v = het_state_eval (ab, bb) v \<and>
        het_state_eval (aa, ba) v = het_state_eval (ac, bc) v"
        have fact1: "\<forall>v. het_state_eval (a, b) (Inl v) = het_state_eval (ab, bb) (Inl v) \<and>
        het_state_eval (aa, ba) (Inl v) = het_state_eval (ac, bc) (Inl v)"
          using assm by blast
        have fact2: "\<forall>v. het_state_eval (a, b) (Inr v) = het_state_eval (ab, bb) (Inr v) \<and>
        het_state_eval (aa, ba) (Inr v) = het_state_eval (ac, bc) (Inr v)"
          using assm by blast
        show ?thesis          
        using strong_extensionality2
        unfolding het_prog_eval.simps
        using fact1 fact2
        apply (simp add: common_atom_eval_def)
        apply (elim allE[where x=x], erule allE[where x=b], erule allE[where x=bb], erule allE[where x=ba], erule allE[where x=bc])
        by presburger
    qed.
qed
  next
    case (HAVOC x)
    then show ?case
      using hdl_havoc.full_prog_eval.simps(2) het_fol.fol_equal_everywhere_but_def het_fol.fol_states_agree_on_def by presburger
  qed.


end

end