subsection\<open>A Minimal Running Example of the Versaille Theorem\<close>

text\<open>
This theory applies \<open>dt_versaille_syn\<close> to the ordered-semi-ring dynamic theory
of \<open>SemiRingDL\<close>, instantiated at integer values and string variables.

The example is deliberately tiny.  Its purpose is to show what a user has to
supply, and that the variable side conditions really do reduce by \<open>simp\<close>:

  \<^item> \<open>Env\<close>   -- the environment: the position moves by the current velocity.
  \<^item> \<open>Ctl\<close>   -- the model controller: may accelerate to 1 only while below 5,
                and may always brake to 0.  Non-deterministic.
  \<^item> \<open>Impl\<close>  -- the ``implementation'': a deterministic refinement of \<open>Ctl\<close>
                that accelerates whenever it is allowed to.
  \<^item> \<open>Monitor\<close> -- the ModelPlex controller monitor relating the read variables
                to the post-state copy \<open>VELP\<close> of the written variable \<open>VEL\<close>.
  \<^item> \<open>Inv\<close>   -- the loop invariant, here also used as pre- and postcondition.

Note that all variables of this theory are twins: states are total functions
\<open>'var \<Rightarrow> 'val\<close>, so every variable admits every value.  That is what makes
\<open>fresh_twins\<close> cheap here; in a theory with a restricted state space it would
not be.
\<close>

theory SemiRingVersailleExample
  imports
    Main
    "DynamicLogicProof"
    "SemiRingDL"
    "DynamicLogicVersailleSyntactic"
begin

subsubsection\<open>Two missing rewrite rules for the regular lifting\<close>

text\<open>\<open>KATDynamicLogic\<close> provides \<open>full_prog_rewrite_seq\<close> and
\<open>full_prog_rewrite_choice\<close> but not the two base cases.  They belong next to
those two.\<close>

context regular_lifting
begin

lemma full_prog_rewrite_atom:
  "full_prog_eval (KATPROG \<pi>) \<mu> \<omega> = prog_eval \<pi> \<mu> \<omega>"
  unfolding full_prog_eval_def by simp

lemma full_prog_rewrite_check:
  "full_prog_eval (? \<phi>) \<mu> \<omega> = (fol_eval \<phi> \<mu> \<and> state_eval \<mu> = state_eval \<omega>)"
  unfolding full_prog_eval_def by simp

end

subsubsection\<open>The dynamic theory\<close>

text\<open>Bound variables of the atomic programs: an assignment writes exactly its
left-hand side.\<close>

type_synonym exvar = "char list"
type_synonym exval = "int"
type_synonym exatom = "(exvar, exval) semiringfol_atom"
type_synonym exprog = "(exvar, exval) semiring_prog"
type_synonym exkat  = "(exatom, exvar, exprog) kat_prog"
type_synonym exfml  = "(exatom, exvar, exkat) dyn_formula"

interpretation sr:
  dynamic_theory_versaille_bv
    "semiringfol_AtomEval :: exatom \<Rightarrow> (exvar \<Rightarrow> exval) \<Rightarrow> bool"
    "semiringfol_AtomFVSyn :: exatom \<Rightarrow> exvar \<Rightarrow> bool"
    "state_id :: (exvar \<Rightarrow> exval) \<Rightarrow> exvar \<Rightarrow> exval"
    semiring_prog_eval semiring_prog_fv semiring_eq semiring_prog_bv
proof (unfold_locales)
  show "\<And>\<pi> v. semiring_dl.dyn_prog_bv_sem \<pi> v \<Longrightarrow> semiring_prog_bv \<pi> v"
    by (smt (verit) semiring_dl.dyn_prog_bv_sem.elims(2)
        semiring_folCore.fol_equal_everywhere_but_def
        semiring_folCore.fol_states_agree_on_def semiring_prog_bv.elims(3)
        semiring_prog_eval.simps)
qed

subsubsection\<open>All variables are twins\<close>

lemma sr_var_vals_UNIV: "{\<delta>. \<exists>\<mu>. state_id \<mu> v = \<delta>} = UNIV"
proof (intro set_eqI iffI UNIV_I)
  fix \<delta>
  have "state_id (\<lambda>_. \<delta>) v = \<delta>"
    by (simp add: state_id_def)
  then show "\<delta> \<in> {\<delta>. \<exists>\<mu>. state_id \<mu> v = \<delta>}"
    by blast
qed

declare [[show_types, show_sorts]]

lemma sr_twin_var:
  "semiring_folCore.twin_var TYPE(exval) (v::exvar) (w::exvar)"
  unfolding semiring_folCore.twin_var_def semiring_folCore.var_vals_def
  by force


lemma sr_fresh_twins:
  assumes "distinct us"
      and "length ws = length us"
      and "disjnt A (set us)"
    shows "sr.fresh_twins ws A us"
  unfolding sr.fresh_twins_def
  using assms sr_twin_var
  by (simp add: list_all2_iff)

subsubsection\<open>The model\<close>



abbreviation POS :: exvar where "POS \<equiv> ''x''"
abbreviation VEL :: exvar where "VEL \<equiv> ''v''"
abbreviation VELP :: exvar where "VELP \<equiv> ''vp''"

abbreviation Guard :: "(exatom, exvar) fol_formula"
  where "Guard \<equiv> ATOM (Less (Var POS) (Const 5))"

definition Ctl :: exkat
  where "Ctl = (((? Guard) ; KATPROG (VEL := Const 1)) \<squnion> KATPROG (VEL := Const 0))"

definition Env :: exkat
  where "Env = KATPROG (POS := Add (Var POS) (Var VEL))"

definition Impl :: exkat
  where "Impl = (((? Guard) ; KATPROG (VEL := Const 1))
                 \<squnion> ((? folnot Guard) ; KATPROG (VEL := Const 0)))"

definition Inv :: exfml
  where "Inv = FOL (folnot (ATOM (Less (Const 10) (Var POS))))"

definition Monitor :: exfml
  where "Monitor = FOL ((Guard foland (ATOM (Eq (Var VELP) (Const 1))))
                        folor (ATOM (Eq (Var VELP) (Const 0))))"

abbreviation MonitorMinus :: exfml
  where "MonitorMinus \<equiv> (\<bbbA>\<bbbA> [VELP] . ((FOL (semiring_dl_eq.eqPredV [VEL] [VELP])) \<Rrightarrow> Monitor))"

subsubsection\<open>Effect lemmas for the programs\<close>

text\<open>Everything below unfolds to plain statements about states, which here are
just functions \<open>exvar \<Rightarrow> exval\<close>.\<close>

named_theorems sr_eval
declare sr.full_prog_eval_def[sr_eval]
  sr.full_prog_eval_def[sr_eval]
  sr.full_prog_eval_int.simps[sr_eval]
  semiring_dl.dyn_eval.simps[sr_eval]
  semiring_folCore.fol_eval.simps[sr_eval]
  semiringfol_AtomEval.simps[sr_eval]
  semiringfol_TermEval.simps[sr_eval]
  semiring_prog_eval.simps[sr_eval]
  semiring_folCore.fol_equal_everywhere_but_def[sr_eval]
  semiring_folCore.fol_states_agree_on_def[sr_eval]
  sr.kat_dl.dyn_eval.simps[sr_eval]
        (*sr.full_prog_rewrite_seq [sr_eval]
        sr.full_prog_rewrite_choice [sr_eval]
        sr.full_prog_rewrite_atom [sr_eval]
        sr.full_prog_rewrite_check [sr_eval]
        semiring_prog_eval.simps [sr_eval]
        semiring_folCore.fol_equal_everywhere_but_def [sr_eval]
        semiring_folCore.fol_states_agree_on_def [sr_eval]
        state_id_def [sr_eval] id_def [sr_eval]*)

lemma ctl_effect:
  assumes "sr.full_prog_eval Ctl \<mu> \<omega>"
  shows "(\<omega> VEL = 1 \<and> \<mu> POS < 5 \<and> (\<forall>u. u \<noteq> VEL \<longrightarrow> \<omega> u = \<mu> u))
       \<or> (\<omega> VEL = 0 \<and> (\<forall>u. u \<noteq> VEL \<longrightarrow> \<omega> u = \<mu> u))"
  using assms
  unfolding Ctl_def
  apply (simp only: sr_eval)
  by auto


lemma ctl_accelerate:
  assumes "\<mu> POS < 5"
  shows "sr.full_prog_eval Ctl \<mu> (\<mu>(VEL := 1))"
  using assms
  unfolding Ctl_def
  apply (simp only: sr_eval)
  by auto

lemma ctl_brake:
  "sr.full_prog_eval Ctl \<mu> (\<mu>(VEL := 0))"
  unfolding Ctl_def
  apply (simp only: sr_eval)
  by auto

lemma env_effect:
  assumes "sr.full_prog_eval Env \<mu> \<omega>"
  shows "\<omega> POS = \<mu> POS + \<mu> VEL \<and> (\<forall>u. u \<noteq> POS \<longrightarrow> \<omega> u = \<mu> u)"
  using assms
  unfolding Env_def
  apply (simp only: sr_eval)
  by auto

lemma impl_effect:
  assumes "sr.full_prog_eval Impl \<mu> \<omega>"
  shows "(\<mu> POS < 5 \<and> \<omega> VEL = 1 \<and> (\<forall>u. u \<noteq> VEL \<longrightarrow> \<omega> u = \<mu> u))
       \<or> (\<not> (\<mu> POS < 5) \<and> \<omega> VEL = 0 \<and> (\<forall>u. u \<noteq> VEL \<longrightarrow> \<omega> u = \<mu> u))"
  using assms
  unfolding Impl_def
  apply (simp only: sr_eval)
  by auto

subsubsection\<open>The five logical premises\<close>

lemma ex_inv_init: "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> Inv"
  by sr.kat_dl.dt_prop

lemma ex_inv_post: "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> Inv"
  by sr.kat_dl.dt_prop

text\<open>\<open>Inv\<close> is inductive: braking leaves the position alone, and accelerating is
only possible below 5, so the position never exceeds 5 after a step.\<close>

lemma ex_inv_pres: "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> \<lbrakk>Ctl\<rbrakk>\<lbrakk>Env\<rbrakk> Inv"
  unfolding theory_valid_def
proof (intro allI)
  fix \<mu> :: "exvar \<Rightarrow> exval"
  have "sr.kat_dl.dyn_eval Inv \<mu> \<Longrightarrow> sr.kat_dl.dyn_eval (\<lbrakk>Ctl\<rbrakk>\<lbrakk>Env\<rbrakk> Inv) \<mu>"
  proof -
    assume inv\<mu>: "sr.kat_dl.dyn_eval Inv \<mu>"
    then have pos\<mu>: "\<mu> POS \<le> 10"
      unfolding Inv_def
      by (simp only: sr_eval)
    show "sr.kat_dl.dyn_eval (\<lbrakk>Ctl\<rbrakk>\<lbrakk>Env\<rbrakk> Inv) \<mu>"
    proof (simp only: sr.kat_dl.dyn_eval.simps, intro allI impI)
      fix \<omega> \<sigma>
      assume ctl: "sr.full_prog_eval Ctl \<mu> \<omega>"
      assume env: "sr.full_prog_eval Env \<omega> \<sigma>"
      have "\<sigma> POS \<le> 10"
        using ctl_effect[OF ctl] env_effect[OF env] pos\<mu>
        by auto
      then show "sr.kat_dl.dyn_eval Inv \<sigma>"
        unfolding Inv_def
        by (simp only: sr_eval)
    qed
  qed
  then show "sr.kat_dl.dyn_eval (Inv \<Rrightarrow> \<lbrakk>Ctl\<rbrakk>\<lbrakk>Env\<rbrakk> Inv) \<mu>"
    using sr.kat_dl.IMP_def sr.kat_dl.dt_ev_not sr.kat_dl.dyn_eval.simps(2)
    by auto
qed

text\<open>The ModelPlex obligation: whatever the monitor accepts, the model
controller can actually do.\<close>

lemma ex_modelplex:
  "\<Turnstile>[sr.kat_dl.dyn_eval] Monitor \<Rrightarrow> \<langle>Ctl\<rangle> (FOL (semiring_dl_eq.eqPredV [VEL] [VELP]))"
  unfolding theory_valid_def
proof (intro allI)
  fix \<mu> :: "exvar \<Rightarrow> exval"
  have "sr.kat_dl.dyn_eval Monitor \<mu>
          \<Longrightarrow> sr.kat_dl.dyn_eval (\<langle>Ctl\<rangle> (FOL (semiring_dl_eq.eqPredV [VEL] [VELP]))) \<mu>"
  proof -
    assume mon: "sr.kat_dl.dyn_eval Monitor \<mu>"
    then have cases: "(\<mu> POS < 5 \<and> \<mu> VELP = 1) \<or> \<mu> VELP = 0"
      unfolding Monitor_def
      apply (simp only: sr_eval OR_def)
      by auto
    show "sr.kat_dl.dyn_eval (\<langle>Ctl\<rangle> (FOL (semiring_dl_eq.eqPredV [VEL] [VELP]))) \<mu>"
      using cases
    proof
      assume acc: "\<mu> POS < 5 \<and> \<mu> VELP = 1"
      have "sr.full_prog_eval Ctl \<mu> (\<mu>(VEL := 1))"
        using acc
        by (simp only: ctl_accelerate)
      moreover have "sr.kat_dl.dyn_eval (FOL (semiring_dl_eq.eqPredV [VEL] [VELP])) (\<mu>(VEL := 1))"
        using acc
        apply (simp only: sr_eval semiring_dl_eq.eqPredV.simps semiring_eq.simps)
        apply (simp only: sr_eval FOLTRUE_def OR_def)
        by auto
      ultimately show ?thesis
        by (simp only: sr.dia_is_ex) blast
    next
      assume brk: "\<mu> VELP = 0"
      have "sr.full_prog_eval Ctl \<mu> (\<mu>(VEL := 0))"
        by (rule ctl_brake)
      moreover have "sr.kat_dl.dyn_eval (FOL (semiring_dl_eq.eqPredV [VEL] [VELP])) (\<mu>(VEL := 0))"
        using brk
        apply (simp only: sr_eval semiring_dl_eq.eqPredV.simps semiring_eq.simps)
        apply (simp only: sr_eval FOLTRUE_def OR_def)
        by auto
      ultimately show ?thesis
        by (simp only: sr.dia_is_ex) blast
    qed
  qed
  then show "sr.kat_dl.dyn_eval (Monitor \<Rrightarrow> \<langle>Ctl\<rangle> (FOL (semiring_dl_eq.eqPredV [VEL] [VELP]))) \<mu>"
    apply (simp only: sr_eval sr.kat_dl.IMP_def)
    by auto
qed

text\<open>The ``neural network verification'' obligation: every run of \<open>Impl\<close> ends
in a state the monitor accepts.  \<open>Inv\<close> is not even needed for it here.\<close>

lemma ex_nnv: "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> \<lbrakk>Impl\<rbrakk> MonitorMinus"
  unfolding theory_valid_def
proof (intro allI)
  fix \<mu> :: "exvar \<Rightarrow> exval"
  have "sr.kat_dl.dyn_eval (\<lbrakk>Impl\<rbrakk> MonitorMinus) \<mu>"
  proof (simp only: sr.kat_dl.dyn_eval.simps, intro allI impI)
    fix \<omega>
    assume impl: "sr.full_prog_eval Impl \<mu> \<omega>"
    show "sr.kat_dl.dyn_eval MonitorMinus \<omega>"
      \<comment> \<open>the block quantifies the single variable \<open>VELP\<close>\<close>
    proof (simp only: sr.kat_dl.FOR_ALL_VEC.simps sr.kat_dl.dyn_eval.simps,
           intro allI impI)
      fix \<sigma>
      assume ag: "semiring_folCore.fol_equal_everywhere_but VELP \<omega> \<sigma>"
      then have same: "\<And>u. u \<noteq> VELP \<Longrightarrow> \<sigma> u = \<omega> u"
        apply (simp only: sr_eval)
        by auto
      show "sr.kat_dl.dyn_eval ((FOL (semiring_dl_eq.eqPredV [VEL] [VELP])) \<Rrightarrow> Monitor) \<sigma>"
        unfolding semiring_dl_eq.eqPredV.simps semiring_eq.simps
        unfolding sr.kat_dl.IMP_def FOLTRUE_def
      proof (simp only: sr_eval, standard)
        assume assm1: "(\<sigma> VEL = \<sigma> VELP \<and>
                 semiring_folCore.fol_eval (undefined folor folnot undefined) \<sigma>) \<and>
                \<not> sr.kat_dl.dyn_eval Monitor \<sigma>"
        then have eq: "\<sigma> VEL = \<sigma> VELP"
          by (simp only: sr_eval)
        have "sr.kat_dl.dyn_eval Monitor \<sigma>"
          using impl_effect[OF impl] eq same
          unfolding Monitor_def
          apply (simp only: sr_eval OR_def)
          by force
        then show "False"
          using assm1 by blast
      qed
    qed
  qed
  then show "sr.kat_dl.dyn_eval (Inv \<Rrightarrow> \<lbrakk>Impl\<rbrakk> MonitorMinus) \<mu>"
    apply (simp only: sr.kat_dl.IMP_def)
    using sr.kat_dl.dyn_eval.simps(2,3) by presburger
qed

subsubsection\<open>The variable side conditions\<close>

text\<open>These are the goals the syntactic corollary exists for: they are
computations on the syntax of the model.\<close>

abbreviation ExRead :: "exvar set" where "ExRead \<equiv> {POS}"
abbreviation ExA :: "exvar set" where "ExA \<equiv> {POS, VEL}"

lemma ex_A_covers:
  "(Collect (sr.kat_dl.dyn_FV Inv)) \<union>
   (Collect (sr.kat_dl.dyn_FV Inv)) \<union>
   (Collect (sr.kat_dl.dyn_FV Inv)) \<union>
   (Collect (sr.full_prog_fv_syn Ctl)) \<union>
   (Collect (sr.full_prog_fv_syn Env)) \<union> (set [VEL]) \<union> ExRead \<subseteq> ExA"
  unfolding Inv_def Ctl_def Env_def
  by auto

lemma ex_ws_bound: "Collect (sr.kat_BV Ctl) \<subseteq> set [VEL]"
  unfolding Ctl_def by auto

lemma ex_impl_bound: "Collect (sr.kat_BV Impl) \<inter> ExA \<subseteq> set [VEL]"
  unfolding Impl_def by auto

lemma ex_fv_monitor:
  "Collect (sr.kat_dl.dyn_FV Monitor) \<subseteq> ExRead \<union> set [VELP]"
  unfolding Monitor_def
  apply simp
  unfolding sr.kat_dl.dyn_FV.simps semiring_folCore.fol_fv_syn.simps OR_def
  unfolding semiringfol_AtomFVSyn.simps semiringfol_TermFVSyn.simps
  apply simp
  by fastforce 

lemma ex_read_ws_disjnt: "disjnt ExRead (set [VEL])"
  by (simp add: disjnt_def)

lemma ex_ws_dist: "distinct [VEL]"
  by simp

lemma ex_fresh_twins: "sr.fresh_twins [VEL] ExA [VELP]"
  by (rule sr_fresh_twins) (auto simp add: disjnt_def)

subsubsection\<open>Putting it together\<close>

theorem example_safe:
  "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> \<lbrakk> ((Impl ; Env) *) \<rbrakk> Inv"
  proof (rule sr.dt_versaille_syn[
          where ctl=Ctl,
          where monitor=Monitor,
          where J=Inv,
          where ws="[VEL]",
          where wsplus="[VELP]",
          where A="ExA",
          where Read="ExRead"
    ])
    show "Collect (sr.kat_dl.dyn_FV Inv) \<union> Collect (sr.kat_dl.dyn_FV Inv) \<union>
        Collect (sr.kat_dl.dyn_FV Inv) \<union>
        Collect (sr.full_prog_fv_syn Ctl) \<union>
        Collect (sr.full_prog_fv_syn Env) \<union>
        set [VEL] \<union>
        ExRead
        \<subseteq> ExA"
      using ex_A_covers by blast
    show "Collect (sr.kat_BV Ctl) \<subseteq> set [VEL]"
      using ex_ws_bound by blast
    show "disjnt ExRead (set [VEL])"
      using ex_read_ws_disjnt by blast
    show "distinct [VEL]"
      by simp
    show "Collect (sr.kat_dl.dyn_FV Monitor) \<subseteq> ExRead \<union> set [VELP]"
      using ex_fv_monitor by fastforce
    show "sr.fresh_twins [VEL] ExA [VELP]"
      using ex_fresh_twins by blast
    show "Collect (sr.kat_BV Impl) \<inter> ExA \<subseteq> set [VEL]"
      using ex_impl_bound by blast
    (* The interesting bits *)
    (* Safety of original model *)
    show "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> Inv"
      by sr.kat_dl.dt_prop
    show "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> \<lbrakk> Ctl \<rbrakk> \<lbrakk> Env \<rbrakk> Inv"
      using ex_inv_pres by force
    show "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow> Inv"
      by sr.kat_dl.dt_prop
    (* Verification *)
    show "\<Turnstile>[sr.kat_dl.dyn_eval] Inv \<Rrightarrow>
              \<lbrakk> Impl \<rbrakk> \<bbbA>\<bbbA> [VELP] .
                (FOL (semiring_dl_eq.eqPredV [VEL] [VELP]) \<Rrightarrow> Monitor)"
      using ex_nnv by fastforce
    (* ModelPlex *)
    show " \<Turnstile>[sr.kat_dl.dyn_eval] Monitor \<Rrightarrow>
                           \<langle> Ctl \<rangle> FOL (semiring_dl_eq.eqPredV [VEL] [VELP])"
      using ex_modelplex by blast
  qed

end
