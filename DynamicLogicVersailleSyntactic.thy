subsection\<open>A Syntactic Corollary of the Versaille Theorem\<close>

text\<open>
\texttt{dt\_versaille} states all its variable side conditions semantically in
terms of \texttt{dyn\_fv\_sem}, \texttt{dyn\_prog\_fv\_sem}, and
\texttt{dyn\_prog\_bv\_sem}.

This theory adds a corollary whose side conditions are stated over the
syntactic functions \<open>kat_dl.dyn_FV\<close>, \<open>full_prog_fv_syn\<close> and
\<open>full_dyn_prog_BV dyn_prog_BV\<close>, which are plain recursive functions
over the formula and program datatypes and therefore reduce by \<open>simp\<close>.

The set \<open>AllV\<close> is likewise replaced by an arbitrary superset \<open>A\<close> so the user may
pick whatever is convenient
(typically: all variables occurring anywhere in the model).
\<close>

theory DynamicLogicVersailleSyntactic
  imports
    Main
    "DynamicLogicVersaille"
    "DynamicLogicBV"
begin

locale dynamic_theory_versaille_bv =
    dynamic_theory_versaille atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV eqPred
  + dynamic_theory_bv       atom_eval atom_fv_syn state_eval prog_eval dyn_prog_FV dyn_prog_BV
    for atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
    and prog_eval :: "'prog \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    and dyn_prog_FV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
    and eqPred :: "'var \<Rightarrow> 'var \<Rightarrow> ('atom, 'var) fol_formula"
    and dyn_prog_BV :: "'prog \<Rightarrow> 'var \<Rightarrow> bool"
begin

subsubsection\<open>Lifting the syntactic sets to the regular closure\<close>

text\<open>\<open>full_dyn_prog_BV\<close> lifts a bound-variable over-approximation of the atomic
programs to the whole regular closure; \<open>BV_overapprox\<close> discharges soundness.\<close>

abbreviation kat_BV :: "('atom,'var,'prog) kat_prog \<Rightarrow> 'var \<Rightarrow> bool"
  where "kat_BV \<equiv> full_dyn_prog_BV dyn_prog_BV"

lemma kat_BV_overapprox:
  "kat_dl.dyn_prog_bv_sem \<pi> v \<Longrightarrow> kat_BV \<pi> v"
  by (rule BV_overapprox[OF dyn_prog_BV_overapprox])

lemma kat_BV_subset:
  "Collect (kat_dl.dyn_prog_bv_sem \<pi>) \<subseteq> Collect (kat_BV \<pi>)"
  using kat_BV_overapprox by blast

text\<open>The two soundness lemmas for free variables.\<close>

lemma kat_FV_fml_subset:
  "Collect (kat_dl.dyn_fv_sem \<phi>) \<subseteq> Collect (kat_dl.dyn_FV \<phi>)"
  using kat_dl.dyn_FV_fml_sound by blast

lemma kat_FV_prog_subset:
  "Collect (kat_dl.dyn_prog_fv_sem \<pi>) \<subseteq> Collect (full_prog_fv_syn \<pi>)"
  using kat_dl.dyn_FV_prog_sound by blast

lemma fresh_twins_mono:
  assumes "fresh_twins ws A us"
      and "B \<subseteq> A"
    shows "fresh_twins ws B us"
  using assms
  unfolding fresh_twins_def
  by (meson disjnt_subset1)

subsubsection\<open>The corollary\<close>

corollary dt_versaille_syn:
  fixes ctl :: "('atom,'var,'prog) kat_prog"
    and env :: "('atom,'var,'prog) kat_prog"
    and impl :: "('atom,'var,'prog) kat_prog"
    and pre :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and post :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and J :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and monitor :: "('atom, 'var, ('atom, 'var, 'prog) kat_prog) dyn_formula"
    and Read :: "'var set"
    and A :: "'var set"
    and ws :: "'var list"
    and wsplus :: "'var list"
  defines "monitorminus \<equiv> (\<bbbA>\<bbbA> wsplus . ((FOL (eqPredV ws wsplus)) \<Rrightarrow> monitor))"
  (* A is any superset of the variables the model talks about *)
  assumes A_covers:
        "(Collect (kat_dl.dyn_FV J)) \<union>
         (Collect (kat_dl.dyn_FV pre)) \<union>
         (Collect (kat_dl.dyn_FV post)) \<union>
         (Collect (full_prog_fv_syn ctl)) \<union>
         (Collect (full_prog_fv_syn env)) \<union> (set ws) \<union> Read \<subseteq> A"
  (* ws over-approximates the variables written by ctl *)
      and ws_bound: "Collect (kat_BV ctl) \<subseteq> set ws"
  (* no writing of read model variables *)
      and Read_ws_disjnt: "disjnt Read (set ws)"
      and ws_dist: "distinct ws"
  (* Read and wsplus are the only variables in the monitor *)
      and fv_monitor: "Collect (kat_dl.dyn_FV monitor) \<subseteq> Read \<union> set wsplus"
  (* wsplus is a fresh, distinct vector of twins of ws *)
      and ws_fresh_twins: "fresh_twins ws A wsplus"
  (* impl writes only ws, plus variables nothing else mentions *)
      and impl_bound: "Collect (kat_BV impl) \<inter> A \<subseteq> set ws"
  (* J is a loop invariant *)
      and inv_init: "\<Turnstile>[kat_dl.dyn_eval] pre \<Rrightarrow> J"
      and inv_pres: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk>ctl\<rbrakk>\<lbrakk>env\<rbrakk> J"
      and inv_post: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> post"
  (* NN verification worked *)
      and nnv: "\<Turnstile>[kat_dl.dyn_eval] J \<Rrightarrow> \<lbrakk>impl\<rbrakk> monitorminus"
  (* Modelplex worked *)
      and modelplex: "\<Turnstile>[kat_dl.dyn_eval] monitor \<Rrightarrow> \<langle>ctl\<rangle> (FOL (eqPredV ws wsplus))"
  shows "\<Turnstile>[kat_dl.dyn_eval] pre \<Rrightarrow> \<lbrakk> ( ( impl ; env) * ) \<rbrakk> post"
proof -
  text\<open>The semantic \<open>AllV\<close> of \<open>dt_versaille\<close>.  Kept as a \<open>let\<close> rather than a
       \<open>define\<close> so that the facts below are literally about the expanded term
       and unify with the \<open>defines\<close> premise of \<open>dt_versaille\<close>.\<close>
  let ?AllV = "(Collect (kat_dl.dyn_fv_sem J)) \<union>
               (Collect (kat_dl.dyn_fv_sem pre)) \<union>
               (Collect (kat_dl.dyn_fv_sem post)) \<union>
               (Collect (kat_dl.dyn_prog_fv_sem ctl)) \<union>
               (Collect (kat_dl.dyn_prog_fv_sem env)) \<union> (set ws) \<union> Read"

  have AllV_A: "?AllV \<subseteq> A"
    using A_covers kat_FV_fml_subset kat_FV_prog_subset
    by blast

  have ws_bound': "Collect (kat_dl.dyn_prog_bv_sem ctl) \<subseteq> set ws"
    using kat_BV_subset ws_bound by blast

  have fv_monitor': "Collect (kat_dl.dyn_fv_sem monitor) \<subseteq> Read \<union> set wsplus"
    using kat_FV_fml_subset fv_monitor by blast

  have fresh': "fresh_twins ws ?AllV wsplus"
    by (rule fresh_twins_mono[OF ws_fresh_twins AllV_A])

  have impl_bound': "Collect (kat_dl.dyn_prog_bv_sem impl) \<inter> ?AllV \<subseteq> set ws"
  proof -
    have "Collect (kat_dl.dyn_prog_bv_sem impl) \<inter> ?AllV
            \<subseteq> Collect (kat_BV impl) \<inter> A"
      using kat_BV_subset AllV_A by blast
    then show ?thesis using impl_bound by blast
  qed

  show ?thesis
    using ws_bound' Read_ws_disjnt ws_dist fv_monitor'
           fresh' impl_bound'
           inv_init inv_pres inv_post
           nnv[unfolded monitorminus_def] modelplex
    using dt_versaille
    by force
  qed

end

end
