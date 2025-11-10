theory DLRewriting
  imports
    Main
    "DynamicLogic"
begin

context dynLog
begin

definition progRefine :: "'prog \<Rightarrow> 'prog \<Rightarrow> bool"
  where "progRefine \<alpha> \<beta> = (\<forall> \<sigma> \<mu> . ((prog_eval \<alpha> \<sigma> \<mu>) \<longrightarrow> (prog_eval \<beta> \<sigma> \<mu>)))"

definition progEquiv :: "'prog \<Rightarrow> 'prog \<Rightarrow> bool"
  where "progEquiv \<alpha> \<beta> = ((progRefine \<alpha> \<beta>) \<and> (progRefine \<beta> \<alpha>))"

lemma progEquivSimplification:
  "progEquiv \<alpha> \<beta> = ((prog_eval \<alpha>) = (prog_eval \<beta>))"
  unfolding progEquiv_def progRefine_def
  by fastforce

notation progRefine ("_ \<le> _" [190, 190] 190)

notation progEquiv ("_ \<rightleftharpoons> _ " [200, 200] 200)

lemma progEquiv_refl:
  "reflp progEquiv"
  unfolding reflp_def
  unfolding progEquiv_def progRefine_def
  by simp

lemma progEquiv_symp:
  "symp progEquiv"
  unfolding symp_def
  unfolding progEquiv_def progRefine_def
  by simp

lemma progEquiv_transp:
  "transp progEquiv"
  unfolding transp_def
  unfolding progEquiv_def progRefine_def
  by blast

theorem progEquiv_equivp:
  "equivp progEquiv"
  using equivpI[of progEquiv]
  using progEquiv_refl progEquiv_symp progEquiv_transp
  by simp

declare progEquiv_equivp[quot_equiv]

lemma progEquiv_transp_expl:
  assumes "\<alpha> \<rightleftharpoons> \<beta>" and "\<beta> \<rightleftharpoons> \<gamma>"
  shows "\<alpha> \<rightleftharpoons> \<gamma>"
  using assms unfolding progEquiv_def progRefine_def by blast

lemma progEquiv_symp_expl:
  assumes "\<alpha> \<rightleftharpoons> \<beta>"
  shows "\<beta> \<rightleftharpoons> \<alpha>"
  using assms unfolding progEquiv_def by blast

declare progEquiv_transp_expl [trans]

declare progEquiv_symp_expl [sym]

lemma prog_eval_cong:
  "\<alpha> \<rightleftharpoons> \<beta> \<Longrightarrow> prog_eval \<alpha> = prog_eval \<beta>"
  using progEquivSimplification by simp

lemma rewriteAxiomReplace:
  fixes \<alpha> \<beta> :: "'prog"
  fixes \<phi> :: "('atom,'var,'prog) dyn_formula"
  shows "\<alpha> \<rightleftharpoons> \<beta> \<Longrightarrow> \<Turnstile>[dyn_eval] (\<lbrakk>\<alpha>\<rbrakk>\<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<beta>\<rbrakk>\<phi>)"
  using prog_eval_cong by auto

end

end