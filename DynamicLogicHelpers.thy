theory DynamicLogicHelpers
  imports
    Main
    "DynamicLogic"
begin


text\<open>
Results that are sometimes useful for (first-order) reasoning.
\<close>

context dynamic_theory
begin


lemma ex_vec_witnessI:
  assumes agree: "fol_states_agree_on (\<lambda>v. v \<notin> set vs) \<mu> \<omega>"
      and holds: "dyn_eval \<phi> \<omega>"
    shows "dyn_eval (\<bbbE>\<bbbE> vs . \<phi>) \<mu>"
  using assms
proof (induct vs arbitrary: \<mu>)
  case Nil
  then have "\<And>v. state_eval \<mu> v = state_eval \<omega> v"
    by (simp add: fol_states_agree_on_def)
  then have "dyn_eval \<phi> \<mu>"
    using Nil.prems(2) dyn_differing_state_eval_due_to_vars by blast
  then show ?case
    unfolding EX_VEC_def FOR_ALL_VEC.simps(1) by simp
next
  case (Cons x xs)
  obtain \<nu> where n1: "\<And>u. u \<in> {x} \<Longrightarrow> state_eval \<nu> u = state_eval \<omega> u"
             and n2: "\<And>u. u \<notin> {x} \<Longrightarrow> state_eval \<nu> u = state_eval \<mu> u"
    using state_mixI
    by blast
  have eq_but: "fol_equal_everywhere_but x \<mu> \<nu>"
    using n2 by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def)
  have agree': "fol_states_agree_on (\<lambda>u. u \<notin> set xs) \<nu> \<omega>"
    using Cons.prems(1) n1 n2
    using fol_states_agree_on_def
    by fastforce
  have "dyn_eval (\<bbbE>\<bbbE> xs . \<phi>) \<nu>"
    by (rule Cons.hyps[OF agree' Cons.prems(2)])
  then show ?case
    unfolding ex_vec_single
    using eq_but by blast
qed

end

context dynamic_theory_eq
begin

text\<open>The copy state: \<open>wsplus\<close> carries \<open>ws\<close>'s values, everything else is untouched.\<close>
lemma eqPredV_copy:
  assumes "twin_vec ws wsplus"
      and "distinct wsplus"
      and "disjnt (set ws) (set wsplus)"
  shows "\<exists>\<omega>. fol_states_agree_on (\<lambda>v. v \<notin> set wsplus) \<mu> \<omega>
             \<and> dyn_eval (FOL (eqPredV ws wsplus)) \<omega>"
  using assms
proof (induct ws arbitrary: wsplus \<mu>)
  case Nil
  then have "wsplus = []" by simp
  then show ?case
    by (auto simp add: fol_states_agree_on_def dyn_sem)
next
  case (Cons v vs)
  obtain v' vs' where wp: "wsplus = v' # vs'"
                  and twin_head: "twin_var v v'"
                  and twin_tail: "twin_vec vs vs'"
    using Cons.prems(1) by (cases wsplus) (auto simp add: list_all2_Cons1)

  have v'_fresh: "v' \<notin> set vs'" and dist': "distinct vs'"
    using Cons.prems(2) wp by auto
  have vv': "v \<noteq> v'" and v_out: "v \<notin> set vs'" and disj': "disjnt (set vs) (set vs')"
    using Cons.prems(3) wp by (auto simp add: disjnt_def)

  obtain \<nu> where \<nu>1: "fol_equal_everywhere_but v' \<mu> \<nu>"
             and \<nu>2: "state_eval \<nu> v' = state_eval \<mu> v"
    by (rule twin_update[OF twin_head])

  obtain \<omega> where \<omega>1: "fol_states_agree_on (\<lambda>u. u \<notin> set vs') \<nu> \<omega>"
             and \<omega>2: "dyn_eval (FOL (eqPredV vs vs')) \<omega>"
    using Cons.hyps[OF twin_tail dist' disj'] by blast

  have agree: "fol_states_agree_on (\<lambda>u. u \<notin> set (v' # vs')) \<mu> \<omega>"
    using \<omega>1 \<nu>1
    by (auto simp add: fol_states_agree_on_def fol_equal_everywhere_but_def)

  have head: "dyn_eval (FOL (eqPred v v')) \<omega>"
  proof -
    have "state_eval \<omega> v' = state_eval \<mu> v"
      using \<omega>1 v'_fresh \<nu>2 by (simp add: fol_states_agree_on_def)
    moreover have "state_eval \<omega> v = state_eval \<mu> v"
      using \<omega>1 v_out \<nu>1 vv'
      by (simp add: fol_states_agree_on_def fol_equal_everywhere_but_def)
    ultimately show ?thesis
      using eqPred_sound vv' by metis
  qed

  show ?case
    unfolding wp
    using agree head \<omega>2
    by (auto simp add: eqPredV.simps)
qed

end

end