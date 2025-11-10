theory FirstOrder
  imports
    Main

begin
section \<open> First-Order Logic \<close>
subsection \<open> General Definitions \<close>
text \<open>
We begin with some general definitions which are not bound to the First-Order Logic locale defined below.
\<close>
subsubsection \<open> Syntax \<close>
text \<open>
First-Order Formulas can consist of atoms of some generic type \texttt{'a} as well as
the logical operators and and or.
Additionally, we allow for all quantification w.r.t. variables of type \texttt{'vr}.
All other operators and connectives (implication, equivalence, or, existential quantification) are syntactic sugar.
\<close>
datatype ('a, 'vr) fol_formula =
  ATOM "'a"
  | AND "('a,'vr) fol_formula" "('a,'vr) fol_formula"
  | NOT "('a,'vr) fol_formula"
  | FOL_ALL "'vr" "('a,'vr) fol_formula"

notation AND (infix "and" 120)
notation AND (infix "foland" 120)
(* OR 110 *)
notation NOT ("\<rceil> _" [130] 130)
notation NOT ("folnot _" [130] 130)
notation FOL_ALL ("folall _ _" 200)

definition IMP :: "('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula"
 (infixr "\<Rrightarrow>" 100)
 where[simp]: "a \<Rrightarrow> b = \<rceil>(a and \<rceil>b)"

definition EQUIV :: "('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula"
 (infixr "\<Lleftarrow>\<Rrightarrow>" 90)
 where[simp]: "a \<Lleftarrow>\<Rrightarrow> b = (a \<Rrightarrow> b) and (b \<Rrightarrow> a)"

definition OR :: "('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula \<Rightarrow> ('a, 'vr) fol_formula"
  (infix "or" 110)
  where[simp]: "a or b = \<rceil>(\<rceil>a and \<rceil>b)"

definition FOLTRUE :: "('a, 'vr) fol_formula"
  where[simp]: "FOLTRUE = (undefined or \<rceil>undefined)"

subsubsection \<open> Semantics \<close>
text\<open>
First order formulas are evaluated w.r.t. states.
We do not fix states to, e.g., mappings from variables to values,
but instead rely on the presence of an additional function which allows us
to evaluate variables w.r.t. a given state.
\<close>

text\<open>
For a formula to be valid it needs to be satisfied in all its states.
To this end, we assume that a given formula $\phi$ can be evaluated w.r.t. a state $\mu$ using a (theory)
evaluation function \texttt{T}.
We then define validity as $\phi$ being satisifed w.r.t. all possible states $\mu$.
This is captured in the definition \texttt{theory\_valid} which is also used down the line for dynamic logic.
\<close>

definition theory_valid :: "('formula \<Rightarrow> 'state \<Rightarrow> bool) \<Rightarrow> 'formula \<Rightarrow> bool" ("\<Turnstile>[_] _" 20)
  where [simp]: "theory_valid T \<phi> = (\<forall> \<mu> . T \<phi> \<mu>)"

paragraph \<open> Helpers \<close>
text\<open>
These definitions help us to reason about states.
First, we define the set of variables that differ between states (possibly filtered by some function).
Secondly, we define predicates for checking whether two states are equal w.r.t. variables satisfying
a given predicate or if states are equal up to one variable.
\<close>

definition fol_states_agree_on_gen :: "(('state \<Rightarrow> 'var \<Rightarrow> 'val) \<Rightarrow> ('var \<Rightarrow> bool) \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool)"
    where [simp]: "fol_states_agree_on_gen eval f \<mu> \<omega> = (\<forall> v . ((f v) \<longrightarrow> ((eval \<mu>) v = (eval \<omega>) v)))"

definition fol_equal_everywhere_but_gen :: "('state \<Rightarrow> 'var \<Rightarrow> 'val) \<Rightarrow> 'var \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    where [simp]: "fol_equal_everywhere_but_gen eval v \<mu> \<omega> = fol_states_agree_on_gen eval (\<lambda> w. w \<noteq> v) \<mu> \<omega>"
subsection \<open> The First-Order Logic Locale \<close>
text \<open>
This locale captures a First-Order logic that is evaluated w.r.t. states.
Atoms are given via the type \texttt{'atom} and evaluated using the provided \texttt{atom\_eval}
function which takes an atom and a state of type \texttt{'state} and returns a truth value.
We also require a function \texttt{state\_eval} which evaluates a variable w.r.t. a given state.
Some First-Order Logic properties (e.g. the coincidence lemma) require us that the truth value of
atoms only depends on a finite set of variables.
For example, we cannot have an atom which is true iff an infinite number of variables has value 1
in a given state.
We capture this notion by requiring a function \texttt{atom\_fv\_syn} which returns an overapproximation
of the set of free variables of a given atom (\texttt{fv\_overapprox}).
For any given atom \texttt{atom\_fv\_syn} must be true only for a finite set of variables (\texttt{fv\_finite}).
\<close>
locale folCore =
  fixes atom_eval :: "'atom \<Rightarrow> 'state \<Rightarrow> bool"
    and atom_fv_syn :: "'atom \<Rightarrow> 'var \<Rightarrow> bool"
    and state_eval :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  assumes fv_finite: "finite (Collect (atom_fv_syn a))"
      and fv_overapprox: "(fol_states_agree_on_gen state_eval (atom_fv_syn (a::'atom)) (\<mu>::'state) (\<omega>::'state)) \<Longrightarrow> (atom_eval a \<mu>) = (atom_eval a \<omega>)"
      and state_space_convexity:
          "\<forall> \<omega> :: 'state . \<forall> \<mu>  :: 'state . \<forall> V :: 'var set . (
            (\<exists> \<nu>  :: 'state . (
              (\<forall> v . 
              (v \<in> V \<longrightarrow> ((state_eval \<nu>) v) = ((state_eval \<mu>) v)) \<and>
              (v \<notin> V \<longrightarrow> ((state_eval \<nu>) v) = ((state_eval \<omega>) v))))))"
begin

  definition fol_state_var_diff_set :: "'state \<Rightarrow> 'state \<Rightarrow> 'var set"
    where "fol_state_var_diff_set \<mu> \<omega> = Collect (\<lambda> v :: 'var . (state_eval \<mu>) v \<noteq> (state_eval \<omega>) v)"
  
  definition fol_state_var_diff_set_filter :: "'state \<Rightarrow> 'state \<Rightarrow> ('var \<Rightarrow> bool) \<Rightarrow> 'var set"
    where "fol_state_var_diff_set_filter \<mu> \<omega> f = Collect (\<lambda> v :: 'var . (((state_eval \<mu>) v \<noteq> (state_eval \<omega>) v) \<and> (f v)))"
  
  definition fol_states_agree_on :: "(('var \<Rightarrow> bool) \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool)"
    where "fol_states_agree_on f \<mu> \<omega> = (\<forall> v . ((f v) \<longrightarrow> ((state_eval \<mu>) v = (state_eval \<omega>) v)))"
  
  definition fol_equal_everywhere_but :: "'var \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    where "fol_equal_everywhere_but v \<mu> \<omega> = fol_states_agree_on (\<lambda> w. w \<noteq> v) \<mu> \<omega>"

  subsubsection \<open> Syntactic Free Variables \<close>
  text \<open>
    We extend the notion of syntactic free variables (given for atoms by \texttt{atom\_fv\_syn})
    to formulas and show that formulas also have a finite set of free variables.
  \<close>
  fun fol_fv_syn :: "('atom,'var) fol_formula \<Rightarrow> 'var \<Rightarrow> bool"
   where
      "fol_fv_syn (ATOM \<phi>) v = atom_fv_syn \<phi> v"
    | "fol_fv_syn (\<phi> and \<psi>) v = (fol_fv_syn \<phi> v \<or> fol_fv_syn \<psi> v)"
    | "fol_fv_syn (\<rceil> \<phi>) v = (fol_fv_syn \<phi> v)"
    | "fol_fv_syn (folall v \<phi>) w = fol_fv_syn \<phi> w"

  lemma fol_fv_syn_finite: "finite (Collect (fol_fv_syn \<phi>))"
    proof (induct \<phi>)
      case (ATOM x)
      then show ?case
        using fv_finite
        by simp
    next
      case (AND \<phi>1 \<phi>2)
      then show ?case
        by simp
    next
      case (NOT \<phi>)
      then show ?case
        by simp
    next
      case (FOL_ALL x1a \<phi>)
      then show ?case
        by simp
    qed

  subsubsection \<open> Semantics \<close>
  text \<open>
    We define the evaluation of first-order formulas w.r.t. states, define validity and prove the validity of our truth representation.
  \<close>

  fun fol_eval :: "('atom,'var) fol_formula \<Rightarrow> 'state \<Rightarrow> bool"
    where
      "fol_eval (ATOM \<phi>) \<mu> = atom_eval \<phi> \<mu>"
    | "fol_eval (\<phi> and \<psi>) \<mu> = ((fol_eval \<phi> \<mu>) \<and> (fol_eval \<psi> \<mu>))"
    | "fol_eval (\<rceil> \<phi>) \<mu> = (\<not> (fol_eval \<phi> \<mu>))"
    | "fol_eval (folall v \<phi>) \<mu> = (\<forall> \<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<longrightarrow> (fol_eval \<phi> \<omega>))"

  definition fol_valid :: "('atom,'var) fol_formula \<Rightarrow> bool"
    where [simp]: "fol_valid \<phi> = (\<Turnstile>[fol_eval] \<phi>)"

  (* Let's quickly show that our definition of true is correct *)
  lemma fol_true_valid :"\<Turnstile>[fol_eval] FOLTRUE" 
    by simp

  subsection \<open>  Free Variables (Semantic Definitions) \<close>

  text \<open>
    We now turn to the question which variables influence the evaluation of a formula.
    To this end, we formalize a \emph{semantic} definition of free variables.
    While the syntactic formalization is an overapproximation (e.g. it may contain $x$ for $x=x$)
    the semantic definition is precise (e.g. it does not contain $x$ for the tautology $x=x$).
  \<close>

  text \<open>
    This definition only works for predicates which are dependent on finitely many variables.
    To this end, consider the following counterexample:
    "$\phi$ is true iff there is an infinite number of variables which are 1"
    In this case fol\_fv\_sem $\phi$ would be empty, because changing any single variable wouldn't
    change the truth value of the formula.
    Nonetheless, the evaluation of formula does depend on this variable in some sense.
    In particular, using this definition for infinitary predicates would break the coincidence property.
    Moreover, it's unclear what the minimal set would be....
  \<close>
  fun fol_fv_sem :: "('atom,'var) fol_formula \<Rightarrow> 'var \<Rightarrow> bool" where
    "fol_fv_sem \<phi> v = (\<exists> \<mu> \<omega>. (fol_equal_everywhere_but v \<mu> \<omega> \<and> (fol_eval \<phi> \<mu> \<noteq> fol_eval \<phi> \<omega>)))"

  paragraph \<open>Results on Syntactically Free Variables \<close>

  text \<open>
    Using a helper definition on when two states are equal w.r.t. syntactically free variables,
    we prove the coincidence lemma for syntactically free variables.
  \<close>

  definition fol_fv_syn_mirror_state :: "('atom,'var) fol_formula \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool"
    where "fol_fv_syn_mirror_state F \<mu> \<omega> = fol_states_agree_on (fol_fv_syn F) \<mu> \<omega>"

  text\<open>
  We can then prove the syntactic coincidence lemma:
  \<close>

  lemma fol_fv_syn_coincidence:
    "\<forall> \<mu> \<omega> . fol_fv_syn_mirror_state F \<mu> \<omega> \<longrightarrow> fol_eval F \<mu> = fol_eval F \<omega>"
  proof (induction F)
    case (ATOM x)
    then show ?case 
      using fv_overapprox
      unfolding fol_fv_syn_mirror_state_def
      unfolding fol_states_agree_on_def
      by simp
  next
    case (AND F1 F2)
    then show ?case
      unfolding fol_fv_syn_mirror_state_def
      unfolding fol_states_agree_on_def
    by (metis (no_types, lifting) fol_eval.simps(2) fol_fv_syn.simps(2))
  next
    case (NOT F)
    then show ?case
      unfolding fol_fv_syn_mirror_state_def
      unfolding fol_states_agree_on_def
    by simp
  next
    case (FOL_ALL x F)
    then show ?case
    proof -
  
      show ?thesis
      proof (rule allI, rule allI, rule impI)
        fix \<mu>
        fix \<omega>
        assume omega_is_mirror: "fol_fv_syn_mirror_state (folall x F) \<mu> \<omega>"
        thus "fol_eval (folall x F) \<mu> = fol_eval (folall x F) \<omega>"
        proof -
          let ?VDiff = "fol_state_var_diff_set \<mu> \<omega>"
          let ?VDiffRelevant = "fol_state_var_diff_set_filter \<mu> \<omega> (fol_fv_syn F)"

          obtain S :: "'var set \<Rightarrow> 'state"
            where S_cond: "\<forall> V. \<forall> w . (((state_eval (S V)) w) = (if w \<in> V then ((state_eval \<omega>) w) else ((state_eval \<mu>) w)))"
            using state_space_convexity
            by metis

          have "(state_eval \<mu>) = (state_eval (S {}))"
            using S_cond
            by fastforce
    
          then have eq1: "fol_eval (folall x F) \<mu> = fol_eval (folall x F) (S {})"
            unfolding fol_eval.simps fol_equal_everywhere_but_def
            unfolding fol_states_agree_on_def
            by force

    
          have eq2: "fol_eval (folall x F) \<omega> = fol_eval (folall x F) (S ?VDiff)"
            proof -
              have "(state_eval \<omega>) = (state_eval (S ?VDiff))"
                apply (simp add: fol_state_var_diff_set_def)
                using S_cond
                by auto
              then show "fol_eval (folall x F) \<omega> = fol_eval (folall x F) (S ?VDiff)"
                unfolding fol_state_var_diff_set_def
                unfolding fol_eval.simps
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                by simp
            qed
    
            have VDiff_VDiffRelevant_mirrors: "fol_fv_syn_mirror_state F (S ?VDiff) (S ?VDiffRelevant)"
              using S_cond
              by (smt (verit, best) fol_fv_syn.simps(4) fol_fv_syn_mirror_state_def omega_is_mirror fol_states_agree_on_def)
    
    
          have diff_eval_equal: "fol_eval F (S ?VDiff) = fol_eval F (S ?VDiffRelevant)"
            using VDiff_VDiffRelevant_mirrors
            using FOL_ALL by blast
    
          
          have dir1: "( fol_eval (folall x F) (S ?VDiff)) ==> (fol_eval (folall x F) (S ?VDiffRelevant))"
          proof -
            assume vdiff_state_satisfies_formula: "( fol_eval (folall x  F) (S ?VDiff))"
            show "(fol_eval (folall x  F) (S ?VDiffRelevant))"
            proof (simp, rule ccontr, simp)
              assume "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set_filter \<mu> \<omega> (fol_fv_syn F))) \<omega>' \<and>
                        \<not> fol_eval F \<omega>'"
              then have cex_state: "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set_filter \<mu> \<omega> (fol_fv_syn F))) \<omega>' \<and>
                \<not> fol_eval F \<omega>'"
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                by simp
              obtain \<sigma> where sigma_constraints: "fol_equal_everywhere_but x (S ?VDiffRelevant) \<sigma> \<and>  \<not> fol_eval F \<sigma>"
                using cex_state by blast

              obtain \<gamma> where \<gamma>_cond1: "(state_eval \<gamma>) x = (state_eval \<sigma>) x"
                         and \<gamma>_cond2: "\<forall> v . v \<noteq> x \<longrightarrow> (state_eval \<gamma>) v = (state_eval (S ?VDiff)) v"
                using state_space_convexity
                by (meson emptyE insert_iff)
      
              have sigma_gamma_mirror: "fol_fv_syn_mirror_state F \<sigma> \<gamma>"
                using \<gamma>_cond1 \<gamma>_cond2
                using VDiff_VDiffRelevant_mirrors
                using sigma_constraints
                apply (simp add: fol_state_var_diff_set_def fol_state_var_diff_set_filter_def)
                by (smt (verit) VDiff_VDiffRelevant_mirrors fol_equal_everywhere_but_def fol_fv_syn_mirror_state_def sigma_constraints fol_states_agree_on_def)
      
              have gamma_sat: "fol_eval F \<gamma>"
              proof -
                have "fol_equal_everywhere_but x (S ?VDiff) \<gamma>"
                  using \<gamma>_cond1 \<gamma>_cond2
                  using vdiff_state_satisfies_formula fol_equal_everywhere_but_def fol_states_agree_on_def
                  by fastforce          
      
                thus ?thesis
                  using vdiff_state_satisfies_formula
                  using fol_eval.simps(4) by blast
              qed
      
              have sigma_unsat: "\<not> (fol_eval F \<sigma>)"
                using sigma_constraints by auto
      
              have gamma_unsat: "\<not> (fol_eval F \<gamma>)"
                using sigma_gamma_mirror
                using sigma_unsat
                using FOL_ALL by blast
    
              show False
                using gamma_sat gamma_unsat
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                by auto
          qed
        qed
    
        have dir2: "(fol_eval (folall x  F) (S ?VDiffRelevant)) \<Longrightarrow> ( fol_eval (folall x F) (S ?VDiff))"
          proof -
            assume vdiff_state_satisfies_formula: "(fol_eval (folall x F) (S ?VDiffRelevant))"
            show "( fol_eval (folall x  F) (S ?VDiff))"
            proof (simp, rule ccontr, simp)
              assume "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set \<mu> \<omega>)) \<omega>' \<and> \<not> fol_eval F \<omega>'"
              then have cex_state: "\<exists>\<omega>'. fol_equal_everywhere_but x (S (fol_state_var_diff_set \<mu> \<omega>)) \<omega>' \<and> \<not> fol_eval F \<omega>'"
                unfolding fol_equal_everywhere_but_def fol_states_agree_on_def
                by simp
              obtain \<sigma> where sigma_constraints: "fol_equal_everywhere_but x (S (fol_state_var_diff_set \<mu> \<omega>)) \<sigma> \<and>  \<not> fol_eval F \<sigma>"
                using cex_state by blast
              
              obtain \<gamma> where \<gamma>_cond1: "(state_eval \<gamma>) x = (state_eval \<sigma>) x"
                         and \<gamma>_cond2: "\<forall> v . v \<noteq> x \<longrightarrow> (state_eval \<gamma>) v = (state_eval (S ?VDiffRelevant)) v"
                using state_space_convexity
                by (meson emptyE insert_iff)
      
              have sigma_gamma_mirror: "fol_fv_syn_mirror_state F \<sigma> \<gamma>"
                using \<gamma>_cond1 \<gamma>_cond2
                using VDiff_VDiffRelevant_mirrors
                using sigma_constraints
                apply (simp add: fol_state_var_diff_set_def fol_state_var_diff_set_filter_def)
                by (smt (verit) VDiff_VDiffRelevant_mirrors fol_equal_everywhere_but_def fol_fv_syn_mirror_state_def sigma_constraints fol_states_agree_on_def)
      
              have gamma_sat: "fol_eval F \<gamma>"
              proof -
                have "fol_equal_everywhere_but x (S ?VDiffRelevant) \<gamma>"
                  using \<gamma>_cond1 \<gamma>_cond2
                  using vdiff_state_satisfies_formula fol_equal_everywhere_but_def fol_states_agree_on_def
                  by fastforce          
      
                thus ?thesis
                  using vdiff_state_satisfies_formula
                  using fol_eval.simps(4) by blast
              qed
      
              have sigma_unsat: "\<not> (fol_eval F \<sigma>)"
                using sigma_constraints by auto
      
              have gamma_unsat: "\<not> (fol_eval F \<gamma>)"
                using sigma_gamma_mirror
                using sigma_unsat
                using FOL_ALL by blast
    
              show False
                using gamma_sat gamma_unsat by auto
          qed
        qed
    
        have eq3: "(fol_eval (folall x F) (S ?VDiffRelevant)) = ( fol_eval (folall x F) (S ?VDiff))"
          using dir1 dir2
          by blast
    
        have relevantEmpty: "?VDiffRelevant = {}"
          using omega_is_mirror
          unfolding fol_state_var_diff_set_filter_def fol_fv_syn_mirror_state_def fol_states_agree_on_def
          by (simp, blast)
    
        have eq4: "fol_eval (folall x F) (S {}) = fol_eval (folall x F) (S ?VDiffRelevant)"
          using relevantEmpty by simp
    
        show ?thesis
          using eq1 eq2 eq3 eq4 by blast
      qed
    qed
  qed
qed

paragraph\<open>Results on Semantically Free Variables\<close>
text \<open>
  With coincidence proven for syntactically free variables, we can now move on to the stronger result:
  Coincidence w.r.t. semantically free variables which are a subset of the syntactically free variables.
  This result requires the former results, which provides us with the knowledge that only a finite number
  of variables are relevant to a given formula.
\<close>

  lemma fol_fv_sem_coincidence:
  assumes fol_states_agree_on_free: "(fol_states_agree_on (fol_fv_sem F) \<mu> \<omega>)"
    shows "(fol_eval F \<mu> = fol_eval F \<omega>)"
  proof -

    let ?synFV = "Collect (fol_fv_syn F)"

    have synFV_finite: "finite ?synFV"
      using fol_fv_syn_finite
      by blast

    obtain \<nu> where \<nu>_cond1: "\<forall> v . ((v \<in> ?synFV) \<longrightarrow> (state_eval \<omega>) v = (state_eval \<nu>) v)"
               and \<nu>_cond2: "\<forall> v . ((v \<notin> ?synFV) \<longrightarrow> (state_eval \<mu>) v = (state_eval \<nu>) v)"
      using state_space_convexity
      by metis

    have eq1: "fol_eval F \<nu> = fol_eval F \<omega>"
    proof -
      have "fol_fv_syn_mirror_state F \<nu> \<omega>"
        using \<nu>_cond1 \<nu>_cond2
        unfolding fol_fv_syn_mirror_state_def
        unfolding fol_states_agree_on_def
        by simp

      thus ?thesis
        using fol_fv_syn_coincidence
        by blast
    qed

    have eq5: "fol_states_agree_on (fol_fv_sem F) \<nu> \<omega>"
      using \<nu>_cond1 \<nu>_cond2
      by (smt (verit, del_insts) fol_states_agree_on_def fol_states_agree_on_free)

    let ?V = "fol_state_var_diff_set \<mu> \<nu>"

    have "?V \<subseteq> ?synFV"
      using \<nu>_cond1 \<nu>_cond2
      apply (simp add: fol_state_var_diff_set_def)
      by force

    then have V_finite: "finite ?V"
      using synFV_finite
      using rev_finite_subset by blast

    obtain S :: "'var set \<Rightarrow> 'state"
            where S_cond: "\<forall> V. \<forall> w . (((state_eval (S V)) w) = (if w \<in> V then ((state_eval \<nu>) w) else ((state_eval \<mu>) w)))"
            using state_space_convexity
            by metis

    have eq3: "(state_eval \<mu>) = (state_eval (S {}))"
      using S_cond
      by auto

    have eq2: "fol_eval F (S ?V) = fol_eval F \<nu>"
      using fol_states_agree_on_def fol_fv_syn_coincidence fol_fv_syn_mirror_state_def fol_state_var_diff_set_def
      using S_cond \<nu>_cond1 \<nu>_cond2
      by auto

    have inductive_argument: "\<And> x Vold . x \<in> ?V \<Longrightarrow>
          fol_eval F (S {}) = fol_eval F (S Vold) \<Longrightarrow>
          fol_eval F (S {}) = fol_eval F (S (insert x Vold))"
    proof -
      fix x
      fix Vold
      show "x \<in> ?V \<Longrightarrow>
          fol_eval F (S {}) = fol_eval F (S Vold) \<Longrightarrow>
          fol_eval F (S {}) = fol_eval F (S (insert x Vold))"
    proof (cases "fol_fv_sem F x")
      assume x_in_diff: "x \<in> ?V"
      case True
      then show ?thesis
      proof -
        (* Variable cannot be part of fol_fv_sem because states must agree on those *)
        have "fol_eval F (S {}) = fol_eval F (S (insert x Vold))"
        proof (rule ccontr)
          have "(state_eval \<mu>) x \<noteq> (state_eval \<nu>) x"
            using x_in_diff
            unfolding fol_state_var_diff_set_def
            by blast

          also have "(state_eval \<mu>) x = (state_eval \<nu>) x"
            using fol_states_agree_on_free
            using \<nu>_cond1 \<nu>_cond2
            by (metis True fol_states_agree_on_def)   
            
          thus False
            using calculation by blast
        qed

        thus ?thesis by simp
      qed
    next
      assume prev_equal: "fol_eval F (S {}) = fol_eval F (S Vold)"
        case False
        then show ?thesis 
        proof -
          assume x_not_free: "\<not> fol_fv_sem F x"
          have "fol_eval F (S Vold) = fol_eval F (S (insert x Vold))"
          proof (rule ccontr)
            assume states_unequal_now: "\<not> ?thesis"
            then have "fol_equal_everywhere_but x (S Vold) (S (insert x Vold))"
              using S_cond
              by (simp add: fol_equal_everywhere_but_def fol_states_agree_on_def)

            then have "fol_fv_sem F x"
              apply simp
              apply (rule_tac x="(S Vold)" in exI)
              apply (rule_tac x="(S (insert x Vold))" in exI)
              using S_cond
              using states_unequal_now by blast

            thus False
              using x_not_free
              by simp
          qed
          thus ?thesis
            using prev_equal
            by blast
        qed
      qed
    qed

    
            

      have "\<And> VarSet . VarSet \<subseteq> ?V \<Longrightarrow> fol_eval F (S {}) = fol_eval F (S VarSet)"
      proof -
        fix VarSet
        show "VarSet \<subseteq> ?V \<Longrightarrow> fol_eval F (S {}) = fol_eval F (S VarSet)"
        proof -
          assume "VarSet \<subseteq> ?V"
          have "finite VarSet"
            using V_finite
            using \<open>VarSet \<subseteq> fol_state_var_diff_set \<mu> \<nu>\<close> rev_finite_subset by blast
  
          thus "VarSet \<subseteq> ?V \<Longrightarrow> fol_eval F (S {}) = fol_eval F (S VarSet)"
          proof (induction VarSet rule: finite_induct)
            case empty
              then show ?case by simp
            next
            case (insert x Vold)
              have "fol_eval F (S {}) = fol_eval F (S Vold)"
                using insert.IH insert.prems by blast
  
              also have "x \<in> ?V"
                using insert.prems by fastforce
  
              thus "fol_eval F (S {}) = fol_eval F (S (insert x Vold))"
                using inductive_argument[of "x" "Vold"] \<open>x \<in> ?V\<close> \<open>fol_eval F (S {}) = fol_eval F (S Vold)\<close>
                by fastforce
            qed
          qed
        qed

      then have eq4: "fol_eval F (S {}) = fol_eval F (S ?V)" 
        by blast

      thus ?thesis
        using eq1 eq2 eq3 eq4 eq5
        by (metis (mono_tags, opaque_lifting) folCore.fol_fv_syn_mirror_state_def folCore.fol_states_agree_on_def folCore_axioms fol_fv_syn_coincidence)
    qed

(*text \<open>
Next, we show that the set of semantically free variables is indeed the smallest set for which
coincidence holds.
Note, that smallest here is in the sense of \emph{cardinality} and not just in the sense of 
a subset relation.
\<close>*)

lemma fol_fv_sem_coincidence_smallest:
    fixes FVTest :: "('atom, 'var) fol_formula \<Rightarrow> 'var \<Rightarrow> bool"
    assumes FVTest_finite: "finite (Collect (FVTest F))"
    assumes semFVSmaller: "card (Collect (FVTest F)) < card (Collect (fol_fv_sem F))"
    shows "\<exists> \<mu> \<omega> . ( (fol_states_agree_on (FVTest F) \<mu> \<omega>) \<and> fol_eval F \<mu> \<noteq> fol_eval F \<omega>)"
  proof (rule ccontr, simp)
    assume fv_complete: " \<forall>\<mu> \<omega>. fol_states_agree_on (FVTest F) \<mu> \<omega> \<longrightarrow> fol_eval F \<mu> = fol_eval F \<omega>"

    have "(Collect (FVTest F)) \<subseteq> (Collect (fol_fv_sem F))"
    proof (rule ccontr)
      assume "\<not> ((Collect (FVTest F)) \<subseteq> (Collect (fol_fv_sem F)))"

      obtain w where w_cond: "w \<notin> (Collect (FVTest F)) \<and> w \<in> (Collect (fol_fv_sem F))"
        using semFVSmaller
        by (meson FVTest_finite card_mono leD subsetI)

      then obtain s 
        where w_may_differ: "fol_equal_everywhere_but w (fst s) (snd s)"
          and F_eval_unequal: "(fol_eval F (fst s) \<noteq> fol_eval F (snd s))"
        unfolding fol_fv_sem.simps
        by (smt (verit, best) fst_conv mem_Collect_eq snd_conv)

      have F_eval_equal: "fol_eval F (fst s) = fol_eval F (snd s)"
        using w_may_differ
        using fv_complete
        using w_cond
        unfolding fol_equal_everywhere_but_def
        unfolding fol_states_agree_on_def
        by (metis (mono_tags, lifting) CollectI)
      
      show False
        using F_eval_equal F_eval_unequal
        by blast
    qed

    then have semFVSubset: "(Collect (FVTest F)) \<subset> Collect (fol_fv_sem F)"
      using semFVSmaller
      by force
      
    then have "\<exists> \<mu> \<omega> . ( (fol_states_agree_on (FVTest F) \<mu> \<omega>) \<and> fol_eval F \<mu> \<noteq> fol_eval F \<omega>)"
    proof -
      obtain w :: 'var where w_condition: "\<not>(FVTest F w) \<and> (fol_fv_sem F w)" using semFVSubset by blast
    
      obtain \<mu> \<omega> where agree: "fol_states_agree_on (\<lambda>wa. wa \<noteq> w) \<mu> \<omega>"
                 and eval_diff: "fol_eval F \<mu> = (\<not> fol_eval F \<omega>)"
        using w_condition fol_equal_everywhere_but_def by auto
    
      then have "(fol_states_agree_on (FVTest F) \<mu> \<omega>)"
        using agree semFVSubset w_condition
        by (metis (mono_tags, lifting) fol_states_agree_on_def)
    
      thus ?thesis
        using eval_diff
        by blast
    qed
        
    thus "False"
      using fv_complete
      by auto
  qed

  subsection\<open>Elementary Axioms\<close>

text \<open>
With these results out of the way, we can now move on to proving the validity of a number of Hilbert axioms
for our FOL formalization.
Note, that \texttt{fol\_hilbert\_axiom\_7} indeed uses the definition of semantically free variables.
\<close>

lemma fol_hilbert_axiom_1: "\<Turnstile>[fol_eval]  \<phi> \<Rrightarrow> \<phi>"
  by simp

lemma fol_hilbert_axiom_2: "\<Turnstile>[fol_eval]  (\<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<phi>))"
  by simp

lemma fol_hilbert_axiom_3: "\<Turnstile>[fol_eval] (\<phi> \<Rrightarrow> (\<psi> \<Rrightarrow> \<xi>)) \<Rrightarrow> ((\<phi> \<Rrightarrow> \<psi>) \<Rrightarrow> (\<phi> \<Rrightarrow> \<xi>))"
  by simp

lemma fol_hilbert_axiom_4: "\<Turnstile>[fol_eval] (\<rceil>\<phi> \<Rrightarrow> \<rceil>\<psi>) \<Rrightarrow> (\<psi> \<Rrightarrow> \<phi>)"
  by simp

lemma fol_hilbert_axiom_6: "\<Turnstile>[fol_eval] (folall v (\<phi> \<Rrightarrow> \<psi>)) \<Rrightarrow> ( (folall v \<phi>) \<Rrightarrow> (folall v \<psi>) )"
  apply simp
  by blast

lemma fol_hilbert_axiom_7:
  assumes fv_assumption: "\<not> fol_fv_sem \<phi> v"
  shows "\<Turnstile>[fol_eval] \<phi> \<Rrightarrow> folall v \<phi>"
proof (simp, intro allI, intro impI)
  fix \<mu>
  assume phi_satisfied: "fol_eval \<phi> \<mu>"
  
  show "\<forall>\<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<longrightarrow> fol_eval \<phi> \<omega>"
  proof (rule ccontr, simp)
    assume "\<exists>\<omega>. fol_equal_everywhere_but v \<mu> \<omega> \<and> \<not> fol_eval \<phi> \<omega>"

    then obtain \<omega> where almost_equal: "fol_equal_everywhere_but v \<mu> \<omega>"
                    and not_satisfied: "\<not> fol_eval \<phi> \<omega>" by auto

    have "fol_eval \<phi> \<omega>"
      using phi_satisfied
      using almost_equal
      using fv_assumption
      by auto
    
    thus False
      using not_satisfied by simp
  qed
qed

lemma fol_hilbert_axiom_conj_i:
  fixes \<phi> :: "('atom, 'var) fol_formula"
    and \<psi> :: "('atom, 'var) fol_formula"
  shows "\<Turnstile>[fol_eval]  \<phi> \<Rrightarrow> \<psi> \<Rrightarrow> (\<phi> and \<psi>)"
  unfolding fol_valid_def
  by fastforce

lemma fol_hilbert_axiom_conj_e1:
  fixes \<phi> :: "('atom, 'var) fol_formula"
    and \<psi> :: "('atom, 'var) fol_formula"
  shows "\<Turnstile>[fol_eval] (\<phi> and \<psi>) \<Rrightarrow> \<phi>"
  unfolding fol_valid_def
  by fastforce


lemma fol_hilbert_axiom_conj_e2:
  fixes \<phi> :: "('atom, 'var) fol_formula"
    and \<psi> :: "('atom, 'var) fol_formula"
  shows "\<Turnstile>[fol_eval] (\<phi> and \<psi>) \<Rrightarrow> \<psi>"
  unfolding fol_valid_def
  by fastforce

lemma fol_hilbert_mp:
  fixes \<phi> :: "('atom, 'var) fol_formula"
    and \<psi> :: "('atom, 'var) fol_formula"
  assumes "\<Turnstile>[fol_eval] \<phi>"
      and "\<Turnstile>[fol_eval] \<phi> \<Rrightarrow> \<psi>"
  shows "\<Turnstile>[fol_eval] \<psi>"
  using assms
  unfolding fol_valid_def
  by force

(* Boolean Algebra *)

lemma "\<And>a b c. fol_eval ((a foland b) foland c) = fol_eval (a foland (b foland c))"
  unfolding fol_eval.simps
  by simp

lemma bool_and_comm: "\<And>a b. fol_eval (a foland b) = fol_eval (b foland a)"  
  unfolding fol_eval.simps
  by auto

lemma "\<And>a b c. fol_eval ((a or b) or c) = fol_eval (a or (b or c) )"
  unfolding OR_def fol_eval.simps
  by auto

lemma "\<And>a b. fol_eval (a or b) = fol_eval (b or a)"
  unfolding OR_def fol_eval.simps
  by auto

lemma "\<And>x y z. fol_eval (x foland (y or z)) = fol_eval (x foland y or x foland z)"
  unfolding OR_def fol_eval.simps
  by auto

lemma bool_or_distrib: "\<And>x y z. fol_eval (x or y foland z) = fol_eval ((x or y) foland (x or z))"
  unfolding OR_def fol_eval.simps
  by auto

lemma "\<And>x. fol_eval (x foland FOLTRUE) = fol_eval x"
  unfolding fol_eval.simps
  by auto

lemma "\<And>x. fol_eval (x or folnot FOLTRUE) = fol_eval x"
  unfolding OR_def fol_eval.simps
  by auto

lemma "\<And>x. fol_eval (x foland folnot x) = fol_eval (folnot FOLTRUE)"
  unfolding OR_def fol_eval.simps
  by auto

lemma "\<And>x. fol_eval (x or folnot x) = fol_eval FOLTRUE"
  unfolding fol_eval.simps OR_def
  by auto

  

end

end