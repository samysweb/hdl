subsection\<open>Neural Dynamic Theory\<close>
text\<open>
Implementation formalized by Claude Opus after
intensive discussion with Samuel Teuber on 19th of August 2026.
Cross-checked by Samuel Teuber.
\<close>

theory SemiRingNDL
  imports
    Complex_Main
    "SemiRingFOL"
    "SemiRingDL"
    "HavocDynamicLogic"
    "KATDynamicLogic"
    "NatKATDynamicLogic"
    "KATRewriting"
    "DynamicTheorySum"
    "Deep_Learning.Tensor"
begin

subsubsection\<open>Shape-Correct Tensor Functions\<close>

type_synonym ndl_var_sym = string

datatype tensor_fun_raw =
  TensorFun (tf_apply: "real tensor \<Rightarrow> real tensor")
            (tf_in:    "nat list")
            (tf_out:   "nat list")

typedef shaped_tensor_fun =
  "{f. \<forall>x. dims x = tf_in f \<longrightarrow> dims (tf_apply f x) = tf_out f}"
  by (rule exI[of _ "TensorFun id [] []"]) simp

setup_lifting type_definition_shaped_tensor_fun

lift_definition stf_apply :: "shaped_tensor_fun \<Rightarrow> real tensor \<Rightarrow> real tensor" is tf_apply .
lift_definition stf_in    :: "shaped_tensor_fun \<Rightarrow> nat list"                   is tf_in .
lift_definition stf_out   :: "shaped_tensor_fun \<Rightarrow> nat list"                   is tf_out .

lemma stf_shape: "dims x = stf_in N \<Longrightarrow> dims (stf_apply N x) = stf_out N"
  by transfer simp

definition mk_stf :: "(real tensor \<Rightarrow> real tensor) \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> shaped_tensor_fun"
  where "mk_stf f si so = Abs_shaped_tensor_fun (TensorFun f si so)"

lemma mk_stf_sel:
  assumes "\<And>x. dims x = si \<Longrightarrow> dims (f x) = so"
  shows "stf_apply (mk_stf f si so) = f"
    and "stf_in    (mk_stf f si so) = si"
    and "stf_out   (mk_stf f si so) = so"
  using assms
    apply (simp add: Abs_shaped_tensor_fun_inverse mk_stf_def stf_apply.rep_eq)
   apply (simp add: Abs_shaped_tensor_fun_inverse assms mk_stf_def stf_in.rep_eq)
  by (simp add: Abs_shaped_tensor_fun_inverse assms mk_stf_def stf_out.rep_eq)

lemma mk_stf_id_trivial: "stf_in (mk_stf id [] []) = [] \<and> stf_out (mk_stf id [] []) = []"
  using mk_stf_sel(2,3)[of "[]" id "[]"] by simp

subsubsection\<open>Tensor Variables and Lookups\<close>

datatype ndl_var = NVar (var_sym: ndl_var_sym) (var_shape: "nat list")

definition valid_index :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "valid_index s i \<longleftrightarrow> list_all2 (<) i s"

datatype ndl_var_lookup_gen =
  VarLookup (lookup_var: ndl_var) (lookup_idx: "nat list")

definition wf_lookup :: "ndl_var_lookup_gen \<Rightarrow> bool" where
  "wf_lookup x \<longleftrightarrow> lookup_idx x \<lhd> var_shape (lookup_var x)"

typedef ndl_var_lookup = "{x. wf_lookup x}"
  by (rule exI[of _ "VarLookup (NVar ''x'' []) []"])
     (simp add: wf_lookup_def valid_index.Nil)

setup_lifting type_definition_ndl_var_lookup

lift_definition lk_var :: "ndl_var_lookup \<Rightarrow> ndl_var"  is lookup_var .
lift_definition lk_idx :: "ndl_var_lookup \<Rightarrow> nat list" is lookup_idx .

lemma lk_valid [simp]: "lk_idx x \<lhd> var_shape (lk_var x)"
  by transfer (simp add: wf_lookup_def)

definition mk_lookup :: "ndl_var \<Rightarrow> nat list \<Rightarrow> ndl_var_lookup" where
  "mk_lookup v i = Abs_ndl_var_lookup (VarLookup v i)"

lemma mk_lookup_sel:
  assumes "i \<lhd> var_shape v"
  shows "lk_var (mk_lookup v i) = v"
    and "lk_idx (mk_lookup v i) = i"
  using assms
   apply (simp add: eq_onp_same_args lk_var.abs_eq mk_lookup_def wf_lookup_def)
  by (simp add: assms eq_onp_same_args lk_idx.abs_eq mk_lookup_def wf_lookup_def)

lemma lookup_eqI: "lk_var x = lk_var y \<Longrightarrow> lk_idx x = lk_idx y \<Longrightarrow> x = y"
  by transfer (metis ndl_var_lookup_gen.expand)

lemma mk_lookup_lk [simp]: "mk_lookup (lk_var x) (lk_idx x) = x"
  by (rule lookup_eqI) (simp_all add: mk_lookup_sel)

lemma lookup_cases:
  obtains v i where "x = mk_lookup v i" "i \<lhd> var_shape v"
  using mk_lookup_lk lk_valid by metis

paragraph\<open>Finiteness of the lookups of a variable.\<close>
text\<open>
This is needed for the free-variable finiteness obligation of neural programs:
a neural program reads all components of its source variable, and there are
finitely many of those.
\<close>

lemma finite_valid_index_set: "finite {i. i \<lhd> ds}"
proof -
  have "{i. i \<lhd> ds} \<subseteq> {xs. set xs \<subseteq> {..<Suc (sum_list ds)} \<and> length xs = length ds}"
  proof
    fix i assume "i \<in> {i. i \<lhd> ds}"
    hence v: "i \<lhd> ds" by simp
    hence len: "length i = length ds" by (rule valid_index_length)
    have "\<And>x. x \<in> set i \<Longrightarrow> x < Suc (sum_list ds)"
    proof -
      fix x assume "x \<in> set i"
      then obtain m where m: "m < length i" "i!m = x" by (metis in_set_conv_nth)
      hence lt: "i!m < ds!m" using valid_index_lt[OF v] len by auto
      have "ds!m \<le> sum_list ds" using m len by (simp add: member_le_sum_list)
      thus "x < Suc (sum_list ds)" using lt m by simp
    qed
    thus "i \<in> {xs. set xs \<subseteq> {..<Suc (sum_list ds)} \<and> length xs = length ds}"
      using len by auto
  qed
  moreover have "finite {xs. set xs \<subseteq> {..<Suc (sum_list ds)} \<and> length xs = length ds}"
    by (rule finite_lists_length_eq) simp
  ultimately show ?thesis by (rule finite_subset)
qed

lemma finite_lookups_of_var: "finite {x. lk_var x = v}"
proof -
  have "{x. lk_var x = v} \<subseteq> mk_lookup v ` {i. i \<lhd> var_shape v}"
  proof
    fix x assume "x \<in> {x. lk_var x = v}"
    hence "lk_var x = v" by simp
    hence "x = mk_lookup v (lk_idx x)" and "lk_idx x \<lhd> var_shape v"
      using mk_lookup_lk lk_valid by auto
    thus "x \<in> mk_lookup v ` {i. i \<lhd> var_shape v}" by blast
  qed
  thus ?thesis using finite_valid_index_set finite_surj by blast
qed

subsubsection\<open>Well-Shaped States\<close>
text\<open>
A state maps every tensor variable to a tensor of that variable's declared
shape.  Restricting the state space in this way is what makes the free-variable
overapproximation of neural programs sound: two states that agree on all
lookups of the source variable then agree on the whole source tensor.
\<close>

definition wf_nstate :: "(ndl_var \<Rightarrow> real tensor) \<Rightarrow> bool" where
  "wf_nstate \<mu> \<longleftrightarrow> (\<forall>v. dims (\<mu> v) = var_shape v)"

lemma wf_nstate_zero: "wf_nstate (\<lambda>v. tensor_from_lookup (var_shape v) (\<lambda>i. 0))"
  by (simp add: wf_nstate_def dims_tensor_from_lookup)

typedef ndl_state = "{\<mu> :: (ndl_var \<Rightarrow> real tensor) . wf_nstate \<mu>}"
  using wf_nstate_zero by blast

definition nst :: "ndl_state \<Rightarrow> ndl_var \<Rightarrow> real tensor"
  where "nst = Rep_ndl_state"

lemma nst_dims [simp]: "dims (nst \<mu> v) = var_shape v"
  using Rep_ndl_state[of \<mu>] by (simp add: nst_def wf_nstate_def)

lemma nst_Abs [simp]: "wf_nstate g \<Longrightarrow> nst (Abs_ndl_state g) = g"
  by (simp add: nst_def Abs_ndl_state_inverse)

lemma nst_inject: "nst \<mu> = nst \<omega> \<Longrightarrow> \<mu> = \<omega>"
  by (simp add: nst_def Rep_ndl_state_inject)

definition ndl_eval :: "ndl_state \<Rightarrow> ndl_var_lookup \<Rightarrow> real" where
  "ndl_eval \<mu> x = lookup (nst \<mu> (lk_var x)) (lk_idx x)"

lemma ndl_eval_mk_lookup [simp]:
  "i \<lhd> var_shape v \<Longrightarrow> ndl_eval \<mu> (mk_lookup v i) = lookup (nst \<mu> v) i"
  by (simp add: ndl_eval_def mk_lookup_sel)

text\<open>
Componentwise agreement on one variable determines the whole tensor stored
in that variable.  This is the bridge between the lookup-level variables of
the locale and the tensor-level state.
\<close>

lemma nst_eqI:
  assumes "\<And>x. lk_var x = v \<Longrightarrow> ndl_eval \<mu> x = ndl_eval \<omega> x"
  shows "nst \<mu> v = nst \<omega> v"
proof (rule tensor_lookup_eqI)
  show "dims (nst \<mu> v) = dims (nst \<omega> v)" by simp
next
  fix i assume "i \<lhd> dims (nst \<mu> v)"
  hence valid: "i \<lhd> var_shape v" by simp
  have "lk_var (mk_lookup v i) = v" using valid by (simp add: mk_lookup_sel)
  hence "ndl_eval \<mu> (mk_lookup v i) = ndl_eval \<omega> (mk_lookup v i)" using assms by blast
  thus "lookup (nst \<mu> v) i = lookup (nst \<omega> v) i" using valid by simp
qed

lemma ndl_state_eqI:
  assumes "\<And>x. ndl_eval \<mu> x = ndl_eval \<omega> x"
  shows "\<mu> = \<omega>"
proof (rule nst_inject, rule ext)
  fix v show "nst \<mu> v = nst \<omega> v" using assms by (intro nst_eqI) blast
qed

paragraph\<open>State space convexity.\<close>
text\<open>
Given two states and a set of lookups we build the mixed state componentwise.
The result is well-shaped by construction, which is why the state typedef does
not obstruct this obligation.
\<close>

lemma ndl_convex:
  "\<forall>\<omega> \<mu> V. \<exists>\<nu>. \<forall>x. (x \<in> V \<longrightarrow> ndl_eval \<nu> x = ndl_eval \<mu> x) \<and>
                     (x \<notin> V \<longrightarrow> ndl_eval \<nu> x = ndl_eval \<omega> x)"
proof (intro allI)
  fix \<omega> \<mu> V
  define g where
    "g = (\<lambda>v. tensor_from_lookup (var_shape v)
                (\<lambda>i. if mk_lookup v i \<in> V then lookup (nst \<mu> v) i else lookup (nst \<omega> v) i))"
  have wf: "wf_nstate g" by (simp add: g_def wf_nstate_def dims_tensor_from_lookup)
  define \<nu> where "\<nu> = Abs_ndl_state g"
  have nst_nu: "nst \<nu> = g" using wf by (simp add: \<nu>_def)
  have mix: "\<And>x. ndl_eval \<nu> x = (if x \<in> V then ndl_eval \<mu> x else ndl_eval \<omega> x)"
  proof -
    fix x
    have "ndl_eval \<nu> x = lookup (g (lk_var x)) (lk_idx x)"
      by (simp add: ndl_eval_def nst_nu)
    also have "... = (if mk_lookup (lk_var x) (lk_idx x) \<in> V
                      then lookup (nst \<mu> (lk_var x)) (lk_idx x)
                      else lookup (nst \<omega> (lk_var x)) (lk_idx x))"
      using lk_valid[of x] by (simp add: g_def lookup_tensor_from_lookup)
    finally show "ndl_eval \<nu> x = (if x \<in> V then ndl_eval \<mu> x else ndl_eval \<omega> x)"
      by (simp add: ndl_eval_def)
  qed
  show "\<exists>\<nu>. \<forall>x. (x \<in> V \<longrightarrow> ndl_eval \<nu> x = ndl_eval \<mu> x) \<and>
                 (x \<notin> V \<longrightarrow> ndl_eval \<nu> x = ndl_eval \<omega> x)"
    by (intro exI[where x = \<nu>]) (simp add: mix)
qed

subsubsection\<open>The Assignment Fragment\<close>
text\<open>
The semi-ring assignment theory is obtained for free from the generic
instantiation lemma: the only theory-specific ingredient is convexity.
\<close>

lemma ndl_folCore:
  "folCore (semiringfol_AtomEval_flex ndl_eval) semiringfol_AtomFVSyn ndl_eval"
  using semiring_folCore_via[of ndl_eval] ndl_convex by blast

lemma ndl_assign_dyn:
  "dynamic_theory (semiringfol_AtomEval_flex ndl_eval) semiringfol_AtomFVSyn ndl_eval
                  (semiringfol_ProgramEval_flex ndl_eval) semiring_prog_fv"
  using semiring_dyn_theory_via[of ndl_eval] ndl_convex by blast

subsubsection\<open>Neural Programs\<close>
text\<open>
Definition 6.2.3 sorts the source and target variable by the input and output
shape of the network.  We keep that constraint in the type of programs, which
makes the neural assignment total and hence box and diamond interchangeable.
\<close>

datatype ndl_nn_raw =
  NNApply (nn_tgt: ndl_var) (nn_fun: shaped_tensor_fun) (nn_src: ndl_var)

definition wf_nn :: "ndl_nn_raw \<Rightarrow> bool" where
  "wf_nn p \<longleftrightarrow> stf_in (nn_fun p) = var_shape (nn_src p) \<and>
               stf_out (nn_fun p) = var_shape (nn_tgt p)"

typedef ndl_nn_prog = "{p. wf_nn p}"
  by (rule exI[of _ "NNApply (NVar ''w'' []) (mk_stf id [] []) (NVar ''v'' [])"])
     (simp add: wf_nn_def mk_stf_id_trivial)

definition nnp :: "ndl_nn_prog \<Rightarrow> ndl_nn_raw" where "nnp = Rep_ndl_nn_prog"

abbreviation ntgt :: "ndl_nn_prog \<Rightarrow> ndl_var" where "ntgt p \<equiv> nn_tgt (nnp p)"
abbreviation nfun :: "ndl_nn_prog \<Rightarrow> shaped_tensor_fun" where "nfun p \<equiv> nn_fun (nnp p)"
abbreviation nsrc :: "ndl_nn_prog \<Rightarrow> ndl_var" where "nsrc p \<equiv> nn_src (nnp p)"

lemma nnp_shapes [simp]:
  "stf_in (nfun p) = var_shape (nsrc p)"
  "stf_out (nfun p) = var_shape (ntgt p)"
  using Rep_ndl_nn_prog[of p] by (simp_all add: nnp_def wf_nn_def)

text\<open>
The semantics is stated at the level of tensor variables, as in Definition
6.2.4: everything but the target is unchanged, and the target receives the
network's output.
\<close>

definition nn_eval :: "ndl_nn_prog \<Rightarrow> ndl_state \<Rightarrow> ndl_state \<Rightarrow> bool" where
  "nn_eval p \<mu> \<omega> =
     ((\<forall>v. v \<noteq> ntgt p \<longrightarrow> nst \<omega> v = nst \<mu> v) \<and>
     nst \<omega> (ntgt p) = stf_apply (nfun p) (nst \<mu> (nsrc p)))"

definition nn_fv :: "ndl_nn_prog \<Rightarrow> ndl_var_lookup \<Rightarrow> bool" where
  "nn_fv p x = (lk_var x = nsrc p)"

text\<open>
The output of the network always has the shape declared for the target
variable, so the successor state exists and is unique.
\<close>

lemma nn_result_shape: "dims (stf_apply (nfun p) (nst \<mu> (nsrc p))) = var_shape (ntgt p)"
  using stf_shape[of "nst \<mu> (nsrc p)" "nfun p"] by simp

lemma nn_total_det: "\<exists>!\<omega>. nn_eval p \<mu> \<omega>"
proof -
  define g where "g = (nst \<mu>)(ntgt p := stf_apply (nfun p) (nst \<mu> (nsrc p)))"
  have wf: "wf_nstate g" by (simp add: g_def wf_nstate_def nn_result_shape)
  define \<omega> where "\<omega> = Abs_ndl_state g"
  have nst_omega: "nst \<omega> = g" using wf by (simp add: \<omega>_def)
  have ex: "nn_eval p \<mu> \<omega>" by (simp add: nn_eval_def nst_omega g_def)
  have uniq: "\<And>\<upsilon>. nn_eval p \<mu> \<upsilon> \<Longrightarrow> \<upsilon> = \<omega>"
  proof -
    fix \<upsilon> assume "nn_eval p \<mu> \<upsilon>"
    hence "nst \<upsilon> = g" unfolding nn_eval_def g_def by (auto simp: fun_upd_def)
    thus "\<upsilon> = \<omega>" using nst_omega nst_inject by simp
  qed
  show ?thesis using ex uniq by blast
qed

lemma ndl_nn_dyn:
  "dynamic_theory (semiringfol_AtomEval_flex ndl_eval) semiringfol_AtomFVSyn ndl_eval
                  nn_eval nn_fv"
proof
  show "\<And>a. finite (Collect (semiringfol_AtomFVSyn a))"
    using ndl_folCore
    using semiring_folCore.fv_finite by blast
  show "\<And>a \<mu> \<omega>. fol_states_agree_on_gen ndl_eval (semiringfol_AtomFVSyn a) \<mu> \<omega> \<Longrightarrow>
          semiringfol_AtomEval_flex ndl_eval a \<mu> = semiringfol_AtomEval_flex ndl_eval a \<omega>"
    using ndl_folCore by (simp add: folCore_def)
  show convexity: "\<forall>\<omega> \<mu> V. \<exists>\<nu>. \<forall>v. (v \<in> V \<longrightarrow> ndl_eval \<nu> v = ndl_eval \<mu> v) \<and>
                                     (v \<notin> V \<longrightarrow> ndl_eval \<nu> v = ndl_eval \<omega> v)"
    using ndl_convex by blast

  show "\<And>p. finite (Collect (nn_fv p))"
    using nn_fv_def
    using finite_lookups_of_var
    by presburger

  show "\<And>p V \<mu> \<omega> \<nu>.
          ((\<forall>v. nn_fv p v \<longrightarrow> V v) \<and>
           folCore.fol_states_agree_on ndl_eval V \<mu> \<omega> \<and>
           nn_eval p \<mu> \<nu>) \<longrightarrow>
          (\<exists>\<upsilon>. nn_eval p \<omega> \<upsilon> \<and> folCore.fol_states_agree_on ndl_eval V \<nu> \<upsilon>)"
  proof -
    fix p V \<mu> \<omega> \<nu>
    show "((\<forall>v. nn_fv p v \<longrightarrow> V v) \<and>
           folCore.fol_states_agree_on ndl_eval V \<mu> \<omega> \<and>
           nn_eval p \<mu> \<nu>) \<longrightarrow>
          (\<exists>\<upsilon>. nn_eval p \<omega> \<upsilon> \<and> folCore.fol_states_agree_on ndl_eval V \<nu> \<upsilon>)"
    proof (intro impI)
      assume asm: "(\<forall>v. nn_fv p v \<longrightarrow> V v) \<and>
                   folCore.fol_states_agree_on ndl_eval V \<mu> \<omega> \<and>
                   nn_eval p \<mu> \<nu>"
      hence fv_sub: "\<forall>x. lk_var x = nsrc p \<longrightarrow> V x" by (simp add: nn_fv_def)
      have agree: "\<And>x. V x \<Longrightarrow> ndl_eval \<mu> x = ndl_eval \<omega> x"
        using asm
        by (meson folCore.fol_states_agree_on_def ndl_folCore)
      have step: "nn_eval p \<mu> \<nu>" using asm by simp

      text\<open>The source tensors coincide, because all their lookups are free.\<close>
      have src_eq: "nst \<mu> (nsrc p) = nst \<omega> (nsrc p)"
        using fv_sub agree by (intro nst_eqI) blast

      define g where "g = (nst \<omega>)(ntgt p := nst \<nu> (ntgt p))"
      have wf: "wf_nstate g" by (simp add: g_def wf_nstate_def)
      define \<upsilon> where "\<upsilon> = Abs_ndl_state g"
      have nst_ups: "nst \<upsilon> = g" using wf by (simp add: \<upsilon>_def)

      have tgt: "nst \<nu> (ntgt p) = stf_apply (nfun p) (nst \<omega> (nsrc p))"
        using step src_eq by (simp add: nn_eval_def)

      have trans: "nn_eval p \<omega> \<upsilon>"
        by (simp add: nn_eval_def nst_ups g_def tgt)

      have "folCore.fol_states_agree_on ndl_eval V \<nu> \<upsilon>"
      proof (unfold folCore.fol_states_agree_on_def[OF ndl_folCore], intro allI impI)
        fix x assume xV: "V x"
        show "ndl_eval \<nu> x = ndl_eval \<upsilon> x"
        proof (cases "lk_var x = ntgt p")
          case True
          thus ?thesis by (simp add: ndl_eval_def nst_ups g_def)
        next
          case False
          have "nst \<nu> (lk_var x) = nst \<mu> (lk_var x)"
            using step False by (simp add: nn_eval_def)
          moreover have "nst \<upsilon> (lk_var x) = nst \<omega> (lk_var x)"
            using False by (simp add: nst_ups g_def)
          ultimately show ?thesis
            using agree[OF xV] by (simp add: ndl_eval_def)
        qed
      qed
      thus "\<exists>\<upsilon>. nn_eval p \<omega> \<upsilon> \<and> folCore.fol_states_agree_on ndl_eval V \<nu> \<upsilon>"
        using trans by blast
    qed
  qed

  show "\<forall>p \<mu> \<omega>. (\<forall>v. ndl_eval \<mu> v = ndl_eval \<omega> v) \<longrightarrow> nn_eval p \<mu> = nn_eval p \<omega>"
    using ndl_state_eqI by metis
qed

subsubsection\<open>The Combined Theory\<close>

interpretation ndl_dl:
  dynamic_theory_sum
    "semiringfol_AtomEval_flex ndl_eval" semiringfol_AtomFVSyn ndl_eval
    "semiringfol_ProgramEval_flex ndl_eval" semiring_prog_fv
    nn_eval nn_fv
  by (simp add: dynamic_theory_sum_def ndl_assign_dyn ndl_nn_dyn)

print_interps FirstOrder.folCore

lemma ndl_box_diamond_iff:
  "\<Turnstile>[ndl_dl.sum_dl.dyn_eval] ((\<langle>\<pi>\<rangle> \<phi>) \<Lleftarrow>\<Rrightarrow> (\<lbrakk>\<pi>\<rbrakk> \<phi>))"
proof -
  have "\<And>\<mu>. \<exists>!\<omega>. ndl_dl.sum_prog_eval \<pi> \<mu> \<omega>"
  proof (induct \<pi>)
    case (Inl a)
    then show "\<And>\<mu>. Ex1 (ndl_dl.sum_prog_eval (Inl a) \<mu>)"
    proof (cases a)
      case (ASSIGN x1 x2)
      also have "\<And>\<mu>. \<exists>!\<omega>. ndl_dl.sum_prog_eval (Inl (ASSIGN x1 x2)) \<mu> \<omega>"
      proof -
        fix \<mu>
        obtain var shape pos where var_cond1: "x1 = (Abs_ndl_var_lookup (VarLookup (NVar var shape) pos))"
                               and var_cond2: "pos \<lhd> shape"
          by (metis lk_valid mk_lookup_def mk_lookup_lk ndl_var.collapse)
        then have var_cond3: "pos \<lhd> var_shape (NVar var shape)"
          unfolding var_shape_def
          by simp
        let ?targetvar = "(NVar var shape)"
        let ?map = "
            \<lambda> (\<nu> :: ndl_state) .
            \<lambda> (v :: ndl_var) .
              if (v=?targetvar)
              then
                (tensor_from_lookup shape (\<lambda> i.
                  if (i=pos) then (semiringfol_TermEval x2 (ndl_eval \<nu>)) else (lookup ((nst \<nu>) v) i)))
              else
                ((nst \<nu>) v)"
        have mapped_wf: "wf_nstate (?map \<mu>)"
          unfolding wf_nstate_def
          apply simp
          using dims_tensor_from_lookup by blast
        let ?fullmap = "Abs_ndl_state \<circ> ?map"
        show "\<exists>!\<omega>. ndl_dl.sum_prog_eval (Inl (x1:=x2)) \<mu> \<omega>"
          unfolding Ex1_def
          apply (rule exI[of _ "?fullmap \<mu>"])
          unfolding ndl_dl.sum_prog_eval_def
          unfolding semiringfol_ProgramEval_flex.simps
          apply (simp del: semiring_prog_eval.simps)
          unfolding semiring_prog_eval.simps
          apply (intro conjI)
          using var_cond1 var_cond2 mapped_wf
          subgoal
            unfolding ndl_eval_def
            unfolding id_def
            unfolding folCore.fol_equal_everywhere_but_def[OF semiring_folCore.folCore_axioms]
            unfolding folCore.fol_states_agree_on_def[OF semiring_folCore.folCore_axioms]
            unfolding state_id_def
            apply simp
            by (smt (verit) lk_valid lookup_tensor_from_lookup mk_lookup_def mk_lookup_lk
                ndl_var.sel(2))
          subgoal
            unfolding nst_def
            unfolding ndl_eval_def
            using var_cond1 var_cond2 mapped_wf
            by (smt (verit, ccfv_threshold) dims_tensor_from_lookup
                length_tensor_vec_from_lookup lookup_def mk_lookup_def mk_lookup_sel(1,2)
                nst_Abs nst_def tensor_from_lookup_def tensor_lookup_base tensor_lookup_cong
                vec_tensor wf_nstate_def)
          apply (intro allI)
          proof
            fix y
            have aux_fact: "Rep_ndl_state
                   (Abs_ndl_state
                     (?map \<mu>)) = ?map \<mu>"
              using mapped_wf Abs_ndl_state_inverse
              by blast
            assume assm1: "semiring_folCore.fol_equal_everywhere_but x1 (ndl_eval \<mu>) (ndl_eval y) \<and>
         ndl_eval y x1 = semiringfol_TermEval x2 (ndl_eval \<mu>)"

            have "y =
               (Abs_ndl_state (?map \<mu>))"
            proof (rule ndl_state_eqI)
              fix x
              show "ndl_eval y x = ndl_eval (Abs_ndl_state (?map \<mu>)) x"
              proof (cases "x = x1")
                case True
                then show ?thesis
                  using assm1
                  unfolding ndl_eval_def nst_Abs[OF mapped_wf]
                  unfolding True
                  unfolding var_cond1
                  unfolding mk_lookup_def[symmetric]
                  unfolding mk_lookup_sel[OF var_cond3]
                  by (simp add: lookup_tensor_from_lookup var_cond2)
              next
                case False
                then show ?thesis
                  using assm1
                  unfolding ndl_eval_def nst_Abs[OF mapped_wf]
                  unfolding var_cond1
                  unfolding mk_lookup_def[symmetric]
                  unfolding mk_lookup_sel[OF var_cond3]
                  unfolding folCore.fol_equal_everywhere_but_def[OF semiring_folCore.folCore_axioms]
                  unfolding folCore.fol_states_agree_on_def[OF semiring_folCore.folCore_axioms]
                  unfolding state_id_def id_def
                  apply simp
                  by (smt (verit, best) lk_valid lookup_tensor_from_lookup ndl_var.sel(2))
              qed
            qed

            thus "y =
                   (Abs_ndl_state
          (\<lambda>v. if v = NVar var shape
         then tensor_from_lookup shape
               (\<lambda>i. if i = pos then semiringfol_TermEval x2 (ndl_eval \<mu>)
                     else lookup (nst \<mu> v) i)
         else nst \<mu> v))"
              using Rep_ndl_state_inject by auto
          qed
        qed
      finally show "\<And>\<mu> . Ex1 (ndl_dl.sum_prog_eval (Inl a) \<mu>) "
        by fastforce
    qed
  next
    case (Inr b)
    then show "\<And>\<mu>. Ex1 (ndl_dl.sum_prog_eval (Inr b) \<mu>)"
    proof (cases b)
      case (Abs_ndl_nn_prog y)
      then show "\<And>\<mu> . Ex1 (ndl_dl.sum_prog_eval (Inr b) \<mu>) "
        by (simp add: nn_total_det)
    qed
  qed
  thus ?thesis
    using ndl_dl.sum_dl.dt_box_diamond_iff
    by simp
qed

abbreviation NNPROG :: "ndl_nn_prog \<Rightarrow>
    ((ndl_var_lookup, real) semiring_prog + ndl_nn_prog)"
  where "NNPROG p \<equiv> Inr p"

abbreviation NASSIGN :: "(ndl_var_lookup, real) semiring_prog \<Rightarrow>
    ((ndl_var_lookup, real) semiring_prog + ndl_nn_prog)"
  where "NASSIGN p \<equiv> Inl p"

type_synonym ndl_prog = "(ndl_var_lookup, real) semiring_prog + ndl_nn_prog"
type_synonym ndl_formula =
  "((ndl_var_lookup, real) semiringfol_atom, ndl_var_lookup, ndl_prog) dyn_formula"


end