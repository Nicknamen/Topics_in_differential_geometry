theory Fiber_bundles
  imports Chart
     "HOL-Analysis.Equivalence_Lebesgue_Henstock_Integration"
    "HOL-Library.Function_Algebras"
    "HOL-Types_To_Sets.Linear_Algebra_On"
begin

(* There seems to not be a definition of open map for the generic topology library... *)
definition "is_open_map_on U f \<equiv> \<forall> S. open S \<longrightarrow> open (f ` (S \<inter> U))"

lemma continuous_on_eq_continuous_at': "open s \<Longrightarrow> continuous_on s f \<longleftrightarrow> (\<forall>x\<in>s. continuous (at x) f)"
  by (simp add: continuous_on_def continuous_at at_within_open[of _ s])

(* 'a and 'b need to be t2 because the topology library is not general enough... *)

locale fiber_bundle =
  fixes \<pi> :: "('a :: t2_space) \<Rightarrow> ('b :: t2_space)" and
    local_triv :: "('a \<Rightarrow> 'b \<times> ('c :: t2_space)) set" and inverse base_set
  assumes open_base_set: "\<forall> f \<in> local_triv. open (base_set f)" (* can I prove this? *)
  and open_dom: "\<forall> f \<in> local_triv. open (\<pi> -` base_set f)"
  and locally_trivial: "\<forall> f \<in> local_triv.
    homeomorphism (\<pi> -` (base_set f)) (base_set f \<times> UNIV) f (inverse f)"
  and commuting_diagram': "\<forall> f \<in> local_triv. \<forall> x \<in>  \<pi> -` (base_set f). fst (f x) = \<pi> x"
begin

definition "carrier_base_space = (\<Union>(base_set ` local_triv))"

definition "carrier_total_space = \<pi> -` carrier_base_space"

definition "domn f = \<pi> -` base_set f"

definition "codomn f =  base_set f \<times> (UNIV :: 'c set)"

lemma commuting_diagram: "\<forall> f \<in> local_triv. \<forall> x \<in> domn f. fst (f x) = \<pi> x"
  by (simp add: commuting_diagram' domn_def)

lemma carrier_total_space_eq_un_domn: "carrier_total_space = (\<Union>f \<in> local_triv. domn f)"
  using carrier_base_space_def carrier_total_space_def domn_def by auto

lemma open_codomn: assumes "f \<in> local_triv"
  shows "open (codomn f)"
  by (metis assms codomn_def open_base_set open_vimage_fst vimage_fst)

lemma codomn_image_domn: assumes "f \<in> local_triv"
  shows "codomn f = f ` domn f"
  by (metis assms codomn_def domn_def homeomorphism_image1 locally_trivial)

lemma domain_local_triv: assumes "f \<in> local_triv"
  shows "homeomorphism (domn f) (codomn f) f (inverse f)"
  by (simp add: assms codomn_def domn_def locally_trivial)

lemma dom_preimage_codomn: assumes "f \<in> local_triv"
    shows "domn f = f -` codomn f"
proof
  show "domn f \<subseteq> f -` codomn f"
    using codomn_image_domn assms by auto
next
  show "f -` codomn f \<subseteq> domn f" (* Need to use that f is bijective on domn f*)
    using codomn_def assms locally_trivial domn_def
    sorry
qed

lemma open_carrier_base_space: "open carrier_base_space"
  by (simp add: carrier_base_space_def open_UN open_base_set)

lemma open_domn: assumes "f \<in> local_triv"
  shows "open (domn f)"
  by (simp add: assms domn_def open_dom)

lemma open_carrier_total_space: "open carrier_total_space"
  by (simp add: carrier_base_space_def carrier_total_space_def open_UN open_dom vimage_UN)

lemma continuous_on_proj: "continuous_on carrier_total_space \<pi>"
proof -
  have "\<forall> x \<in> carrier_total_space. \<exists> f \<in> local_triv. continuous (at x) f"
    by (smt (verit, del_insts) UnionE at_within_open carrier_base_space_def carrier_total_space_def
        continuous_on_eq_continuous_within homeomorphism_cont1 imageE locally_trivial open_dom
        vimageE vimageI)
  also have "\<forall> x \<in> carrier_total_space. continuous (at x) \<pi>"  
  proof
    fix x assume "x \<in> carrier_total_space"
    have "\<exists> f \<in> local_triv. x \<in> domn f"
      using \<open>x \<in> carrier_total_space\<close> carrier_base_space_def carrier_total_space_def domn_def
      by auto 
    then obtain f where mem_f: "f \<in> local_triv" and mem_x: "x \<in> domn f" by blast
    also have "continuous (at x) f"
      by (metis at_within_open continuous_on_eq_continuous_within domain_local_triv
          homeomorphism_cont1 mem_f mem_x open_domn)
    then have "continuous (at x) (\<lambda> x. fst (f x))"
      by (simp add: \<open>isCont f x\<close>)
    then have "eventually (\<lambda>x. fst (f x) = \<pi> x) (nhds x)" using commuting_diagram
      by (metis (mono_tags, lifting) eventually_nhds mem_f mem_x open_domn)      
    then show "continuous (at x) \<pi>" using isCont_cong
    proof -
      show ?thesis
        using \<open>\<forall>\<^sub>F x in nhds x. fst (f x) = \<pi> x\<close> \<open>isCont (\<lambda>x. fst (f x)) x\<close> isCont_cong by force
    qed      
  qed    
  then show ?thesis
    by (simp add: continuous_at_imp_continuous_on)  
qed

lemma is_open_proj: "is_open_map_on carrier_total_space \<pi>"
  sorry

end

lemma trivial_bunlde_is_fiber_bundle: "fiber_bundle fst {id} id (\<lambda> f. UNIV)"
proof
  show "\<forall>f\<in>{id}. open UNIV" by auto
next
  show "\<forall>f\<in>{id}. open (fst -` UNIV)" by auto
next
  show "\<forall>f\<in>{id}. homeomorphism (fst -` UNIV) (UNIV \<times> UNIV) f (id f)"
  by (metis UNIV_Times_UNIV eq_id_iff homeomorphism_ident singletonD vimage_UNIV)
next
  show "\<forall>f\<in>{id}. \<forall>x\<in>fst -` UNIV. fst (f x) = fst x"
   by auto
qed

locale fiber_bundle' =
  fixes \<pi> :: "('a :: topological_space) \<Rightarrow> ('b :: topological_space)" and
    local_triv :: "('a, 'b \<times> ('c :: topological_space)) chart set"
  assumes dom: "\<forall> f \<in> local_triv. domain f = \<pi> -` (fst ` codomain f)"
  and codom: "\<forall> f \<in> local_triv. codomain f = (fst ` codomain f) \<times> UNIV"
  and commuting_diagram: "\<forall> f \<in> local_triv. \<forall> x \<in> domain f. fst (f x) = \<pi> x"
begin

definition "carrier_total_space = \<Union>(domain ` local_triv)"

definition "carrier_base_space = fst ` (\<Union>(codomain ` local_triv))"

definition "base_set f = fst ` codomain f"

lemma domain_local_triv: assumes "f \<in> local_triv"
  shows "domain f = \<pi> -` base_set f"
  using dom assms
  by (simp add: base_set_def)

lemma "carrier_total_space = \<pi> -` (\<Union>(base_set ` local_triv))"
  using carrier_total_space_def domain_local_triv by auto

lemma "carrier_base_space = \<Union>(base_set ` local_triv)"
  using base_set_def carrier_base_space_def
  by (smt (verit, best) Inf.INF_cong image_UN)

lemma "carrier_total_space = \<pi> -` carrier_base_space"
  using carrier_base_space_def carrier_total_space_def dom
  by auto

end

lift_definition trivial_trivialization :: "(('a:: topological_space) \<times> ('b :: topological_space), 'a \<times> 'b) chart" is
"(UNIV:: ('a \<times> 'b) set, UNIV:: ('a \<times> 'b) set, id:: ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b), id:: ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b))"
  by (metis (no_types, lifting) case_prodI eq_id_iff homeomorphism_ident mem_Collect_eq open_UNIV)
  
lemma trivial_bunlde_is_fiber_bundle' : "fiber_bundle' fst {trivial_trivialization}"
proof
  show "\<forall>f\<in>{trivial_trivialization}. domain f = fst -` fst ` codomain f"
    using domain_def codomain_def trivial_trivialization_def
  sorry
next
  show " \<forall>f\<in>{trivial_trivialization}. codomain f = fst ` codomain f \<times> UNIV"
    using codomain_def
    sorry
next
  show "\<forall>f\<in>{trivial_trivialization}. \<forall>x\<in>domain f. fst (apply_chart f x) = fst x"
    sorry
qed

end