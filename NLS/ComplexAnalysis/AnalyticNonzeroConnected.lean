/-
Portions copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
The countable-complement proof is adapted from Mathlib and modified to
remain inside a convex open domain. This file is released under the
Apache 2.0 license, reproduced in LICENSES/Apache-2.0.txt.
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-! # Connected nonzero loci of complex analytic functions

The nonzero locus of a nontrivial scalar analytic function on an open
connected complex normed space domain is connected. On convex domains,
complex lines reduce the assertion to avoiding a countable discrete zero
set. A chain of open balls gives the general result.
-/
noncomputable section
open Set Metric
open scoped Convex
namespace NLS.ComplexAnalysis

/-- Removing a countable set from a nonempty convex open set in real
dimension greater than one preserves path connectedness.

The proof adapts Sébastien Gouëzel's Mathlib theorem
`Set.Countable.isPathConnected_compl_of_one_lt_rank` (Apache 2.0),
keeping the intermediate point inside the given open set. -/
theorem isPathConnected_convex_diff_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) {s U : Set E} (hs : s.Countable)
    (hU : IsOpen U) (hconv : Convex ℝ U) (hne : U.Nonempty) : IsPathConnected (U \ s) := by
  have : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans h)
  obtain ⟨a,ha,haU⟩ := (hs.dense_compl ℝ).exists_mem_open hU hne
  refine ⟨a,⟨haU,ha⟩,?_⟩
  intro b hb
  rcases hb with ⟨hbU,hb⟩
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ⟨haU,ha⟩
  let c := (2 : ℝ)⁻¹ • (a + b)
  let x := (2 : ℝ)⁻¹ • (b - a)
  have Ia : c - x = a := by
    simp only [c, x]
    module
  have Ib : c + x = b := by
    simp only [c, x]
    module
  have x_ne_zero : x ≠ 0 := by simpa [x] using sub_ne_zero.2 hab.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h x_ne_zero
  have A : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using ha
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  have hcU : c ∈ U := by
    let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
    simpa only [midpoint_eq_smul_add,invOf_eq_inv] using hconv.midpoint_mem haU hbU
  let T := {t : ℝ | c + t • y ∈ U}
  have hT : IsOpen T := hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hTne : T.Nonempty := ⟨0,by simpa [T] using hcU⟩
  obtain ⟨t,ht,hzU⟩ := ((A.union B).dense_compl ℝ).exists_mem_open hT hTne
  let z := c + t • y
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_nonempty_iff_eq_empty]
    at ht
  have JA : JoinedIn (U \ s) a z := by
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨hconv.segment_subset haU hzU hw,?_⟩
    have havoid : segment ℝ a z ⊆ sᶜ := by
      rw [subset_compl_iff_disjoint_right,disjoint_iff_inter_eq_empty]
      convert! ht.2
      exact Ia.symm
    exact havoid hw
  have JB : JoinedIn (U \ s) b z := by
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨hconv.segment_subset hbU hzU hw,?_⟩
    have havoid : segment ℝ b z ⊆ sᶜ := by
      rw [subset_compl_iff_disjoint_right,disjoint_iff_inter_eq_empty]
      convert! ht.1
      exact Ib.symm
    exact havoid hw
  exact JA.trans JB.symm

end NLS.ComplexAnalysis

namespace NLS.ComplexAnalysis
open Filter Topology

/-- On a convex open complex domain, a nontrivial analytic function has
a path-connected nonzero locus. -/
theorem isPathConnected_convex_analytic_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (a : E) (ha : a ∈ U) (hfa : f a ≠ 0) : IsPathConnected {x ∈ U | f x ≠ 0} := by
  refine ⟨a,⟨ha,hfa⟩,?_⟩
  intro b hb
  let e : ℂ → E := fun z => a+z • (b-a)
  have hec : Continuous e := continuous_const.add (continuous_id.smul continuous_const)
  have he0 : e 0 = a := by simp [e]
  have he1 : e 1 = b := by simp [e]
  let T := e ⁻¹' U
  have hT : IsOpen T := hU.preimage hec
  have h0 : (0 : ℂ) ∈ T := by change e 0 ∈ U; rwa [he0]
  have h1 : (1 : ℂ) ∈ T := by change e 1 ∈ U; rw [he1]; exact hb.1
  let eR : ℂ →ᵃ[ℝ] E := AffineMap.const ℝ ℂ a+
    ((LinearMap.toSpanSingleton ℂ E (b-a)).restrictScalars ℝ).toAffineMap
  have hcT : Convex ℝ T := hconv.affine_preimage eR
  have hfe : AnalyticOnNhd ℂ (f ∘ e) T := by
    intro z hz
    apply (hf _ hz).comp
    dsimp [e]
    fun_prop
  have hnz : (f ∘ e) 0 ≠ 0 := by simpa only [Function.comp_apply,he0] using hfa
  have hd := hfe.preimage_zero_mem_codiscreteWithin hnz h0 (hcT.isConnected ⟨0,h0⟩)
  have hdisc : IsDiscrete ((f ∘ e) ⁻¹' {0} ∩ T) := isDiscrete_of_codiscreteWithin (by simpa only [preimage_compl] using hd)
  have hcount : ((f ∘ e) ⁻¹' {0} ∩ T).Countable := IsLindelof.of_coe.countable_of_isDiscrete hdisc
  have hp := isPathConnected_convex_diff_countable
    (by simp [Complex.rank_real_complex]) hcount hT hcT ⟨0,h0⟩
  have h0' : (0 : ℂ) ∈ T \ ((f ∘ e) ⁻¹' {0} ∩ T) := by
    exact ⟨h0,fun h => hnz h.1⟩
  have h1' : (1 : ℂ) ∈ T \ ((f ∘ e) ⁻¹' {0} ∩ T) := by
    refine ⟨h1,fun h => hb.2 ?_⟩
    simpa only [mem_preimage,mem_singleton_iff,Function.comp_apply,he1] using h.1
  have hj := (hp.joinedIn 0 h0' 1 h1').map hec
  rw [he0,he1] at hj
  apply hj.mono
  rintro _ ⟨z,hz,rfl⟩
  refine ⟨hz.1,fun h => hz.2 ⟨h,hz.1⟩⟩
end NLS.ComplexAnalysis

namespace NLS.ComplexAnalysis
open Filter Topology Relation

/-- A nontrivial analytic function on a connected domain cannot vanish
on a nonempty open subset of that domain. -/
theorem analytic_exists_nonzero_in_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U V : Set E} (hc : IsConnected U) (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (a : E) (ha : a ∈ U) (hne : f a ≠ 0)
    (hV : IsOpen V) (hv : V.Nonempty) (hVU : V ⊆ U) : ∃ x ∈ V, f x ≠ 0 := by
  by_contra h
  have hz : ∀ x ∈ V, f x = 0 := by simpa using h
  obtain ⟨x,hx⟩ := hv
  have hg : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hz y hy
  exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected (hVU hx) hg ha)

/-- The nonzero locus of a nontrivial complex analytic function on an
open connected domain is connected, also in infinite dimension. -/
theorem isConnected_analytic_nonzero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (hU : IsOpen U) (hc : IsConnected U)
    (f : E → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (a : E) (ha : a ∈ U) (hfa : f a ≠ 0) : IsConnected {x ∈ U | f x ≠ 0} := by
  let B := {cr : E × ℝ // 0 < cr.2 ∧ ball cr.1 cr.2 ⊆ U}
  let s : B → Set E := fun b => ball b.val.1 b.val.2
  let t : B → Set E := fun b => {x ∈ s b | f x ≠ 0}
  have hs (b : B) : IsOpen (s b) := isOpen_ball
  have hne (b : B) : (s b).Nonempty := ⟨b.val.1,mem_ball_self b.property.1⟩
  have hunion : (⋃ b : B, s b) = U := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      exact b.property.2 hb
    · intro x hx
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
      exact mem_iUnion.mpr ⟨⟨(x,r),hr,hball⟩,mem_ball_self hr⟩
  have hB : Nonempty B := by
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
    exact ⟨⟨(a,r),hr,hball⟩⟩
  let : Nonempty B := hB
  have ht (b : B) : IsConnected (t b) := by
    obtain ⟨x,hx,hnx⟩ := analytic_exists_nonzero_in_open hc f hf a ha hfa (hs b) (hne b) b.property.2
    exact (isPathConnected_convex_analytic_nonzero (hs b) (convex_ball _ _)
      f (hf.mono b.property.2) x hx hnx).isConnected
  have hconn : IsPreconnected (⋃ b : B, s b) := hunion.symm ▸ hc.isPreconnected
  have hchain (i j : B) : ReflTransGen (fun i j : B => (t i ∩ t j).Nonempty) i j := by
    apply Relation.TransGen.to_reflTransGen
    apply Relation.TransGen.mono (r := fun i j : B => (s i ∩ s j).Nonempty) ?_ i j
      (hconn.transGen_of_iUnion hs i j (hne i) (hne j))
    intro b c hbc
    obtain ⟨x,hx,hnx⟩ := analytic_exists_nonzero_in_open hc f hf a ha hfa
      ((hs b).inter (hs c)) hbc (fun x hx => b.property.2 hx.1)
    exact ⟨x,⟨hx.1,hnx⟩,⟨hx.2,hnx⟩⟩
  have he : (⋃ b : B, t b) = {x ∈ U | f x ≠ 0} := by
    ext x
    simp only [t,mem_iUnion,mem_ofPred_eq]
    rw [exists_and_right,← mem_iUnion,hunion]
  rw [← he]
  exact IsConnected.iUnion_of_reflTransGen ht hchain
end NLS.ComplexAnalysis
