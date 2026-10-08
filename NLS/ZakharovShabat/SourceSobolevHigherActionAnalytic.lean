import NLS.ZakharovShabat.SourceSobolevHigherActionBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic higher-action sequences and sums on H¹

The first three levels form actual ℓ¹-valued analytic maps. Bounded linear
summation then proves analyticity of the literal infinite series.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceSobolevHigherActionSequence (k : ℕ) (a : ScalarDomain 2 × ScalarDomain 2) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion a))

/-- One H¹ neighborhood carries all three analytic ℓ¹-valued maps, with
exact coordinates rather than the constructor's off-domain fallback. -/
theorem exists_local_sourceSobolevHigherActionSequence_analytic
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧ ∀ k : ℕ, k ≤ 2 →
      (∀ b ∈ U, ∀ n : ℤ, sourceSobolevHigherActionSequence k b n =
        sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) ∧
      AnalyticOnNhd ℂ (sourceSobolevHigherActionSequence k) U := by
  let L := sobolevSourceInclusion
  obtain ⟨V,hV,haV,C,hbound⟩ := exists_local_sourceSobolevHigherAction_bound a ha
  let W := sourceComplexHigherActionDomain (p := 2) (by simp) (by norm_num)
  let U := V ∩ L ⁻¹' W
  have hW : IsOpen W := isOpen_sourceComplexHigherActionDomain _ _
  have hU : IsOpen U := hV.inter (hW.preimage L.continuous)
  refine ⟨U,hU,⟨haV,realType_subset_sourceComplexHigherActionDomain _ _ ha⟩,?_⟩
  intro k hk
  have he (b : ScalarDomain 2 × ScalarDomain 2) (hb : b ∈ U) (n : ℤ) :
      sourceSobolevHigherActionSequence k b n = sourceComplexHigherAction (by simp) (by norm_num) n k (L b) := by
    obtain ⟨g,hg,_⟩ := hbound b hb.1 k hk
    rw [sourceSobolevHigherActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
    exact hg n
  refine ⟨he,Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU ?_ C ?_⟩
  · intro n b hb
    have h := (analyticOnNhd_sourceComplexHigherAction (by simp) (by norm_num) n k (L b) hb.2).comp (L.analyticAt b)
    apply h.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    exact (he c hc n).symm
  · intro b hb
    obtain ⟨g,hg,hgn⟩ := hbound b hb.1 k hk
    rwa [sourceSobolevHigherActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]

/-- Absolute convergence and analyticity hold for the literal higher-action
series on a complex H¹ neighborhood, through level three. -/
theorem exists_local_sourceSobolevHigherAction_tsum_analytic
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧ ∀ k : ℕ, k ≤ 2 →
      (∀ b ∈ U, Summable (fun n : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)‖)) ∧
      AnalyticOnNhd ℂ (fun b : ScalarDomain 2 × ScalarDomain 2 =>
        ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) U := by
  obtain ⟨U,hU,haU,hseq⟩ := exists_local_sourceSobolevHigherActionSequence_analytic a ha
  refine ⟨U,hU,haU,?_⟩
  intro k hk
  obtain ⟨he,hA⟩ := hseq k hk
  constructor
  · intro b hb
    simpa only [he b hb] using (sourceSobolevHigherActionSequence k b).property.norm.summable_of_one
  · intro b hb
    have h := (lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd hA b hb
    apply h.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    exact tsum_congr (he c hc)

theorem analyticAt_tsum_sourceSobolevHigherAction
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) (k : ℕ) (hk : k ≤ 2) :
    AnalyticAt ℂ (fun b : ScalarDomain 2 × ScalarDomain 2 =>
      ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) a := by
  obtain ⟨U,_,haU,h⟩ := exists_local_sourceSobolevHigherAction_tsum_analytic a ha
  exact (h k hk).2 a haU

end NLS.ZakharovShabat
