import NLS.ZakharovShabat.SourceHigherSobolevHigherActionBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic higher-action sequences and sums on Hˢ

The levels 1 through 2s+1 form actual ℓ¹-valued analytic maps. Bounded linear
summation then proves analyticity of the literal infinite series.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable (s : ℕ)

def sourceHigherSobolevHigherActionSequence (k : ℕ) (a : SobolevSource s) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s a))

/-- One Hˢ neighborhood carries all 2s+1 analytic ℓ¹-valued maps, with
exact coordinates rather than the constructor's off-domain fallback. -/
theorem exists_local_sourceHigherSobolevHigherActionSequence_analytic
    (a : SobolevSource s)
    (ha : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a ∈ U ∧ ∀ k : ℕ, k ≤ 2*s →
      (∀ b ∈ U, ∀ n : ℤ, sourceHigherSobolevHigherActionSequence s k b n =
        sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)) ∧
      AnalyticOnNhd ℂ (sourceHigherSobolevHigherActionSequence s k) U := by
  let L := higherSobolevSourceInclusion s
  obtain ⟨V,hV,haV,C,hbound⟩ := exists_local_sourceHigherSobolevHigherAction_bound s a ha
  let W := sourceComplexHigherActionDomain (p := 2) (by simp) (by norm_num)
  let U := V ∩ L ⁻¹' W
  have hW : IsOpen W := isOpen_sourceComplexHigherActionDomain _ _
  have hU : IsOpen U := hV.inter (hW.preimage L.continuous)
  refine ⟨U,hU,⟨haV,realType_subset_sourceComplexHigherActionDomain _ _ ha⟩,?_⟩
  intro k hk
  have he (b : SobolevSource s) (hb : b ∈ U) (n : ℤ) :
      sourceHigherSobolevHigherActionSequence s k b n = sourceComplexHigherAction (by simp) (by norm_num) n k (L b) := by
    obtain ⟨g,hg,_⟩ := hbound b hb.1 k hk
    rw [sourceHigherSobolevHigherActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
    exact hg n
  refine ⟨he,Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU ?_ C ?_⟩
  · intro n b hb
    have h := (analyticOnNhd_sourceComplexHigherAction (by simp) (by norm_num) n k (L b) hb.2).comp (L.analyticAt b)
    apply h.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    exact (he c hc n).symm
  · intro b hb
    obtain ⟨g,hg,hgn⟩ := hbound b hb.1 k hk
    rwa [sourceHigherSobolevHigherActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]

/-- Absolute convergence and analyticity hold for the literal higher-action
series on a complex Hˢ neighborhood, through level 2s+1. -/
theorem exists_local_sourceHigherSobolevHigherAction_tsum_analytic
    (a : SobolevSource s)
    (ha : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a ∈ U ∧ ∀ k : ℕ, k ≤ 2*s →
      (∀ b ∈ U, Summable (fun n : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)‖)) ∧
      AnalyticOnNhd ℂ (fun b : SobolevSource s =>
        ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)) U := by
  obtain ⟨U,hU,haU,hseq⟩ := exists_local_sourceHigherSobolevHigherActionSequence_analytic s a ha
  refine ⟨U,hU,haU,?_⟩
  intro k hk
  obtain ⟨he,hA⟩ := hseq k hk
  constructor
  · intro b hb
    simpa only [he b hb] using (sourceHigherSobolevHigherActionSequence s k b).property.norm.summable_of_one
  · intro b hb
    have h := (lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd hA b hb
    apply h.congr
    filter_upwards [hU.mem_nhds hb] with c hc
    exact tsum_congr (he c hc)

theorem analyticAt_tsum_sourceHigherSobolevHigherAction
    (a : SobolevSource s)
    (ha : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))) (k : ℕ) (hk : k ≤ 2*s) :
    AnalyticAt ℂ (fun b : SobolevSource s =>
      ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)) a := by
  obtain ⟨U,_,haU,h⟩ := exists_local_sourceHigherSobolevHigherAction_tsum_analytic s a ha
  exact (h k hk).2 a haU

/-- A single open complex Hˢ domain contains the entire real Hˢ locus and
carries all defining absolutely convergent analytic sums through level 2s+1. -/
theorem exists_sourceHigherSobolevHigherAction_domain :
    ∃ U : Set (SobolevSource s), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))} ⊆ U ∧
      ∀ k : ℕ, k ≤ 2*s →
        (∀ b ∈ U, Summable (fun n : ℤ =>
          ‖sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)‖)) ∧
        AnalyticOnNhd ℂ (fun b : SobolevSource s =>
          ∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s b)) U := by
  let R := {a : SobolevSource s // IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))}
  have hlocal (a : R) := exists_local_sourceHigherSobolevHigherAction_tsum_analytic s a.val a.property
  choose V hV haV hsum using hlocal
  refine ⟨⋃ a : R, V a,isOpen_iUnion hV,?_,?_⟩
  · intro a ha
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,haV ⟨a,ha⟩⟩
  · intro k hk
    constructor
    · intro b hb
      obtain ⟨a,ha⟩ := mem_iUnion.mp hb
      exact (hsum a k hk).1 b ha
    · intro b hb
      obtain ⟨a,ha⟩ := mem_iUnion.mp hb
      exact (hsum a k hk).2 b ha

end NLS.ZakharovShabat
