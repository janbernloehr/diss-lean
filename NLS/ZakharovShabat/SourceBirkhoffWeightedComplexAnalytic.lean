import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexBound
import NLS.ZakharovShabat.SourceBirkhoffWeightedCanonical

/-! # The original Birkhoff map is analytic in every spectral weight

The constructed local complex bounds give one common open weighted domain
containing the entire weighted real source. The full native weighted map
is complex analytic and preserves the original coordinate values.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex map on native weighted spaces, retaining the original raw output coefficients. -/
def originalWeightedBirkhoffMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) : WeightedCoeffPair (sourceFrequencyWeight w) p :=
  (sourcePairWeightCoordinates w).symm ((CoeffPair.toMax p).symm
    (normalizedWeightedBirkhoffMap hp hp1 s w (sourcePairWeightCoordinates w a)))

private theorem pullback_open_domain {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (J : E → F) (hJ : Continuous J) (U : Set F) (hU : IsOpen U) :
    ∃ V : Set E, IsOpen V ∧ ∀ a, a ∈ V ↔ J a ∈ U :=
  ⟨J ⁻¹' U,hU.preimage hJ,fun _ => Iff.rfl⟩

private theorem analytic_linear_transport
    {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (J : E →L[ℂ] F) (L : G →L[ℂ] H) (f : F → G)
    (U : Set F) (V : Set E) (hf : AnalyticOnNhd ℂ f U) (hV : ∀ a ∈ V, J a ∈ U) :
    AnalyticOnNhd ℂ (fun a => L (f (J a))) V := by
  intro a ha
  exact (L.analyticAt _).comp (f := fun b => f (J b))
    ((hf _ (hV a ha)).compContinuousLinearMap (u := J))

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A common complex analytic domain for the normalized weighted map. -/
theorem exists_normalizedWeightedBirkhoffMap_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      (∀ ψ ∈ V, normalizedWeightedSource w ψ ∈ W) ∧
      AnalyticOnNhd ℂ (normalizedWeightedBirkhoffMap hp hp1 s w) V ∧
      ∀ ψ ∈ V, ∀ n : ℤ,
        (normalizedWeightedBirkhoffMap hp hp1 s w ψ).1 n =
          (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n ∧
        (normalizedWeightedBirkhoffMap hp hp1 s w ψ).2 n =
          (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n := by
  choose U hoU hφU hUW M hM hbound using D.exists_local_normalizedWeightedBirkhoffMap_bound w
  let V := ⋃ φ : realTypeSourceLocus p, U φ
  refine ⟨V,isOpen_iUnion hoU,(fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφU ⟨ψ,hψ⟩⟩),?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact hUW φ ψ hφ
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact D.normalizedWeightedBirkhoffMap_analytic_of_bound w (U φ) (hoU φ) (hUW φ)
      (fun χ hχ => (hbound φ χ hχ).1) (M φ) (fun χ hχ => (hbound φ χ hχ).2) ψ hφ
  · intro ψ hψ n
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
    exact normalizedWeightedBirkhoffMap_apply_of_mem hp hp1 s w ψ
      (hbound φ ψ hφ).1.1 (hbound φ ψ hφ).1.2 n

/-- Full native weighted analyticity with exact original complex coordinate values. -/
theorem exists_originalWeightedBirkhoffMap_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    ∃ V : Set (WeightedCoeffPair (sourceFrequencyWeight w) p), IsOpen V ∧
      (∀ a : weightedRealSourceSubmodule (p := p) w, a.val ∈ V) ∧
      (∀ a ∈ V, originalWeightedSourceCLM w a ∈ W) ∧
      AnalyticOnNhd ℂ (originalWeightedBirkhoffMap hp hp1 s w) V ∧
      ∀ a ∈ V, ∀ n : ℤ,
        (originalWeightedBirkhoffMap hp hp1 s w a).fst.val n =
          (sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a)).1 n ∧
        (originalWeightedBirkhoffMap hp hp1 s w a).snd.val n =
          (sourceBirkhoffMap hp hp1 s (originalWeightedSourceCLM w a)).2 n := by
  obtain ⟨U,hoU,hreal,hUW,hA,hcoord⟩ := D.exists_normalizedWeightedBirkhoffMap_analytic w
  let J := (sourcePairWeightCoordinates (p := p) w).toContinuousLinearEquiv.toContinuousLinearMap
  let L := (sourcePairWeightCoordinates (p := p) w).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (CoeffPair.toMax p).symm.toContinuousLinearMap
  obtain ⟨V,hoV,hV⟩ := pullback_open_domain J J.continuous U hoU
  refine ⟨V,hoV,(fun a => (hV a.val).mpr (hreal (weightedRealSourceEquiv w a).property)),
    (fun a ha => hUW _ ((hV a).mp ha)),?_,?_⟩
  · exact analytic_linear_transport J L (normalizedWeightedBirkhoffMap hp hp1 s w)
      U V hA (fun a ha => (hV a).mp ha)
  · intro a ha n
    have hc := hcoord (J a) ((hV a).mp ha) n
    constructor
    · change (normalizedWeightedBirkhoffMap hp hp1 s w (J a)).1 n / (w (2*n):ℂ) = _
      rw [hc.1,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
      rfl
    · change (normalizedWeightedBirkhoffMap hp hp1 s w (J a)).2 n / (w (2*n):ℂ) = _
      rw [hc.2,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
      rfl

/-- The native complex map extends the actual original weighted real map. -/
theorem originalWeightedBirkhoffMap_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (originalWeightedBirkhoffMap hp hp1 s w a.val).fst.val n = (D.originalWeightedRealMap w a).fst.val.val n ∧
    (originalWeightedBirkhoffMap hp hp1 s w a.val).snd.val n = (D.originalWeightedRealMap w a).snd.val.val n := by
  obtain ⟨V,_,hreal,_,_,hcoord⟩ := D.exists_originalWeightedBirkhoffMap_analytic w
  have h := hcoord a.val (hreal a) n
  exact ⟨h.1.trans (D.originalWeightedBirkhoff_real w a n).1,
    h.2.trans (D.originalWeightedBirkhoff_real w a n).2⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
