import NLS.ZakharovShabat.SourceBirkhoffMapReal
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.SequenceSpaces.RealCoeff

/-! # Theorem 15.2: the real analytic Birkhoff sequence map

The real restriction takes values in two actual real `ℓᵖ` spaces. Its
complex inclusion equals the constructed holomorphic map on every real
source. Restriction of scalars and bounded real linear coordinate maps
prove full real power-series analyticity.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real Birkhoff map, retaining the same normalized root family
as the complex map. -/
def sourceRealBirkhoffMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) :
    realTypeSourceSubmodule p → RealCoeff p × RealCoeff p :=
  fun φ => ((Coeff.reCLM p).prodMap (Coeff.reCLM p)) (sourceBirkhoffMap hp hp1 s φ.val)

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The complex map is an actual extension of the real map. -/
theorem real_map_complex_inclusion
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
      (sourceRealBirkhoffMap hp hp1 s φ) = sourceBirkhoffMap hp hp1 s φ.val := by
  apply Prod.ext
  · exact RealCoeff.complexCLM_reCLM p _ (fun n => (D.coordinates_im_eq_zero_of_realType φ.val φ.property n).1)
  · exact RealCoeff.complexCLM_reCLM p _ (fun n => (D.coordinates_im_eq_zero_of_realType φ.val φ.property n).2)

/-- Real analyticity on the complete real source space, for the full
sequence-valued map rather than only its individual coordinates. -/
theorem real_map_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℝ (sourceRealBirkhoffMap hp hp1 s) univ := by
  intro φ _
  have h := (D.analytic φ.val (D.real_subset φ.property)).restrictScalars (𝕜 := ℝ)
  have hsource := h.comp ((realTypeSourceSubmodule p).subtypeL.analyticAt (𝕜 := ℝ) (x := φ))
  exact (((Coeff.reCLM p).prodMap (Coeff.reCLM p)).analyticAt (𝕜 := ℝ) _).comp hsource

/-- The real rectangular action radius agrees with the original real action. -/
theorem real_map_action_radius
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ((sourceRealBirkhoffMap hp hp1 s φ).1 n)^2 +
      ((sourceRealBirkhoffMap hp hp1 s φ).2 n)^2 = 2 * (sourceRealAction hp hp1 φ.val φ.property n).re := by
  have h := D.action_radius φ.val (D.real_subset φ.property) n
  have hreal := D.coordinates_im_eq_zero_of_realType φ.val φ.property n
  have hI := sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property
  have hRe := congrArg Complex.re h
  rw [hI] at hRe
  simpa [sourceRealBirkhoffMap,pow_two,Complex.mul_re,hreal.1,hreal.2] using hRe

end SourceBirkhoffMapComplexData

/-- Theorem 15.2 at every finite exponent above one. The real analytic
map has the constructed complex analytic extension on a neighborhood
of the entire real source locus. -/
theorem exists_sourceBirkhoffMap_theorem15_2 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      AnalyticOnNhd ℝ (sourceRealBirkhoffMap hp hp1 s) univ ∧
      ∀ φ : realTypeSourceSubmodule p,
        ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
          (sourceRealBirkhoffMap hp hp1 s φ) = sourceBirkhoffMap hp hp1 s φ.val := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.real_map_analytic,D.real_map_complex_inclusion⟩

end NLS.ZakharovShabat
