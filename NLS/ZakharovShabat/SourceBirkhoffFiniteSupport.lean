import NLS.ZakharovShabat.SourceBirkhoffProposition17_1
import NLS.ZakharovShabat.SourceFiniteGapHilbertRealization
import NLS.SequenceSpaces.RealCoeffTruncation

/-! # Finite Birkhoff output support characterizes finite-gap sources

This concerns the nonlinear output coordinates, not finite support of
the source's Fourier coefficients. The action-radius identity and the
zero-action characterization identify its support with the open gaps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Both real coordinates vanish exactly at a collapsed periodic gap. -/
theorem real_coordinates_zero_iff_gap_zero
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ((sourceRealBirkhoffMap hp hp1 s φ).1 n = 0 ∧
      (sourceRealBirkhoffMap hp hp1 s φ).2 n = 0) ↔
      sourcePeriodicGapDisplacement hp hp1 φ.val n = 0 := by
  have ha := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ.val φ.property n
  have hr := D.real_map_action_radius φ n
  constructor
  · rintro ⟨hx,hy⟩
    apply ha.2.2.mp
    apply Complex.ext
    · simp only [hx,hy,zero_pow (by norm_num : 2 ≠ 0),zero_add] at hr
      change (sourceRealAction hp hp1 φ.val φ.property n).re = 0
      linarith
    · exact ha.2.1
  · intro hgap
    have hz := ha.2.2.mpr hgap
    rw [hz, Complex.zero_re, mul_zero] at hr
    have hx := sq_nonneg ((sourceRealBirkhoffMap hp hp1 s φ).1 n)
    have hy := sq_nonneg ((sourceRealBirkhoffMap hp hp1 s φ).2 n)
    constructor <;> nlinarith

/-- Open gaps are exactly the support of the real nonlinear output. -/
theorem real_map_pairSupport
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    RealCoeff.pairSupport (sourceRealBirkhoffMap hp hp1 s φ) =
      {n | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0} := by
  ext n
  have h := D.real_coordinates_zero_iff_gap_zero φ n
  rw [sourcePeriodicGapDisplacement_apply] at h
  change (_ ≠ 0 ∨ _ ≠ 0) ↔ _ ≠ 0
  tauto

/-- Actual finite-gap sources are exactly those with finitely supported Birkhoff output. -/
theorem finiteGap_iff_finite_pairSupport
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) :
    φ ∈ sourceFiniteGapLocus hp hp1 ↔
      (RealCoeff.pairSupport (sourceRealBirkhoffMap hp hp1 s φ)).Finite := by
  rw [D.real_map_pairSupport φ]
  rfl

/-- Any source mapped to a finite output truncation is finite-gap. -/
theorem finiteGap_of_real_map_eq_truncatePair
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ) (z : RealCoeff p × RealCoeff p)
    (h : sourceRealBirkhoffMap hp hp1 s φ = RealCoeff.truncatePair S z) :
    φ ∈ sourceFiniteGapLocus hp hp1 := by
  apply (D.finiteGap_iff_finite_pairSupport φ).mpr
  rw [h]
  exact RealCoeff.finite_pairSupport_truncatePair S z

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
