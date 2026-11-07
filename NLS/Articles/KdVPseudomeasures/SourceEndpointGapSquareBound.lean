import NLS.Articles.KdVPseudomeasures.SpectralCanonicalGaps
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalGapSquares
import NLS.Articles.KdVPseudomeasures.OriginalEndpointRealCoordinates

/-! Uniform all-index bounds for the genuine analytic squared Hill gaps
on every original physical endpoint norm ball. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem originalPeriodOneCoefficients_sourceOriginalPotential (r : ℝ)
    (hr : AdmissiblePredualOrder r) (q : Potential r) :
    originalPeriodOneCoefficients (sourceOriginalPotential r hr q)=sourceNativePeriodOneCLM r hr q.val := rfl

theorem source_uniform_canonical_gapSquare_bound (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : Potential r, ‖q.val‖ ≤ R → ∀ n : ℕ+,
      ‖hillHminusCanonicalGapSquare n (sourceNativePeriodOneCLM r hr q.val)‖ ≤
        C^2*(1+(n:ℝ))^(2*r) := by
  obtain ⟨C,hC,hbound⟩ := source_uniform_canonical_gap_bound r hr R
  refine ⟨C,hC,?_⟩
  intro q hq n
  have hw : Weight.sobolev (-r) (n:ℤ)=((1+(n:ℝ))^r)⁻¹ := by
    rw [Weight.sobolev_apply]
    simp only [Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ)≤n)]
    exact Real.rpow_neg (by positivity) r
  have hg := WeightedCoeff.norm_apply_le (Weight.sobolev (-r)) ⊤ (sourceCanonicalGaps r hr q) (n:ℤ)
  rw [sourceCanonicalGaps_apply,hw,div_inv_eq_mul] at hg
  have hgle : ‖sourceCanonicalGapValues r hr q (n:ℤ)‖ ≤ C*(1+(n:ℝ))^r :=
    hg.trans (mul_le_mul_of_nonneg_right (hbound q hq) (Real.rpow_nonneg (by positivity) r))
  rw [← originalPeriodOneCoefficients_sourceOriginalPotential r hr q,originalCanonicalGapSquare_eq,
    originalCanonicalGapValues_sourceOriginalPotential,norm_pow]
  have hpow : ((1+(n:ℝ))^r)^2=(1+(n:ℝ))^(2*r) := by
    rw [← Real.rpow_two,← Real.rpow_mul (by positivity : (0:ℝ)≤1+(n:ℝ))]
    congr 1
    ring
  calc
    _ ≤ (C*(1+(n:ℝ))^r)^2 := pow_le_pow_left₀ (norm_nonneg _) hgle 2
    _ = _ := by rw [mul_pow,hpow]

end NLS.Articles.KdVPseudomeasures
