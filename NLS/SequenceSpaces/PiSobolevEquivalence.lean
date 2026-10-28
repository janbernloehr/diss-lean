import NLS.SequenceSpaces.WeightComparison
import NLS.SequenceSpaces.SpectralWeight

/-! # The source Sobolev normalization

The Section 6 bracket is `1 + |nπ|`. Its s-th power and `(1 + |n|)^s`
give coefficient-preserving equivalent spaces for `s ≥ 0`, with explicit
pair-norm factors 1 and `π^s` and the exact source Fourier power sum.
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source π-scaled Sobolev weight dominates the integer-scaled weight. -/
theorem sobolev_le_piSobolev (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    Weight.sobolev s n ≤ SpectralWeight.piSobolev s hs n := by
  simp only [Weight.sobolev_apply,SpectralWeight.piSobolev_apply,abs_mul,abs_of_pos Real.pi_pos]
  apply Real.rpow_le_rpow (by positivity) _ hs
  nlinarith [abs_nonneg (n : ℝ),Real.one_le_pi_div_two]

/-- The reverse Sobolev weight comparison has the explicit factor π^s. -/
theorem piSobolev_le_mul_sobolev (s : ℝ) (hs : 0 ≤ s) (n : ℤ) :
    SpectralWeight.piSobolev s hs n ≤ Real.pi^s * Weight.sobolev s n := by
  simp only [Weight.sobolev_apply,SpectralWeight.piSobolev_apply,abs_mul,abs_of_pos Real.pi_pos]
  calc
    _ ≤ (Real.pi*(1+|(n : ℝ)|))^s := by
      apply Real.rpow_le_rpow (by positivity) _ hs
      nlinarith [Real.one_le_pi_div_two]
    _ = _ := Real.mul_rpow Real.pi_pos.le (by positivity)

/-- Identify the two Sobolev normalizations without changing Fourier coefficients. -/
def piSobolevPairEquiv (s : ℝ) (hs : 0 ≤ s) :
    WeightedCoeffPair (Weight.sobolev s) p ≃L[ℂ] WeightedCoeffPair (SpectralWeight.piSobolev s hs).toWeight p :=
  WeightComparison.pairEquiv _ _ (Real.pi^s) 1 (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one
    (piSobolev_le_mul_sobolev s hs) (by simpa using sobolev_le_piSobolev s hs)

/-- The first component keeps its original Fourier indices and coefficients. -/
@[simp] theorem piSobolevPairEquiv_fst (s : ℝ) (hs : 0 ≤ s) (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    (piSobolevPairEquiv s hs a).fst.val n = a.fst.val n := by
  exact WeightComparison.equiv_apply _ _ (Real.pi^s) 1 (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one
    (piSobolev_le_mul_sobolev s hs) (by simpa using sobolev_le_piSobolev s hs) a.fst n

/-- The second component keeps its original Fourier indices and coefficients. -/
@[simp] theorem piSobolevPairEquiv_snd (s : ℝ) (hs : 0 ≤ s) (a : WeightedCoeffPair (Weight.sobolev s) p) (n : ℤ) :
    (piSobolevPairEquiv s hs a).snd.val n = a.snd.val n := by
  exact WeightComparison.equiv_apply _ _ (Real.pi^s) 1 (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one
    (piSobolev_le_mul_sobolev s hs) (by simpa using sobolev_le_piSobolev s hs) a.snd n

/-- The inverse identification preserves the first component. -/
@[simp] theorem piSobolevPairEquiv_symm_fst (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeffPair (SpectralWeight.piSobolev s hs).toWeight p) (n : ℤ) :
    ((piSobolevPairEquiv s hs).symm a).fst.val n = a.fst.val n := by
  exact WeightComparison.equiv_symm_apply _ _ (Real.pi^s) 1 (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one
    (piSobolev_le_mul_sobolev s hs) (by simpa using sobolev_le_piSobolev s hs) a.fst n

/-- The inverse identification preserves the second component. -/
@[simp] theorem piSobolevPairEquiv_symm_snd (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeffPair (SpectralWeight.piSobolev s hs).toWeight p) (n : ℤ) :
    ((piSobolevPairEquiv s hs).symm a).snd.val n = a.snd.val n := by
  exact WeightComparison.equiv_symm_apply _ _ (Real.pi^s) 1 (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one
    (piSobolev_le_mul_sobolev s hs) (by simpa using sobolev_le_piSobolev s hs) a.snd n

/-- The two original p-sum Sobolev norms differ by at most π^s. -/
theorem piSobolevPairEquiv_norm_bounds (hp : p ≠ ⊤) (s : ℝ) (hs : 0 ≤ s) (a : WeightedCoeffPair (Weight.sobolev s) p) :
    ‖a‖ ≤ ‖piSobolevPairEquiv s hs a‖ ∧ ‖piSobolevPairEquiv s hs a‖ ≤ Real.pi^s*‖a‖ := by
  constructor
  · have h := WeightComparison.norm_pairEquiv_symm_le hp _ _ (Real.pi^s) 1
      (Real.rpow_nonneg Real.pi_pos.le s) zero_le_one (piSobolev_le_mul_sobolev s hs)
      (by simpa using sobolev_le_piSobolev s hs) (piSobolevPairEquiv s hs a)
    change ‖(piSobolevPairEquiv s hs).symm (piSobolevPairEquiv s hs a)‖ ≤ 1*‖piSobolevPairEquiv s hs a‖ at h
    simpa only [ContinuousLinearEquiv.symm_apply_apply,one_mul] using h
  · exact WeightComparison.norm_pairEquiv_le hp _ _ _ _ _ _ _ _ a

/-- The source Sobolev norm is exactly the full signed Fourier power sum with bracket 1+|nπ|. -/
theorem piSobolevPairEquiv_norm_rpow_eq_tsum (hp : p ≠ ⊤) (s : ℝ) (hs : 0 ≤ s)
    (a : WeightedCoeffPair (Weight.sobolev s) p) :
    ‖piSobolevPairEquiv s hs a‖^p.toReal = ∑' n : ℤ, (1+|(n : ℝ)*Real.pi|)^(s*p.toReal) *
      (‖a.fst.val n‖^p.toReal+‖a.snd.val n‖^p.toReal) := by
  rw [WeightedCoeffPair.norm_rpow_eq_tsum hp]
  simp only [SpectralWeight.piSobolev_apply,piSobolevPairEquiv_fst,piSobolevPairEquiv_snd]
  apply tsum_congr
  intro n
  rw [← Real.rpow_mul (by positivity : 0 ≤ 1+|(n : ℝ)*Real.pi|)]

end NLS.SpectralWeight
