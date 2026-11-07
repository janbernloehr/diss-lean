import NLS.KdV.PeriodOneHminusOneOriginal
import NLS.SequenceSpaces.WeightedWeakStarLowerTopology

/-! Literal unit-period endpoint coefficients as original period-two
Fourier-Lebesgue distributions. Original even modes and physical period
one are preserved, at every Banach exponent including infinity. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def periodOneEndpointWeight (r : ℝ) : Weight :=
  (Weight.sobolev (-r)).pullback (Coeff.parityEmbedding 0)

theorem periodOneEndpointWeight_le (r : ℝ) (hr : 0 ≤ r) (n : ℤ) :
    periodOneEndpointWeight r n ≤ Weight.sobolev (-r) n := by
  simp only [periodOneEndpointWeight,Weight.pullback_apply,Coeff.parityEmbedding_apply,add_zero,
    Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_nonneg (n:ℝ)]) (neg_nonpos.mpr hr)

def periodOneEndpointCoefficients (r : ℝ) (hr : 0 ≤ r) :
    WeightedCoeff (Weight.sobolev (-r)) p →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) p :=
  (WeightedCoeff.insertIsometry (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)).toContinuousLinearMap.comp
    (WeightedCoeff.inclusionCLM _ _ (periodOneEndpointWeight_le r hr))

theorem periodOneEndpointCoefficients_even (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) (n : ℤ) :
    (periodOneEndpointCoefficients r hr q).val (2*n)=q.val n := by
  change (WeightedCoeff.insertIsometry (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM _ _ (periodOneEndpointWeight_le r hr) q)).val (2*n)=q.val n
  have h := WeightedCoeff.insertIsometry_image (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM _ _ (periodOneEndpointWeight_le r hr) q) n
  simpa only [Coeff.parityEmbedding_apply,
    add_zero,WeightedCoeff.inclusionCLM_apply] using h

theorem periodOneEndpointCoefficients_odd (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) (n : ℤ) :
    (periodOneEndpointCoefficients r hr q).val (2*n+1)=0 := by
  change (WeightedCoeff.insertIsometry (Weight.sobolev (-r)) (Coeff.parityEmbedding 0)
    (WeightedCoeff.inclusionCLM _ _ (periodOneEndpointWeight_le r hr) q)).val (2*n+1)=0
  dsimp only [periodOneEndpointWeight]
  apply WeightedCoeff.insertIsometry_outside
  rintro ⟨k,hk⟩
  change 2*k+0=2*n+1 at hk
  omega

def periodOneEndpointOriginal (r : ℝ) (hr : 0 ≤ r) :
    WeightedCoeff (Weight.sobolev (-r)) p →L[ℂ] FourierLebesgueSpace (2:ℝ) (-r) p :=
  (sobolevCoefficients (-r) p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodOneEndpointCoefficients r hr)

theorem periodOneEndpointOriginal_even (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) (n : ℤ) :
    (periodOneEndpointOriginal r hr q).val (mode (-(2*n)))=q.val n := by
  change ((sobolevCoefficients (-r) p) ((sobolevCoefficients (-r) p).symm _)).val (2*n)=_
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneEndpointCoefficients_even r hr q n

theorem periodOneEndpointOriginal_odd (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) (n : ℤ) :
    (periodOneEndpointOriginal r hr q).val (mode (-(2*n+1)))=0 := by
  change ((sobolevCoefficients (-r) p) ((sobolevCoefficients (-r) p).symm _)).val (2*n+1)=_
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneEndpointCoefficients_odd r hr q n

theorem periodOneEndpointOriginal_periodic (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) :
    IsPeriodicDistribution 1 (periodOneEndpointOriginal r hr q).val.toTempered :=
  (Distribution.toTempered_period_one_iff_odd _).mpr (periodOneEndpointOriginal_odd r hr q)

theorem norm_periodOneEndpointOriginal_le (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) : ‖periodOneEndpointOriginal r hr q‖ ≤ ‖q‖ := by
  change ‖(sobolevCoefficients (-r) p).symm _‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  change ‖WeightedCoeff.insertIsometry _ _ (WeightedCoeff.inclusionCLM _ _ (periodOneEndpointWeight_le r hr) q)‖ ≤ _
  dsimp only [periodOneEndpointWeight]
  rw [WeightedCoeff.norm_insertIsometry]
  exact WeightedCoeff.norm_inclusionCLM_le _ _ _ q

end NLS.KdV
