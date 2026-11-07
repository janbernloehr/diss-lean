import NLS.KdV.PeriodOneEndpointExtract

/-! Physical reality and mean zero for the endpoint adapters, with both
norm comparisons and no change of any original distribution. -/
noncomputable section
open Set
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem periodOneEndpointOriginal_real_iff (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) :
    (periodOneEndpointOriginal r hr q).val=(periodOneEndpointOriginal r hr q).val.conjugate ↔
      ∀ n : ℤ, q.val (-n)=(starRingEnd ℂ) (q.val n) := by
  rw [Distribution.eq_conjugate_iff_coefficients]
  constructor
  · intro h n
    have hh := h (2*(-n))
    rw [periodOneEndpointOriginal_even,show 2*(-n)=-(2*n) by ring,periodOneEndpointOriginal_even] at hh
    simpa only [Complex.star_def] using hh
  · intro h k
    by_cases hk : k % 2=0
    · have he : k=2*(k/2) := by omega
      rw [he,periodOneEndpointOriginal_even,
        show 2*(k/2)=-(2*(-(k/2))) by ring,periodOneEndpointOriginal_even]
      simpa only [neg_neg,Complex.star_def] using h (-(k/2))
    · have he : k=2*(k/2)+1 := by omega
      rw [he,periodOneEndpointOriginal_odd,
        show 2*(k/2)+1=-(2*(-(k/2)-1)+1) by ring,periodOneEndpointOriginal_odd]
      exact (map_zero (starRingEnd ℂ)).symm

theorem periodOneEndpointOriginal_mean_zero_iff (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) :
    (periodOneEndpointOriginal r hr q).val (mode 0)=0 ↔ q.val 0=0 := by
  simpa only [mul_zero,neg_zero] using
    (show (periodOneEndpointOriginal r hr q).val (mode (-(2*0)))=0 ↔ q.val 0=0 from
      (periodOneEndpointOriginal_even r hr q 0).symm ▸ Iff.rfl)

theorem periodOneEndpointOriginal_source_iff (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) p) :
    (periodOneEndpointOriginal r hr q).val.IsRealMeanZeroPeriodOne ↔
      (∀ n : ℤ, q.val (-n)=(starRingEnd ℂ) (q.val n)) ∧ q.val 0=0 := by
  rw [Distribution.IsRealMeanZeroPeriodOne,periodOneEndpointOriginal_real_iff,
    periodOneEndpointOriginal_mean_zero_iff]
  exact and_congr_right fun _ => and_iff_left (periodOneEndpointOriginal_periodic r hr q)

theorem periodOneEndpointExtract_real (r : ℝ) (hr : 0 ≤ r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : q.val=q.val.conjugate) :
    ∀ n : ℤ, (periodOneEndpointExtract r hr q).val (-n)=
      (starRingEnd ℂ) ((periodOneEndpointExtract r hr q).val n) := by
  intro n
  have hh := (Distribution.eq_conjugate_iff_coefficients q.val q.val).mp hq (2*(-n))
  simpa only [periodOneEndpointExtract_apply,mul_neg,neg_neg,Complex.star_def] using hh

theorem norm_periodOneEndpointOriginal_bounds (r : ℝ) (hr : 0 ≤ r)
    (q : WeightedCoeff (Weight.sobolev (-r)) ⊤) :
    ‖periodOneEndpointOriginal r hr q‖ ≤ ‖q‖ ∧ ‖q‖ ≤ (2:ℝ)^r*‖periodOneEndpointOriginal r hr q‖ := by
  refine ⟨norm_periodOneEndpointOriginal_le r hr q,?_⟩
  have h := norm_periodOneEndpointExtract_le r hr (periodOneEndpointOriginal r hr q)
  rwa [periodOneEndpointExtract_original] at h

end NLS.KdV
