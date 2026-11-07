import NLS.KdV.PeriodOneOriginalRegularity

/-! Continuous insertion of unit-period Sobolev coefficients into the exact
original period-two distribution space, with every even coefficient retained
and every odd coefficient zero. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original period-one insertion at every nonpositive Sobolev order. -/
def periodOneOriginalSobolev (s : ℝ) (hs : s ≤ 0) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ] FourierLebesgueSpace (2:ℝ) s p :=
  let e := Coeff.parityEmbedding 0
  let hw := fun n : ℤ => (show (Weight.sobolev s).pullback e n ≤ Weight.sobolev s n from by
    simpa only [Weight.pullback_apply,e,Coeff.parityEmbedding_apply,add_zero] using
      sobolev_even_weight_le_of_nonpos s hs n)
  ((sobolevCoefficients s p).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((WeightedCoeff.insertIsometry (Weight.sobolev s) e).toContinuousLinearMap.comp
      (WeightedCoeff.inclusionCLM (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw))

/-- The continuous insertion retains every original unit-period Fourier mode. -/
theorem periodOneOriginalSobolev_even (s : ℝ) (hs : s ≤ 0)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (periodOneOriginalSobolev s hs a).val (mode (-(2*n))) = a.val n := by
  let e := Coeff.parityEmbedding 0
  have hw (k : ℤ) : (Weight.sobolev s).pullback e k ≤ Weight.sobolev s k := by
    simpa only [Weight.pullback_apply,e,Coeff.parityEmbedding_apply,add_zero] using
      sobolev_even_weight_le_of_nonpos s hs k
  let z := WeightedCoeff.inclusionCLM (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw a
  let b := WeightedCoeff.insertIsometry (Weight.sobolev s) e z
  have he : (sobolevCoefficients s p (periodOneOriginalSobolev s hs a)) = b := by
    change (sobolevCoefficients s p) ((sobolevCoefficients s p).symm b) = b
    exact (sobolevCoefficients s p).apply_symm_apply b
  have hn := congrArg (fun v : WeightedCoeff (Weight.sobolev s) p => v.val (2*n)) he
  have hi := (WeightedCoeff.insertIsometry_image (Weight.sobolev s) e z n).trans
    (WeightedCoeff.inclusionCLM_apply (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw a n)
  exact hn.trans (by simpa only [e,Coeff.parityEmbedding_apply,add_zero,b] using hi)

/-- All odd original period-two modes vanish in the period-one realization. -/
theorem periodOneOriginalSobolev_odd (s : ℝ) (hs : s ≤ 0)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    (periodOneOriginalSobolev s hs a).val (mode (-(2*n+1))) = 0 := by
  let e := Coeff.parityEmbedding 0
  have hw (k : ℤ) : (Weight.sobolev s).pullback e k ≤ Weight.sobolev s k := by
    simpa only [Weight.pullback_apply,e,Coeff.parityEmbedding_apply,add_zero] using
      sobolev_even_weight_le_of_nonpos s hs k
  let z := WeightedCoeff.inclusionCLM (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw a
  let b := WeightedCoeff.insertIsometry (Weight.sobolev s) e z
  have he : (sobolevCoefficients s p (periodOneOriginalSobolev s hs a)) = b := by
    change (sobolevCoefficients s p) ((sobolevCoefficients s p).symm b) = b
    exact (sobolevCoefficients s p).apply_symm_apply b
  have hn := congrArg (fun v : WeightedCoeff (Weight.sobolev s) p => v.val (2*n+1)) he
  have hout : 2*n+1 ∉ range e := by
    rintro ⟨j,hj⟩
    change 2*j+0 = 2*n+1 at hj
    omega
  exact hn.trans (WeightedCoeff.insertIsometry_outside (Weight.sobolev s) e z (2*n+1) hout)

/-- The Sobolev insertion represents the identical entire H-minus-one
distribution whenever its raw unit-period coefficients agree. -/
theorem periodOneOriginalSobolev_val (s : ℝ) (hs : s ≤ 0)
    (a : WeightedCoeff (Weight.sobolev s) p) (q : PeriodOneHminusOne)
    (ha : a.val = q.val) :
    (periodOneOriginalSobolev s hs a).val = (periodOneOriginal q).val := by
  apply Distribution.ext_coefficients
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,periodOneOriginalSobolev_even,periodOneOriginal_even,ha]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,periodOneOriginalSobolev_odd,periodOneOriginal_odd]

end NLS.KdV
