import NLS.KdV.PeriodOneHminusOneOriginal

/-! Transfer unit-period coefficient regularity to the identical entire
original period-two smooth-test distribution. Negative Sobolev weights
decrease under the original even-index insertion. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem sobolev_even_weight_le_of_nonpos (s : ℝ) (hs : s ≤ 0) (n : ℤ) :
    Weight.sobolev s (2*n) ≤ Weight.sobolev s n := by
  simp only [Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_nonneg (n:ℝ)]) hs

/-- Extra finite-p regularity of the raw unit-period coefficients gives
an original physical representative with the same entire distribution. -/
theorem exists_periodOneOriginal_regular_realization (q : PeriodOneHminusOne)
    (s : ℝ) (hs : s ≤ 0) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hreg : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*q.val n) p) :
    ∃ Q : FourierLebesgueSpace (2:ℝ) s p, Q.val = (periodOneOriginal q).val := by
  let a : WeightedCoeff (Weight.sobolev s) p := ⟨q.val,hreg⟩
  let e := Coeff.parityEmbedding 0
  have hw (n : ℤ) : (Weight.sobolev s).pullback e n ≤ Weight.sobolev s n := by
    simpa only [Weight.pullback_apply,e,Coeff.parityEmbedding_apply,add_zero] using
      sobolev_even_weight_le_of_nonpos s hs n
  let b := WeightedCoeff.insertIsometry (Weight.sobolev s) e
    (WeightedCoeff.inclusionCLM (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw a)
  let Q : FourierLebesgueSpace (2:ℝ) s p := (sobolevCoefficients s p).symm b
  refine ⟨Q,?_⟩
  have hQ (k : ℤ) : Q.val (mode (-k)) = b.val k := by
    change ((sobolevCoefficients s p) ((sobolevCoefficients s p).symm b)).val k = _
    rw [LinearIsometryEquiv.apply_symm_apply]
  apply Distribution.ext_coefficients
  intro k
  rw [hQ]
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,periodOneOriginal_even]
    have hh := WeightedCoeff.insertIsometry_image (Weight.sobolev s) e
      (WeightedCoeff.inclusionCLM (Weight.sobolev s) ((Weight.sobolev s).pullback e) hw a) (k/2)
    have hi := WeightedCoeff.inclusionCLM_apply (Weight.sobolev s)
      ((Weight.sobolev s).pullback e) hw a (k/2)
    have ht := hh.trans hi
    simpa only [e,Coeff.parityEmbedding_apply,add_zero,b,a] using ht
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,periodOneOriginal_odd]
    apply WeightedCoeff.insertIsometry_outside
    rintro ⟨j,hj⟩
    change 2*j+0 = 2*(k/2)+1 at hj
    omega

end NLS.KdV
