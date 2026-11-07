import NLS.Articles.KdVPseudomeasures.SpectralAdaptedInverse
import NLS.KdV.PseudomeasureDiagonalRootConjugation
import NLS.SequenceSpaces.EvenTailConjugation

/-! Physical real-type symmetry of the actual diagonal root and adapted map.
All conjugations are on the original smooth-test distributions. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue NLS.KdV

/-- Physical conjugation in the exact original weighted source space. -/
def sourceWeightedConjugate (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ :=
  conjugate _ (w.negativeSobolev_neg r) q

@[simp] theorem sourceWeightedConjugate_val (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    (sourceWeightedConjugate w r q).val = q.val.conjugate := rfl

@[simp] theorem norm_sourceWeightedConjugate (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    ‖sourceWeightedConjugate w r q‖ = ‖q‖ := norm_conjugate _ _ q

/-- Forgetting only the extra weight commutes with the same physical conjugation. -/
theorem sourceForgetWeight_conj (w : SpectralWeight) (r : ℝ)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) :
    sourceForgetWeight w r (sourceWeightedConjugate w r q) =
      sobolevConjugation (-r) ⊤ (sourceForgetWeight w r q) := by
  apply Subtype.ext
  rw [sourceForgetWeight_val, sourceWeightedConjugate_val, sobolevConjugation_val, sourceForgetWeight_val]

/-- Original-distribution conjugation is exactly native endpoint Fourier conjugation. -/
theorem sourceEndpointCoefficients_conj (r : ℝ) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceEndpointCoefficients r (sobolevConjugation (-r) ⊤ q) =
      endpointConjugate SpectralWeight.one r (sourceEndpointCoefficients r q) := by
  apply Subtype.ext
  funext k
  simp only [sourceEndpointCoefficients_apply, sobolevConjugation_coefficient,
    endpointConjugate_apply, neg_neg, Complex.star_def]

/-- The actual original auxiliary root has physical real-type symmetry. -/
theorem sourceDiagonalRoot_conj (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceDiagonalRoot r hr n hn (sobolevConjugation (-r) ⊤ q) =
      (starRingEnd ℂ) (sourceDiagonalRoot r hr n hn q) := by
  simpa only [sourceDiagonalRoot, sourceEndpointCoefficients_conj] using
    endpointHillDiagonalRoot_conj r hr.1 hr.2 n hn (sourceEndpointCoefficients r q)
      (by simpa only [norm_sourceEndpointCoefficients] using hs)

/-- Real original potentials have real alpha; this is stronger than real-scalar analyticity. -/
theorem sourceDiagonalRoot_im_eq_zero_of_real (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (hq : q.val = q.val.conjugate) :
    (sourceDiagonalRoot r hr n hn q).im = 0 := by
  have hC : sobolevConjugation (-r) ⊤ q = q := Subtype.ext hq.symm
  have he := sourceDiagonalRoot_conj r hr n hn q hs
  rw [hC] at he
  have hi := congrArg Complex.im he
  simp only [Complex.conj_im] at hi
  linarith

/-- The literal original physical entries transform by conjugation and column swap. -/
theorem sourceEndpointEntries_conj (r : ℝ) (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceEndpointEntries r hr n (sobolevConjugation (-r) ⊤ q,(starRingEnd ℂ) z) =
      ((starRingEnd ℂ) (sourceEndpointEntries r hr n (q,z)).1,
        (starRingEnd ℂ) (sourceEndpointEntries r hr n (q,z)).2.2,
        (starRingEnd ℂ) (sourceEndpointEntries r hr n (q,z)).2.1) := by
  obtain ⟨ha, hb, hc⟩ := endpointCoefficients_conj r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q)
    (by simpa only [norm_sourceEndpointCoefficients] using hs)
  simp only [sourceEndpointEntries, sourceEndpointCoefficients_conj]
  exact Prod.ext ha (Prod.ext hb hc)

/-- The actual adapted physical coupling pair commutes with physical conjugation. -/
theorem sourceAdaptedCouplings_conj (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sourceAdaptedCouplings w r hr n hn (sourceWeightedConjugate w r q) =
      ((starRingEnd ℂ) (sourceAdaptedCouplings w r hr n hn q).2,
        (starRingEnd ℂ) (sourceAdaptedCouplings w r hr n hn q).1) := by
  have hsmall : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceForgetWeight w r q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs
  have hstrip := (sourceDiagonalRoot_spec r hr n hn (sourceForgetWeight w r q) hsmall).1
  have he := sourceEndpointEntries_conj r hr n hn (sourceForgetWeight w r q)
    (sourceDiagonalRoot r hr n hn (sourceForgetWeight w r q)) hstrip hsmall
  simpa only [sourceAdaptedCouplings, sourceWeightedDiagonalRoot, sourceForgetWeight_conj,
    sourceDiagonalRoot_conj r hr n hn _ hsmall] using congrArg Prod.snd he

/-- Raw actual adapted Fourier coefficients have physical real-type symmetry;
only the high pairs require the uniform spectral smallness. -/
theorem sourceAdaptedFourierValues_conj (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (k : ℤ) :
    sourceAdaptedFourierValues r hr N (sourceForgetWeight w r (sourceWeightedConjugate w r q)) k =
      (starRingEnd ℂ) (sourceAdaptedFourierValues r hr N (sourceForgetWeight w r q) (-k)) := by
  apply evenTailReplacement_conj_of_pairs
  · intro j
    simp only [sourceForgetWeight_val, sourceWeightedConjugate_val, Distribution.conjugate_coefficient,
      neg_neg, Complex.star_def]
  · intro n hn hN
    have he := sourceAdaptedCouplings_conj w r hr n hn q (hs n hn hN)
    simpa only [sourceAdaptedPair, dif_pos hn, sourceAdaptedCouplings, sourceWeightedDiagonalRoot] using he

/-- Reality of the SAME original root persists in every stronger source weight. -/
theorem sourceWeightedDiagonalRoot_im_eq_zero_of_real (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 1 ≤ n)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (hq : q.val = q.val.conjugate) :
    (sourceWeightedDiagonalRoot w r hr n hn q).im = 0 := by
  apply sourceDiagonalRoot_im_eq_zero_of_real r hr n hn (sourceForgetWeight w r q)
  · exact (mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
      (by positivity [endpointHillConstant_pos r hr.2])).trans hs
  · simpa only [sourceForgetWeight_val] using hq

/-- At real physical data,the actual two adapted couplings are conjugates. -/
theorem sourceAdaptedCouplings_real (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 1 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) (hq : q.val = q.val.conjugate) :
    (sourceAdaptedCouplings w r hr n hn q).2 = (starRingEnd ℂ) (sourceAdaptedCouplings w r hr n hn q).1 := by
  have hC : sourceWeightedConjugate w r q = q := Subtype.ext hq.symm
  have he := sourceAdaptedCouplings_conj w r hr n hn q hs
  rw [hC] at he
  exact congrArg Prod.snd he

/-- The actual adapted map commutes with conjugation on EVERY original smooth test. -/
theorem sourceWeightedAdaptedFourier_conj (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R) :
    (sourceWeightedAdaptedFourier w r hr N (sourceWeightedConjugate w r q)).val =
      (sourceWeightedAdaptedFourier w r hr N q).val.conjugate := by
  have hs (n : ℕ) (hn : 1 ≤ n) (hN : N ≤ n) : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
    have hc : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2) := by positivity [endpointHillConstant_pos r hr.2]
    have hh := hcut n hn hN
    have hi := mul_le_mul_of_nonneg_left hq hc
    nlinarith
  have hv := (sourceWeightedAdaptedFourier_spec w r hr N R hR hcut q hq).1
  have hvC := (sourceWeightedAdaptedFourier_spec w r hr N R hR hcut (sourceWeightedConjugate w r q)
    (by simpa only [norm_sourceWeightedConjugate] using hq)).1
  apply Distribution.ext_coefficients
  intro k
  rw [hvC, sourceAdaptedFourierValues_conj w r hr N q hs k, Distribution.conjugate_coefficient]
  simpa only [neg_neg, Complex.star_def] using congrArg (starRingEnd ℂ) (hv (-k)).symm

/-- In particular real original physical potentials map to real original distributions. -/
theorem sourceWeightedAdaptedFourier_real (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*R) ≤ 1/2)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ R)
    (hreal : q.val = q.val.conjugate) :
    (sourceWeightedAdaptedFourier w r hr N q).val = (sourceWeightedAdaptedFourier w r hr N q).val.conjugate := by
  have hC : sourceWeightedConjugate w r q = q := Subtype.ext hreal.symm
  simpa only [hC] using sourceWeightedAdaptedFourier_conj w r hr N R hR hcut q hq

/-- On the proved injective source ball,real-valuedness is reflected as well
as preserved. Thus actual inverse images of real data are real. -/
theorem sourceWeightedAdaptedFourier_real_iff (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (N : ℕ) (m : ℝ) (hm : 0 ≤ m)
    (hcut : ∀ n : ℕ, 1 ≤ n → N ≤ n → endpointHillConstant r*(n:ℝ)^(r-1/2)*(64*(2*m)) ≤ 1/2)
    (hinj : Set.InjOn (sourceWeightedAdaptedFourier w r hr N) (closedBall 0 m))
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤) (hq : ‖q‖ ≤ m) :
    ((sourceWeightedAdaptedFourier w r hr N q).val = (sourceWeightedAdaptedFourier w r hr N q).val.conjugate) ↔
      q.val = q.val.conjugate := by
  have hq2 : ‖q‖ ≤ 2*m := by linarith
  constructor
  · intro hreal
    have he := sourceWeightedAdaptedFourier_conj w r hr N (2*m) (by positivity) hcut q hq2
    have hmap : sourceWeightedAdaptedFourier w r hr N (sourceWeightedConjugate w r q) =
        sourceWeightedAdaptedFourier w r hr N q := Subtype.ext (he.trans hreal.symm)
    have hCmem : sourceWeightedConjugate w r q ∈ closedBall 0 m := by
      simpa only [mem_closedBall, dist_zero_right, norm_sourceWeightedConjugate] using hq
    have hqmem : q ∈ closedBall 0 m := by simpa only [mem_closedBall, dist_zero_right] using hq
    have hCq := hinj hCmem hqmem hmap
    exact (congrArg Subtype.val hCq).symm
  · exact sourceWeightedAdaptedFourier_real w r hr N (2*m) (by positivity) hcut q hq2

/-- The actual weighted analytic inverse on a neighborhood of the closed half
ball preserves the ENTIRE original real,mean-zero,period-one source locus. -/
theorem source_uniform_real_adapted_inverse (r : ℝ) (hr : AdmissiblePredualOrder r)
    (m : ℝ) (hm : 0 < m) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ w : SpectralWeight,
      ∃ g : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ →
          PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
        AnalyticOnNhd ℂ g (ball 0 (3*m/4)) ∧
        ∀ y, ‖y‖ ≤ m/2 → g y ∈ ball 0 m ∧ sourceWeightedAdaptedFourier w r hr N (g y) = y ∧
          ((g y).val.IsRealMeanZeroPeriodOne ↔ y.val.IsRealMeanZeroPeriodOne) := by
  obtain ⟨N, hN, hcut, hmap⟩ := source_uniform_adaptedFourier_inverse r hr m hm
  refine ⟨N, hN, fun w => ?_⟩
  obtain ⟨_, _, g, hg, hinj, hright, _, hconstraints⟩ := hmap w
  refine ⟨g, hg, fun y hy => ?_⟩
  obtain ⟨hgm, he⟩ := hright y (by linarith)
  obtain ⟨hmean, hperiod⟩ := hconstraints y hy
  have hreal := sourceWeightedAdaptedFourier_real_iff w r hr N m hm.le hcut hinj (g y)
    (mem_ball_zero_iff.mp hgm).le
  rw [he] at hreal
  refine ⟨hgm, he, ?_⟩
  simp only [Distribution.IsRealMeanZeroPeriodOne, ← hreal, hmean, hperiod]

end NLS.Articles.KdVPseudomeasures
