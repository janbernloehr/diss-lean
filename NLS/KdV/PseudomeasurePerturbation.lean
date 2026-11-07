import NLS.KdV.PseudomeasureKernel
import NLS.SequenceSpaces.InfinityMatrix
import NLS.SequenceSpaces.ShiftReflection

/-! # Actual shifted weighted-infinity Hill perturbation rows -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The exact normalized row matrix for V A_lambda^(-1) Q_n in the +n norm. -/
def endpointHillMatrix (w : SpectralWeight) (r : ℝ) (n : ℕ) (hn : 1≤n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (m k : ℤ) : ℂ :=
  ((w.negativeSobolev r (m+(n:ℤ)) : ℝ):ℂ) *
    (((w.negativeSobolev r (k+(n:ℤ)) : ℝ):ℂ))⁻¹ *
      q.val (m-k) * reducedHillSymbol n hn z hz k

/-- Every normalized row has one common summable kernel majorant, with no
constant depending on the weight or the output frequency. -/
theorem endpointHillMatrix_bound (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) (m k : ℤ) :
    ‖endpointHillMatrix w r n hn z hz q m k‖ ≤
      (2*‖q‖)*ReciprocalSeries.mixedHillKernel (1-2*r) n k := by
  let W := w.negativeSobolev r
  have hq : ‖q.val (m-k)‖ ≤ ‖q‖ / W (m-k) := WeightedCoeff.norm_apply_le W ⊤ q (m-k)
  have hW := w.negativeSobolev_shift_ratio_le r hr m k (n:ℤ)
  have hsym := sobolevReducedSymbol_bound r hr hr1 n hn z hz k
  have he : ‖endpointHillMatrix w r n hn z hz q m k‖ =
      W (m+(n:ℤ)) * (W (k+(n:ℤ)))⁻¹ * ‖q.val (m-k)‖ * ‖reducedHillSymbol n hn z hz k‖ := by
    simp only [W, endpointHillMatrix, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ((w.negativeSobolev r).positive _)]
  rw [he]
  calc
    _ ≤ W (m+(n:ℤ)) * (W (k+(n:ℤ)))⁻¹ * (‖q‖/W (m-k)) *
        ‖reducedHillSymbol n hn z hz k‖ := by
      gcongr
      exact mul_nonneg (W.positive _).le (inv_nonneg.mpr (W.positive _).le)
    _ = ‖q‖ * (W (m+(n:ℤ))/(W (m-k)*W (k+(n:ℤ)))) *
        ‖reducedHillSymbol n hn z hz k‖ := by ring
    _ ≤ ‖q‖ * (Weight.sobolev r (k+(n:ℤ)))^2 * ‖reducedHillSymbol n hn z hz k‖ := by
      gcongr
    _ ≤ ‖q‖ * (2*ReciprocalSeries.mixedHillKernel (1-2*r) n k) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsym (norm_nonneg q)
    _ = _ := by ring

/-- Explicit constant, independent of the spectral weight and potential. -/
def endpointHillConstant (r : ℝ) : ℝ := 8+16/(1-2*r)

/-- The normalized operator is defined by the full absolutely summable rows. -/
def endpointHillNormalizedPerturbation (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) : Coeff ⊤ →L[ℂ] Coeff ⊤ :=
  Coeff.infinityMatrixCLM (endpointHillMatrix w r n hn z hz q)
    (fun k => (2*‖q‖)*ReciprocalSeries.mixedHillKernel (1-2*r) n k)
    ((ReciprocalSeries.summable_mixedHillKernel (1-2*r) (by linarith) (by linarith) n hn).mul_left _)
    (fun k => mul_nonneg (by positivity) (ReciprocalSeries.mixedHillKernel_nonneg _ _ _))
    (endpointHillMatrix_bound w r hr hr1 n hn z hz q)

/-- The actual weighted endpoint operator in the source's +n shifted norm. -/
def endpointHillPerturbation (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤ →L[ℂ]
      WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤ :=
  (WeightedCoeff.weightIsometry _ ⊤).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((endpointHillNormalizedPerturbation w r hr hr1 n hn z hz q).comp
      (WeightedCoeff.weightIsometry _ ⊤).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The full operator estimate, with the exact real decay exponent 1/2-r. -/
theorem norm_endpointHillPerturbation_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤) :
    ‖endpointHillPerturbation w r hr hr1 n hn z hz q f‖ ≤
      endpointHillConstant r * (n:ℝ)^(r-1/2) * ‖q‖ * ‖f‖ := by
  let e := WeightedCoeff.weightIsometry ((w.negativeSobolev r).shift (n:ℤ)) ⊤
  change ‖e.symm (endpointHillNormalizedPerturbation w r hr hr1 n hn z hz q (e f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  have hbound := Coeff.norm_infinityMatrixCLM_apply_le
    (endpointHillMatrix w r n hn z hz q)
    (fun k => (2*‖q‖)*ReciprocalSeries.mixedHillKernel (1-2*r) n k)
    ((ReciprocalSeries.summable_mixedHillKernel (1-2*r) (by linarith) (by linarith) n hn).mul_left _)
    (fun k => mul_nonneg (by positivity) (ReciprocalSeries.mixedHillKernel_nonneg _ _ _))
    (endpointHillMatrix_bound w r hr hr1 n hn z hz q) (e f)
  simp only [LinearIsometryEquiv.norm_map] at hbound
  apply hbound.trans
  rw [tsum_mul_left]
  calc
    _ ≤ (2*‖q‖)*((4+8/(1-2*r))*(n:ℝ)^(-(1-2*r)/2))*‖f‖ := by
      gcongr
      exact ReciprocalSeries.tsum_mixedHillKernel_le (1-2*r) (by linarith) (by linarith) n hn
    _ = _ := by
      rw [show -(1-2*r)/2 = r-1/2 by ring]
      unfold endpointHillConstant
      ring

/-- Normalization cancels exactly in each original Fourier convolution term. -/
theorem endpointHillMatrix_term (w : SpectralWeight) (r : ℝ)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤) (m k : ℤ) :
    (endpointHillMatrix w r n hn z hz q m k *
      WeightedCoeff.weightIsometry ((w.negativeSobolev r).shift (n:ℤ)) ⊤ f k) /
      (w.negativeSobolev r (m+(n:ℤ)):ℂ) =
        q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k := by
  change (((w.negativeSobolev r (m+(n:ℤ)):ℂ) *
      (w.negativeSobolev r (k+(n:ℤ)):ℂ)⁻¹ * q.val (m-k) * reducedHillSymbol n hn z hz k) *
      ((w.negativeSobolev r (k+(n:ℤ)):ℂ)*f.val k)) /
      (w.negativeSobolev r (m+(n:ℤ)):ℂ) = _
  let A : ℂ := (w.negativeSobolev r (m+(n:ℤ)):ℂ)
  let B : ℂ := (w.negativeSobolev r (k+(n:ℤ)):ℂ)
  have hA : A≠0 := (w.negativeSobolev r).complex_ne_zero _
  have hB : B≠0 := (w.negativeSobolev r).complex_ne_zero _
  change ((A*B⁻¹*q.val (m-k)*reducedHillSymbol n hn z hz k)*(B*f.val k))/A = _
  field_simp [hA,hB]

/-- Every original Fourier row is absolutely convergent at the infinity endpoint. -/
theorem summable_norm_endpointHill_terms (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤) (m : ℤ) :
    Summable (fun k => ‖q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k‖) := by
  have hh := Coeff.summable_norm_matrixRow (endpointHillMatrix w r n hn z hz q)
    (fun k => (2*‖q‖)*ReciprocalSeries.mixedHillKernel (1-2*r) n k)
    ((ReciprocalSeries.summable_mixedHillKernel (1-2*r) (by linarith) (by linarith) n hn).mul_left _)
    (fun k => mul_nonneg (by positivity) (ReciprocalSeries.mixedHillKernel_nonneg _ _ _))
    (endpointHillMatrix_bound w r hr hr1 n hn z hz q)
    (WeightedCoeff.weightIsometry ((w.negativeSobolev r).shift (n:ℤ)) ⊤ f) m
  apply (hh.div_const (w.negativeSobolev r (m+(n:ℤ)))).congr
  intro k
  rw [← endpointHillMatrix_term w r n hn z hz q f m k, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ((w.negativeSobolev r).positive _)]

/-- The bounded operator is exactly the original coefficient formula for
V A_lambda^(-1) Q_n, rather than an abstract operator with the same bound. -/
theorem endpointHillPerturbation_apply (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (n:ℤ)) ⊤) (m : ℤ) :
    (endpointHillPerturbation w r hr hr1 n hn z hz q f).val m =
      ∑' k : ℤ, q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k := by
  change (∑' k : ℤ, endpointHillMatrix w r n hn z hz q m k *
    WeightedCoeff.weightIsometry ((w.negativeSobolev r).shift (n:ℤ)) ⊤ f k) /
      (w.negativeSobolev r (m+(n:ℤ)):ℂ) = _
  rw [← tsum_div_const]
  exact tsum_congr (endpointHillMatrix_term w r n hn z hz q f m)

/-- The free reduced symbol is even in the signed mode, including the cutoffs. -/
theorem reducedHillSymbol_neg (n : ℕ) (hn : 1≤n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    reducedHillSymbol n hn z hz (-k) = reducedHillSymbol n hn z hz k := by
  simp only [reducedHillSymbol, Int.natAbs_neg, freeHillValue_neg]

/-- The same actual operator in the source's -n shifted norm, constructed
by isometric reflection of the potential and both shifted sequence spaces. -/
def endpointHillPerturbationMinus (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤ →L[ℂ]
      WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤ :=
  (WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((endpointHillPerturbation w r hr hr1 n hn z hz
      (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q)).comp
        (WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The -n shifted bound has the identical constant and decay exponent. -/
theorem norm_endpointHillPerturbationMinus_le (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤) :
    ‖endpointHillPerturbationMinus w r hr hr1 n hn z hz q f‖ ≤
      endpointHillConstant r * (n:ℝ)^(r-1/2) * ‖q‖ * ‖f‖ := by
  let e := WeightedCoeff.shiftReflection (w.negativeSobolev r) (w.negativeSobolev_neg r) (n:ℤ) (p := ⊤)
  change ‖e (endpointHillPerturbation w r hr hr1 n hn z hz
    (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q) (e.symm f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using norm_endpointHillPerturbation_le
    w r hr hr1 n hn z hz (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q) (e.symm f)

/-- The -n construction has precisely the same original Fourier formula. -/
theorem endpointHillPerturbationMinus_apply (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤) (m : ℤ) :
    (endpointHillPerturbationMinus w r hr hr1 n hn z hz q f).val m =
      ∑' k : ℤ, q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k := by
  change (WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)
    (endpointHillPerturbation w r hr hr1 n hn z hz
      (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q)
      ((WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).symm f))).val m = _
  rw [WeightedCoeff.shiftReflection_apply, endpointHillPerturbation_apply]
  have he := (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
    (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q).val (-m-k) *
      reducedHillSymbol n hn z hz k *
      ((WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).symm f).val k)
  rw [← he]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, WeightedCoeff.weightReflection_apply,
    WeightedCoeff.shiftReflection_symm_apply, neg_neg, reducedHillSymbol_neg]
  rw [show -(-m- -k)=m-k by omega]

/-- Absolute convergence also holds for the original -n shifted Fourier rows. -/
theorem summable_norm_endpointHillMinus_terms (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (f : WeightedCoeff ((w.negativeSobolev r).shift (-(n:ℤ))) ⊤) (m : ℤ) :
    Summable (fun k => ‖q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k‖) := by
  have hh := (summable_norm_endpointHill_terms w r hr hr1 n hn z hz
    (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q)
    ((WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).symm f) (-m)).comp_injective
      (Equiv.neg ℤ).injective
  have he : (fun k : ℤ => ‖
    (WeightedCoeff.weightReflection _ (w.negativeSobolev_neg r) q).val (-m- -k) *
      reducedHillSymbol n hn z hz (-k) *
      ((WeightedCoeff.shiftReflection _ (w.negativeSobolev_neg r) (n:ℤ)).symm f).val (-k)‖) =
      (fun k : ℤ => ‖q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k‖) := by
    funext k
    simp only [WeightedCoeff.weightReflection_apply, WeightedCoeff.shiftReflection_symm_apply,
      neg_neg, reducedHillSymbol_neg, show -(-m- -k)=m-k by omega]
  exact he ▸ hh

/-- The Fourier perturbation on the one unshifted source Banach space. -/
def unshiftedEndpointHillPerturbation (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (w.negativeSobolev r) ⊤ :=
  (w.negativeShiftEquiv r hr (n:ℤ) ⊤).symm.toContinuousLinearMap.comp
    ((endpointHillPerturbation w r hr hr1 n hn z hz q).comp
      (w.negativeShiftEquiv r hr (n:ℤ) ⊤).toContinuousLinearMap)

/-- The operator on the source space has the original Fourier convolution formula. -/
theorem unshiftedEndpointHillPerturbation_apply (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) (m : ℤ) :
    (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f).val m =
      ∑' k : ℤ, q.val (m-k)*reducedHillSymbol n hn z hz k*f.val k := by
  change ((w.negativeShiftEquiv r hr (n:ℤ) ⊤).symm
    (endpointHillPerturbation w r hr hr1 n hn z hz q
      (w.negativeShiftEquiv r hr (n:ℤ) ⊤ f))).val m = _
  rw [SpectralWeight.negativeShiftEquiv_symm_apply, endpointHillPerturbation_apply]
  exact tsum_congr (fun k => by rw [SpectralWeight.negativeShiftEquiv_apply])

/-- The -n shifted realization is the very same source operator, not a
separate operator whose norm happens to satisfy a similar estimate. -/
theorem negativeShift_unshiftedEndpointHillPerturbation (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (n : ℕ) (hn : 1≤n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f) =
        endpointHillPerturbationMinus w r hr hr1 n hn z hz q
          (w.negativeShiftEquiv r hr (-(n:ℤ)) ⊤ f) := by
  apply Subtype.ext
  funext m
  rw [SpectralWeight.negativeShiftEquiv_apply, unshiftedEndpointHillPerturbation_apply,
    endpointHillPerturbationMinus_apply]
  exact tsum_congr (fun k => by rw [SpectralWeight.negativeShiftEquiv_apply])

/-- Both source shifted norms, on one original unshifted space and operator. -/
theorem negativeShiftedNorm_endpointHillPerturbation_le (w : SpectralWeight)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 1≤n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeShiftedNorm r hr (n:ℤ) ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f) ≤
        endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ * w.negativeShiftedNorm r hr (n:ℤ) ⊤ f ∧
    w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f) ≤
        endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ * w.negativeShiftedNorm r hr (-(n:ℤ)) ⊤ f := by
  constructor
  · change ‖w.negativeShiftEquiv r hr (n:ℤ) ⊤
      ((w.negativeShiftEquiv r hr (n:ℤ) ⊤).symm
        (endpointHillPerturbation w r hr hr1 n hn z hz q
          (w.negativeShiftEquiv r hr (n:ℤ) ⊤ f)))‖ ≤ _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact norm_endpointHillPerturbation_le w r hr hr1 n hn z hz q _
  · unfold SpectralWeight.negativeShiftedNorm
    rw [negativeShift_unshiftedEndpointHillPerturbation]
    exact norm_endpointHillPerturbationMinus_le w r hr hr1 n hn z hz q _

end NLS.KdV
