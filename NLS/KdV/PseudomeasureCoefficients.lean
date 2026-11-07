import NLS.KdV.PseudomeasureLocalization

/-! # Weighted endpoint coefficients of the actual effective Hill potential

The coefficient error estimate retains every source spectral weight and the
negative Sobolev power. The two resonant corrections are constructed by the
actual tail inverse; the estimates require only the previously proved cutoff.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The exact shifted weighted coordinate bound, including the negative Sobolev factor. -/
theorem negativeShiftedNorm_coefficient_le (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r)
    (i k : ℤ) (a : WeightedCoeff (w.negativeSobolev r) ⊤) :
    w.negativeSobolev r (k+i)*‖a.val k‖ ≤ w.negativeShiftedNorm r hr i ⊤ a := by
  have h := lp.norm_apply_le_norm (by simp : (⊤:ℝ≥0∞) ≠ 0)
    (WeightedCoeff.weightEquiv ((w.negativeSobolev r).shift i) ⊤
      (w.negativeShiftEquiv r hr i ⊤ a)) k
  change ‖WeightedCoeff.weightEquiv ((w.negativeSobolev r).shift i) ⊤
    (w.negativeShiftEquiv r hr i ⊤ a) k‖ ≤ ‖w.negativeShiftEquiv r hr i ⊤ a‖ at h
  simpa only [WeightedCoeff.weightEquiv_apply, SpectralWeight.negativeShiftEquiv_apply,
    Weight.shift_apply, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ((w.negativeSobolev r).positive _).le,
    SpectralWeight.negativeShiftedNorm] using h

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The corrected potential of an actual signed Fourier unit mode. -/
def endpointHillCorrectedMode (j : ℤ) : WeightedCoeff (w.negativeSobolev r) ⊤ :=
  endpointHillTailInverse w r hr hr1 n hn z hz q hs (w.negativeModulation r hr j q)

/-- Its opposite shifted norm has the bound two at either resonant frequency. -/
theorem negativeShiftedNorm_endpointHillCorrectedMode_le (j : ℤ)
    (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeShiftedNorm r hr (-j) ⊤
      (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) ≤ 2*‖q‖ := by
  have h := negativeShiftedNorm_endpointHillTailInverse_le w r hr hr1 n hn z hz q hs
    (w.negativeModulation r hr j q)
  have hnorm := w.negativeShiftedNorm_negativeModulation r hr j q
  rcases hj with rfl | rfl
  · simpa only [endpointHillCorrectedMode, hnorm] using h.2
  · simp only [neg_neg] at hnorm
    simpa only [endpointHillCorrectedMode, neg_neg, hnorm] using h.1

/-- Weighted endpoint error at every coefficient of either corrected resonant mode. -/
theorem endpointHillCorrectedMode_coefficient_error (j k : ℤ)
    (hj : j = (n:ℤ) ∨ j = -(n:ℤ)) :
    w.negativeSobolev r (k-j)*
        ‖(endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j).val k-q.val (k-j)‖ ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  let a := endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j
  have hInv := endpointHillTailInverse_right w r hr hr1 n hn z hz q hs
    (w.negativeModulation r hr j q)
  have he : a-w.negativeModulation r hr j q =
      unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a := by
    change a-unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a =
      w.negativeModulation r hr j q at hInv
    exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hInv).trans (add_comm _ _))
  have ht : w.negativeShiftedNorm r hr (-j) ⊤
      (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q a) ≤
        (endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (-j) ⊤ a := by
    rcases hj with rfl | rfl
    · exact (negativeShiftedNorm_endpointHillPerturbation_le w r hr hr1 n hn z hz q a).2
    · simpa only [neg_neg] using
        (negativeShiftedNorm_endpointHillPerturbation_le w r hr hr1 n hn z hz q a).1
  calc
    _ = w.negativeSobolev r (k-j)*‖(a-w.negativeModulation r hr j q).val k‖ := by
      rw [WeightedCoeff.sub_val, SpectralWeight.negativeModulation_apply]
    _ ≤ w.negativeShiftedNorm r hr (-j) ⊤ (a-w.negativeModulation r hr j q) := by
      simpa only [sub_eq_add_neg] using negativeShiftedNorm_coefficient_le w r hr (-j) k _
    _ ≤ (endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*w.negativeShiftedNorm r hr (-j) ⊤ a := by
      rw [he]
      exact ht
    _ ≤ (endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*(2*‖q‖) := by
      apply mul_le_mul_of_nonneg_left
        (negativeShiftedNorm_endpointHillCorrectedMode_le w r hr hr1 n hn z hz q hs j hj)
      exact mul_nonneg (mul_nonneg (endpointHillConstant_pos r hr1).le
        (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
    _ = _ := by ring

/-- The first resonant corrected mode is the original physical effective source column. -/
theorem endpointHillCorrectedMode_pos (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs n =
      endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0) := by
  change endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (SpectralWeight.one.negativeModulation r hr (n:ℤ) q) =
    endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (endpointHillModePotential r hr hr1 n q (1,0))
  rw [endpointHillModePotential_basis_pos]

/-- The second physical effective source column is the opposite corrected mode. -/
theorem endpointHillCorrectedMode_neg (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillCorrectedMode SpectralWeight.one r hr hr1 n hn z hz q hs (-(n:ℤ)) =
      endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1) := by
  change endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (SpectralWeight.one.negativeModulation r hr (-(n:ℤ)) q) =
    endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
      (endpointHillModePotential r hr hr1 n q (0,1))
  rw [endpointHillModePotential_basis_neg]

/-- The total analytic effective family is the previously constructed physical one. -/
theorem endpointEffectiveFamily_eq (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    endpointEffectiveFamily r hr hr1 n p =
      endpointHillEffectivePotential r hr hr1 n hn p.2 hz p.1 hs := by
  unfold endpointEffectiveFamily endpointHillEffectivePotential
  rw [endpointInverseFamily_eq r hr hr1 n hn p hz hs, endpointModePotentialFamily_eq]

/-- The proof-independent actual upper diagonal correction. -/
def endpointDiagonal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) : ℂ :=
  (endpointEffectiveFamily r hr hr1 n p (1,0)).val n

/-- The actual coupling from the negative to the positive resonant mode. -/
def endpointUpperCoupling (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) : ℂ :=
  (endpointEffectiveFamily r hr hr1 n p (0,1)).val n

/-- The actual coupling from the positive to the negative resonant mode. -/
def endpointLowerCoupling (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ) : ℂ :=
  (endpointEffectiveFamily r hr hr1 n p (1,0)).val (-(n:ℤ))

/-- Diagonal error in the exact endpoint norm, uniformly over the entire strip. -/
theorem endpointDiagonal_error_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    ‖endpointDiagonal r hr hr1 n (q,z)-q.val 0‖ ≤
      2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  have h := endpointHillCorrectedMode_coefficient_error SpectralWeight.one r hr hr1
    n hn z hz q hs n n (Or.inl rfl)
  rw [endpointHillCorrectedMode_pos, sub_self] at h
  unfold endpointDiagonal
  rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs]
  simpa only [SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply,
    Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero, Real.one_rpow, div_one, one_mul] using h

/-- Both coupling errors obey the source's weighted negative-order bound. -/
theorem endpointCoupling_errors_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    (Weight.sobolev r (2*(n:ℤ)))⁻¹*
      ‖endpointUpperCoupling r hr hr1 n (q,z)-q.val (2*(n:ℤ))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ ∧
    (Weight.sobolev r (2*(n:ℤ)))⁻¹*
      ‖endpointLowerCoupling r hr hr1 n (q,z)-q.val (-(2*(n:ℤ)))‖ ≤
        2*(endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖ := by
  unfold endpointUpperCoupling endpointLowerCoupling
  rw [endpointEffectiveFamily_eq r hr hr1 n hn (q,z) hz hs]
  constructor
  · have h := endpointHillCorrectedMode_coefficient_error SpectralWeight.one r hr hr1
      n hn z hz q hs (-(n:ℤ)) n (Or.inr rfl)
    rw [endpointHillCorrectedMode_neg, show (n:ℤ)- -(n:ℤ) = 2*(n:ℤ) by ring] at h
    simpa only [SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply, one_div] using h
  · have h := endpointHillCorrectedMode_coefficient_error SpectralWeight.one r hr hr1
      n hn z hz q hs n (-(n:ℤ)) (Or.inl rfl)
    rw [endpointHillCorrectedMode_pos, show -(n:ℤ)-(n:ℤ) = -(2*(n:ℤ)) by ring,
      SpectralWeight.negativeSobolev_neg] at h
    simpa only [SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply, one_div] using h

/-- Every actual effective coefficient is jointly analytic in the full endpoint norm and lambda. -/
theorem analyticAt_endpointEffective_coefficient (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2)
    (u : ℂ × ℂ) (k : ℤ) :
    AnalyticAt ℂ (fun x => (endpointEffectiveFamily r hr hr1 n x u).val k) p := by
  have hE := SchurComplement.analyticAt_compCLM
    (analyticAt_endpointInverseFamily r hr hr1 n hn p hz hs)
    (analyticAt_endpointModePotentialFamily r hr hr1 n p)
  let e := (WeightedCoeff.evalCLM (SpectralWeight.one.negativeSobolev r) ⊤ k).comp
    (ContinuousLinearMap.apply ℂ (WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) u)
  exact (e.analyticAt _).comp (f := endpointEffectiveFamily r hr hr1 n) hE

/-- Analyticity of the three literal scalar entries used in the source determinant. -/
theorem analyticAt_endpointCoefficients (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ × ℂ)
    (hz : p.2 ∈ reducedHillStrip n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖p.1‖ ≤ 1/2) :
    AnalyticAt ℂ (endpointDiagonal r hr hr1 n) p ∧
      AnalyticAt ℂ (endpointUpperCoupling r hr hr1 n) p ∧
      AnalyticAt ℂ (endpointLowerCoupling r hr hr1 n) p :=
  ⟨analyticAt_endpointEffective_coefficient r hr hr1 n hn p hz hs (1,0) n,
    analyticAt_endpointEffective_coefficient r hr hr1 n hn p hz hs (0,1) n,
    analyticAt_endpointEffective_coefficient r hr hr1 n hn p hz hs (1,0) (-(n:ℤ))⟩

end NLS.KdV
