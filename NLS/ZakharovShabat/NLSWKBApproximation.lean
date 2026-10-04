import NLS.ZakharovShabat.NLSRiccatiResidualBounds
import NLS.ZakharovShabat.ClassicalNLSHamiltonians

/-! # Finite Hamiltonian approximations to the spectral equation

The exponential carrier integrates the truncated Riccati correction.
Together with its second component it solves the original spectral
system up to an explicitly identified forcing term.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The exponential carrier with its free oscillation and finite Riccati correction. -/
def nlsWKBCarrier (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  exp (-I*z*x + ∫ t in (0 : ℝ)..x, a t*nlsRiccatiApproximation a b N (2*I*z)⁻¹ t)

/-- The corresponding two-component approximate spectral solution. -/
def nlsWKBVector (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (x : ℝ) : ℂ × ℂ :=
  (nlsWKBCarrier a b N z x,-I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ x*nlsWKBCarrier a b N z x)

@[simp] theorem nlsWKBCarrier_zero (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    nlsWKBCarrier a b N z 0 = 1 := by simp [nlsWKBCarrier]

theorem nlsWKBCarrier_ne_zero (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (x : ℝ) :
    nlsWKBCarrier a b N z x ≠ 0 := exp_ne_zero _

theorem hasDerivAt_nlsWKBCarrier (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (z : ℂ) (x : ℝ) :
    HasDerivAt (nlsWKBCarrier a b N z)
      ((-I*z+a x*nlsRiccatiApproximation a b N (2*I*z)⁻¹ x)*nlsWKBCarrier a b N z x) x := by
  have hr : Continuous (nlsRiccatiApproximation a b N (2*I*z)⁻¹) :=
    (show Differentiable ℝ _ from fun t => (hasDerivAt_nlsRiccatiApproximation a b ha hb N _ t).differentiableAt).continuous
  have hc := ha.continuous.mul hr
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-I*z)).add hi
  convert! hd.cexp using 1
  simp [nlsWKBCarrier,mul_comm]

/-- The exact forcing term in the original two-component spectral system. -/
theorem hasDerivAt_nlsWKBVector (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (z : ℂ) (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (nlsWKBVector a b N z)
      (classicalODECoefficient (a x,b x) z (nlsWKBVector a b N z x) +
        (0,I*(nlsRiccatiResidualPolynomial a b N).eval₂ (Pi.evalRingHom (fun _ : ℝ => ℂ) x)
          (2*I*z)⁻¹*nlsWKBCarrier a b N z x)) x := by
  let w : ℂ := (2*I*z)⁻¹
  have hw : w ≠ 0 := inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz)
  have hr := hasDerivAt_nlsRiccatiApproximation a b ha hb N w x
  have hc := hasDerivAt_nlsWKBCarrier a b ha hb N z x
  have he := nlsRiccatiApproximation_residual_eq a b ha hb N w hw x
  rw [hr.deriv] at he
  simp only [w,inv_inv] at he
  have hv := hc.prodMk (((hr.const_mul (-I)).mul hc))
  convert! hv using 1
  apply Prod.ext
  · simp [nlsWKBVector,classicalODECoefficient,smul_eq_mul]
    ring_nf
    simp [I_sq]
  · simp only [nlsWKBVector,Prod.snd_add,classicalODECoefficient_apply]
    dsimp only [w] at *
    linear_combination I*nlsWKBCarrier a b N z x * he

/-- The exponential over one period contains exactly the finite Hamiltonian
sum with the dissertation's normalization. -/
theorem nlsWKBCarrier_one (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (z : ℂ) :
    nlsWKBCarrier a b N z 1 = exp (-I*z+
      ∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) := by
  have hi (k : ℕ) : IntervalIntegrable
      (fun x => a x*nlsRiccatiDensity a b k x*((2*I*z)⁻¹)^(k+1)) volume 0 1 :=
    (intervalIntegrable_nlsRiccatiDensity a b ha hb k).mul_const _
  have he : (∫ x in (0 : ℝ)..1, a x*nlsRiccatiApproximation a b N (2*I*z)⁻¹ x) =
      ∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1) := by
    simp only [nlsRiccatiApproximation,Finset.mul_sum,← mul_assoc]
    rw [intervalIntegral.integral_finsetSum (fun k _ => hi k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_mul_const]
    simpa only [div_eq_mul_inv,inv_pow] using classicalNLSHamiltonian_riccati_coefficient a b k z
  simp only [nlsWKBCarrier,ofReal_one,mul_one,he]

/-- For periodic potentials the finite approximation satisfies the exact
endpoint multiplier relation, with the finite Hamiltonian sum as exponent. -/
theorem nlsWKBVector_one (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) (z : ℂ) :
    nlsWKBVector a b N z 1 =
      exp (-I*z+∑ k ∈ Finset.range N, I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1)) •
        nlsWKBVector a b N z 0 := by
  have hr : nlsRiccatiApproximation a b N (2*I*z)⁻¹ 1 =
      nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0 := by
    unfold nlsRiccatiApproximation
    apply Finset.sum_congr rfl
    intro k _
    have he := periodic_nlsRiccatiDensity a b 1 hpa hpb k 0
    simp only [zero_add] at he
    rw [he]
  apply Prod.ext
  · simp [nlsWKBVector,nlsWKBCarrier_one a b ha hb]
  · simp only [nlsWKBVector,Prod.smul_snd,smul_eq_mul,nlsWKBCarrier_zero,mul_one]
    rw [hr,nlsWKBCarrier_one a b ha hb]
    ring

/-- The original spectral-system residual, relative to the nonzero carrier,
is bounded at the prescribed inverse-frequency order uniformly on one period. -/
theorem exists_nlsWKBVector_residual_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, 1 ≤ ‖z‖ →
      ‖deriv (nlsWKBVector a b N z) x -
        classicalODECoefficient (a x,b x) z (nlsWKBVector a b N z x)‖ ≤
        (C/(2*‖z‖)^N)*‖nlsWKBCarrier a b N z x‖ := by
  obtain ⟨C,hC,hbound⟩ := exists_nlsRiccatiApproximation_spectral_residual_bound a b ha hb N
  refine ⟨C,hC,?_⟩
  intro x hx z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hw : (2*I*z)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz0)
  have he := nlsRiccatiApproximation_residual_eq a b ha hb N _ hw x
  simp only [inv_inv] at he
  have hq := hbound x hx z hz
  rw [he,norm_neg] at hq
  rw [(hasDerivAt_nlsWKBVector a b ha hb N z hz0 x).deriv,add_sub_cancel_left]
  simp only [Prod.norm_def,norm_zero,norm_mul,norm_I,one_mul]
  rw [max_eq_right (by positivity)]
  exact mul_le_mul_of_nonneg_right hq (norm_nonneg (nlsWKBCarrier a b N z x))

end NLS.ZakharovShabat
