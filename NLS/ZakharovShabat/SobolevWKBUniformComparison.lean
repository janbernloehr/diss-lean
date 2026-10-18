import NLS.ZakharovShabat.SobolevRiccatiResidualIntegralUniform
import NLS.ZakharovShabat.SobolevWKBCarrierUniform
import NLS.ZakharovShabat.ClassicalIntegralResidualStability
import NLS.ZakharovShabat.NLSWKBComparison

/-! # Uniform Sobolev WKB solution comparison

The actual initial-value error is bounded by C/(2 norm(z))^N uniformly on Hs balls and complex spectral strips, for smooth periodic representatives and N <= s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Every admissible WKB order has a solution-error constant uniform on the
original Hs ball and complex spectral strip, using no extra source derivative. -/
theorem exists_uniform_nlsWKBVector_strip_solution_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBVector a b N z t-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z
            (nlsWKBVector a b N z 0) t‖ ≤ C/(2*‖z‖)^N := by
  obtain ⟨A,hA,haB⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨D,hD,hres⟩ := exists_uniform_nlsRiccatiResidual_integral_bound s N hs hNs R hR
  obtain ⟨B,hB,hcarrier⟩ := exists_uniform_nlsWKBCarrier_strip_bounds s N hs hNs R hR H
  refine ⟨4*(Real.exp (A+H))^2*(D*B),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    change ‖(a x,b x)‖ ≤ A
    apply norm_prod_le_iff.mpr
    exact ⟨haB ab hab a b ha hb hpa hpb hca hcb x,
      haB (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  have hz : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hu : Continuous (nlsWKBVector a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBVector a b ha hb N z hz x).differentiableAt).continuous
  have hc : Continuous (nlsWKBCarrier a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  let w : ℂ := (2*I*z)⁻¹
  let q (x : ℝ) := (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w
  have hq : Continuous q :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f : ℝ → ℂ × ℂ := fun x => (0,I*q x*nlsWKBCarrier a b N z x)
  have hf : Continuous f := continuous_const.prodMk ((continuous_const.mul hq).mul hc)
  let g : Curve (ℂ × ℂ) := ⟨fun x => f x,hf.comp continuous_subtype_val⟩
  have hd (x : Icc (0:ℝ) 1) : HasDerivAt (nlsWKBVector a b N z)
      (classicalODECoefficient (Φ x) z (nlsWKBVector a b N z x)+g x) x :=
    hasDerivAt_nlsWKBVector a b ha hb N z hz x
  have hw : ‖w‖ ≤ 1 := by
    change ‖(2*I*z)⁻¹‖ ≤ 1
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hg : (∫ x in (0:ℝ)..1, ‖extend g x‖) ≤ D*B/(2*‖z‖)^N := by
    have hi : (∫ x in (0:ℝ)..1, ‖extend g x‖) ≤
        ∫ x in (0:ℝ)..1, B*‖q x‖ := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((continuous_extend g).norm.intervalIntegrable 0 1)
        ((continuous_const.mul hq.norm).intervalIntegrable 0 1)
      intro x hx
      let u : Icc (0:ℝ) 1 := ⟨x,hx⟩
      change ‖extend g u‖ ≤ B*‖q u‖
      rw [extend_coe]
      change ‖(0,I*q u*nlsWKBCarrier a b N z u)‖ ≤ _
      simp only [Prod.norm_def,norm_zero,norm_mul,norm_I,one_mul,max_eq_right (by positivity : 0 ≤ ‖q u‖*‖nlsWKBCarrier a b N z u‖)]
      exact (mul_le_mul_of_nonneg_left
        (hcarrier ab hab a b ha hb hpa hpb hca hcb u u.property z hzn hzH).1
        (norm_nonneg _)).trans_eq (mul_comm _ _)
    rw [intervalIntegral.integral_const_mul] at hi
    apply hi.trans
    apply (mul_le_mul_of_nonneg_left (hres ab hab a b ha hb hpa hpb hca hcb w hw) hB.le).trans_eq
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one,inv_pow]
    ring
  have h := norm_sub_classicalSolution_strip_le_integral_residual Φ g z H hzH _ hu hd t
  apply h.trans
  calc
    _ ≤ 4*(Real.exp (A+H))^2*(D*B/(2*‖z‖)^N) := by
      apply mul_le_mul _ hg (intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
