import NLS.ZakharovShabat.SobolevRiccatiResidualCorrectionUniform
import NLS.ZakharovShabat.SobolevWKBCarrierFreeUniform

/-! # The leading oscillatory WKB forcing

Removing the explicit top-density forcing leaves an L1 error of order N+1. The highest density needs only L2 control.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual scalar WKB forcing has an explicit leading oscillatory
density, with an L1 remainder one order smaller uniformly on an Hs ball. -/
theorem exists_uniform_nlsWKB_leading_forcing_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        (∫ x in (0:ℝ)..1, ‖I*(nlsRiccatiResidualPolynomial a b N).eval₂
            (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹*nlsWKBCarrier a b N z x+
          I*nlsRiccatiDensity a b N x*((2*I*z)⁻¹)^N*exp (-I*z*x)‖) ≤
          C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨C,hC,hcorr⟩ := exists_uniform_nlsRiccatiResidual_correction_bound s N hs hNs R hR
  obtain ⟨B,hB,hcarrier⟩ := exists_uniform_nlsWKBCarrier_strip_bounds s N hs hNs R hR H
  obtain ⟨D,hD,hfree⟩ := exists_uniform_nlsWKBCarrier_free_error_bound s N hs hNs R hR H
  obtain ⟨K,hK,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨C*B+D*K,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH
  let w : ℂ := (2*I*z)⁻¹
  let q (x : ℝ) := (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w
  let ρ := nlsRiccatiDensity a b N
  let c := nlsWKBCarrier a b N z
  let e (x : ℝ) := exp (-I*z*x)
  let f (x : ℝ) := I*q x*c x+I*ρ x*w^N*e x
  have hw : ‖w‖ ≤ 1 := by
    change ‖(2*I*z)⁻¹‖ ≤ 1
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hc : Continuous c :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  have hq : Continuous q :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  have he : Continuous e := by dsimp only [e]; fun_prop
  have hf : Continuous f := ((continuous_const.mul hq).mul hc).add
    (((continuous_const.mul hρ).mul continuous_const).mul he)
  have hp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      ‖f x‖ ≤ (C*B+D*‖ρ x‖)*‖w‖^(N+1) := by
    have hid : f x = I*(q x+ρ x*w^N)*c x-I*ρ x*w^N*(c x-e x) := by dsimp only [f]; ring
    rw [hid]
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_I,one_mul,norm_pow]
    calc
      _ ≤ (C*‖w‖^(N+1))*B+(‖ρ x‖*‖w‖^N)*(D*‖w‖) := add_le_add
        (mul_le_mul (hcorr ab hab a b ha hb hpa hpb hca hcb x w hw)
          (hcarrier ab hab a b ha hb hpa hpb hca hcb x hx z hzn hzH).1
          (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left (hfree ab hab a b ha hb hpa hpb hca hcb x hx z hzn hzH) (by positivity))
      _ = _ := by rw [pow_succ]; ring
  have hiρ : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ K := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  change (∫ x in (0:ℝ)..1, ‖f x‖) ≤ _
  calc
    _ ≤ ∫ x in (0:ℝ)..1, (C*B+D*‖ρ x‖)*‖w‖^(N+1) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hf.norm.intervalIntegrable 0 1)
        (((continuous_const.add (continuous_const.mul hρ.norm)).mul continuous_const).intervalIntegrable 0 1) hp
    _ = (C*B+D*(∫ x in (0:ℝ)..1, ‖ρ x‖))*‖w‖^(N+1) := by
      have h1 : IntervalIntegrable (fun _ : ℝ => C*B) volume 0 1 := continuous_const.intervalIntegrable 0 1
      have h2 : IntervalIntegrable (fun x : ℝ => D*‖ρ x‖) volume 0 1 :=
        (continuous_const.mul hρ.norm).intervalIntegrable 0 1
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_add h1 h2,
        intervalIntegral.integral_const_mul]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hiρ hD)) (by positivity)

end NLS.ZakharovShabat
