import NLS.ZakharovShabat.SobolevRiccatiResidualNextOrder
import NLS.ZakharovShabat.SobolevWKBCarrierFirstOrder

/-! # The next oscillatory term in the full WKB forcing

After retaining the leading forcing and the explicit next density, the full scalar forcing has an order-(N+2) L1 error without an extra source derivative.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The explicit next density in the scalar WKB forcing after its free
leading term; the only top derivative appears in the L2 density rho_N. -/
def nlsWKBNextForcingDensity (a b : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  I*(nlsRiccatiResidualNextDensity a b N x+
    nlsRiccatiDensity a b N x*nlsWKBMassPrimitive a b x)

theorem continuous_nlsWKBNextForcingDensity (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    Continuous (nlsWKBNextForcingDensity a b N) :=
  continuous_const.mul ((continuous_nlsRiccatiResidualNextDensity a b ha hb N).add
    ((contDiff_nlsRiccatiDensity a b ha hb N).continuous.mul
      (continuous_nlsWKBMassPrimitive a b ha.continuous hb.continuous)))

/-- The actual scalar WKB forcing has an explicit next free-oscillatory
density and a uniform L1 remainder of order N+2, through N=s on the
original complex Hs ball. -/
theorem exists_uniform_nlsWKB_next_forcing_error_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
        (∫ x in (0:ℝ)..1, ‖I*(nlsRiccatiResidualPolynomial a b N).eval₂
            (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹*nlsWKBCarrier a b N z x-
          nlsWKBLeadingScalar a b N z x-
          ((2*I*z)⁻¹)^(N+1)*nlsWKBNextForcingDensity a b N x*exp (-I*z*x)‖) ≤
          C*‖(2*I*z)⁻¹‖^(N+2) := by
  have hs := hN.trans hNs
  obtain ⟨C,hC,hres⟩ := exists_uniform_nlsRiccatiResidual_next_order_bounds s N hs hNs R hR
  obtain ⟨B,hB,hcarrier⟩ := exists_uniform_nlsWKBCarrier_strip_bounds s N hs hNs R hR H
  obtain ⟨D,hD,hlinear⟩ := exists_uniform_nlsWKBCarrier_first_order_bound s N hN hNs R hR H
  obtain ⟨F,hF,hfree⟩ := exists_uniform_nlsWKBCarrier_free_error_bound s N hs hNs R hR H
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨C*B+C*F+D*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH
  let w := (2*I*z)⁻¹
  let ρ := nlsRiccatiDensity a b N
  let c := nlsRiccatiResidualNextDensity a b N
  let P := nlsWKBMassPrimitive a b
  let v := nlsWKBCarrier a b N z
  let e (x : ℝ) := exp (-I*z*x)
  let q (x : ℝ) := (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w
  let f (x : ℝ) := I*q x*v x+I*ρ x*w^N*e x-w^(N+1)*(I*(c x+ρ x*P x))*e x
  have hw : ‖w‖ ≤ 1 := by
    simp only [w,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    apply inv_le_one_of_one_le₀
    linarith
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hc : Continuous c := continuous_nlsRiccatiResidualNextDensity a b ha hb N
  have hP : Continuous P := continuous_nlsWKBMassPrimitive a b ha.continuous hb.continuous
  have hv : Continuous v :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  have hq : Continuous q :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  have he : Continuous e := by dsimp only [e]; fun_prop
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      ‖f x‖ ≤ (C*B+C*F+D*‖ρ x‖)*‖w‖^(N+2) := by
    have hid : f x = I*(q x+ρ x*w^N-c x*w^(N+1))*v x-
        I*ρ x*w^N*(v x-e x*(1-w*P x))+I*c x*w^(N+1)*(v x-e x) := by
      dsimp only [f]
      rw [pow_succ]
      ring
    rw [hid]
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    simp only [norm_mul,norm_I,one_mul,norm_pow]
    have hrc := hres ab hab a b ha hb hpa hpb hca hcb x
    calc
      _ ≤ (C*‖w‖^(N+2))*B+(‖ρ x‖*‖w‖^N)*(D*‖w‖^2)+
          (C*‖w‖^(N+1))*(F*‖w‖) := add_le_add
        (add_le_add
          (mul_le_mul (hrc.2 w hw) (hcarrier ab hab a b ha hb hpa hpb hca hcb x hx z hz hzH).1
            (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (hlinear ab hab a b ha hb hpa hpb hca hcb x hx z hz hzH) (by positivity)))
        (mul_le_mul (mul_le_mul_of_nonneg_right hrc.1 (by positivity))
          (hfree ab hab a b ha hb hpa hpb hca hcb x hx z hz hzH) (norm_nonneg _) (by positivity))
      _ = _ := by rw [pow_add,pow_succ]; ring
  have hiρ : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ L := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  have hnorm (x : ℝ) : ‖I*q x*v x-nlsWKBLeadingScalar a b N z x-
      w^(N+1)*nlsWKBNextForcingDensity a b N x*e x‖ = ‖f x‖ := by
    congr 1
    dsimp only [f,nlsWKBLeadingScalar,nlsWKBNextForcingDensity,ρ,c,P,w,e]
    ring
  change (∫ x in (0:ℝ)..1, ‖I*q x*v x-nlsWKBLeadingScalar a b N z x-
    w^(N+1)*nlsWKBNextForcingDensity a b N x*e x‖) ≤ _
  simp_rw [hnorm]
  calc
    _ ≤ ∫ x in (0:ℝ)..1, (C*B+C*F+D*‖ρ x‖)*‖w‖^(N+2) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hf.norm.intervalIntegrable 0 1)
        ((by fun_prop : Continuous (fun x => (C*B+C*F+D*‖ρ x‖)*‖w‖^(N+2))).intervalIntegrable 0 1) hpoint
    _ = (C*B+C*F+D*(∫ x in (0:ℝ)..1, ‖ρ x‖))*‖w‖^(N+2) := by
      have h₁ : IntervalIntegrable (fun _ : ℝ => C*B+C*F) volume 0 1 := continuous_const.intervalIntegrable 0 1
      have h₂ : IntervalIntegrable (fun x : ℝ => D*‖ρ x‖) volume 0 1 :=
        (continuous_const.mul hρ.norm).intervalIntegrable 0 1
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_add h₁ h₂,
        intervalIntegral.integral_const_mul]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hiρ hD)) (by positivity)

end NLS.ZakharovShabat
