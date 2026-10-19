import NLS.ZakharovShabat.ClassicalLowerKernelExpansion
import NLS.ZakharovShabat.ClassicalLowerForcingExpansion

/-! # The lower response to the leading WKB forcing

The actual leading forced response has an explicit mass correction and an order-(N+2) error on the original Hs ball through N=s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The mass-primitive correction to the lower oscillatory response. -/
def nlsWKBMassCorrectionIntegral (a b r : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  exp (I*z*t)*(nlsWKBMassPrimitive a b t*(∫ x in (0:ℝ)..t, r x*exp (-2*I*z*x))-
    (∫ x in (0:ℝ)..t, nlsWKBMassPrimitive a b x*r x*exp (-2*I*z*x)))

/-- The lower response to the leading WKB forcing retains an explicit
order-(N+1) oscillatory correction and has a uniform order-(N+2) remainder.
The top Riccati density needs only its original L2 bound. -/
theorem exists_uniform_nlsWKB_leading_lower_first_order_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖(classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
              (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).2-
          nlsWKBLeadingTerm a b N z t-
          (-I)*((2*I*z)⁻¹)^(N+1)*nlsWKBMassCorrectionIntegral a b (nlsRiccatiDensity a b N) z t‖ ≤
          C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨C,hC,hkernel⟩ := exists_uniform_classical_lowerKernel_first_order_expansion s hs R hR H
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨C*Real.exp H*L,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let ρ := nlsRiccatiDensity a b N
  let w := (2*I*z)⁻¹
  let P := nlsWKBMassPrimitive a b
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hP : Continuous P := continuous_nlsWKBMassPrimitive a b ha.continuous hb.continuous
  have hiρ : (∫ x in (0:ℝ)..1, ‖ρ x‖) ≤ L := by
    have hi := integral_norm_le_sqrt_length_mul_L2 ρ 1 (by norm_num)
      (memLp_two_interval hρ 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    exact hi.trans (hL2 ab hab a b ha hb hpa hpb hca hcb)
  let f (x : ℝ) := exp (-I*z*x)*ρ x
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hscaled :
      (classicalForcedKernelSolution Φ
        (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
          (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).2 =
      (-I)*w^N*(classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z t).2 := by
    rw [classicalScalarForcing_snd_eq_lowerKernel_integral,
      classicalScalarForcing_snd_eq_lowerKernel_integral,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [nlsWKBLeadingScalar,f,ρ,w]
    ring
  have hk (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :=
    hkernel ab hab a b ha hb hpa hpb hca hcb z hz hzH t ⟨x,hx⟩
  have hbnd := norm_classical_lower_forcing_first_order_error_le Φ z ρ P hρ hP w C (Real.exp H)
    hC (Real.exp_pos H).le t (norm_exp_neg_I_mul_strip_le z H hzH) hk
  let Y := (classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z t).2
  let S := exp (I*z*t.val)*(∫ x in (0:ℝ)..t.val, ρ x*exp (-2*I*z*x))
  let Q := nlsWKBMassCorrectionIntegral a b ρ z t
  have hbnd' : ‖Y-S-w*Q‖ ≤ C*Real.exp H*‖w‖^2*L := by
    simpa only [Y,f,S,Q,nlsWKBMassCorrectionIntegral,P,mul_assoc] using
      hbnd.trans (mul_le_mul_of_nonneg_left hiρ (by positivity : 0 ≤ C*Real.exp H*‖w‖^2))
  rw [hscaled]
  have hid : (-I)*w^N*Y-nlsWKBLeadingTerm a b N z t-(-I)*w^(N+1)*Q =
      (-I)*w^N*(Y-S-w*Q) := by
    dsimp only [nlsWKBLeadingTerm,S,ρ,w]
    rw [pow_succ]
    ring
  change ‖(-I)*w^N*Y-nlsWKBLeadingTerm a b N z t-(-I)*w^(N+1)*Q‖ ≤ _
  rw [hid,norm_mul,norm_mul,norm_neg,norm_I,one_mul,norm_pow]
  calc
    _ ≤ ‖w‖^N*(C*Real.exp H*‖w‖^2*L) := mul_le_mul_of_nonneg_left hbnd' (by positivity)
    _ = (C*Real.exp H*L)*‖w‖^(N+2) := by rw [pow_add]; ring

end NLS.ZakharovShabat
