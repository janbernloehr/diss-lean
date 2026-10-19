import NLS.ZakharovShabat.ClassicalDiagonalApproximation
import NLS.ZakharovShabat.SobolevWKBSecondColumn

/-! # The leading diagonal approximation on Sobolev balls

The actual leading upper response has an order-(N+2) approximation uniformly on original Hs balls through N=s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The leading diagonal approximation retains the full free lower
oscillatory response inside the integration-by-parts formula. -/
def nlsWKBLeadingDiagonalApproximation (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  classicalDiagonalApproximation a (nlsWKBLeadingScalar a b N z)
    (nlsWKBLeadingTerm a b N z) z t

/-- The actual leading upper response differs from its diagonal
approximation by order N+2 on original Hs balls, including N=s. -/
theorem exists_uniform_nlsWKB_leading_diagonal_approximation_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖(classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
              (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).1-
          nlsWKBLeadingDiagonalApproximation a b N z t‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨L,hL,hder⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s 1 hs R hR
  obtain ⟨C₀,hC₀,hforced⟩ := exists_uniform_nlsWKB_leading_forced_solution_error_bound s N hs hNs R hR H
  obtain ⟨C₁,hC₁,hfree⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s N hs hNs R hR H
  refine ⟨(A+(Real.exp H)^2*(L+A^2))*(C₀+C₁),by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let f := nlsWKBLeadingScalar a b N z
  let S := nlsWKBLeadingTerm a b N z
  let w := (2*I*z)⁻¹
  have hf : Continuous f := continuous_nlsWKBLeadingScalar a b ha hb N z
  have hρ : Continuous (nlsRiccatiDensity a b N) := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hS : Continuous S := by
    have hi := (intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ))
      (show Continuous (fun x : ℝ => nlsRiccatiDensity a b N x*exp (-2*I*z*x)) by fun_prop)).continuous
    change Continuous (fun t : ℝ => -I*w^N*exp (I*z*t)*
      (∫ x in (0:ℝ)..t, nlsRiccatiDensity a b N x*exp (-2*I*z*x)))
    fun_prop
  have habswap : ‖(ab.2,ab.1)‖ ≤ R := by simpa only [Prod.norm_def,max_comm] using hab
  have hp (x : ℝ) (_ : x ∈ Icc (0:ℝ) 1) : ‖a x‖ ≤ A ∧ ‖b x‖ ≤ A :=
    ⟨hpot ab hab a b ha hb hpa hpb hca hcb x,
      hpot (ab.2,ab.1) habswap b a hb ha hpb hpa hcb hca x⟩
  have hd : (∫ x in (0:ℝ)..1, ‖deriv a x‖) ≤ L := by
    have hda : Continuous (deriv a) := ha.continuous_deriv (by simp)
    have hi := integral_norm_le_sqrt_length_mul_L2 (deriv a) 1 (by norm_num)
      (memLp_two_interval hda 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    apply hi.trans
    simpa only [nlsRiccatiDensity_one,Pi.neg_apply,norm_neg] using
      hder (ab.2,ab.1) habswap b a hb ha hpb hpa hcb hca
  have he (x : Icc (0:ℝ) 1) :
      ‖classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z x-(0,S x)‖ ≤
      (C₀+C₁)*‖w‖^(N+1) := by
    let X := nlsWKBVector a b N z x-classicalSolution Φ z (nlsWKBVector a b N z 0) x
    let Y := classicalForcedKernelSolution Φ (classicalScalarForcing f hf) z x
    let Z : ℂ × ℂ := (0,S x)
    have h₀ : ‖X-Y‖ ≤ C₀*‖w‖^(N+1) := hforced ab hab a b ha hb hpa hpb hca hcb z hzn hzH x
    have h₁ : ‖X-Z‖ ≤ C₁*‖w‖^(N+1) := hfree ab hab a b ha hb hpa hpb hca hcb z hzn hzH x
    change ‖Y-Z‖ ≤ _
    calc
      _ = ‖-(X-Y)+(X-Z)‖ := by congr 1; abel
      _ ≤ ‖-(X-Y)‖+‖X-Z‖ := norm_add_le _ _
      _ ≤ C₀*‖w‖^(N+1)+C₁*‖w‖^(N+1) := by rw [norm_neg]; exact add_le_add h₀ h₁
      _ = _ := by ring
  have hexp (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      ‖exp (I*z*x)‖ ≤ Real.exp H ∧ ‖exp (-I*z*x)‖ ≤ Real.exp H := by
    constructor
    · simpa only [mul_neg,neg_mul,neg_neg] using norm_exp_neg_I_mul_strip_le (-z) H (by simpa using hzH) x hx
    · exact norm_exp_neg_I_mul_strip_le z H hzH x hx
  have hh := norm_classicalScalarForcing_diagonal_approximation_le a b f S
    (ha.of_le (by simp)) hb.continuous hf hS z (norm_pos_iff.mp (by linarith))
    A (Real.exp H) ((C₀+C₁)*‖w‖^(N+1)) L hA (Real.exp_pos _).le (by positivity) hp hexp hd he t
  apply hh.trans_eq
  change ‖w‖*(A+(Real.exp H)^2*(L+A^2))*((C₀+C₁)*‖w‖^(N+1)) = _
  rw [show N+2 = (N+1)+1 by omega,pow_succ]
  ring

end NLS.ZakharovShabat
