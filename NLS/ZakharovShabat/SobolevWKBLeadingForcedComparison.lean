import NLS.ZakharovShabat.SobolevWKBLeadingForcing
import NLS.ZakharovShabat.ClassicalLeadingForcedResidual
import NLS.ZakharovShabat.ClassicalScalarForcingFreeComparison
import NLS.ZakharovShabat.NLSWKBComparison

/-! # Uniform leading forced WKB comparison

The actual leading forced correction leaves an order-(N+1) error on every original Hs ball, retaining the top density exactly.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The explicit leading scalar forcing, retaining its free oscillation. -/
def nlsWKBLeadingScalar (a b : ℝ → ℂ) (N : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  -I*nlsRiccatiDensity a b N x*((2*I*z)⁻¹)^N*exp (-I*z*x)

theorem continuous_nlsWKBLeadingScalar (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) (z : ℂ) :
    Continuous (nlsWKBLeadingScalar a b N z) := by
  have hρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  unfold nlsWKBLeadingScalar
  fun_prop

/-- The actual leading forced correction leaves a uniform order-(N+1)
solution error, while retaining the top Riccati density exactly. -/
theorem exists_uniform_nlsWKB_leading_forced_solution_error_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBVector a b N z t-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (nlsWKBVector a b N z 0) t-
          classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z) (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t‖ ≤
            C*‖(2*I*z)⁻¹‖^(N+1) := by
  obtain ⟨A,hA,haB⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨C,hC,hres⟩ := exists_uniform_nlsWKB_leading_forcing_error_bound s N hs hNs R hR H
  refine ⟨4*(Real.exp (A+H))^2*C,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hzn hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    apply norm_prod_le_iff.mpr
    exact ⟨haB ab hab a b ha hb hpa hpb hca hcb x,
      haB (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  have hz : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hu : Continuous (nlsWKBVector a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBVector a b ha hb N z hz x).differentiableAt).continuous
  have hc : Continuous (nlsWKBCarrier a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  let q (x : ℝ) := (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) (2*I*z)⁻¹
  have hq : Continuous q :=
    (continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f (x : ℝ) := I*q x*nlsWKBCarrier a b N z x
  have hf : Continuous f := (continuous_const.mul hq).mul hc
  let g := classicalScalarForcing f hf
  let h := classicalScalarForcing (nlsWKBLeadingScalar a b N z) (continuous_nlsWKBLeadingScalar a b ha hb N z)
  have hd (x : Icc (0:ℝ) 1) : HasDerivAt (nlsWKBVector a b N z)
      (classicalODECoefficient (Φ x) z (nlsWKBVector a b N z x)+g x) x :=
    hasDerivAt_nlsWKBVector a b ha hb N z hz x
  have hdiff : (∫ x in (0:ℝ)..1, ‖extend (g-h) x‖) ≤ C*‖(2*I*z)⁻¹‖^(N+1) := by
    convert hres ab hab a b ha hb hpa hpb hca hcb z hzn hzH using 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    let u : Icc (0:ℝ) 1 := ⟨x,hx⟩
    change ‖extend (g-h) u‖ = _
    rw [extend_coe]
    simp only [g,h,classicalScalarForcing,ContinuousMap.sub_apply,ContinuousMap.coe_mk,
      Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _),nlsWKBLeadingScalar,f,q]
    congr 1
    ring
  have he := norm_sub_classicalSolution_sub_forced_le_integral_residual Φ g h z H hzH _ hu hd t
  apply he.trans
  calc
    _ ≤ 4*(Real.exp (A+H))^2*(C*‖(2*I*z)⁻¹‖^(N+1)) := by
      apply mul_le_mul _ hdiff (intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
