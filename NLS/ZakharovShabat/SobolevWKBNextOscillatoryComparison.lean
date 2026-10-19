import NLS.ZakharovShabat.SobolevWKBNextScalarComparison
import NLS.ZakharovShabat.ClassicalForcedKernelLinearity
import NLS.ZakharovShabat.ClassicalLeadingForcedResidual

/-! # The full WKB error after the next oscillatory correction

Retaining the actual leading forced response and the next free term leaves an order-(N+2) vector error on original Hs balls.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- After retaining the actual leading forced response and the explicit
next free term, the full WKB vector has an order-(N+2) error uniformly on
the original Hs ball, including N=s. -/
theorem exists_uniform_nlsWKB_next_oscillatory_error_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖nlsWKBVector a b N z t-
          classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (nlsWKBVector a b N z 0) t-
          classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
              (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t-
          (0,nlsWKBNextFreeTerm a b N z t)‖ ≤ C*‖(2*I*z)⁻¹‖^(N+2) := by
  have hs := hN.trans hNs
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨C,hC,hres⟩ := exists_uniform_nlsWKB_next_forcing_error_bound s N hN hNs R hR H
  obtain ⟨D,hD,hnext⟩ := exists_uniform_nlsWKB_next_scalar_free_error_bound s N hs hNs R hR H
  refine ⟨4*(Real.exp (A+H))^2*C+D,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let w := (2*I*z)⁻¹
  have hΦ : ‖Φ‖ ≤ A := by
    apply (ContinuousMap.norm_le _ hA).mpr
    intro x
    apply norm_prod_le_iff.mpr
    exact ⟨hpot ab hab a b ha hb hpa hpb hca hcb x,
      hpot (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca x⟩
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hu : Continuous (nlsWKBVector a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBVector a b ha hb N z hz0 x).differentiableAt).continuous
  have hc : Continuous (nlsWKBCarrier a b N z) :=
    (show Differentiable ℝ _ from fun x => (hasDerivAt_nlsWKBCarrier a b ha hb N z x).differentiableAt).continuous
  let q (x : ℝ) := (nlsRiccatiResidualPolynomial a b N).eval₂
    (Pi.evalRingHom (fun _ : ℝ => ℂ) x) w
  have hq : Continuous q :=
    (NLS.ComplexAnalysis.continuous_polynomial_function_eval _ (continuous_coeff_nlsRiccatiResidualPolynomial a b ha hb N)).comp
      (continuous_id.prodMk continuous_const)
  let f (x : ℝ) := I*q x*nlsWKBCarrier a b N z x
  have hf : Continuous f := (continuous_const.mul hq).mul hc
  let g := classicalScalarForcing f hf
  let h₁ := classicalScalarForcing (nlsWKBLeadingScalar a b N z) (continuous_nlsWKBLeadingScalar a b ha hb N z)
  let h₂ := classicalScalarForcing (nlsWKBNextScalar a b N z) (continuous_nlsWKBNextScalar a b ha hb N z)
  have hd (x : Icc (0:ℝ) 1) : HasDerivAt (nlsWKBVector a b N z)
      (classicalODECoefficient (Φ x) z (nlsWKBVector a b N z x)+g x) x :=
    hasDerivAt_nlsWKBVector a b ha hb N z hz0 x
  have hdiff : (∫ x in (0:ℝ)..1, ‖extend (g-(h₁+h₂)) x‖) ≤ C*‖w‖^(N+2) := by
    convert hres ab hab a b ha hb hpa hpb hca hcb z hz hzH using 1
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    let u : Icc (0:ℝ) 1 := ⟨x,hx⟩
    change ‖extend (g-(h₁+h₂)) u‖ = _
    rw [extend_coe]
    simp only [g,h₁,h₂,classicalScalarForcing,ContinuousMap.sub_apply,ContinuousMap.add_apply,
      ContinuousMap.coe_mk,Prod.mk_add_mk,Prod.mk_sub_mk,add_zero,sub_self,
      Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
    congr 1
    dsimp only [f,q,w,nlsWKBNextScalar]
    ring
  have he := norm_sub_classicalSolution_sub_forced_le_integral_residual Φ g (h₁+h₂) z H hzH _ hu hd t
  have he' : ‖nlsWKBVector a b N z t-classicalSolution Φ z (nlsWKBVector a b N z 0) t-
      classicalForcedKernelSolution Φ (h₁+h₂) z t‖ ≤
      (4*(Real.exp (A+H))^2*C)*‖w‖^(N+2) := by
    apply he.trans
    calc
      _ ≤ 4*(Real.exp (A+H))^2*(C*‖w‖^(N+2)) := by
        apply mul_le_mul _ hdiff (intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)) (by positivity)
        gcongr
      _ = _ := by ring
  rw [classicalForcedKernelSolution_add_forcing] at he'
  have hn := hnext ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let X := nlsWKBVector a b N z t-classicalSolution Φ z (nlsWKBVector a b N z 0) t
  let Y := classicalForcedKernelSolution Φ h₁ z t
  let Z := classicalForcedKernelSolution Φ h₂ z t
  let T : ℂ × ℂ := (0,nlsWKBNextFreeTerm a b N z t)
  change ‖X-Y-T‖ ≤ _
  calc
    _ = ‖(X-(Y+Z))+(Z-T)‖ := by congr 1; abel
    _ ≤ ‖X-(Y+Z)‖+‖Z-T‖ := norm_add_le _ _
    _ ≤ (4*(Real.exp (A+H))^2*C)*‖w‖^(N+2)+D*‖w‖^(N+2) := add_le_add he' hn
    _ = _ := by ring

end NLS.ZakharovShabat
