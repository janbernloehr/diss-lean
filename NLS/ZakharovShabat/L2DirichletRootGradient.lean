import NLS.ZakharovShabat.L2DirichletNormalization
import NLS.ZakharovShabat.ClassicalDirichletGradientNormalization

/-! # Normalized squared-eigenfunction gradients of actual physical L2 roots

The normalization is bilinear, without complex conjugation. Simplicity
supplies its nonvanishing, and the formula differentiates any continuous
local selection of Dirichlet zeros in the full physical L2 space.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra
namespace NLS.ZakharovShabat

def l2DirichletNormalizedGradient (u : IntervalPairL2) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  ((l2DirichletEigenfunction u z s).2^2/l2DirichletNormalization u z,
   (l2DirichletEigenfunction u z s).1^2/l2DirichletNormalization u z)

theorem l2DirichletNormalizedGradient_eq_characteristic_quotient
    (u : IntervalPairL2) (z : ℂ)
    (hz : l2SeparatedCharacteristic .dirichlet u z = 0)
    (hsimple : deriv (l2SeparatedCharacteristic .dirichlet u) z ≠ 0) (s : ℝ) :
    l2DirichletNormalizedGradient u z s =
      -(deriv (l2SeparatedCharacteristic .dirichlet u) z)⁻¹ •
        l2SeparatedGradient .dirichlet u z s := by
  have hQ := l2DirichletNormalization_ne_zero_of_simple u z hz hsimple
  have hα : l2DirichletDualFactor u z ≠ 0 := by
    rw [deriv_l2DirichletCharacteristic_of_root u z hz] at hsimple
    exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hsimple).1).2
  rw [l2SeparatedGradient_dirichlet_of_root u z hz s,
    deriv_l2DirichletCharacteristic_of_root u z hz]
  apply Prod.ext <;> simp only [l2DirichletNormalizedGradient,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals field_simp [hQ,hα,I_ne_zero]

/-- G.7's normalized integral is the actual derivative of a local simple root. -/
theorem fderiv_l2DirichletRoot_eq_normalized_integral
    (μ : IntervalPairL2 → ℂ) (u : IntervalPairL2)
    (hμ : ContinuousAt μ u)
    (hroot : ∀ᶠ w in 𝓝 u, l2SeparatedCharacteristic .dirichlet w (μ w) = 0)
    (hsimple : deriv (l2SeparatedCharacteristic .dirichlet u) (μ u) ≠ 0)
    (h : IntervalPairL2) :
    (fderiv ℂ μ u) h = ∫ s in (0 : ℝ)..1,
      (l2DirichletNormalizedGradient u (μ u) s).1*h.ofLp.1 s+
      (l2DirichletNormalizedGradient u (μ u) s).2*h.ofLp.2 s := by
  rw [fderiv_l2SeparatedRoot_eq_gradient_quotient .dirichlet μ u hμ hroot hsimple h,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [l2DirichletNormalizedGradient_eq_characteristic_quotient u (μ u)
    hroot.self_of_nhds hsimple s]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem l2DirichletEigenfunction_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (s : Icc (0 : ℝ) 1) :
    l2DirichletEigenfunction (continuousPotentialL2Class Φ) z s =
      classicalDirichletEigenfunction Φ z s := by
  simp only [l2DirichletEigenfunction,extend_coe,l2SolutionCurve_of_continuous,
    classicalSolutionCurve_apply,classicalDirichletEigenfunction]

theorem l2DirichletNormalization_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    l2DirichletNormalization (continuousPotentialL2Class Φ) z =
      classicalDirichletNormalization Φ z := by
  unfold l2DirichletNormalization classicalDirichletNormalization
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  dsimp only
  rw [l2DirichletEigenfunction_of_continuous Φ z ⟨s,hs'⟩]

theorem l2DirichletNormalizedGradient_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (s : Icc (0 : ℝ) 1) :
    l2DirichletNormalizedGradient (continuousPotentialL2Class Φ) z s =
      classicalDirichletNormalizedGradient Φ z s := by
  simp only [l2DirichletNormalizedGradient,classicalDirichletNormalizedGradient,
    l2DirichletNormalization_of_continuous,l2DirichletEigenfunction_of_continuous]

@[simp] theorem l2DirichletNormalization_free (z : ℂ) :
    l2DirichletNormalization 0 z = 2 := by
  rw [← continuousPotentialL2Class_zero,l2DirichletNormalization_of_continuous,
    classicalDirichletNormalization_free]

theorem l2DirichletNormalizedGradient_free (z : ℂ) (s : Icc (0 : ℝ) 1) :
    l2DirichletNormalizedGradient 0 z s =
      (exp (2*I*z*s.val)/2,exp (-2*I*z*s.val)/2) := by
  rw [← continuousPotentialL2Class_zero,l2DirichletNormalizedGradient_of_continuous,
    classicalDirichletNormalizedGradient_free]

end NLS.ZakharovShabat
