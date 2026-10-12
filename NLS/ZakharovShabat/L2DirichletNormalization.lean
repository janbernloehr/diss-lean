import NLS.ZakharovShabat.L2SpectralVariation
import NLS.ZakharovShabat.L2SeparatedRootGradient

/-! # Bilinear normalization of actual physical L2 Dirichlet eigenfunctions

At a root the dual solution is proportional to the forward eigenfunction.
The spectral integral identifies their common factor, so simplicity gives
a nonzero bilinear normalization without a separate assumption.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

def l2DirichletEigenfunction (u : IntervalPairL2) (z : ℂ) : ℝ → ℂ × ℂ :=
  extend (l2SolutionCurve u z (1,1))

def l2DirichletNormalization (u : IntervalPairL2) (z : ℂ) : ℂ :=
  2*∫ s in (0 : ℝ)..1, (l2DirichletEigenfunction u z s).1*(l2DirichletEigenfunction u z s).2

def l2DirichletDualFactor (u : IntervalPairL2) (z : ℂ) : ℂ :=
  classicalSeparatedEndpointCLM .dirichlet (l2SolutionCurve u z (1,0) ⟨1,by norm_num⟩)

/-- This polynomial identity holds at every point, before imposing a root. -/
theorem l2SeparatedGradient_eq_dual_product (b : BoundaryCondition) (u : IntervalPairL2) (z : ℂ) (s : ℝ) :
    l2SeparatedGradient b u z s =
      (I*(extend (l2EndpointDualCurve u z (classicalSeparatedEndpointCLM b)) s).2*
          (extend (l2SolutionCurve u z (1,extensionSign b)) s).2,
       I*(extend (l2EndpointDualCurve u z (classicalSeparatedEndpointCLM b)) s).1*
          (extend (l2SolutionCurve u z (1,extensionSign b)) s).1) := by
  simp only [l2SeparatedGradient,l2EndpointGradient,l2EndpointDualCurve,NLS.LinearVolterra.extend,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

theorem l2DirichletDualCurve_of_root (u : IntervalPairL2) (z : ℂ)
    (hz : l2SeparatedCharacteristic .dirichlet u z = 0) :
    l2EndpointDualCurve u z (classicalSeparatedEndpointCLM .dirichlet) =
      l2DirichletDualFactor u z • l2SolutionCurve u z (1,1) := by
  have he := hz
  rw [l2SeparatedCharacteristic_eq_endpoint,l2SolutionCurve_linearCombination] at he
  simp only [extensionSign,ContinuousMap.add_apply,one_smul,map_add] at he
  have hb : classicalSeparatedEndpointCLM .dirichlet (l2SolutionCurve u z (0,1) ⟨1,by norm_num⟩) =
      -l2DirichletDualFactor u z := by
    dsimp only [l2DirichletDualFactor]
    linear_combination he
  unfold l2EndpointDualCurve
  rw [hb,l2SolutionCurve_linearCombination u z (1,1)]
  ext t <;> simp [l2DirichletDualFactor] <;> ring

/-- At a root, the characteristic gradient is the reversed square of the actual eigenfunction. -/
theorem l2SeparatedGradient_dirichlet_of_root (u : IntervalPairL2) (z : ℂ)
    (hz : l2SeparatedCharacteristic .dirichlet u z = 0) (s : ℝ) :
    l2SeparatedGradient .dirichlet u z s = (I*l2DirichletDualFactor u z) •
      ((l2DirichletEigenfunction u z s).2^2,(l2DirichletEigenfunction u z s).1^2) := by
  rw [l2SeparatedGradient_eq_dual_product,l2DirichletDualCurve_of_root u z hz]
  apply Prod.ext <;>
    simp only [l2DirichletEigenfunction,NLS.LinearVolterra.extend,ContinuousMap.smul_apply,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul,extensionSign] <;> ring

/-- The actual spectral derivative has the same dual factor and the bilinear normalization. -/
theorem deriv_l2DirichletCharacteristic_of_root (u : IntervalPairL2) (z : ℂ)
    (hz : l2SeparatedCharacteristic .dirichlet u z = 0) :
    deriv (l2SeparatedCharacteristic .dirichlet u) z =
      -I*l2DirichletDualFactor u z*l2DirichletNormalization u z := by
  have he : l2SeparatedCharacteristic .dirichlet u =
      fun w => classicalSeparatedEndpointCLM .dirichlet (l2SolutionCurve u w (1,1) ⟨1,by norm_num⟩) :=
    funext (l2SeparatedCharacteristic_eq_endpoint .dirichlet u)
  rw [he,deriv_l2Endpoint_eq_spectral_integral,l2DirichletDualCurve_of_root u z hz]
  have hi : (∫ s in (0 : ℝ)..1,
      -I*((extend (l2DirichletDualFactor u z • l2SolutionCurve u z (1,1)) s).2*
        (extend (l2SolutionCurve u z (1,1)) s).1+
        (extend (l2DirichletDualFactor u z • l2SolutionCurve u z (1,1)) s).1*
          (extend (l2SolutionCurve u z (1,1)) s).2)) =
      ∫ s in (0 : ℝ)..1, (-2*I*l2DirichletDualFactor u z)*
        ((l2DirichletEigenfunction u z s).1*(l2DirichletEigenfunction u z s).2) := by
    apply intervalIntegral.integral_congr
    intro s _
    simp only [l2DirichletEigenfunction,NLS.LinearVolterra.extend,ContinuousMap.smul_apply,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [hi,intervalIntegral.integral_const_mul]
  unfold l2DirichletNormalization
  ring

/-- Simplicity proves nonzero normalization in the full physical L2 space. -/
theorem l2DirichletNormalization_ne_zero_of_simple (u : IntervalPairL2) (z : ℂ)
    (hz : l2SeparatedCharacteristic .dirichlet u z = 0)
    (hsimple : deriv (l2SeparatedCharacteristic .dirichlet u) z ≠ 0) :
    l2DirichletNormalization u z ≠ 0 := by
  rw [deriv_l2DirichletCharacteristic_of_root u z hz] at hsimple
  exact (mul_ne_zero_iff.mp hsimple).2

end NLS.ZakharovShabat
