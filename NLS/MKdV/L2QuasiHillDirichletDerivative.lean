import NLS.MKdV.L2QuasiHillWeakEquation
import NLS.MKdV.L2QuasiHillScalarNontrivial
import NLS.FunctionalAnalysis.UnitIntervalMean

/-! # The actual rough Dirichlet energy derivative

Symmetry of the factored bilinear form and its two Green identities give
the two-energy Lagrange identity. Analyticity in the uniform curve norm
then gives the original Dirichlet characteristic derivative at a zero.
The integral is the unconjugated scalar square, so its nonvanishing for
real original potentials is a separate weak spectral argument.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem shiftedMiuraWeakForm_comm (u : IntervalL2) (c : ℂ) (y φ : Curve ℂ) :
    shiftedMiuraWeakForm u c y φ = shiftedMiuraWeakForm u c φ y := by
  unfold shiftedMiuraWeakForm
  congr 1
  · apply intervalIntegral.integral_congr
    intro s _
    ring
  · congr 1
    apply intervalIntegral.integral_congr
    intro s _
    ring

theorem analyticAt_l2QuasiHillPosition_energy (u : IntervalL2) (mu : ℂ) (v : ℂ × ℂ) :
    AnalyticAt ℂ (fun lambda => l2QuasiHillPosition u lambda v) mu := by
  have hs := (analyticOnNhd_l2QuasiHillSolution_joint v (mu,u) (mem_univ _)).comp
    (f := fun lambda : ℂ => (lambda,u)) (analyticAt_id.prod analyticAt_const)
  exact ((ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).analyticAt _).comp hs

/-- The Lagrange identity at a Dirichlet zero, with initial position zero
and initial quasi-derivative one in both solutions. -/
theorem l2QuasiHillDirichlet_two_energy_identity (u : IntervalL2) (lambda mu : ℂ)
    (hz : extend (l2QuasiHillPosition u lambda (0,1)) 1 = 0) :
    extend (l2QuasiHillMomentum u lambda (0,1)) 1*
        extend (l2QuasiHillPosition u mu (0,1)) 1 =
      (mu-lambda)*(∫ s in (0 : ℝ)..1,
        extend (l2QuasiHillPosition u lambda (0,1)) s*extend (l2QuasiHillPosition u mu (0,1)) s) := by
  let y := l2QuasiHillPosition u lambda (0,1)
  let z := l2QuasiHillPosition u mu (0,1)
  have hg := l2QuasiHill_weak_green_identity u lambda 0 (0,1) z
    (absolutelyContinuous_l2QuasiHillPosition u mu (0,1)) (memLp_deriv_l2QuasiHillPosition u mu (0,1))
  have hh := l2QuasiHill_weak_green_identity u mu 0 (0,1) y
    (absolutelyContinuous_l2QuasiHillPosition u lambda (0,1)) (memLp_deriv_l2QuasiHillPosition u lambda (0,1))
  have hm : (∫ s in (0 : ℝ)..1, extend z s*extend y s) =
      ∫ s in (0 : ℝ)..1, extend y s*extend z s := by
    apply intervalIntegral.integral_congr
    intro s _
    ring
  change shiftedMiuraWeakForm u 0 y z = _ at hg
  change shiftedMiuraWeakForm u 0 z y = _ at hh
  rw [shiftedMiuraWeakForm_comm u 0 z y] at hh
  have hy₀ : extend y 0 = 0 := l2QuasiHillPosition_initial _ _ _
  have hz₀ : extend z 0 = 0 := l2QuasiHillPosition_initial _ _ _
  have hy₁ : extend y 1 = 0 := hz
  rw [hy₀,hy₁,mul_zero,mul_zero,sub_self,zero_add,hm,sub_zero] at hh
  rw [hz₀,mul_zero,sub_zero,sub_zero] at hg
  dsimp only [y,z] at hg hh
  linear_combination hh-hg

/-- Exact energy derivative normalization at every complex rough
Dirichlet root, before any reality or simplicity assumption. -/
theorem l2QuasiHillDirichlet_derivative_identity (u : IntervalL2) (lambda : ℂ)
    (hz : extend (l2QuasiHillPosition u lambda (0,1)) 1 = 0) :
    extend (l2QuasiHillMomentum u lambda (0,1)) 1*
        deriv (fun mu : ℂ => extend (l2QuasiHillPosition u mu (0,1)) 1) lambda =
      ∫ s in (0 : ℝ)..1, extend (l2QuasiHillPosition u lambda (0,1)) s*
        extend (l2QuasiHillPosition u lambda (0,1)) s := by
  let Y := l2QuasiHillPosition u lambda (0,1)
  let M : ℂ → ℂ := fun mu => unitIntervalMean (Y*l2QuasiHillPosition u mu (0,1))
  let S : ℂ → ℂ := fun mu => extend (l2QuasiHillPosition u mu (0,1)) 1
  have hM : AnalyticAt ℂ M lambda :=
    (unitIntervalMean (E := ℂ)).analyticAt _ |>.comp
      (analyticAt_const.mul (analyticAt_l2QuasiHillPosition_energy u lambda (0,1)))
  have hS : AnalyticAt ℂ S lambda := by
    have he := ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0 : ℝ) 1)).analyticAt _).comp
      (analyticAt_l2QuasiHillPosition_energy u lambda (0,1))
    apply he.congr
    exact Filter.Eventually.of_forall (fun mu =>
      (extend_coe (l2QuasiHillPosition u mu (0,1)) ⟨1,by constructor <;> norm_num⟩).symm)
  have he : (fun mu => extend (l2QuasiHillMomentum u lambda (0,1)) 1*S mu) =
      fun mu => (mu-lambda)*M mu := by
    funext mu
    exact l2QuasiHillDirichlet_two_energy_identity u lambda mu hz
  have hL := hS.differentiableAt.hasDerivAt.const_mul (extend (l2QuasiHillMomentum u lambda (0,1)) 1)
  have hR := ((hasDerivAt_id lambda).sub_const lambda).mul hM.differentiableAt.hasDerivAt
  rw [he] at hL
  simpa only [id_eq,sub_self,zero_mul,one_mul,add_zero,S,M,Y,unitIntervalMean_apply,
    NLS.LinearVolterra.extend,ContinuousMap.mul_apply] using hL.unique hR

end NLS.MKdV
