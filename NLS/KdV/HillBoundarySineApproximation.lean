import NLS.KdV.HillFreeModeProjection
import NLS.KdV.DirichletFreeSine
import NLS.Fourier.CircleUnitContinuous
import NLS.KdV.SingularHillSpectralAction

/-! A zero boundary trace turns the literal two-mode approximation into
a nearby physical sine vector. This applies to arbitrary complex vectors. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- The ACTUAL continuous contour projection fixes the identical H1
representative of every physical spectral-range vector. -/
theorem singularHillContinuousRieszProjection_fixed_of_physical_range
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (c : ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hc : sphere c rho ⊆ singularHillResolventSet q)
    (G : FourierLebesgueSpace (2:ℝ) 1 2)
    (hG : singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection q c rho).range) :
    singularHillContinuousRieszProjection q c rho (singularHillL2DomainInclusion G) =
      singularHillContinuousDomainInclusion G := by
  change singularHillContinuousDomainInclusion (singularHillRieszToH1 q c rho
    (singularHillL2BaseInclusion (singularHillL2DomainInclusion G))) = _
  rw [singularHillL2BaseInclusion_domain]
  change singularHillContinuousDomainInclusion (singularHillDomainRieszProjection q c rho G) = _
  rw [singularHillDomainRieszProjection_fixed_of_physical_range q c rho hrho hc G hG]

/-- A zero-trace continuous periodic function is within twice its actual
two-mode uniform approximation error of the corresponding sine line. -/
theorem exists_sine_approximation_of_zero_trace (n : ℕ+)
    (F : C(AddCircle (2:ℝ),ℂ)) (H : CircleL2) (h0 : F 0 = 0) :
    ∃ a : ℂ, ‖circleUnitContinuousRestriction F-a • dirichletFreeSineCurve n‖ ≤
      2*‖F-hillFreeContinuousModeProjection (n:ℕ) H‖ := by
  let a := fourierCoeff H (n:ℤ)
  let b := fourierCoeff H (-(n:ℤ))
  let E := ‖F-hillFreeContinuousModeProjection (n:ℕ) H‖
  have hab : ‖a+b‖ ≤ E := by
    have he := (F-hillFreeContinuousModeProjection (n:ℕ) H).norm_coe_le_norm (0 : AddCircle (2:ℝ))
    have hz : (F-hillFreeContinuousModeProjection (n:ℕ) H) 0 = -(a+b) := by
      simp [hillFreeContinuousModeProjection_apply,h0,a,b]
    rw [hz,norm_neg] at he
    exact he
  refine ⟨2*I*a,?_⟩
  apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ 2*E)).mpr
  intro x
  have hw : ‖wave (-(n:ℤ)) x.val‖ = 1 := by
    simp [wave,Complex.norm_exp]
  have hs : wave (n:ℤ) x.val-wave (-(n:ℤ)) x.val =
      2*I*sin ((Real.pi:ℂ)*(n:ℕ)*x.val) := by
    have hp : ((Real.pi:ℂ)*I*(n:ℤ))*x.val = ((Real.pi:ℂ)*(n:ℕ)*x.val)*I := by push_cast; ring
    have hm : ((Real.pi:ℂ)*I*(-(n:ℤ)))*x.val = -((Real.pi:ℂ)*(n:ℕ)*x.val)*I := by push_cast; ring
    simp only [wave,Int.cast_neg,hp,hm]
    rw [Complex.exp_mul_I,Complex.exp_mul_I,Complex.cos_neg,Complex.sin_neg]
    ring
  have he : (circleUnitContinuousRestriction F-(2*I*a) • dirichletFreeSineCurve n) x =
      (F-hillFreeContinuousModeProjection (n:ℕ) H) (x.val : AddCircle (2:ℝ))+
        (a+b)*wave (-(n:ℤ)) x.val := by
    change F (x.val : AddCircle (2:ℝ))-(2*I*a)*sin ((Real.pi:ℂ)*(n:ℕ)*x.val) = _
    rw [ContinuousMap.sub_apply,hillFreeContinuousModeProjection_apply]
    simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul,fourier_two_eq_wave]
    change F (x.val : AddCircle (2:ℝ))-(2*I*a)*sin ((Real.pi:ℂ)*(n:ℕ)*x.val) =
      F (x.val : AddCircle (2:ℝ))-(a*wave (n:ℤ) x.val+b*wave (-(n:ℤ)) x.val)+
        (a+b)*wave (-(n:ℤ)) x.val
    linear_combination a*hs
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul,hw,mul_one]
  have hx := (F-hillFreeContinuousModeProjection (n:ℕ) H).norm_coe_le_norm (x.val : AddCircle (2:ℝ))
  change _ ≤ E at hx
  linarith

end NLS.KdV
