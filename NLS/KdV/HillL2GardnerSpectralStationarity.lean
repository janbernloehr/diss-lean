import NLS.KdV.HillL2GardnerDirections
import NLS.KdV.HillL2SourcePrimitive
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Actual source stationarity of the continued Hill spectral data

Actual Fourier Gardner directions annihilate the joint discriminant
variation. The proved normalized primitive derivative then gives primitive
stationarity on its actual open continuation domain, with no presumed
isospectral path or differentiated pointwise invariance statement.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- Joint trace differentiation in the actual source tangent also vanishes. -/
theorem fderiv_hillL2Discriminant_joint_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) :
    (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
      (0,hillL2DiscriminantGardnerDirection q b)=0 := by
  have hd := ((analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)).differentiableAt.hasFDerivAt.comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b)) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p a) q)
    (hillL2DiscriminantGardnerDirection q b)=
      (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
        (0,hillL2DiscriminantGardnerDirection q b) at he
  exact he.symm.trans (fderiv_hillL2Discriminant_gardnerDirection_eq_zero q a b)

/-- The actual continued primitive has zero source variation along every trace direction. -/
theorem fderiv_hillL2ContinuedPrimitive_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedPrimitive (a,p)) q)
      (hillL2DiscriminantGardnerDirection q b)=0 := by
  have hd := ((hasFDerivAt_hillL2ContinuedPrimitive (a,q) ha).comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b)) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedPrimitive (a,p)) q)
    (hillL2DiscriminantGardnerDirection q b)=
      (hillL2ContinuedRoot (a,q))⁻¹*
        (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
          (0,hillL2DiscriminantGardnerDirection q b) at he
  rw [fderiv_hillL2Discriminant_joint_gardnerDirection_eq_zero,mul_zero] at he
  exact he

/-- The joint primitive differential is stationary on exactly the same actual domain. -/
theorem fderiv_hillL2ContinuedPrimitive_joint_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ hillL2ContinuedPrimitive (a,q)) (0,hillL2DiscriminantGardnerDirection q b)=0 := by
  rw [(hasFDerivAt_hillL2ContinuedPrimitive (a,q) ha).fderiv]
  change (hillL2ContinuedRoot (a,q))⁻¹*
    (fderiv ℂ (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) (a,q))
      (0,hillL2DiscriminantGardnerDirection q b)=0
  rw [fderiv_hillL2Discriminant_joint_gardnerDirection_eq_zero,mul_zero]

/-- The sign-normalized continued root is also stationary on its actual open domain. -/
theorem fderiv_hillL2ContinuedRoot_joint_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,hillL2DiscriminantGardnerDirection q b)=0 := by
  have heq : (fun t : ℂ × Coeff 2 => 2*sinh (hillL2ContinuedPrimitive t)) =ᶠ[𝓝 (a,q)]
      hillL2ContinuedRoot := by
    filter_upwards [isOpen_hillL2ContinuationDomain.mem_nhds ha] with t ht
    exact (hillL2ContinuedPrimitive_trace t ht).2
  have hd := (((analyticOnNhd_hillL2ContinuedPrimitive (a,q) ha).differentiableAt.hasFDerivAt.csinh).const_smul (2 : ℂ)).congr_of_eventuallyEq heq.symm
  have he := congrArg (fun L : (ℂ × Coeff 2) →L[ℂ] ℂ => L (0,hillL2DiscriminantGardnerDirection q b)) hd.fderiv
  change (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,hillL2DiscriminantGardnerDirection q b)=
    2*(cosh (hillL2ContinuedPrimitive (a,q))*
      (fderiv ℂ hillL2ContinuedPrimitive (a,q)) (0,hillL2DiscriminantGardnerDirection q b)) at he
  rw [fderiv_hillL2ContinuedPrimitive_joint_gardnerDirection_eq_zero q a b ha,mul_zero,mul_zero] at he
  exact he

theorem fderiv_hillL2ContinuedRoot_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) (ha : (a,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedRoot (a,p)) q)
      (hillL2DiscriminantGardnerDirection q b)=0 := by
  have hd := ((analyticOnNhd_hillL2ContinuedRoot (a,q) ha).differentiableAt.hasFDerivAt.comp
    q (hasFDerivAt_prodMk_right a q)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (hillL2DiscriminantGardnerDirection q b)) hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2ContinuedRoot (a,p)) q)
    (hillL2DiscriminantGardnerDirection q b)=
      (fderiv ℂ hillL2ContinuedRoot (a,q)) (0,hillL2DiscriminantGardnerDirection q b) at he
  exact he.trans (fderiv_hillL2ContinuedRoot_joint_gardnerDirection_eq_zero q a b ha)

/-- Source stationarity commutes with the actual spectral derivative of the trace. -/
theorem fderiv_deriv_hillL2Discriminant_gardnerDirection_eq_zero
    (q : Coeff 2) (a b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => deriv (hillL2Discriminant p) a) q)
      (hillL2DiscriminantGardnerDirection q b)=0 := by
  let F (t : ℂ × Coeff 2) := hillL2Discriminant t.2 t.1
  let X := hillL2DiscriminantGardnerDirection q b
  let e : ℂ × Coeff 2 := (1,0)
  let v : ℂ × Coeff 2 := (0,X)
  let ev : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ v
  let ee : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ e
  have ha := analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)
  have hdF : DifferentiableAt ℂ (fderiv ℂ F) (a,q) :=
    (analyticOnNhd_hillL2Discriminant_joint.fderiv (a,q) (mem_univ _)).differentiableAt
  have hv := (ev.hasFDerivAt.comp (a,q) hdF.hasFDerivAt).comp_hasDerivAt a
    ((hasDerivAt_id a).prodMk (hasDerivAt_const a q))
  have hdf : (fderiv ℂ (fderiv ℂ F) (a,q)) e v=0 := by
    have heq : (fun z : ℂ => (fderiv ℂ F (z,q)) v)=(fun _ : ℂ => (0 : ℂ)) := by
      funext z
      exact fderiv_hillL2Discriminant_joint_gardnerDirection_eq_zero q z b
    have he := hv.deriv
    change deriv (fun z : ℂ => (fderiv ℂ F (z,q)) v) a=
      (fderiv ℂ (fderiv ℂ F) (a,q)) e v at he
    rw [heq,deriv_const] at he
    exact he.symm
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (((ee.hasFDerivAt.comp (a,q) hdF.hasFDerivAt).comp q (hasFDerivAt_prodMk_right a q)).fderiv)
  change (fderiv ℂ (fun p : Coeff 2 => (fderiv ℂ F (a,p)) e) q) X=
    (fderiv ℂ (fderiv ℂ F) (a,q)) v e at he
  have hspec : (fun p : Coeff 2 => deriv (hillL2Discriminant p) a)=
      (fun p : Coeff 2 => (fderiv ℂ F (a,p)) e) := by
    funext p
    exact deriv_spectral_section_eq_fderiv F a p
      (analyticOnNhd_hillL2Discriminant_joint (a,p) (mem_univ _)).differentiableAt
  rw [hspec]
  exact he.trans (((ha.contDiffAt.isSymmSndFDerivAt_of_omega).eq v e).trans hdf)

end NLS.KdV
