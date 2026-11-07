import NLS.KdV.SmoothKdVFourierEquation
import NLS.KdV.ClassicalKdVPhysicalAdapter

/-! For smooth physical profiles the independent integrated Fourier equation
is equivalent to the actual KdV PDE. This is not a converse regularity
claim for arbitrary L² distributional solutions. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open scoped ContDiff
namespace NLS.KdV

theorem hasDerivAt_kdvUnitFourierCoefficient
    {Q : ℝ → C(AddCircle (2 : ℝ),ℂ)} (ht : Differentiable ℝ Q) (n : ℤ) (t : ℝ) :
    HasDerivAt (fun τ => kdvUnitFourierCLM (Q τ) n)
      (kdvUnitFourierCLM (deriv Q t) n) t := by
  let L := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp kdvUnitFourierCLM).restrictScalars ℝ
  have h := L.hasFDerivAt.comp_hasDerivAt t (ht t).hasDerivAt
  simpa only [L,Function.comp_def,ContinuousLinearMap.coe_restrictScalars,
    ContinuousLinearMap.comp_apply] using! h

theorem periodic_kdv_time_derivative
    {Q : ℝ → C(AddCircle (2 : ℝ),ℂ)} (ht : Differentiable ℝ Q)
    (hp : ∀ t, Function.Periodic (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))) 1) (t : ℝ) :
    Function.Periodic (fun x : ℝ => deriv Q t (x : AddCircle (2 : ℝ))) 1 := by
  intro x
  let L := (ContinuousMap.evalCLM (R := ℝ) (M := ℂ) ((x+1 : ℝ) : AddCircle (2 : ℝ)))
  let R := (ContinuousMap.evalCLM (R := ℝ) (M := ℂ) (x : AddCircle (2 : ℝ)))
  have hl := L.hasFDerivAt.comp_hasDerivAt t (ht t).hasDerivAt
  have hr := R.hasFDerivAt.comp_hasDerivAt t (ht t).hasDerivAt
  have he : (fun τ => L (Q τ)) = fun τ => R (Q τ) := funext (fun τ => hp τ x)
  change HasDerivAt (fun τ => L (Q τ)) (L (deriv Q t)) t at hl
  change HasDerivAt (fun τ => R (Q τ)) (R (deriv Q t)) t at hr
  rw [he] at hl
  exact hl.unique hr

/-- Smooth physical equivalence, with no assumed spectral conservation. -/
theorem isFourierWeakPhysicalKdV_iff_equation
    (Q : ℝ → C(AddCircle (2 : ℝ),ℂ)) (ht : Differentiable ℝ Q)
    (hs : ∀ t, ContDiff ℝ ∞ (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))))
    (hp : ∀ t, Function.Periodic (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))) 1) :
    IsFourierWeakPhysicalKdV Q ↔
      ∀ t x : ℝ, deriv Q t (x : AddCircle (2 : ℝ)) =
        scalarClassicalKdVField (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))) x := by
  unfold IsFourierWeakPhysicalKdV
  have hcont : Continuous (fun t => kdvUnitFourierCLM (Q t)) :=
    kdvUnitFourierCLM.continuous.comp ht.continuous
  rw [isFourierWeakKdVCoefficients_iff (fun t => kdvUnitFourierCLM (Q t)) hcont]
  have hfield (t : ℝ) (n : ℤ) := periodOneCoefficient_scalarClassicalKdVField
    (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))) (hs t) (hp t)
    (kdvUnitFourierCLM (Q t)) (kdvUnitFourierCLM_eq_periodOneCoefficient _ (hp t)) n
  have hcoeff (t : ℝ) (n : ℤ) := kdvUnitFourierCLM_eq_periodOneCoefficient
    (deriv Q t) (periodic_kdv_time_derivative ht hp t) n
  constructor
  · intro h t x
    have hmode (n : ℤ) := (hasDerivAt_kdvUnitFourierCoefficient ht n t).unique (h n t)
    have h1 := (contDiff_infty_iff_deriv.mp (hs t)).2
    have h2 := (contDiff_infty_iff_deriv.mp h1).2
    have h3 := (contDiff_infty_iff_deriv.mp h2).2
    have hc : Continuous (scalarClassicalKdVField (fun y : ℝ => Q t (y : AddCircle (2 : ℝ)))) :=
      h3.continuous.neg.add ((continuous_const.mul (hs t).continuous).mul h1.continuous)
    have he := Fourier.eq_of_periodOneCoefficient_eq
      (fun y : ℝ => deriv Q t (y : AddCircle (2 : ℝ)))
      (scalarClassicalKdVField (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))))
      ((deriv Q t).continuous.comp (show Continuous (fun y : ℝ => (y : AddCircle (2 : ℝ))) by fun_prop))
      hc (periodic_kdv_time_derivative ht hp t) (periodic_scalarClassicalKdVField _ (hp t))
      (fun n => (hcoeff t n).symm.trans ((hmode n).trans (hfield t n).symm))
    exact congrFun he x
  · intro h n t
    have he : (fun x : ℝ => deriv Q t (x : AddCircle (2 : ℝ))) =
        scalarClassicalKdVField (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))) := funext (h t)
    have hv : kdvUnitFourierCLM (deriv Q t) n = kdvFourierModeField (kdvUnitFourierCLM (Q t)) n := by
      rw [hcoeff t n,he,hfield t n]
    exact hv ▸ hasDerivAt_kdvUnitFourierCoefficient ht n t

/-- In the stated classical regularity class, the PDE condition may be
replaced by the independent integrated weak equation. -/
theorem isSmoothPhysicalKdVTrajectory_iff_fourierWeak
    (Q : ℝ → C(AddCircle (2 : ℝ),ℂ)) (ht : Differentiable ℝ Q)
    (hs : ∀ t, ContDiff ℝ ∞ (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))))
    (hp : ∀ t, Function.Periodic (fun x : ℝ => Q t (x : AddCircle (2 : ℝ))) 1)
    (hr : ∀ t x : ℝ, (Q t (x : AddCircle (2 : ℝ))).im = 0)
    (hd : ∃ d : ℝ → C(AddCircle (2 : ℝ),ℂ), Continuous d ∧ ∀ t x : ℝ,
      d t (x : AddCircle (2 : ℝ)) = deriv (fun y : ℝ => Q t (y : AddCircle (2 : ℝ))) x) :
    IsSmoothPhysicalKdVTrajectory Q ↔ IsFourierWeakPhysicalKdV Q := by
  constructor
  · intro h
    exact (isFourierWeakPhysicalKdV_iff_equation Q ht hs hp).mpr h.equation
  · intro h
    exact ⟨ht,hs,hp,hr,hd,(isFourierWeakPhysicalKdV_iff_equation Q ht hs hp).mp h⟩

/-- The classical regularity used for uniqueness implies the original
Fourier-L² PDE notion used in physical-action conservation. -/
theorem IsSmoothPhysicalKdVTrajectory.toClassicalKdVTrajectory
    {Q : ℝ → C(AddCircle (2 : ℝ),ℂ)} (hQ : IsSmoothPhysicalKdVTrajectory Q)
    (u : ℝ → RealPeriodOneHillPotential)
    (hu : ∀ t, SpectralWeight.one.toCoeff (u t).val = Fourier.continuousFourierCLM (Q t)) :
    IsClassicalKdVTrajectory u := by
  apply isClassicalKdVTrajectory_of_physical u Q hu hQ.time_differentiable hQ.spatial_smooth hQ.periodic
  intro t x
  rw [hQ.equation]
  simp only [scalarClassicalKdVField,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

end NLS.KdV
