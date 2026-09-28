import NLS.ComplexAnalysis.BanachC1ImplicitRoot

/-!
# Derivative of a Banach-valued implicit zero

Differentiating a local zero branch gives a balance between the
derivative in the unknown and in the parameter. When the former is
bijective, this balance determines the derivative of the branch.
-/

noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis

variable {E P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace E] [CompleteSpace P] in
/-- The joint Fréchet derivative vanishes along the tangent to a
local zero branch. -/
theorem implicitBanachRoot_fderiv_balance
    (F : E × P → E) (s : P → E) (x : P)
    (hF : DifferentiableAt ℂ F (s x,x))
    (hs : DifferentiableAt ℂ s x)
    (hzero : ∀ᶠ y in 𝓝 x, F (s y,y) = 0)
    (h : P) :
    (fderiv ℂ F (s x,x)) ((fderiv ℂ s x) h,h) = 0 := by
  have hpair : DifferentiableAt ℂ (fun y : P => (s y,y)) x :=
    hs.prodMk differentiableAt_id
  have hpairDeriv : fderiv ℂ (fun y : P => (s y,y)) x =
      (fderiv ℂ s x).prod (ContinuousLinearMap.id ℂ P) := by
    simpa [id,fderiv_id] using hs.fderiv_prodMk differentiableAt_id
  have hcomp : fderiv ℂ (fun y : P => F (s y,y)) x =
      (fderiv ℂ F (s x,x)).comp
        ((fderiv ℂ s x).prod (ContinuousLinearMap.id ℂ P)) := by
    simpa only [Function.comp_def,hpairDeriv] using
      fderiv_comp (f := fun y : P => (s y,y)) x hF hpair
  have hzeroF : (fun y : P => F (s y,y)) =ᶠ[𝓝 x]
      (fun _ => (0 : E)) := hzero
  have hderZero : fderiv ℂ (fun y : P => F (s y,y)) x = 0 := by
    rw [hzeroF.fderiv_eq]
    simp
  have heval := congrArg (fun T : P →L[ℂ] E => T h)
    (hcomp.symm.trans hderZero)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply,zero_apply] using heval

omit [CompleteSpace P] in
/-- Inverting the root-direction derivative gives the derivative of
the implicit solution in each parameter direction. -/
theorem implicitBanachRoot_fderiv_apply
    (F : E × P → E) (s : P → E) (x : P)
    (hF : DifferentiableAt ℂ F (s x,x))
    (hs : DifferentiableAt ℂ s x)
    (hzero : ∀ᶠ y in 𝓝 x, F (s y,y) = 0)
    (hbij : Function.Bijective
      ((fderiv ℂ F (s x,x)).comp
        (ContinuousLinearMap.inl ℂ E P)))
    (h : P) :
    let Q : E →L[ℂ] E :=
      (fderiv ℂ F (s x,x)).comp
        (ContinuousLinearMap.inl ℂ E P)
    let Qinv : E ≃L[ℂ] E :=
      ContinuousLinearEquiv.ofBijective Q
        (LinearMap.ker_eq_bot.mpr hbij.1)
        (LinearMap.range_eq_top.mpr hbij.2)
    (fderiv ℂ s x) h =
      - Qinv.symm ((fderiv ℂ F (s x,x)) (0,h)) := by
  dsimp
  let A : (E × P) →L[ℂ] E := fderiv ℂ F (s x,x)
  let Q : E →L[ℂ] E := A.comp (ContinuousLinearMap.inl ℂ E P)
  let Qinv : E ≃L[ℂ] E :=
    ContinuousLinearEquiv.ofBijective Q
      (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)
  have hbalance := implicitBanachRoot_fderiv_balance F s x hF hs hzero h
  have hdecomp : ((fderiv ℂ s x) h,h) =
      ((fderiv ℂ s x) h,(0 : P)) + ((0 : E),h) := by
    ext <;> simp
  rw [hdecomp,map_add] at hbalance
  have hQ : Q ((fderiv ℂ s x) h) = - A (0,h) := by
    change Q ((fderiv ℂ s x) h) + A (0,h) = 0 at hbalance
    exact eq_neg_of_add_eq_zero_left hbalance
  have happly := congrArg Qinv.symm hQ
  change Qinv.symm (Qinv ((fderiv ℂ s x) h)) =
    Qinv.symm (-A (0,h)) at happly
  simpa only [Qinv.symm_apply_apply, map_neg] using happly

end NLS.ComplexAnalysis
