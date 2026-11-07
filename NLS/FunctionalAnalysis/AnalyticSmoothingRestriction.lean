import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Restricting an analytic Banach equivalence to stronger spaces.
An analytic smoothing defect relative to a compatible linear equivalence
constructs BOTH stronger-space maps. No stronger inverse regularity is
assumed: it follows from the ambient inverse and the same defect. -/
noncomputable section
open Set
namespace NLS.FunctionalAnalysis
variable {𝕜 E F E₀ F₀ G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
  [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

def smoothingRestrictionForward (iE : E →L[𝕜] E₀) (A : E ≃L[𝕜] F)
    (S : G →L[𝕜] F) (R : E₀ → G) (x : E) : F := A x + S (R (iE x))

def smoothingRestrictionInverse (iF : F →L[𝕜] F₀) (A : E ≃L[𝕜] F)
    (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀) (y : F) : E :=
  A.symm (y - S (R (e.symm (iF y))))

theorem smoothingRestrictionForward_inclusion (iE : E →L[𝕜] E₀) (iF : F →L[𝕜] F₀)
    (A : E ≃L[𝕜] F) (A₀ : E₀ ≃L[𝕜] F₀) (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀)
    (hA : ∀ x, iF (A x) = A₀ (iE x))
    (hR : ∀ x, e x = A₀ x + iF (S (R x))) (x : E) :
    iF (smoothingRestrictionForward iE A S R x) = e (iE x) := by
  rw [smoothingRestrictionForward, map_add, hA, hR]

theorem smoothingRestrictionInverse_inclusion (iE : E →L[𝕜] E₀) (iF : F →L[𝕜] F₀)
    (A : E ≃L[𝕜] F) (A₀ : E₀ ≃L[𝕜] F₀) (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀)
    (hA : ∀ x, iF (A x) = A₀ (iE x))
    (hR : ∀ x, e x = A₀ x + iF (S (R x))) (y : F) :
    iE (smoothingRestrictionInverse iF A S R e y) = e.symm (iF y) := by
  apply A₀.injective
  rw [← hA, smoothingRestrictionInverse, A.apply_symm_apply, map_sub]
  have h := hR (e.symm (iF y))
  rw [e.apply_symm_apply] at h
  exact sub_eq_of_eq_add h

def smoothingRestrictionEquiv (iE : E →L[𝕜] E₀) (iF : F →L[𝕜] F₀)
    (hiE : Function.Injective iE) (hiF : Function.Injective iF)
    (A : E ≃L[𝕜] F) (A₀ : E₀ ≃L[𝕜] F₀) (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀)
    (hA : ∀ x, iF (A x) = A₀ (iE x)) (hR : ∀ x, e x = A₀ x + iF (S (R x))) : E ≃ F where
  toFun := smoothingRestrictionForward iE A S R
  invFun := smoothingRestrictionInverse iF A S R e
  left_inv x := by
    apply hiE
    rw [smoothingRestrictionInverse_inclusion iE iF A A₀ S R e hA hR,
      smoothingRestrictionForward_inclusion iE iF A A₀ S R e hA hR, e.symm_apply_apply]
  right_inv y := by
    apply hiF
    rw [smoothingRestrictionForward_inclusion iE iF A A₀ S R e hA hR,
      smoothingRestrictionInverse_inclusion iE iF A A₀ S R e hA hR, e.apply_symm_apply]

theorem analyticAt_smoothingRestrictionForward (iE : E →L[𝕜] E₀) (A : E ≃L[𝕜] F)
    (S : G →L[𝕜] F) (R : E₀ → G) (hR : ∀ x, AnalyticAt 𝕜 R x) (x : E) :
    AnalyticAt 𝕜 (smoothingRestrictionForward iE A S R) x :=
  (A.analyticAt x).add ((S.analyticAt _).comp ((hR _).comp (iE.analyticAt x)))

theorem analyticAt_smoothingRestrictionInverse (iF : F →L[𝕜] F₀) (A : E ≃L[𝕜] F)
    (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀)
    (hR : ∀ x, AnalyticAt 𝕜 R x) (he : ∀ y, AnalyticAt 𝕜 e.symm y) (y : F) :
    AnalyticAt 𝕜 (smoothingRestrictionInverse iF A S R e) y :=
  (A.symm.analyticAt _).comp (analyticAt_id.sub
    ((S.analyticAt _).comp ((hR _).comp ((he _).comp (iF.analyticAt y)))))

theorem exists_analytic_smoothingRestrictionEquiv (iE : E →L[𝕜] E₀) (iF : F →L[𝕜] F₀)
    (hiE : Function.Injective iE) (hiF : Function.Injective iF)
    (A : E ≃L[𝕜] F) (A₀ : E₀ ≃L[𝕜] F₀) (S : G →L[𝕜] F) (R : E₀ → G) (e : E₀ ≃ F₀)
    (hA : ∀ x, iF (A x) = A₀ (iE x)) (hR : ∀ x, e x = A₀ x + iF (S (R x)))
    (hRa : ∀ x, AnalyticAt 𝕜 R x) (hei : ∀ y, AnalyticAt 𝕜 e.symm y) :
    ∃ e' : E ≃ F, (∀ x, iF (e' x) = e (iE x)) ∧
      (∀ x, AnalyticAt 𝕜 e' x) ∧ (∀ y, AnalyticAt 𝕜 e'.symm y) := by
  refine ⟨smoothingRestrictionEquiv iE iF hiE hiF A A₀ S R e hA hR, ?_, ?_, ?_⟩
  · exact smoothingRestrictionForward_inclusion iE iF A A₀ S R e hA hR
  · exact analyticAt_smoothingRestrictionForward iE A S R hRa
  · exact analyticAt_smoothingRestrictionInverse iF A S R e hRa hei

theorem isCompactOperator_smoothingRestriction_fderiv_sub_linear
    (iE : E →L[𝕜] E₀) (A : E ≃L[𝕜] F) (S : G →L[𝕜] F) (R : E₀ → G)
    (hS : IsCompactOperator S) (hR : ∀ x, AnalyticAt 𝕜 R x) (x : E) :
    IsCompactOperator (fderiv 𝕜 (smoothingRestrictionForward iE A S R) x - A.toContinuousLinearMap) := by
  let D := S.comp ((fderiv 𝕜 R (iE x)).comp iE)
  have hd : HasFDerivAt (smoothingRestrictionForward iE A S R)
      (A.toContinuousLinearMap + D) x :=
    A.hasFDerivAt.add (S.hasFDerivAt.comp x
      (((hR (iE x)).differentiableAt.hasFDerivAt).comp x iE.hasFDerivAt))
  rw [hd.fderiv, add_sub_cancel_left]
  exact hS.comp_clm _

end NLS.FunctionalAnalysis
