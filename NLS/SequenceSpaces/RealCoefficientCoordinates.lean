import NLS.SequenceSpaces.RealOperatorInverse
import NLS.SequenceSpaces.RealAnalyticInverseRestriction
import NLS.ComplexAnalysis.LinearCoordinatesLocalInverse

/-! # Real coefficient coordinates on a complex Banach space -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pull back real coefficient sequences through complex linear coordinates. -/
def coordinateRealSubmodule (e : E ≃L[ℂ] Coeff p) : Submodule ℝ E :=
  (realSubmodule p).comap (e.toContinuousLinearMap.restrictScalars ℝ).toLinearMap

@[simp] theorem mem_coordinateRealSubmodule (e : E ≃L[ℂ] Coeff p) (x : E) :
    x ∈ coordinateRealSubmodule e ↔ e x ∈ realLocus p := Iff.rfl

theorem isClosed_coordinateRealSubmodule (e : E ≃L[ℂ] Coeff p) :
    IsClosed (coordinateRealSubmodule e : Set E) := isClosed_realSubmodule.preimage e.continuous

/-- Real coefficient projection in linear coordinates. -/
def coordinateToReal (e : E ≃L[ℂ] Coeff p) : coordinateRealSubmodule e →L[ℝ] RealCoeff p :=
  (reCLM p).comp ((e.toContinuousLinearMap.restrictScalars ℝ).comp
    (coordinateRealSubmodule e).subtypeL)

/-- Inclusion of real coefficient coordinates into the original closed subspace. -/
def coordinateFromReal (e : E ≃L[ℂ] Coeff p) : RealCoeff p →L[ℝ] coordinateRealSubmodule e :=
  (((e.symm.toContinuousLinearMap).restrictScalars ℝ).comp (RealCoeff.complexCLM p)).codRestrict
    (coordinateRealSubmodule e) (by
      intro b
      rw [mem_coordinateRealSubmodule]
      change e (e.symm (RealCoeff.complexCLM p b)) ∈ realLocus p
      rw [e.apply_symm_apply]
      intro n
      simp)

/-- Coordinates identify the closed real subspace with actual real lp sequences. -/
def coordinateRealEquiv (e : E ≃L[ℂ] Coeff p) : coordinateRealSubmodule e ≃L[ℝ] RealCoeff p where
  toFun := coordinateToReal e
  invFun := coordinateFromReal e
  left_inv a := by
    apply Subtype.ext
    have ha : e a.val ∈ realLocus p := a.property
    change e.symm (RealCoeff.complexCLM p (reCLM p (e a.val))) = a.val
    rw [RealCoeff.complexCLM_reCLM p _ ha,e.symm_apply_apply]
  right_inv b := by
    change reCLM p (e (e.symm (RealCoeff.complexCLM p b))) = b
    rw [e.apply_symm_apply,RealCoeff.reCLM_complexCLM]
  map_add' := (coordinateToReal e).map_add
  map_smul' := (coordinateToReal e).map_smul
  continuous_toFun := (coordinateToReal e).continuous
  continuous_invFun := (coordinateFromReal e).continuous

@[simp] theorem coordinateRealEquiv_apply (e : E ≃L[ℂ] Coeff p) (a : coordinateRealSubmodule e) :
    coordinateRealEquiv e a = reCLM p (e a.val) := rfl

theorem complex_coordinateRealEquiv (e : E ≃L[ℂ] Coeff p) (a : coordinateRealSubmodule e) :
    RealCoeff.complexCLM p (coordinateRealEquiv e a) = e a.val :=
  RealCoeff.complexCLM_reCLM p _ a.property

/-- Real projection in the original coordinates. -/
def coordinateReCLM (e : E ≃L[ℂ] Coeff p) : E →L[ℝ] coordinateRealSubmodule e :=
  (coordinateRealEquiv e).symm.toContinuousLinearMap.comp
    ((reCLM p).comp (e.toContinuousLinearMap.restrictScalars ℝ))

@[simp] theorem coordinateRealEquiv_coordinateReCLM (e : E ≃L[ℂ] Coeff p) (a : E) :
    coordinateRealEquiv e (coordinateReCLM e a) = reCLM p (e a) :=
  (coordinateRealEquiv e).apply_symm_apply _

@[simp] theorem coordinateReCLM_val (e : E ≃L[ℂ] Coeff p) (a : coordinateRealSubmodule e) :
    coordinateReCLM e a.val = a := by
  apply (coordinateRealEquiv e).injective
  rw [coordinateRealEquiv_coordinateReCLM]
  rfl

/-- The real projection recovers the full original value on the real locus. -/
theorem val_coordinateReCLM (e : E ≃L[ℂ] Coeff p) (a : E) (ha : e a ∈ realLocus p) :
    (coordinateReCLM e a).val = a := by
  apply e.injective
  rw [← complex_coordinateRealEquiv,coordinateRealEquiv_coordinateReCLM]
  exact RealCoeff.complexCLM_reCLM p _ ha

/-- The actual real map obtained by restricting in the original coordinates. -/
def coordinateRestriction (e : E ≃L[ℂ] Coeff p) (f : E → E) :
    coordinateRealSubmodule e → coordinateRealSubmodule e := fun y => coordinateReCLM e (f y.val)

/-- Restriction to real sequences commutes with the complex coordinate change. -/
theorem realRestriction_linear_conjugate (e : E ≃L[ℂ] Coeff p) (f : E → E) :
    realRestriction (fun z => e (f (e.symm z))) =
      fun y => coordinateRealEquiv e (coordinateRestriction e f ((coordinateRealEquiv e).symm y)) := by
  funext y
  have hj := complex_coordinateRealEquiv e ((coordinateRealEquiv e).symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hj
  change reCLM p (e (f (e.symm (RealCoeff.complexCLM p y)))) =
    coordinateRealEquiv e (coordinateReCLM e (f ((coordinateRealEquiv e).symm y).val))
  rw [coordinateRealEquiv_coordinateReCLM,hj,e.symm_apply_apply]

/-- Real local inverse germs are unchanged by the complex and real coordinate changes. -/
theorem hasAnalyticInverse_coordinateRestriction_iff (e : E ≃L[ℂ] Coeff p)
    {f : E → E} {x : coordinateRealSubmodule e} :
    ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
      (realRestriction (fun z => e (f (e.symm z)))) (coordinateRealEquiv e x) ↔
    ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ) (coordinateRestriction e f) x := by
  rw [realRestriction_linear_conjugate]
  exact ComplexAnalysis.hasAnalyticInverse_linear_conjugate_iff (coordinateRealEquiv e)

/-- Restriction is real analytic wherever the original extension is complex analytic. -/
theorem analyticAt_coordinateRestriction (e : E ≃L[ℂ] Coeff p)
    {f : E → E} {x : coordinateRealSubmodule e} (hf : AnalyticAt ℂ f x.val) :
    AnalyticAt ℝ (coordinateRestriction e f) x :=
  ((coordinateReCLM e).analyticAt _).comp
    (hf.restrictScalars.comp ((coordinateRealSubmodule e).subtypeL.analyticAt x))

/-- The restriction agrees with the original map on real arguments after projection. -/
theorem coordinateRestriction_coordinateReCLM (e : E ≃L[ℂ] Coeff p)
    (f : E → E) (x : E) (hx : e x ∈ realLocus p) :
    coordinateRestriction e f (coordinateReCLM e x) = coordinateReCLM e (f x) := by
  change coordinateReCLM e (f (coordinateReCLM e x).val) = _
  rw [val_coordinateReCLM e x hx]

/-- A differentiable real left inverse supplies the same seed in normalized coordinates. -/
theorem differentiableLeftInverse_coordinateRestriction (e : E ≃L[ℂ] Coeff p)
    {f : E → E} {x : coordinateRealSubmodule e}
    (h : ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ) (coordinateRestriction e f) x) :
    ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ)
      (realRestriction (fun z => e (f (e.symm z)))) (coordinateRealEquiv e x) := by
  rw [realRestriction_linear_conjugate]
  exact h.linear_conjugate (coordinateRealEquiv e)

end NLS.Coeff
