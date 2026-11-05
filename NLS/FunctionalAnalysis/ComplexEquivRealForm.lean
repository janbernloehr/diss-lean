import NLS.FunctionalAnalysis.ComplexEquivRealRestriction

/-! An actual complex equivalence restricts to an actual equivalence
of physical real forms when the forward derivative agrees there.
Bounded real/imaginary projections construct the exact inverse. -/
noncomputable section
open Complex
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℝ E] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F]

/-- The bounded projected complex inverse is a true right inverse of
the real-form operator; no inverse preservation assumption is needed. -/
theorem realForm_rightInverse (S : Submodule ℝ E) (T : Submodule ℝ F)
    (P : E →L[ℝ] S) (Q : F →L[ℝ] T)
    (hP : ∀ z : E, (P z : E)+I • (P (-I • z) : E)=z)
    (hQ : ∀ t : T, Q (t : F)=t) (hQI : ∀ t : T, Q (I • (t : F))=0)
    (e : E ≃L[ℂ] F) (A : S →L[ℝ] T) (hA : ∀ s : S, e (s : E)=(A s : F)) :
    A.comp (P.comp ((e.symm.toContinuousLinearMap.restrictScalars ℝ).comp T.subtypeL))=
      ContinuousLinearMap.id ℝ T := by
  apply ContinuousLinearMap.ext
  intro t
  let z := e.symm (t : F)
  have he : e z = (A (P z) : F)+I • (A (P (-I • z)) : F) := by
    conv_lhs => rw [← hP z]
    rw [map_add,map_smul,hA,hA]
  change A (P z)=t
  calc
    _ = Q (e z) := by rw [he,map_add,hQ,hQI,add_zero]
    _ = t := by rw [show e z=(t : F) from e.apply_symm_apply _,hQ]

/-- The real derivative equivalence retains the actual forward map and
uses the bounded projection of the actual complex inverse. -/
def equivOfComplexEquivRealForm (S : Submodule ℝ E) (T : Submodule ℝ F)
    (P : E →L[ℝ] S) (Q : F →L[ℝ] T)
    (hP : ∀ z : E, (P z : E)+I • (P (-I • z) : E)=z)
    (hQ : ∀ t : T, Q (t : F)=t) (hQI : ∀ t : T, Q (I • (t : F))=0)
    (e : E ≃L[ℂ] F) (A : S →L[ℝ] T) (hA : ∀ s : S, e (s : E)=(A s : F)) : S ≃L[ℝ] T where
  toFun := A
  invFun := P.comp ((e.symm.toContinuousLinearMap.restrictScalars ℝ).comp T.subtypeL)
  map_add' := map_add A
  map_smul' := map_smul A
  left_inv s := by
    have hi : Function.Injective A := by
      intro a b h
      apply Subtype.ext
      apply e.injective
      rw [hA,hA,h]
    apply hi
    exact congrArg (fun L : T →L[ℝ] T => L (A s)) (realForm_rightInverse S T P Q hP hQ hQI e A hA)
  right_inv t := congrArg (fun L : T →L[ℝ] T => L t) (realForm_rightInverse S T P Q hP hQ hQI e A hA)
  continuous_toFun := A.continuous
  continuous_invFun := (P.comp ((e.symm.toContinuousLinearMap.restrictScalars ℝ).comp T.subtypeL)).continuous

@[simp] theorem equivOfComplexEquivRealForm_toContinuousLinearMap (S : Submodule ℝ E) (T : Submodule ℝ F)
    (P : E →L[ℝ] S) (Q : F →L[ℝ] T)
    (hP : ∀ z : E, (P z : E)+I • (P (-I • z) : E)=z)
    (hQ : ∀ t : T, Q (t : F)=t) (hQI : ∀ t : T, Q (I • (t : F))=0)
    (e : E ≃L[ℂ] F) (A : S →L[ℝ] T) (hA : ∀ s : S, e (s : E)=(A s : F)) :
    (equivOfComplexEquivRealForm S T P Q hP hQ hQI e A hA).toContinuousLinearMap=A := rfl

/-- The true complex inverse itself preserves the physical real form. -/
theorem equivOfComplexEquivRealForm_symm_coe (S : Submodule ℝ E) (T : Submodule ℝ F)
    (P : E →L[ℝ] S) (Q : F →L[ℝ] T)
    (hP : ∀ z : E, (P z : E)+I • (P (-I • z) : E)=z)
    (hQ : ∀ t : T, Q (t : F)=t) (hQI : ∀ t : T, Q (I • (t : F))=0)
    (e : E ≃L[ℂ] F) (A : S →L[ℝ] T) (hA : ∀ s : S, e (s : E)=(A s : F)) (t : T) :
    ((equivOfComplexEquivRealForm S T P Q hP hQ hQI e A hA).symm t : E)=e.symm (t : F) := by
  apply e.injective
  rw [hA,e.apply_symm_apply]
  exact congrArg (fun a : T => (a : F))
    ((equivOfComplexEquivRealForm S T P Q hP hQ hQI e A hA).apply_symm_apply t)

end NLS.FunctionalAnalysis
