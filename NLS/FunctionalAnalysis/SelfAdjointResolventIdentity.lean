import NLS.FunctionalAnalysis.SelfAdjointNonrealResolvent
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Resolvent identities for actual self-adjoint partial operators -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →ₗ.[ℂ] E}

/-- The bounded base-space resolvent recovers every actual domain vector. -/
theorem selfAdjointNonrealResolvent_pencil (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0)
    (f : T.domain) : selfAdjointNonrealResolvent hT z hz (linearPMapPencil T z f) = (f : E) :=
  congrArg Subtype.val (selfAdjointNonrealResolventToDomain_linearPMapPencil hT z hz f)

/-- Evaluating one physical pencil on the other resolvent's domain image. -/
theorem linearPMapPencil_cross_resolvent (hT : IsSelfAdjoint T) (z w : ℂ)
    (hw : w.im ≠ 0) (g : E) :
    linearPMapPencil T z (selfAdjointNonrealResolventToDomain hT w hw g) =
      (z-w) • selfAdjointNonrealResolvent hT w hw g+g := by
  have h := linearPMapPencil_selfAdjointNonrealResolventToDomain hT w hw g
  change w • selfAdjointNonrealResolvent hT w hw g-
    T (selfAdjointNonrealResolventToDomain hT w hw g) = g at h
  change z • selfAdjointNonrealResolvent hT w hw g-
    T (selfAdjointNonrealResolventToDomain hT w hw g) = _
  calc
    _ = (z-w) • selfAdjointNonrealResolvent hT w hw g+
        (w • selfAdjointNonrealResolvent hT w hw g-
          T (selfAdjointNonrealResolventToDomain hT w hw g)) := by module
    _ = _ := by rw [h]

/-- The resolvent identity uses the original partial operator and its actual domain. -/
theorem selfAdjointNonrealResolvent_sub_apply (hT : IsSelfAdjoint T) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) (g : E) :
    selfAdjointNonrealResolvent hT z hz g-selfAdjointNonrealResolvent hT w hw g =
      (w-z) • selfAdjointNonrealResolvent hT z hz (selfAdjointNonrealResolvent hT w hw g) := by
  have h := selfAdjointNonrealResolvent_pencil hT z hz
    (selfAdjointNonrealResolventToDomain hT w hw g)
  rw [linearPMapPencil_cross_resolvent,map_add,map_smul] at h
  change (z-w) • selfAdjointNonrealResolvent hT z hz (selfAdjointNonrealResolvent hT w hw g)+
    selfAdjointNonrealResolvent hT z hz g = selfAdjointNonrealResolvent hT w hw g at h
  calc
    _ = selfAdjointNonrealResolvent hT z hz g-
        ((z-w) • selfAdjointNonrealResolvent hT z hz (selfAdjointNonrealResolvent hT w hw g)+
          selfAdjointNonrealResolvent hT z hz g) := congrArg (fun v => _-v) h.symm
    _ = _ := by module

theorem selfAdjointNonrealResolvent_sub (hT : IsSelfAdjoint T) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    selfAdjointNonrealResolvent hT z hz-selfAdjointNonrealResolvent hT w hw =
      (w-z) • (selfAdjointNonrealResolvent hT z hz).comp (selfAdjointNonrealResolvent hT w hw) := by
  ext g
  exact selfAdjointNonrealResolvent_sub_apply hT z w hz hw g

omit [CompleteSpace E] in
/-- The formal-adjoint pairing conjugates the spectral parameter. -/
theorem inner_linearPMapPencil_conj (hs : T.IsFormalAdjoint T) (z : ℂ) (f g : T.domain) :
    inner ℂ (linearPMapPencil T z f) (g : E) =
      inner ℂ (f : E) (linearPMapPencil T (star z) g) := by
  simp only [linearPMapPencil_apply,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,hs f g]
  rfl

/-- The Hilbert adjoint of the actual resolvent is the conjugate-parameter resolvent. -/
theorem adjoint_selfAdjointNonrealResolvent (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    ContinuousLinearMap.adjoint (selfAdjointNonrealResolvent hT z hz) =
      selfAdjointNonrealResolvent hT (star z) (by simpa using hz) := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have hs : T.IsFormalAdjoint T := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  have h := inner_linearPMapPencil_conj hs (star z)
    (selfAdjointNonrealResolventToDomain hT (star z) (by simpa using hz) x)
    (selfAdjointNonrealResolventToDomain hT z hz y)
  rw [star_star,linearPMapPencil_selfAdjointNonrealResolventToDomain,
    linearPMapPencil_selfAdjointNonrealResolventToDomain] at h
  exact h.symm

end NLS.FunctionalAnalysis
