import NLS.FunctionalAnalysis.SelfAdjointResolventIdentity
import Mathlib.Algebra.Star.Unitary

/-! # The actual unitary Cayley transform of a self-adjoint partial operator -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →ₗ.[ℂ] E}

/-- The bounded Cayley transform (T-i)(T+i) inverse, expressed through
the actual resolvent convention R(z)=(z-T) inverse. -/
def selfAdjointCayley (hT : IsSelfAdjoint T) : E →L[ℂ] E :=
  1+(2*I) • selfAdjointNonrealResolvent hT (-I) (by simp)

theorem star_selfAdjointCayley (hT : IsSelfAdjoint T) :
    star (selfAdjointCayley hT) = 1-(2*I) • selfAdjointNonrealResolvent hT I (by simp) := by
  have ha : ContinuousLinearMap.adjoint (selfAdjointNonrealResolvent hT (-I) (by simp)) =
      selfAdjointNonrealResolvent hT I (by simp) := by
    simpa using adjoint_selfAdjointNonrealResolvent hT (-I) (by simp)
  unfold selfAdjointCayley
  rw [star_add,star_one,star_smul,ContinuousLinearMap.star_eq_adjoint,ha]
  simp [sub_eq_add_neg]

/-- The actual resolvent identity proves both unitary inverse equations. -/
theorem selfAdjointCayley_mem_unitary (hT : IsSelfAdjoint T) :
    selfAdjointCayley hT ∈ unitary (E →L[ℂ] E) := by
  let Rp := selfAdjointNonrealResolvent hT I (by simp)
  let Rm := selfAdjointNonrealResolvent hT (-I) (by simp)
  have hp (g : E) : Rp (selfAdjointCayley hT g) = Rm g := by
    have h : Rp g-Rm g = (-(2*I)) • Rp (Rm g) := by
      have hneg : -I-I = -(2*I) := by ring
      simpa only [Rp,Rm,hneg] using
        selfAdjointNonrealResolvent_sub_apply hT I (-I) (by simp) (by simp) g
    change Rp (g+(2*I) • Rm g) = Rm g
    rw [map_add,map_smul,sub_eq_iff_eq_add.mp h]
    module
  have hm (g : E) : Rm (star (selfAdjointCayley hT) g) = Rp g := by
    have h : Rm g-Rp g = (2*I) • Rm (Rp g) := by
      simpa only [Rp,Rm,sub_neg_eq_add,← two_mul] using
        selfAdjointNonrealResolvent_sub_apply hT (-I) I (by simp) (by simp) g
    rw [star_selfAdjointCayley]
    change Rm (g-(2*I) • Rp g) = Rp g
    rw [map_sub,map_smul,sub_eq_iff_eq_add.mp h]
    module
  apply Unitary.mem_iff.mpr
  constructor
  · ext g
    change star (selfAdjointCayley hT) (selfAdjointCayley hT g) = g
    rw [star_selfAdjointCayley]
    change selfAdjointCayley hT g-(2*I) • Rp (selfAdjointCayley hT g) = g
    rw [hp]
    change (g+(2*I) • Rm g)-(2*I) • Rm g = g
    module
  · ext g
    change selfAdjointCayley hT (star (selfAdjointCayley hT) g) = g
    change star (selfAdjointCayley hT) g+(2*I) • Rm (star (selfAdjointCayley hT) g) = g
    rw [hm,star_selfAdjointCayley]
    change (g-(2*I) • Rp g)+(2*I) • Rp g = g
    module

/-- The actual base-space resolvent is injective. -/
theorem selfAdjointNonrealResolvent_injective (hT : IsSelfAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    Function.Injective (selfAdjointNonrealResolvent hT z hz) := by
  intro x y hxy
  have he : selfAdjointNonrealResolventToDomain hT z hz x =
      selfAdjointNonrealResolventToDomain hT z hz y := Subtype.ext hxy
  have h := congrArg (linearPMapPencil T z) he
  simpa only [linearPMapPencil_selfAdjointNonrealResolventToDomain] using h

/-- The exceptional Cayley point one has no nonzero fixed vector. -/
theorem selfAdjointCayley_apply_eq_self_iff (hT : IsSelfAdjoint T) (x : E) :
    selfAdjointCayley hT x = x ↔ x = 0 := by
  constructor
  · intro h
    have hz : (2*I) • selfAdjointNonrealResolvent hT (-I) (by simp) x = 0 := by
      change x+(2*I) • selfAdjointNonrealResolvent hT (-I) (by simp) x = x at h
      exact add_eq_left.mp h
    have hr := (smul_eq_zero.mp hz).resolve_left (by simp)
    apply selfAdjointNonrealResolvent_injective hT (-I) (by simp)
    simpa using hr
  · rintro rfl
    exact map_zero _

end NLS.FunctionalAnalysis
