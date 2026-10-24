import NLS.ZakharovShabat.L2WholeLineSelfAdjoint
import NLS.FunctionalAnalysis.SelfAdjointNonrealResolvent

/-! # The original whole-line resolvent and spectrum

The resolvent set is defined by a bounded two-sided inverse of the original
physical pencil on the actual graph-closure domain. The domain carries its
inherited L2 norm, so boundedness is precisely base-space boundedness.
Self-adjointness constructs this inverse at every nonreal parameter.
-/
noncomputable section
set_option autoImplicit false
open Set
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The original physical pencil on the actual closed whole-line domain. -/
def wholeLinePencil (u : IntervalPairL2) (z : ℂ) :
    (wholeLineMinimalOperator u).closure.domain →ₗ[ℂ] WholeLineL2 :=
  linearPMapPencil (wholeLineMinimalOperator u).closure z

/-- Resolvent membership means a bounded two-sided inverse on the actual
domain; it is independent of Floquet multipliers and eigenvalue definitions. -/
def wholeLineResolventSet (u : IntervalPairL2) : Set ℂ :=
  {z | ∃ R : WholeLineL2 →L[ℂ] (wholeLineMinimalOperator u).closure.domain,
    (∀ f, wholeLinePencil u z (R f) = f) ∧ (∀ g, R (wholeLinePencil u z g) = g)}

/-- The spectrum is failure of bounded invertibility of the original pencil. -/
def wholeLineSpectrum (u : IntervalPairL2) : Set ℂ := (wholeLineResolventSet u)ᶜ

/-- The actual nonreal inverse takes values in the maximal physical domain. -/
def wholeLineNonrealResolventToDomain (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    WholeLineL2 →L[ℂ] (wholeLineMinimalOperator u).closure.domain :=
  selfAdjointNonrealResolventToDomain (wholeLineMinimalOperator_closure_isSelfAdjoint u hu) z hz

/-- The bounded whole-line inverse acting on the original Hermitian L2 space. -/
def wholeLineNonrealResolvent (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    WholeLineL2 →L[ℂ] WholeLineL2 :=
  selfAdjointNonrealResolvent (wholeLineMinimalOperator_closure_isSelfAdjoint u hu) z hz

theorem wholeLinePencil_nonrealResolventToDomain (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (f : WholeLineL2) : wholeLinePencil u z (wholeLineNonrealResolventToDomain u hu z hz f) = f :=
  linearPMapPencil_selfAdjointNonrealResolventToDomain _ z hz f

theorem wholeLineNonrealResolventToDomain_pencil (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (f : (wholeLineMinimalOperator u).closure.domain) :
    wholeLineNonrealResolventToDomain u hu z hz (wholeLinePencil u z f) = f :=
  selfAdjointNonrealResolventToDomain_linearPMapPencil _ z hz f

/-- Every nonreal parameter belongs to the independently defined resolvent set. -/
theorem nonreal_mem_wholeLineResolventSet (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ wholeLineResolventSet u :=
  ⟨wholeLineNonrealResolventToDomain u hu z hz,
    wholeLinePencil_nonrealResolventToDomain u hu z hz,
    wholeLineNonrealResolventToDomain_pencil u hu z hz⟩

/-- The original bounded resolvent satisfies the standard nonreal bound. -/
theorem norm_wholeLineNonrealResolvent_le (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    ‖wholeLineNonrealResolvent u hu z hz‖ ≤ 1 / |z.im| :=
  norm_selfAdjointNonrealResolvent_le _ z hz

/-- The whole-line spectrum of a real physical potential lies on the real axis. -/
theorem wholeLineSpectrum_subset_real (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    wholeLineSpectrum u ⊆ {z : ℂ | z.im = 0} := by
  intro z hz
  by_contra hnr
  exact hz (nonreal_mem_wholeLineResolventSet u hu z hnr)

theorem wholeLineResolventSet_nonempty (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    (wholeLineResolventSet u).Nonempty :=
  ⟨Complex.I,nonreal_mem_wholeLineResolventSet u hu Complex.I (by simp)⟩

end NLS.ZakharovShabat
