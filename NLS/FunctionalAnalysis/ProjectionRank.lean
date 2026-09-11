import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Rank stability of bounded projections

Two finite-rank projections at operator-norm distance less than one have equal
rank: each projection is injective on the range of the other.
-/

noncomputable section

namespace NLS.ProjectionRank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A map within distance one of a projection is injective on its range. -/
theorem injective_on_range_of_norm_sub_lt_one (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hPQ : ‖P - Q‖ < 1) :
    Function.Injective (Q.toLinearMap.comp P.range.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hQ : Q x = 0 := hx
  have hPx : P x = x := by
    obtain ⟨y, hy⟩ := x.property
    change P y = (x : E) at hy
    have hi := congrArg (fun A : E →L[ℂ] E => A y) hP
    change P (P y) = P y at hi
    simpa only [hy] using hi
  have hn : ‖(x : E)‖ ≤ ‖P - Q‖ * ‖(x : E)‖ := by
    simpa only [sub_apply, hPx, hQ, sub_zero] using (P - Q).le_opNorm (x : E)
  have hx0 : ‖(x : E)‖ = 0 := by nlinarith [norm_nonneg (x : E)]
  exact Subtype.ext (norm_eq_zero.mp hx0)

/-- Finite-rank projections less than one apart in operator norm have equal rank. -/
theorem finrank_eq_of_norm_sub_lt_one (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hPQ : ‖P - Q‖ < 1)
    [FiniteDimensional ℂ P.range] [FiniteDimensional ℂ Q.range] :
    Module.finrank ℂ P.range = Module.finrank ℂ Q.range := by
  have hle (A B : E →L[ℂ] E) (hA : IsIdempotentElem A) (hAB : ‖A - B‖ < 1)
      [FiniteDimensional ℂ B.range] : Module.finrank ℂ A.range ≤ Module.finrank ℂ B.range := by
    let f : A.range →ₗ[ℂ] B.range := B.toLinearMap.rangeRestrict.comp A.range.subtype
    apply LinearMap.finrank_le_finrank_of_injective (f := f)
    intro x y hxy
    exact injective_on_range_of_norm_sub_lt_one A B hA hAB
      (congrArg Subtype.val hxy)
  exact le_antisymm (hle P Q hP hPQ) (hle Q P hQ (by rwa [norm_sub_rev]))

end NLS.ProjectionRank
