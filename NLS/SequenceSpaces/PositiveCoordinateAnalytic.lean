import NLS.SequenceSpaces.PositiveInsertion
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! Banach analyticity in the literal positive-index l2 space from
bounded analytic scalar coordinates. Isometric zero extension keeps
all positive labels and transfers the verified signed-coordinate result. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.LpSequence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analyticOnNhd_positiveL2_of_bounded_coordinatewise
    (f : E → lp (fun _ : ℕ+ => ℂ) 2) {V : Set E} (hV : IsOpen V)
    (hcoord : ∀ m : ℕ+, AnalyticOnNhd ℂ (fun x => f x m) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M) : AnalyticOnNhd ℂ f V := by
  let F : E → Coeff 2 := fun x => positiveInsert (f x)
  have hFcoord (k : ℤ) : AnalyticOnNhd ℂ (fun x => F x k) V := by
    by_cases hk : 0 < k
    · let m : ℕ+ := ⟨k.toNat,by omega⟩
      have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
      have hf : (fun x => F x k) = (fun x => f x m) := by
        funext x
        change positiveInsert (f x) k = f x m
        rw [← he,positiveInsert_apply]
      rw [hf]
      exact hcoord m
    · have hf : (fun x => F x k) = (fun _ : E => (0:ℂ)) :=
        funext (fun x => positiveInsert_apply_nonpos (f x) k (by omega))
      rw [hf]
      exact analyticOnNhd_const
  have hF : AnalyticOnNhd ℂ F V :=
    Coeff.analyticOnNhd_of_bounded_coordinatewise F hV hFcoord M (by
      intro x hx
      change ‖positiveInsert (f x)‖ ≤ M
      rw [norm_positiveInsert]
      exact hbound x hx)
  have he : f = fun x => positiveRestrictionCLM (F x) := by
    funext x
    ext m
    exact (positiveInsert_apply (f x) m).symm
  rw [he]
  intro x hx
  exact (positiveRestrictionCLM.analyticAt (F x)).comp (hF x hx)

end NLS.LpSequence
