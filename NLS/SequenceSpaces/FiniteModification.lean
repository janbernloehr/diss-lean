import NLS.SequenceSpaces.Basic

/-!
# Finite changes of lp sequences

Changing a sequence on a finite set preserves lp membership at every
exponent. The finite correction is an lp sequence independently of the
size of its finitely many values.
-/

open scoped ENNReal
namespace NLS

/-- Agreement outside a finite set transfers lp membership. -/
theorem memℓp_of_eq_outside_finset {p : ℝ≥0∞} {f g : ℤ → ℂ} (hg : Memℓp g p)
    (s : Finset ℤ) (he : ∀ n ∉ s, f n = g n) : Memℓp f p := by
  have hs : Set.Finite {n | f n-g n ≠ 0} := by
    apply s.finite_toSet.subset
    intro n hn
    by_contra hns
    exact hn (by rw [he n hns,sub_self])
  have hd : Memℓp (fun n => f n-g n) p := (memℓp_zero hs).of_exponent_ge zero_le
  have heq : f = (fun n => f n-g n)+g := by funext n; simp
  rw [heq]
  exact hd.add hg

end NLS
