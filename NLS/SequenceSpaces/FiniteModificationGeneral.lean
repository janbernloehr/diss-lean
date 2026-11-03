import NLS.SequenceSpaces.Basic

/-! Finite changes preserve lp membership on any index type. -/
open scoped ENNReal
namespace NLS

theorem memℓp_of_eq_outside_finset_on {I : Type*} [DecidableEq I]
    {p : ℝ≥0∞} {f g : I → ℂ} (hg : Memℓp g p)
    (s : Finset I) (he : ∀ i ∉ s, f i = g i) : Memℓp f p := by
  have hs : Set.Finite {i | f i-g i ≠ 0} := by
    apply s.finite_toSet.subset
    intro i hi
    by_contra hn
    exact hi (by rw [he i hn,sub_self])
  have hd : Memℓp (fun i => f i-g i) p := (memℓp_zero hs).of_exponent_ge zero_le
  have heq : f = (fun i => f i-g i)+g := by funext i; simp
  rw [heq]
  exact hd.add hg

end NLS
