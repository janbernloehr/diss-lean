import NLS.SequenceSpaces.Basic

/-!
# Vanishing coordinates of finite-exponent coefficient sequences

Summability of the positive power of the coordinate norms makes the
set of indices above any fixed threshold finite. Bounding the absolute
values of that finite set gives a two-sided integer tail bound.
-/

noncomputable section
open Filter
open scoped ENNReal
namespace NLS.Coeff

/-- Coordinates of a finite-exponent coefficient sequence vanish in
both directions of the integer lattice. -/
theorem exists_natAbs_norm_lt {r : ℝ≥0∞} (hr : 0 < r.toReal)
    (a : Coeff r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ‖a n‖ < δ := by
  have hsum : Summable (fun n : ℤ => ‖a n‖ ^ r.toReal) :=
    (lp.memℓp a).summable hr
  have hδpow : 0 < δ ^ r.toReal := Real.rpow_pos_of_pos hδ _
  have he : ∀ᶠ n : ℤ in cofinite, ‖a n‖ ^ r.toReal < δ ^ r.toReal :=
    hsum.tendsto_cofinite_zero.eventually_lt_const hδpow
  have hf := Filter.eventually_cofinite.mp he
  let B : ℕ := hf.toFinset.sup (fun n : ℤ => n.natAbs)
  refine ⟨B+1, ?_⟩
  intro n hn
  have hnnot : n ∉ hf.toFinset := by
    intro hmem
    have hle : n.natAbs ≤ B := Finset.le_sup hmem
    omega
  have hpow : ‖a n‖ ^ r.toReal < δ ^ r.toReal := by
    by_contra hbad
    apply hnnot
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using hbad
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hr).mp hpow

end NLS.Coeff
