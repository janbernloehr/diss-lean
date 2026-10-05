import NLS.SequenceSpaces.TailSquareDescentAnalyticLine

/-! # A refined correction target strictly below the action exponent -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [p.HolderTriple p q]

/-- For every finite source exponent above two, there is a Banach target
above one and at least p/3, but strictly below the action exponent p/2. -/
theorem exists_strict_refined_actionExponent (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ r : ℝ≥0∞, r ≠ ⊤ ∧ 1 < r ∧ r < q ∧ ENNReal.ofReal (p.toReal/3) ≤ r := by
  have hq : q ≠ ⊤ := doublingExponent_ne_top hp
  have hpR : 2 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp2
    norm_num at h
    exact h
  have hd := doublingExponent_toReal (p := p) (q := q)
  have hq1 : 1 < q := by
    apply (ENNReal.toReal_lt_toReal (by simp) hq).mp
    norm_num
    linarith
  have hthird : ENNReal.ofReal (p.toReal/3) < q := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hq).mpr
    linarith
  obtain ⟨r,hr,hrq⟩ := exists_between (max_lt hq1 hthird)
  exact ⟨r,ne_top_of_le_ne_top hq hrq.le,(le_max_left _ _).trans_lt hr,hrq,
    (le_max_right _ _).trans hr.le⟩

end NLS.Coeff
