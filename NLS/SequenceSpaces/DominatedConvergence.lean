import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Dominated convergence in finite-exponent coefficient spaces

Coordinatewise convergence and a single `lp` majorant imply norm convergence.
The exponent must be finite; domination alone does not suffice for `p = ∞`.
-/

open scoped ENNReal
open Filter
noncomputable section

namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A coefficient-space dominated convergence theorem, along any filter. -/
theorem tendsto_zero_of_dominated {ι : Type*} {l : Filter ι} (hp : p ≠ ⊤)
    (f : ι → Coeff p) (g : Coeff p)
    (hdom : ∀ᶠ i in l, ∀ n, ‖f i n‖ ≤ ‖g n‖)
    (hlim : ∀ n, Tendsto (fun i => f i n) l (nhds 0)) :
    Tendsto f l (nhds 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le Fact.out)) hp
  have hnorm (n : ℤ) : Tendsto (fun i => ‖f i n‖) l (nhds 0) := by
    simpa only [norm_zero] using (hlim n).norm
  have hs : Tendsto (fun i => ∑' n : ℤ, ‖f i n‖ ^ p.toReal) l (nhds 0) := by
    have h := tendsto_tsum_of_dominated_convergence
      (f := fun i n => ‖f i n‖ ^ p.toReal) (g := fun _ : ℤ => (0 : ℝ))
      ((lp.memℓp g).summable hr)
      (fun n => (hnorm n).rpow_const_nhds_zero hr)
      (hdom.mono fun i hi n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg (f i n)) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hi n) hr.le)
    simpa only [norm_zero, tsum_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := hs.rpow_const_nhds_zero (one_div_pos.mpr hr)
  simpa only [← lp.norm_eq_tsum_rpow hr] using h

end NLS.Coeff
