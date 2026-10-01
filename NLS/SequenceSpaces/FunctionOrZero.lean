import NLS.SequenceSpaces.Basic

/-!
# Total realization of a sequence function

This constructor retains the supplied coefficients whenever they are
in the requested sequence space. The zero fallback only makes the
definition total. Summable power majorants prove actual membership and
bound the resulting norm, so a caller can rule out the fallback.
-/

noncomputable section
open scoped ENNReal Classical
namespace NLS.Coeff

/-- Realize a sequence when it belongs to `ℓᵖ`, with a zero fallback. -/
def ofFunctionOrZero (p : ℝ≥0∞) (f : ℤ → ℂ) : Coeff p :=
  if h : Memℓp f p then ⟨f,h⟩ else 0

/-- Membership makes every coefficient exactly the original function. -/
theorem ofFunctionOrZero_apply_of_mem (p : ℝ≥0∞) (f : ℤ → ℂ)
    (hf : Memℓp f p) (n : ℤ) : ofFunctionOrZero p f n = f n := by
  simp only [ofFunctionOrZero,dif_pos hf]

/-- A summable power majorant constructs actual membership. -/
theorem memℓp_of_power_dominated {p : ℝ≥0∞} (f : ℤ → ℂ) (M : ℤ → ℝ)
    (hs : Summable M) (hb : ∀ n, ‖f n‖^p.toReal ≤ M n) : Memℓp f p :=
  memℓp_gen (hs.of_nonneg_of_le (fun _n => Real.rpow_nonneg (norm_nonneg _) _) hb)

/-- The realized sequence inherits its actual summable power bound. -/
theorem norm_ofFunctionOrZero_rpow_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (f : ℤ → ℂ) (M : ℤ → ℝ)
    (hs : Summable M) (hb : ∀ n, ‖f n‖^p.toReal ≤ M n) :
    ‖ofFunctionOrZero p f‖^p.toReal ≤ ∑' n : ℤ, M n := by
  have hf := memℓp_of_power_dominated f M hs hb
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  rw [lp.norm_rpow_eq_tsum hp0]
  simp only [ofFunctionOrZero_apply_of_mem p f hf]
  exact (hs.of_nonneg_of_le (fun _n => Real.rpow_nonneg (norm_nonneg _) _) hb).tsum_le_tsum hb hs

end NLS.Coeff
