import NLS.ZakharovShabat.ReciprocalRowSummation
import NLS.SequenceSpaces.PuncturedLatticeTail

/-!
# The two exponent regimes in the diagonal estimate

The inner exponent `min(p,p')` treats both sides of two through powered Young.
Its conjugate produces exactly the source decay exponent `min(1,p-1)`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single inner reciprocal exponent for both ranges in Lemma 6.8(i). -/
def diagonalInnerExponent (p : ℝ≥0∞) : ℝ≥0∞ := min p p.conjExponent

/-- The reciprocal exponent stays strictly above one throughout the source range. -/
theorem one_lt_diagonalInnerExponent (hp : p ≠ ⊤) (hp1 : 1 < p) :
    1 < diagonalInnerExponent p :=
  lt_min hp1 ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)

/-- The conjugate of the inner exponent gives exactly the source's two decay regimes. -/
theorem exists_diagonalInnerConjugate (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ s : ℝ, s.HolderConjugate (diagonalInnerExponent p).toReal ∧
      s ≤ max p.toReal p.conjExponent.toReal ∧ p.toReal / s = min 1 (p.toReal-1) := by
  have hq : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hc : p.toReal.HolderConjugate p.conjExponent.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  by_cases h : p ≤ p.conjExponent
  · have hreal := (ENNReal.toReal_le_toReal hp hq).mpr h
    have hmin : p.toReal-1 ≤ 1 := by
      rw [← hc.div_conj_eq_sub_one]
      exact (div_le_one hc.symm.pos).mpr hreal
    refine ⟨p.conjExponent.toReal, ?_, le_max_right _ _, ?_⟩
    · simpa only [diagonalInnerExponent, min_eq_left h] using hc.symm
    · rw [hc.div_conj_eq_sub_one, min_eq_right hmin]
  · have hle := (le_of_not_ge h)
    have hreal := (ENNReal.toReal_le_toReal hq hp).mpr hle
    have hmin : 1 ≤ p.toReal-1 := by
      rw [← hc.div_conj_eq_sub_one]
      exact (one_le_div hc.symm.pos).mpr hreal
    refine ⟨p.toReal, ?_, le_max_left _ _, ?_⟩
    · simpa only [diagonalInnerExponent, min_eq_right hle] using hc
    · rw [div_self hc.pos.ne', min_eq_left hmin]

/-- Explicit reciprocal-row tail decay for an arbitrary admissible inner exponent. -/
theorem exists_reciprocalRowTailMajorant_explicit {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) {s : ℝ}
    (hc : s.HolderConjugate r.toReal) (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    ∃ d : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → ‖complementaryRowEnvelope (hr.trans_le hrq) a n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ 4*s * (‖a‖ * (N : ℝ) ^ (-(1/s)) + ‖Coeff.fourierTail N a‖) := by
  obtain ⟨d, hd, hn⟩ := exists_reciprocalRowTailMajorant hp hr hrp hrq a N
  refine ⟨d, hd, hn.trans ?_⟩
  calc
    _ ≤ ‖a‖ * (4*s * (N : ℝ) ^ (-(1/s))) + ‖Coeff.fourierTail N a‖ * (4*s) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (Coeff.norm_fourierTail_puncturedLattice_le hr hc N hN) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (Coeff.norm_puncturedLattice_le_four_conjugate hr hc) (norm_nonneg _))
    _ = _ := by ring

end NLS.ZakharovShabat
