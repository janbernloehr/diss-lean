import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.ReciprocalNorm

/-!
# Explicit decay of punctured reciprocal tails

At a finite reciprocal exponent, Appendix B.1 gives the exact decay power
needed after the convolution-row bound. The tail includes its boundary.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

omit [Fact (1 ≤ r)] in
/-- The reciprocal tail has explicit norm decay, retaining the boundary `|k|=N`. -/
theorem norm_fourierTail_puncturedLattice_le (hr : 1 < r) {s : ℝ}
    (hc : s.HolderConjugate r.toReal) (N : ℕ) (hN : 0 < N) :
    ‖fourierTail N (puncturedLattice r hr)‖ ≤ 4 * s * (N : ℝ) ^ (-(1/s)) := by
  apply norm_punctured_reciprocal_le hc (by exact_mod_cast hN)
  · simp
  · intro k hk
    by_cases hNk : N ≤ k.natAbs
    · simp only [fourierTail_apply, if_pos hNk, puncturedLattice_apply, if_neg hk, norm_inv, Complex.norm_intCast]
      have hkr : (N : ℝ) ≤ |(k : ℝ)| := by
        have hcast : (N : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast hNk
        simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [inv_eq_one_div]
      apply (div_le_div_iff₀ (hNr.trans_le hkr) (by positivity)).mpr
      linarith
    · simp only [fourierTail_apply, if_neg hNk, norm_zero]
      positivity

omit [Fact (1 ≤ r)] in
/-- Removing only the zero coefficient leaves the punctured reciprocal lattice unchanged. -/
theorem fourierTail_one_puncturedLattice (hr : 1 < r) :
    fourierTail 1 (puncturedLattice r hr) = puncturedLattice r hr := by
  ext k
  by_cases hk : k = 0
  · simp [hk]
  · have h : 1 ≤ k.natAbs := by omega
    simp [fourierTail_apply, h]

omit [Fact (1 ≤ r)] in
/-- A compatible explicit bound for the complete punctured lattice. -/
theorem norm_puncturedLattice_le_four_conjugate (hr : 1 < r) {s : ℝ}
    (hc : s.HolderConjugate r.toReal) : ‖puncturedLattice r hr‖ ≤ 4*s := by
  have h := norm_fourierTail_puncturedLattice_le hr hc 1 (by omega)
  simpa only [fourierTail_one_puncturedLattice, Nat.cast_one, Real.one_rpow, mul_one] using h

end NLS.Coeff
