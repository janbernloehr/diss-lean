import NLS.ZakharovShabat.DoubleReciprocalRows
import NLS.ZakharovShabat.DiagonalSummationExponent

/-!
# The double reciprocal sums after (1.16)

The nested norm agrees with the source sum after a signed reindexing. The
far and near sequence majorants have explicit bounds for both exponent regimes.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] in
/-- The punctured reciprocal norm includes the excluded index through division by zero. -/
theorem norm_puncturedLattice_eq_inv_abs (hq : 1 < q) (k : ℤ) :
    ‖Coeff.puncturedLattice q hq k‖ = |(k : ℝ)|⁻¹ := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [Coeff.puncturedLattice_apply, if_neg hk, norm_inv, Complex.norm_intCast]

/-- The double row power is precisely the physical-frequency reciprocal sum in (1.16). -/
theorem norm_doubleReciprocalRow_rpow (hq : 1 < q) (hqt : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    ‖doubleReciprocalRow hq a n‖^q.toReal =
      ∑' l : ℤ, ∑' k : ℤ, (‖a (l+k)‖ / |((n-l : ℤ) : ℝ)| / |((n-k : ℤ) : ℝ)|)^q.toReal := by
  rw [doubleReciprocalRow, Coeff.norm_iteratedConvolutionRow_rpow
    (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt)]
  rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro l
  rw [← (Equiv.subLeft n).tsum_eq]
  apply tsum_congr
  intro k
  change ‖a (2*n-(n-l)-(n-k)) * Coeff.puncturedLattice q hq (n-k) *
    Coeff.puncturedLattice q hq (n-l)‖^q.toReal = _
  rw [show 2*n-(n-l)-(n-k) = l+k by ring]
  simp only [norm_mul, norm_puncturedLattice_eq_inv_abs, div_eq_mul_inv]
  rw [mul_right_comm]

/-- One far reciprocal factor yields explicit norm decay of the entire region sequence. -/
theorem exists_doubleReciprocalFarMajorant_explicit (hp : p ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) {s : ℝ} (hc : s.HolderConjugate r.toReal)
    (a : Coeff p) (M : ℕ) (hM : 0 < M) :
    ∃ d : Coeff p, (∀ n : ℤ, ‖doubleReciprocalFarRow (hr.trans_le hrq) a M n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ 16*s^2*‖a‖ * (M : ℝ)^(-(1/s)) := by
  obtain ⟨d, hd, hn⟩ := exists_doubleReciprocalFarMajorant hp hr hrp hrq a M
  have hs0 := hc.pos.le
  refine ⟨d, hd, hn.trans ?_⟩
  calc
    _ ≤ ‖a‖ * (4*s*(M : ℝ)^(-(1/s))) * (4*s) := by
      gcongr
      · exact Coeff.norm_fourierTail_puncturedLattice_le hr hc M hM
      · exact Coeff.norm_puncturedLattice_le_four_conjugate hr hc
    _ = _ := by ring

/-- The near region has an explicit bound involving only the potential tail. -/
theorem exists_doubleReciprocalNearMajorant_explicit (hp : p ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) {s : ℝ} (hc : s.HolderConjugate r.toReal)
    (a : Coeff p) (N : ℕ) :
    ∃ d : Coeff p, (∀ n : ℤ, ‖doubleReciprocalNearRow (hr.trans_le hrq) a N n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ 16*s^2*‖Coeff.fourierTail N a‖ := by
  obtain ⟨d, hd, hn⟩ := exists_doubleReciprocalNearMajorant hp hr hrp hrq a N
  have hs0 := hc.pos.le
  refine ⟨d, hd, hn.trans ?_⟩
  calc
    _ ≤ ‖Coeff.fourierTail N a‖ * (4*s)^2 := by
      gcongr
      exact Coeff.norm_puncturedLattice_le_four_conjugate hr hc
    _ = _ := by ring

end NLS.ZakharovShabat
