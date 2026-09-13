import NLS.SequenceSpaces.IteratedRowSums
import NLS.SequenceSpaces.IteratedRowTails
import NLS.ZakharovShabat.ReciprocalRowSummation

/-!
# Double reciprocal rows for the off-diagonal estimate

These are the two-index reciprocal sums following (1.16), sampled at `2n`.
The two far regions and the near-near region retain separate majorants.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The full double reciprocal row in the source off-diagonal Hölder bound. -/
def doubleReciprocalRow (hq : 1 < q) (a : Coeff p) (n : ℤ) : Coeff q :=
  Coeff.iteratedConvolutionRow a (Coeff.puncturedLattice q hq) (Coeff.puncturedLattice q hq) (2*n)

/-- The first far region retains its reciprocal-tail cutoff. -/
def doubleReciprocalFarRow (hq : 1 < q) (a : Coeff p) (M : ℕ) (n : ℤ) : Coeff q :=
  Coeff.iteratedConvolutionRow a (Coeff.fourierTail M (Coeff.puncturedLattice q hq))
    (Coeff.puncturedLattice q hq) (2*n)

/-- The near region is controlled by the actual potential tail. -/
def doubleReciprocalNearRow (hq : 1 < q) (a : Coeff p) (N : ℕ) (n : ℤ) : Coeff q :=
  doubleReciprocalRow hq (Coeff.fourierTail N a) n

/-- Both reciprocal tails have the same exact nested norm. -/
theorem doubleReciprocalFarRow_swap (hq : 1 < q) (hqt : q ≠ ⊤)
    (a : Coeff p) (M : ℕ) (n : ℤ) :
    ‖Coeff.iteratedConvolutionRow a (Coeff.puncturedLattice q hq)
      (Coeff.fourierTail M (Coeff.puncturedLattice q hq)) (2*n)‖ = ‖doubleReciprocalFarRow hq a M n‖ :=
  Coeff.norm_iteratedConvolutionRow_swap (ENNReal.toReal_pos (zero_lt_one.trans hq).ne' hqt) _ _ _ _

/-- The three-region estimate keeps the reciprocal decay and potential tail separate. -/
theorem norm_doubleReciprocalRow_tail_le (hq : 1 < q) (hqt : q ≠ ⊤)
    (a : Coeff p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖doubleReciprocalRow hq a n‖ ≤
      2 * ‖doubleReciprocalFarRow hq a (N/2) n‖ + ‖doubleReciprocalNearRow hq a N n‖ := by
  have h := Coeff.norm_iteratedConvolutionRow_tail_le a (Coeff.puncturedLattice q hq)
    (Coeff.puncturedLattice q hq) N n hn
  rw [doubleReciprocalFarRow_swap hq hqt] at h
  simpa only [doubleReciprocalRow, doubleReciprocalNearRow, doubleReciprocalFarRow, two_mul] using h

/-- A smaller admissible inner exponent controls the full double row. -/
theorem norm_doubleReciprocalRow_le_inner (hr : 1 < r) (hrq : r ≤ q) (a : Coeff p) (n : ℤ) :
    ‖doubleReciprocalRow (hr.trans_le hrq) a n‖ ≤ ‖doubleReciprocalRow hr a n‖ := by
  unfold doubleReciprocalRow
  rw [← exponentInclusion_puncturedLattice hr hrq]
  exact Coeff.norm_iteratedConvolutionRow_exponent_le hrq _ _ _ _

/-- Exponent inclusion preserves reciprocal-tail coefficients exactly. -/
theorem exponentInclusion_fourierTail_puncturedLattice (hr : 1 < r) (hrq : r ≤ q) (M : ℕ) :
    Coeff.exponentInclusion hrq (Coeff.fourierTail M (Coeff.puncturedLattice r hr)) =
      Coeff.fourierTail M (Coeff.puncturedLattice q (hr.trans_le hrq)) := by
  ext k
  simp only [Coeff.exponentInclusion_apply, Coeff.fourierTail_apply, Coeff.puncturedLattice_apply]

/-- The far row also contracts when both reciprocal exponents increase. -/
theorem norm_doubleReciprocalFarRow_le_inner (hr : 1 < r) (hrq : r ≤ q)
    (a : Coeff p) (M : ℕ) (n : ℤ) :
    ‖doubleReciprocalFarRow (hr.trans_le hrq) a M n‖ ≤ ‖doubleReciprocalFarRow hr a M n‖ := by
  unfold doubleReciprocalFarRow
  rw [← exponentInclusion_fourierTail_puncturedLattice hr hrq,
    ← exponentInclusion_puncturedLattice hr hrq]
  exact Coeff.norm_iteratedConvolutionRow_exponent_le hrq _ _ _ _

/-- Powered Young bounds each far region by one reciprocal-tail norm. -/
theorem exists_doubleReciprocalFarMajorant (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) (M : ℕ) :
    ∃ d : Coeff p, (∀ n : ℤ, ‖doubleReciprocalFarRow (hr.trans_le hrq) a M n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ ‖a‖ * ‖Coeff.fourierTail M (Coeff.puncturedLattice r hr)‖ * ‖Coeff.puncturedLattice r hr‖ := by
  obtain ⟨d, hd, hn⟩ := Coeff.exists_evenIteratedConvolutionRowNorm hp hrp a
    (Coeff.fourierTail M (Coeff.puncturedLattice r hr)) (Coeff.puncturedLattice r hr)
  refine ⟨d, ?_, hn⟩
  intro n
  rw [hd, Complex.norm_real, norm_norm]
  exact norm_doubleReciprocalFarRow_le_inner hr hrq a M n

/-- The near region gains a potential tail in its outer sequence norm. -/
theorem exists_doubleReciprocalNearMajorant (hp : p ≠ ⊤) (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q)
    (a : Coeff p) (N : ℕ) :
    ∃ d : Coeff p, (∀ n : ℤ, ‖doubleReciprocalNearRow (hr.trans_le hrq) a N n‖ ≤ ‖d n‖) ∧
      ‖d‖ ≤ ‖Coeff.fourierTail N a‖ * ‖Coeff.puncturedLattice r hr‖^2 := by
  obtain ⟨d, hd, hn⟩ := Coeff.exists_evenIteratedConvolutionRowNorm hp hrp (Coeff.fourierTail N a)
    (Coeff.puncturedLattice r hr) (Coeff.puncturedLattice r hr)
  refine ⟨d, ?_, hn.trans_eq (by ring)⟩
  intro n
  rw [hd, Complex.norm_real, norm_norm]
  exact norm_doubleReciprocalRow_le_inner hr hrq (Coeff.fourierTail N a) n

end NLS.ZakharovShabat
