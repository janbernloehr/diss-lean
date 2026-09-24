import NLS.Fourier.FreeLatticeSampledRows
import NLS.Fourier.SeparatedReciprocalRows

/-!
# Signed physical reciprocal rows

The physical midpoint row is the free sampled Hilbert row plus the
square-kernel correction.  This gives an `ℓp` bound for the full signed
off-diagonal sum at every finite exponent strictly above one.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The true off-diagonal reciprocal row as an `ℓp` sequence. -/
def physicalReciprocalRows
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (hsep : SeparatedReciprocalRows S C R τ z)
    (hfree : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) : Coeff p :=
  freeLatticeRows hp1 hp S z hfree a+
    separatedReciprocalCorrection hsep a

/-- The physical row is an absolutely convergent series. -/
theorem summable_norm_physicalReciprocalRow
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (hsep : SeparatedReciprocalRows S C R τ z)
    (hfree : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    Summable (fun m : ℤ =>
      ‖if m = n then 0 else a m/(τ m-z n)‖) := by
  have hf := summable_norm_freeLatticeRow hp1 hp S z hfree a hn
  have hc := summable_norm_separatedReciprocalTerm hsep a hn
  apply (hf.add hc).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro m
  by_cases hmn : m = n
  · subst m
    simp [separatedReciprocalTerm]
  have heq : a m/(τ m-z n) =
      a m/((Real.pi : ℂ)*m-z n)+separatedReciprocalTerm τ z a n m := by
    simp only [separatedReciprocalTerm, if_neg hmn]
    ring
  rw [if_neg hmn, heq]
  simpa only [if_neg hmn] using
    (norm_add_le (a m/((Real.pi : ℂ)*m-z n))
      (separatedReciprocalTerm τ z a n m))

/-- The coefficient sequence agrees with the true signed midpoint sum
on every selected row. -/
theorem physicalReciprocalRows_apply
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (hsep : SeparatedReciprocalRows S C R τ z)
    (hfree : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    physicalReciprocalRows hp1 hp hsep hfree a n =
      ∑' m : ℤ, (if m = n then 0 else a m/(τ m-z n)) := by
  have hf := (summable_norm_freeLatticeRow hp1 hp S z hfree a hn).of_norm
  have hc := (summable_norm_separatedReciprocalTerm hsep a hn).of_norm
  change freeLatticeRows hp1 hp S z hfree a n+
    separatedReciprocalCorrection hsep a n = _
  rw [freeLatticeRows_apply hp1 hp S z hfree a hn,
    separatedReciprocalCorrection_apply hsep a hn, ← hf.tsum_add hc]
  congr 1
  funext m
  by_cases hmn : m = n
  · subst m
    simp [separatedReciprocalTerm]
  simp only [if_neg hmn, separatedReciprocalTerm]
  ring

/-- The signed physical rows retain the input exponent, uniformly in
all admissible samples. -/
theorem norm_physicalReciprocalRows_le
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    {S : Set ℤ} {C R : ℝ} {τ z : ℤ → ℂ}
    (hsep : SeparatedReciprocalRows S C R τ z)
    (hfree : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) :
    ‖physicalReciprocalRows hp1 hp hsep hfree a‖ ≤
      (Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)+
        C*R*‖hilbertSquareCoeffs‖)*‖a‖ := by
  calc
    ‖physicalReciprocalRows hp1 hp hsep hfree a‖ ≤
        ‖freeLatticeRows hp1 hp S z hfree a‖+
          ‖separatedReciprocalCorrection hsep a‖ := norm_add_le _ _
    _ ≤ Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*‖a‖+
          C*R*(‖a‖*‖hilbertSquareCoeffs‖) :=
      add_le_add (norm_freeLatticeRows_le hp1 hp S z hfree a)
        (norm_separatedReciprocalCorrection_le hsep a)
    _ = _ := by ring

end NLS.Fourier
