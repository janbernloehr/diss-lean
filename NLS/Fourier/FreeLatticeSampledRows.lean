import NLS.Fourier.SampledHilbert

/-!
# Sampled free-lattice reciprocal rows

Points within a quarter-π disc about the free lattice have a normalized
sampling displacement of norm at most one half.  The signed reciprocal
rows on any selected set of indices are therefore a restriction of the
sampled discrete Hilbert transform.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Normalize a family of spectral samples by the free-lattice spacing,
and set unused rows to zero. -/
def freeLatticeSample (S : Set ℤ) (z : ℤ → ℂ) (n : ℤ) : ℂ := by
  classical
  exact if n ∈ S then (z n-(Real.pi : ℂ)*n)/(Real.pi : ℂ) else 0

/-- Samples in free quarter-π discs satisfy the Hilbert sampling bound. -/
theorem norm_freeLatticeSample_le_half
    (S : Set ℤ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (n : ℤ) : ‖freeLatticeSample S z n‖ ≤ (1 : ℝ)/2 := by
  classical
  by_cases hn : n ∈ S
  · simp only [freeLatticeSample, if_pos hn, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have h := hz n hn
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_pos]
  · simp [freeLatticeSample, hn]

/-- The free reciprocal denominator is π times the normalized sampled
Hilbert denominator on selected rows. -/
theorem freeLattice_denominator_eq
    (S : Set ℤ) (z : ℤ → ℂ) {n : ℤ} (hn : n ∈ S) (m : ℤ) :
    ((m : ℂ)-n-freeLatticeSample S z n)*(Real.pi : ℂ) =
      (Real.pi : ℂ)*m-z n := by
  classical
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [freeLatticeSample, if_pos hn]
  calc
    ((m : ℂ)-n-(z n-(Real.pi : ℂ)*n)/(Real.pi : ℂ))*(Real.pi : ℂ) =
        ((m : ℂ)-n)*(Real.pi : ℂ)-(z n-(Real.pi : ℂ)*n) := by
          rw [sub_mul, div_mul_cancel₀ _ hπ]
    _ = (Real.pi : ℂ)*m-z n := by ring

/-- The free reciprocal term is a rescaled sampled Hilbert term. -/
theorem freeLatticeTerm_eq_sampled
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : Set ℤ) (z : ℤ → ℂ) (a : Coeff p)
    {n : ℤ} (hn : n ∈ S) (m : ℤ) :
    (if m = n then 0 else a m/((Real.pi : ℂ)*m-z n)) =
      (Real.pi : ℂ)⁻¹ *
        perturbedHilbertTerm (freeLatticeSample S z) a n m := by
  by_cases hmn : m = n
  · simp [hmn, perturbedHilbertTerm]
  simp only [if_neg hmn, perturbedHilbertTerm]
  rw [← freeLattice_denominator_eq S z hn m]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restrict an `ℓp` sequence to arbitrary selected integer rows. -/
def restrictRows (S : Set ℤ) (a : Coeff p) : Coeff p := by
  classical
  exact ⟨fun n => if n ∈ S then a n else 0,
    (lp.memℓp a).mono' (by
      intro n
      by_cases hn : n ∈ S <;> simp [hn])⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem restrictRows_apply_of_mem
    (S : Set ℤ) (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    restrictRows S a n = a n := by
  classical
  simp [restrictRows, hn]

/-- Row restriction is contractive at every Banach exponent. -/
theorem norm_restrictRows_le (S : Set ℤ) (a : Coeff p) :
    ‖restrictRows S a‖ ≤ ‖a‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro n
  classical
  by_cases hn : n ∈ S <;> simp [restrictRows, hn]

/-- The signed free-lattice reciprocal rows as an `ℓp` coefficient
sequence, with zeros outside the selected set. -/
def freeLatticeRows (hp1 : 1 < p) (hp : p ≠ ⊤)
    (S : Set ℤ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) : Coeff p :=
  restrictRows S ((Real.pi : ℂ)⁻¹ •
    sampledHilbert hp1 hp (freeLatticeSample S z)
      (norm_freeLatticeSample_le_half S z hz) a)

/-- Every selected coefficient equals its absolutely convergent free
reciprocal row. -/
theorem freeLatticeRows_apply
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    (S : Set ℤ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    freeLatticeRows hp1 hp S z hz a n =
      ∑' m : ℤ, (if m = n then 0 else a m/((Real.pi : ℂ)*m-z n)) := by
  rw [freeLatticeRows, restrictRows_apply_of_mem S _ hn]
  change (Real.pi : ℂ)⁻¹ *
    sampledHilbert hp1 hp (freeLatticeSample S z)
      (norm_freeLatticeSample_le_half S z hz) a n = _
  rw [sampledHilbert_apply, ← tsum_mul_left]
  congr 1
  funext m
  exact (freeLatticeTerm_eq_sampled S z a hn m).symm

/-- The sampled free reciprocal row has a uniform `ℓp` norm bound. -/
theorem norm_freeLatticeRows_le
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    (S : Set ℤ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) :
    ‖freeLatticeRows hp1 hp S z hz a‖ ≤
      Real.pi⁻¹*(hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*‖a‖ := by
  let t := freeLatticeSample S z
  let ht := norm_freeLatticeSample_le_half S z hz
  calc
    ‖freeLatticeRows hp1 hp S z hz a‖ ≤
        ‖(Real.pi : ℂ)⁻¹ • sampledHilbert hp1 hp t ht a‖ :=
      norm_restrictRows_le S _
    _ = Real.pi⁻¹*‖sampledHilbert hp1 hp t ht a‖ := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    _ ≤ Real.pi⁻¹*((hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*‖a‖) :=
      mul_le_mul_of_nonneg_left (norm_sampledHilbert_le hp1 hp t ht a)
        (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by ring

/-- Free-lattice rows are absolutely summable coefficientwise. -/
theorem summable_norm_freeLatticeRow
    (hp1 : 1 < p) (hp : p ≠ ⊤)
    (S : Set ℤ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ S, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4)
    (a : Coeff p) {n : ℤ} (hn : n ∈ S) :
    Summable (fun m : ℤ =>
      ‖if m = n then 0 else a m/((Real.pi : ℂ)*m-z n)‖) := by
  have ht := norm_freeLatticeSample_le_half S z hz
  have hbase := summable_norm_perturbedHilbertSeries hp1 hp
    (freeLatticeSample S z) ht a n
  have hscaled := hbase.mul_left ‖(Real.pi : ℂ)⁻¹‖
  simpa only [← norm_mul, ← freeLatticeTerm_eq_sampled S z a hn] using hscaled

end NLS.Fourier
