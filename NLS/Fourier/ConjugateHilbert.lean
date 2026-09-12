import NLS.Fourier.DyadicHilbert
import NLS.Fourier.HilbertDuality

/-!
# Hilbert transforms at conjugates of dyadic exponents

Duality supplies ordinary and shifted transforms at `2, 4/3, 8/7, …`.
These proved exponents lie above one and approach it, while retaining the
ordinary dyadic bounds. Interpolation between the proved exponents remains open.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- The conjugates of the dyadic exponents, starting at `2`. -/
def dyadicConjugateExponent (n : ℕ) : ℝ≥0∞ := (dyadicHilbertExponent n).conjExponent

instance (n : ℕ) : (dyadicHilbertExponent n).HolderConjugate (dyadicConjugateExponent n) :=
  inferInstanceAs ((dyadicHilbertExponent n).HolderConjugate (dyadicHilbertExponent n).conjExponent)

instance (n : ℕ) : Fact (1 ≤ dyadicConjugateExponent n) :=
  ⟨ENNReal.HolderConjugate.one_le _ (dyadicHilbertExponent n)⟩

theorem one_lt_dyadicConjugateExponent (n : ℕ) : 1 < dyadicConjugateExponent n :=
  (ENNReal.HolderConjugate.lt_top_iff_one_lt _ _).mp
    (lt_top_iff_ne_top.mpr (dyadicHilbertExponent_ne_top n))

theorem dyadicConjugateExponent_ne_top (n : ℕ) : dyadicConjugateExponent n ≠ ⊤ :=
  (ENNReal.HolderConjugate.ne_top_iff_ne_one _ (dyadicHilbertExponent n)).mpr
    (one_lt_dyadicHilbertExponent n).ne'

/-- The usual fractional expression for each conjugate exponent. -/
theorem dyadicConjugateExponent_toReal (n : ℕ) :
    (dyadicConjugateExponent n).toReal = (2 : ℝ)^(n+1) / (2^(n+1) - 1) := by
  have hp : 0 < (dyadicHilbertExponent n).toReal := by simp
  have hq : 0 < (dyadicConjugateExponent n).toReal := ENNReal.toReal_pos
    (zero_lt_one.trans (one_lt_dyadicConjugateExponent n)).ne' (dyadicConjugateExponent_ne_top n)
  have h : (dyadicHilbertExponent n).toReal.HolderConjugate
      (dyadicConjugateExponent n).toReal := by
    simpa using ENNReal.HolderTriple.toReal 1 hp hq
  simpa only [dyadicHilbertExponent_toReal] using h.conjugate_eq

/-- Every exponent in this family belongs to `(1,2]`. -/
theorem dyadicConjugateExponent_le_two (n : ℕ) : dyadicConjugateExponent n ≤ 2 := by
  apply (ENNReal.toReal_le_toReal (dyadicConjugateExponent_ne_top n) (by norm_num)).mp
  rw [dyadicConjugateExponent_toReal]
  have hpow : (2 : ℝ) ≤ 2^(n+1) := by
    rw [pow_succ]
    nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := n)]
  norm_num only [ENNReal.toReal_ofNat]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 2^(n+1)-1)).mpr
  linarith

/-- Proved exponents occur arbitrarily close to one from above. -/
theorem dyadicConjugateExponent_near_one {r : ℝ} (hr : 1 < r) :
    ∃ n : ℕ, (dyadicConjugateExponent n).toReal < r := by
  obtain ⟨n, hn⟩ := dyadicHilbertExponent_unbounded (r / (r - 1))
  rw [dyadicHilbertExponent_toReal] at hn
  have he : (1 : ℝ) < 2^(n+1) := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  refine ⟨n, ?_⟩
  rw [dyadicConjugateExponent_toReal]
  apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 2^(n+1)-1)).mpr
  have ht := (div_lt_iff₀ (by linarith : 0 < r-1)).mp hn
  nlinarith

/-- Conjugation of the already proved dyadic estimate. -/
def conjugateHilbertEstimate (n : ℕ) : HilbertEstimate (dyadicConjugateExponent n) :=
  (dyadicHilbertEstimate n).conjugateTo (one_lt_dyadicConjugateExponent n)
    (dyadicConjugateExponent_ne_top n)

theorem conjugateHilbertEstimate_bound (n : ℕ) :
    (conjugateHilbertEstimate n).bound = dyadicHilbertBound n := rfl

/-- The ordinary transform at the conjugate of `2^(n+1)`. -/
def conjugateHilbert (n : ℕ) :
    Coeff (dyadicConjugateExponent n) →L[ℂ] Coeff (dyadicConjugateExponent n) :=
  (conjugateHilbertEstimate n).operator

theorem conjugateHilbert_finite (n : ℕ) (a : ℤ →₀ ℂ) (k : ℤ) :
    conjugateHilbert n (Coeff.ofFinsupp a) k = finiteHilbert a k :=
  (conjugateHilbertEstimate n).operator_finite a k

theorem norm_conjugateHilbert_apply_le (n : ℕ) (a : Coeff (dyadicConjugateExponent n)) :
    ‖conjugateHilbert n a‖ ≤ dyadicHilbertBound n * ‖a‖ :=
  (conjugateHilbertEstimate n).norm_operator_apply_le a

/-- The normalized shifted transform at the conjugate of `2^(n+1)`. -/
def conjugateShiftedHilbert (n : ℕ) :
    Coeff (dyadicConjugateExponent n) →L[ℂ] Coeff (dyadicConjugateExponent n) :=
  (conjugateHilbertEstimate n).shifted

theorem conjugateShiftedHilbert_finite (n : ℕ) (a : ℤ →₀ ℂ) (k : ℤ) :
    conjugateShiftedHilbert n (Coeff.ofFinsupp a) k =
      a.sum (fun j z => z * (2 / ((Real.pi : ℂ) * (2*j - 2*k - 1)))) :=
  (conjugateHilbertEstimate n).shifted_finite a k

theorem norm_conjugateShiftedHilbert_apply_le (n : ℕ) (a : Coeff (dyadicConjugateExponent n)) :
    ‖conjugateShiftedHilbert n a‖ ≤
      Real.pi⁻¹ * (dyadicHilbertBound n + ‖hilbertCorrectionCoeffs‖) * ‖a‖ :=
  (conjugateHilbertEstimate n).norm_shifted_apply_le a

/-- The two completed families satisfy the bilinear transposition identity. -/
theorem dualPairing_dyadicHilbert (n : ℕ) (a : Coeff (dyadicHilbertExponent n))
    (b : Coeff (dyadicConjugateExponent n)) :
    Coeff.dualPairing (dyadicHilbert n a) b = -Coeff.dualPairing a (conjugateHilbert n b) :=
  (dyadicHilbertEstimate n).dualPairing_operator (conjugateHilbertEstimate n) a b

end NLS.Fourier
