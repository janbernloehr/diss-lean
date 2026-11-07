import NLS.SequenceSpaces.PhysicalHilbertQuadratic
import NLS.SequenceSpaces.SignedSobolevWeight

/-! All-order signed Hilbert action sums on the physical Fourier real
form. Both signed modes and the literal max(1,abs(k)) weight are retained.
In particular the negative-half formula uses inverse frequencies. -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

private theorem signed_pair_term (s : ℝ)
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) (k : ℤ) :
    ((Weight.signedSobolev s k:ℂ)*a.val.val.val k)*
        ((Weight.signedSobolev s (-k):ℂ)*b.val.val.val (-k))=
      (((max 1 |(k:ℝ)|)^(2*s):ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k) := by
  rw [Weight.signedSobolev_neg]
  have hw : (Weight.signedSobolev s k:ℂ)*(Weight.signedSobolev s k:ℂ)=
      (((max 1 |(k:ℝ)|)^(2*s):ℝ):ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    change (max (1:ℝ) |(k:ℝ)|)^s*(max (1:ℝ) |(k:ℝ)|)^s = _
    rw [← Real.rpow_add (by positivity),two_mul]
  calc
    _ = ((Weight.signedSobolev s k:ℂ)*(Weight.signedSobolev s k:ℂ))*
      (a.val.val.val k*b.val.val.val (-k)) := by ring
    _ = _ := by rw [hw]; ring

theorem fourierRealZeroHilbertPairing_signed_apply (s : ℝ)
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) :
    fourierRealZeroHilbertPairing (Weight.signedSobolev s) a b=
      ∑' k : ℤ, (((max 1 |(k:ℝ)|)^(2*s):ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k) := by
  rw [fourierRealZeroHilbertPairing_apply]
  exact tsum_congr (signed_pair_term s a b)

theorem summable_norm_fourierRealZeroHilbertPairing_signed (s : ℝ)
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) :
    Summable (fun k : ℤ =>
      ‖(((max 1 |(k:ℝ)|)^(2*s):ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k)‖) := by
  simpa only [signed_pair_term] using
    summable_norm_fourierRealZeroHilbertPairing (Weight.signedSobolev s) a b

/-- The positive-index sum is exactly one half of the full signed pairing. -/
theorem hasSum_positive_signedHilbert_pairing (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) :
    HasSum (fun n : ℕ+ => ((((n:ℕ):ℝ)^(2*s):ℝ):ℂ)*
      a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ)))
      ((1/2:ℂ)*fourierRealZeroHilbertPairing (Weight.signedSobolev s) a a) := by
  let f : ℤ → ℂ := fun k => (((max 1 |(k:ℝ)|)^(2*s):ℝ):ℂ)*
    a.val.val.val k*a.val.val.val (-k)
  have hs : Summable f := (summable_norm_fourierRealZeroHilbertPairing_signed s a a).of_norm
  have hpos : Summable (fun n : ℕ+ => f (n:ℤ)) := hs.comp_injective
    (fun n m h => PNat.coe_injective (Int.ofNat_inj.mp h))
  have heven : f.Even := by
    intro k
    dsimp only [f]
    simp only [Int.cast_neg,neg_neg,abs_neg]
    ring
  have ht := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs
  have hf0 : f 0=0 := by
    dsimp only [f]
    rw [show a.val.val.val 0=0 from a.val.property]
    simp
  rw [hf0,zero_add] at ht
  have hB : fourierRealZeroHilbertPairing (Weight.signedSobolev s) a a=
      2*∑' n : ℕ+, f (n:ℤ) := by
    rw [fourierRealZeroHilbertPairing_signed_apply]
    change (∑' k : ℤ, f k)= _
    simpa only [two_smul,two_mul] using ht
  have he : (fun n : ℕ+ => ((((n:ℕ):ℝ)^(2*s):ℝ):ℂ)*
      a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ)))=(fun n : ℕ+ => f (n:ℤ)) := by
    funext n
    have hn : (1:ℝ) ≤ (n:ℕ) := by exact_mod_cast n.property
    simp only [f,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (n:ℕ) : (0:ℝ) ≤ ((n:ℕ):ℝ)),max_eq_right hn]
  rw [he,hB]
  convert hpos.hasSum using 1
  ring

theorem hasSum_positive_signedHilbert_norm_sq (s : ℝ)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) :
    HasSum (fun n : ℕ+ => ((((n:ℕ):ℝ)^(2*s):ℝ):ℂ)*
      a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ))) (((1/2:ℝ)*‖a‖^2:ℝ):ℂ) := by
  have h := hasSum_positive_signedHilbert_pairing s a
  rw [fourierRealZeroHilbertPairing_self_eq_norm_sq _ (Weight.signedSobolev_neg s)] at h
  simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using h

/-- The inverse-frequency series has no 2*pi factor in the signed norm. -/
theorem hasSum_positive_signedNegativeHalf_norm_sq
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2) :
    HasSum (fun n : ℕ+ => (((n:ℕ):ℂ)⁻¹)*
      a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ))) (((1/2:ℝ)*‖a‖^2:ℝ):ℂ) := by
  have h := hasSum_positive_signedHilbert_norm_sq (-1/2) a
  norm_num only [show (2:ℝ)*(-1/2) = -1 by norm_num, Real.rpow_neg_one] at h
  simpa only [Complex.ofReal_inv,Complex.ofReal_natCast] using h

end NLS.WeightedCoeff
