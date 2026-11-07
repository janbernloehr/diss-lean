import NLS.SequenceSpaces.PhysicalHilbertQuadratic
import NLS.SequenceSpaces.SignedSobolevWeight

/-! Exact signed Hilbert pairings at orders zero and one-half. Positive
and negative physical modes are retained, with ALL sums absolutely
convergent. Finite-support formulas are identities AT THE GIVEN point. -/
noncomputable section
open Complex
namespace NLS.WeightedCoeff

theorem fourierRealZeroHilbertPairing_signed_zero_apply
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev 0) 2) :
    fourierRealZeroHilbertPairing (Weight.signedSobolev 0) a b=
      ∑' k : ℤ, a.val.val.val k*b.val.val.val (-k) := by
  rw [fourierRealZeroHilbertPairing_apply]
  apply tsum_congr
  intro k
  simp only [Weight.signedSobolev,Real.rpow_zero,Complex.ofReal_one,one_mul]

private theorem signed_half_pair_term
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2) (k : ℤ) :
    ((Weight.signedSobolev (1/2) k:ℂ)*a.val.val.val k)*
        ((Weight.signedSobolev (1/2) (-k):ℂ)*b.val.val.val (-k))=
      ((|(k:ℝ)|:ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k) := by
  by_cases hk : k=0
  · subst k
    rw [show a.val.val.val 0=0 from a.val.property]
    simp
  · have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
      exact_mod_cast (show (1:ℤ) ≤ |k| by have h := abs_pos.mpr hk; omega)
    have hw : (Weight.signedSobolev (1/2) k:ℂ)*(Weight.signedSobolev (1/2) (-k):ℂ)=((|(k:ℝ)|:ℝ):ℂ) := by
      rw [Weight.signedSobolev_neg,← Complex.ofReal_mul]
      congr 1
      change (max (1:ℝ) |(k:ℝ)|)^(1/2)*(max (1:ℝ) |(k:ℝ)|)^(1/2)= _
      rw [← pow_two,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),max_eq_right hkabs]
    calc
      _ = ((Weight.signedSobolev (1/2) k:ℂ)*(Weight.signedSobolev (1/2) (-k):ℂ))*
          (a.val.val.val k*b.val.val.val (-k)) := by ring
      _ = _ := by rw [hw]; ring

theorem fourierRealZeroHilbertPairing_signed_half_apply
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2) :
    fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) a b=
      ∑' k : ℤ, ((|(k:ℝ)|:ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k) := by
  rw [fourierRealZeroHilbertPairing_apply]
  exact tsum_congr (signed_half_pair_term a b)

theorem summable_norm_fourierRealZeroHilbertPairing_signed_half
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2) :
    Summable (fun k : ℤ => ‖((|(k:ℝ)|:ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k)‖) := by
  simpa only [signed_half_pair_term] using
    summable_norm_fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) a b

/-- The ENTIRE positive-half pairing at a finite-supported first factor.
This does NOT assert a finite-support identity in a neighborhood. -/
theorem fourierRealZeroHilbertPairing_signed_half_finite
    (a b : fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2) (s : Finset ℕ+)
    (ha : ∀ n : ℕ+, n ∉ s → a.val.val.val (n:ℤ)=0) :
    fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) a b=
      ∑ n ∈ s, ((n:ℕ):ℂ)*(a.val.val.val (n:ℤ)*b.val.val.val (-(n:ℤ))+
        a.val.val.val (-(n:ℤ))*b.val.val.val (n:ℤ)) := by
  let f : ℤ → ℂ := fun k => ((|(k:ℝ)|:ℝ):ℂ)*a.val.val.val k*b.val.val.val (-k)
  have hs : Summable f := (summable_norm_fourierRealZeroHilbertPairing_signed_half a b).of_norm
  have ht := tsum_int_eq_zero_add_tsum_pnat hs
  have hf0 : f 0=0 := by simp [f]
  have hp : (∑' n : ℕ+, f (n:ℤ))=∑ n ∈ s, f (n:ℤ) := by
    apply tsum_eq_sum
    intro n hn
    dsimp only [f]
    rw [ha n hn,mul_zero,zero_mul]
  have hn : (∑' n : ℕ+, f (-(n:ℤ)))=∑ n ∈ s, f (-(n:ℤ)) := by
    apply tsum_eq_sum
    intro n hn
    dsimp only [f]
    rw [a.property,ha n hn,map_zero,mul_zero,zero_mul]
  rw [fourierRealZeroHilbertPairing_signed_half_apply]
  change (∑' k : ℤ, f k)= _
  rw [ht,hf0,zero_add,hp,hn,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [f]
  simp only [Int.cast_natCast,Int.cast_neg,abs_neg,abs_of_nonneg (Nat.cast_nonneg (n:ℕ) : (0:ℝ) ≤ ((n:ℕ):ℝ)),neg_neg]
  push_cast
  ring

/-- The whole positive action-energy series converges, with EXACT original
2*pi*n weights, to pi times the signed positive-half squared norm. -/
theorem hasSum_positive_signedHalf_energy
    (a : fourierRealZeroSubmodule (Weight.signedSobolev (1/2)) 2) :
    HasSum (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ)))
      ((Real.pi:ℂ)*fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) a a) := by
  let f : ℤ → ℂ := fun k => ((|(k:ℝ)|:ℝ):ℂ)*a.val.val.val k*a.val.val.val (-k)
  have hs : Summable f := (summable_norm_fourierRealZeroHilbertPairing_signed_half a a).of_norm
  have hpos : Summable (fun n : ℕ+ => f (n:ℤ)) := hs.comp_injective
    (fun n m h => PNat.coe_injective (Int.ofNat_inj.mp h))
  have heven : f.Even := by
    intro k
    dsimp only [f]
    simp only [Int.cast_neg,neg_neg,abs_neg]
    ring
  have ht := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs
  have hf0 : f 0=0 := by simp [f]
  rw [hf0,zero_add] at ht
  have hB : fourierRealZeroHilbertPairing (Weight.signedSobolev (1/2)) a a=
      2*∑' n : ℕ+, f (n:ℤ) := by
    rw [fourierRealZeroHilbertPairing_signed_half_apply]
    change (∑' k : ℤ, f k)= _
    simpa only [two_smul,two_mul] using ht
  have hh := hpos.hasSum.mul_left (2*Real.pi:ℂ)
  have he : (fun n : ℕ+ => ((2*Real.pi*(n:ℕ):ℝ):ℂ)*a.val.val.val (n:ℤ)*a.val.val.val (-(n:ℤ)))=
      (fun n : ℕ+ => (2*Real.pi:ℂ)*f (n:ℤ)) := by
    funext n
    dsimp only [f]
    simp only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (n:ℕ) : (0:ℝ) ≤ ((n:ℕ):ℝ))]
    push_cast
    ring
  rw [he,hB]
  have hv : (Real.pi:ℂ)*(2*∑' n : ℕ+, f (n:ℤ))=(2*Real.pi:ℂ)*(∑' n : ℕ+, f (n:ℤ)) := by ring
  rw [hv]
  exact hh

end NLS.WeightedCoeff
