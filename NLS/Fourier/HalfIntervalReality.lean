import NLS.Fourier.HalfIntervalBoundedness

/-!
# Conjugation and the source half-interval extension

Conjugation reverses the raw Fourier index. The completed half-interval map
preserves this relation at every `1 < p < ∞`, including its odd Hilbert tail.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem conj_half_mul (z : ℂ) :
    (1/2 : ℂ) * (starRingEnd ℂ) z = (starRingEnd ℂ) ((1/2 : ℂ)*z) := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_ofReal 2
  rw [map_mul, map_div₀, map_one, h2]

/-- Conjugate-reflected inputs have conjugate-reflected completed half coefficients. -/
theorem halfIntervalCoeffs_conj (hp : 1 < p) (hptop : p ≠ ⊤)
    (a b : Coeff p) (hab : ∀ k : ℤ, b k = (starRingEnd ℂ) (a (-k))) (n : ℤ) :
    halfIntervalCoeffs hp hptop b n = (starRingEnd ℂ) (halfIntervalCoeffs hp hptop a (-n)) := by
  let q := p.conjExponent
  let : p.HolderConjugate q := inferInstanceAs (p.HolderConjugate p.conjExponent)
  let : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hq : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp (lt_top_iff_ne_top.mpr hptop)
  have hqtop : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp.ne'
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, show -(2*(n/2)) = 2*(-(n/2)) by ring,
      halfIntervalCoeffs_even, halfIntervalCoeffs_even, hab]
    exact conj_half_mul _
  · have he : n = 2*(n/2)+1 := by omega
    rw [he, show -(2*(n/2)+1) = 2*(-(n/2)-1)+1 by ring,
      halfIntervalCoeffs_odd, halfIntervalCoeffs_odd,
      shiftedHilbertTransform_apply hp hptop hq hqtop,
      shiftedHilbertTransform_apply hp hptop hq hqtop,
      map_mul, Complex.conj_tsum,
      ← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
        (starRingEnd ℂ) (a k * (2 / ((Real.pi : ℂ) * (2*k - 2*((-(n/2)-1 : ℤ) : ℂ) - 1)))))]
    simp only [map_div₀, map_ofNat, Complex.conj_I, neg_div, neg_mul]
    rw [← mul_neg, ← tsum_neg]
    congr 1
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply, hab, map_mul, map_div₀, map_ofNat,
      map_sub, map_one, map_intCast, Complex.conj_ofReal]
    push_cast
    rw [show 2 * (-(k : ℂ)) - 2 * (-(↑(n / 2) : ℂ) - 1) - 1 =
      -(2 * (k : ℂ) - 2 * ↑(n / 2) - 1) by ring, mul_neg, div_neg]
    ring

end NLS.Fourier
