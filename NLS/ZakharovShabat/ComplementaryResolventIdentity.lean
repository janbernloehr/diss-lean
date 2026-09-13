import NLS.ZakharovShabat.ComplementaryFreeInverse

/-!
# Resolvent identities on the complementary weighted space

The removed resonant frequency contributes zero, so the usual resolvent
identity remains valid at the central lattice point and on closed strip edges.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar resolvent identity also holds at the removed frequency. -/
theorem complementarySymbol_sub (n : ℤ) (z y : ℂ) (hz : z ∈ resonantStrip n)
    (hy : y ∈ resonantStrip n) (k : ℤ) :
    complementarySymbol n z k - complementarySymbol n y k =
      (y-z) * complementarySymbol n y k * complementarySymbol n z k := by
  by_cases hk : k = n
  · simp [hk]
  · simp only [complementarySymbol, if_neg hk]
    field_simp [resonantStrip_denominator_ne_zero hz hk, resonantStrip_denominator_ne_zero hy hk]
    ring

/-- The domain-valued resolvent identity preserves the gain of one derivative. -/
theorem complementaryFreeDomainInverse_sub (w : Weight) (n : ℤ) (z y : ℂ)
    (hz : z ∈ resonantStrip n) (hy : y ∈ resonantStrip n) :
    complementaryFreeDomainInverse (p := p) w n z hz - complementaryFreeDomainInverse w n y hy =
      (y-z) • (complementaryFreeDomainInverse w n y hy).comp (complementaryFreeInverse w n z hz) := by
  apply ContinuousLinearMap.ext
  intro f
  apply weightedPair_ext <;> intro k
  · change complementarySymbol n z (-k) * f.fst.val k - complementarySymbol n y (-k) * f.fst.val k =
      (y-z) * (complementarySymbol n y (-k) * (complementarySymbol n z (-k) * f.fst.val k))
    rw [← sub_mul, complementarySymbol_sub n z y hz hy]; ring
  · change complementarySymbol n z k * f.snd.val k - complementarySymbol n y k * f.snd.val k =
      (y-z) * (complementarySymbol n y k * (complementarySymbol n z k * f.snd.val k))
    rw [← sub_mul, complementarySymbol_sub n z y hz hy]; ring

/-- The base-valued complementary resolvent identity. -/
theorem complementaryFreeInverse_sub (w : Weight) (n : ℤ) (z y : ℂ)
    (hz : z ∈ resonantStrip n) (hy : y ∈ resonantStrip n) :
    complementaryFreeInverse (p := p) w n z hz - complementaryFreeInverse w n y hy =
      (y-z) • (complementaryFreeInverse w n y hy * complementaryFreeInverse w n z hz) := by
  apply ContinuousLinearMap.ext
  intro f
  apply weightedPair_ext <;> intro k
  · change complementarySymbol n z (-k) * f.fst.val k - complementarySymbol n y (-k) * f.fst.val k =
      (y-z) * (complementarySymbol n y (-k) * (complementarySymbol n z (-k) * f.fst.val k))
    rw [← sub_mul, complementarySymbol_sub n z y hz hy]; ring
  · change complementarySymbol n z k * f.snd.val k - complementarySymbol n y k * f.snd.val k =
      (y-z) * (complementarySymbol n y k * (complementarySymbol n z k * f.snd.val k))
    rw [← sub_mul, complementarySymbol_sub n z y hz hy]; ring

end NLS.ZakharovShabat
