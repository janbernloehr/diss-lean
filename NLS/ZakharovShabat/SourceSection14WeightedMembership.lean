import NLS.ZakharovShabat.SourceSection14
import NLS.ZakharovShabat.SourceBirkhoffOriginalWeightedMap

/-! # Remark 14.2(iii): weighted membership and injectivity

One constructed Section 14 map is injective on every weighted real source.
Half-scale spectral weights recover the exact original Sobolev convention for
every nonnegative real regularity. Weighted analyticity, canonicality, and the
local and global inverse assertions are not established by this module.
-/
noncomputable section
namespace NLS.ZakharovShabat
/-- Half-scale on the period-two spectral lattice gives the original period-one Sobolev weight. -/
def sourceSobolevSpectralWeight (t : ℝ) (ht : 0 ≤ t) : SpectralWeight :=
  SpectralWeight.scaledSobolev (1/2) t (by norm_num) ht

@[simp] theorem sourceSobolevSpectralWeight_even (t : ℝ) (ht : 0 ≤ t) (n : ℤ) :
    sourceSobolevSpectralWeight t ht (2*n) = Weight.sobolev t n := by
  change (1 + (1/2 : ℝ) * |((2*n : ℤ) : ℝ)|) ^ t = (1 + |(n : ℝ)|) ^ t
  norm_num [abs_mul]
  congr 1
  ring

@[simp] theorem sourceFrequencyWeight_sobolev (t : ℝ) (ht : 0 ≤ t) :
    sourceFrequencyWeight (sourceSobolevSpectralWeight t ht) = Weight.sobolev t := by
  change Weight.mk _ _ = Weight.mk _ _
  congr 1
  funext n
  exact sourceSobolevSpectralWeight_even t ht n

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One original Section 14 construction works simultaneously on every source spectral weight. -/
theorem sourceSection14_weighted_real_injective (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      ∃ D : SourceSection14Data hp hp1 W₀ W V s,
        ∀ w : SpectralWeight, Function.Injective (D.complex.originalWeightedRealMap w) := by
  obtain ⟨W₀, W, V, s, D⟩ := sourceSection14 hp hp1
  exact ⟨W₀, W, V, s, D, fun w => D.complex.originalWeightedRealMap_injective w⟩

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Exact original Sobolev weights, with no doubling constant, for every nonnegative real order. -/
theorem weightedRealMap_sobolev_norm_rpow (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (t : ℝ) (ht : 0 ≤ t) (a : realTypeSourceSubmodule p) :
    ‖D.weightedRealMap (sourceSobolevSpectralWeight t ht) a‖ ^ p.toReal = ∑' n : ℤ,
      (|Weight.sobolev t n * (sourceRealBirkhoffMap hp hp1 s
        (normalizedWeightedRealSourceLp (sourceSobolevSpectralWeight t ht) a)).1 n| ^ p.toReal +
       |Weight.sobolev t n * (sourceRealBirkhoffMap hp hp1 s
        (normalizedWeightedRealSourceLp (sourceSobolevSpectralWeight t ht) a)).2 n| ^ p.toReal) := by
  simpa only [sourceSobolevSpectralWeight_even] using
    D.weightedRealMap_norm_rpow (sourceSobolevSpectralWeight t ht) a

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
