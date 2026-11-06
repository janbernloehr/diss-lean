import NLS.ZakharovShabat.SourceDiagonalLaurentGeometry
import NLS.ZakharovShabat.SourcePrimitivePowerPositive

/-! # Strictly positive indexed gaps on the real diagonal

Zero lies in the central gap. Global indexed spectral ordering therefore
places every positive gap strictly to its right, including collapsed
gaps. The inverse-frequency cosine profile is continuous without an
open-gap condition.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDiagonal_positive_leftEndpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hdiag : φ.val.fst = φ.val.snd)
    (n : ℤ) (hn : 0 < n) :
    0 < (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
  have hz := sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val 0 0
    (zero_mem_central_segment_of_diagonal hp hp1 φ hdiag)
  have hsep := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
    (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) hn
  change (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) 0).re ≤ 0 ∧
    0 ≤ (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) 0).re at hz
  exact hz.2.trans_lt hsep

theorem sourceDiagonal_positive_gapAffinePoint_cos (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hdiag : φ.val.fst = φ.val.snd)
    (n : ℤ) (hn : 0 < n) (θ : ℝ) :
    0 < realGapAffinePoint hp hp1 φ.val n (Real.cos θ) :=
  (sourceDiagonal_positive_leftEndpoint hp hp1 φ hdiag n hn).trans_le
    (realGapAffinePoint_cos_mem_Icc hp hp1 φ n θ).1

theorem continuous_sourceInverseFrequencyGapProfile (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hdiag : φ.val.fst = φ.val.snd) (n : ℤ) (hn : 0 < n) :
    Continuous (fun θ : ℝ => (realGapAffinePoint hp hp1 φ.val n (Real.cos θ))⁻¹ *
      (Real.sin θ*sourceRealGapCosineProfile hp hp1 φ.val n θ)) := by
  have hx : Continuous (fun θ : ℝ => realGapAffinePoint hp hp1 φ.val n (Real.cos θ)) := by
    unfold realGapAffinePoint
    fun_prop
  exact (hx.inv₀ (fun θ => ne_of_gt (sourceDiagonal_positive_gapAffinePoint_cos hp hp1 φ hdiag n hn θ))).mul
    (Real.continuous_sin.mul (sourceRealGapCosineProfile_continuous hp hp1 φ n))

end NLS.ZakharovShabat
