import NLS.ZakharovShabat.SourceBirkhoffWeightedMembership
import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.ZakharovShabat.SourceBirkhoffProposition17_2

/-! # The weighted real Birkhoff map in normalized coordinates

Membership is proved for every source spectral weight and every finite p>1.
The target carries the component-sum lp norm. The coordinate map is injective,
with an exact weighted norm formula; no stronger-topology inverse is asserted.
-/
noncomputable section
namespace NLS.ZakharovShabat
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Weighted Birkhoff output in real lp coordinates, evaluated at the decoded original input. -/
def weightedRealMap (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : realTypeSourceSubmodule p) : WithLp p (RealCoeff p × RealCoeff p) :=
  WithLp.toLp p
    (⟨fun n => w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).1 n,
      (D.real_map_mem_weighted w (normalizedWeightedRealSourceLp w a) (normalizedWeightedPeriodOne w a.val)
        (weightedBaseToPair_normalizedWeightedPeriodOne w a.val)).1⟩,
     ⟨fun n => w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).2 n,
      (D.real_map_mem_weighted w (normalizedWeightedRealSourceLp w a) (normalizedWeightedPeriodOne w a.val)
        (weightedBaseToPair_normalizedWeightedPeriodOne w a.val)).2⟩)

@[simp] theorem weightedRealMap_fst (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : realTypeSourceSubmodule p) (n : ℤ) :
    (D.weightedRealMap w a).fst n =
      w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).1 n := rfl

@[simp] theorem weightedRealMap_snd (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : realTypeSourceSubmodule p) (n : ℤ) :
    (D.weightedRealMap w a).snd n =
      w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).2 n := rfl

/-- The original unweighted injectivity and positive weights imply weighted injectivity. -/
theorem weightedRealMap_injective (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) : Function.Injective (D.weightedRealMap w) := by
  intro a b hab
  have he : sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a) =
      sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w b) := by
    apply Prod.ext
    · apply lp.ext
      funext n
      have h := congrArg (fun z : WithLp p (RealCoeff p × RealCoeff p) => z.fst n) hab
      exact (mul_left_cancel₀ (w.toWeight.positive (2*n)).ne' h)
    · apply lp.ext
      funext n
      have h := congrArg (fun z : WithLp p (RealCoeff p × RealCoeff p) => z.snd n) hab
      exact (mul_left_cancel₀ (w.toWeight.positive (2*n)).ne' h)
  have hraw := congrArg Subtype.val (D.proposition17_2 he)
  apply Subtype.ext
  exact normalizedWeightedSource_injective w hraw

/-- Exact component-sum norm of the weighted rectangular coordinates. -/
theorem weightedRealMap_norm_rpow (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (a : realTypeSourceSubmodule p) :
    ‖D.weightedRealMap w a‖ ^ p.toReal = ∑' n : ℤ,
      (|w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).1 n| ^ p.toReal +
       |w (2*n) * (sourceRealBirkhoffMap hp hp1 s (normalizedWeightedRealSourceLp w a)).2 n| ^ p.toReal) := by
  have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  rw [norm_withLp_prod_rpow hp, lp.norm_rpow_eq_tsum hp0, lp.norm_rpow_eq_tsum hp0,
    ← Summable.tsum_add
      ((D.weightedRealMap w a).fst.property.summable hp0)
      ((D.weightedRealMap w a).snd.property.summable hp0)]
  rfl

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
