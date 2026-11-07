import NLS.SequenceSpaces.FourierRealZeroMultiplier
import NLS.SequenceSpaces.SignedSobolevWeight

/-! Literal coefficient-preserving inclusion between any two ordered
signed Sobolev spaces on the actual physical real zero-mean form. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def signedRealOrderInclusion (s t : ℝ) (hst : s≤t) :
    fourierRealZeroSubmodule (Weight.signedSobolev t) p →L[ℝ]
      fourierRealZeroSubmodule (Weight.signedSobolev s) p :=
  fourierRealZeroMultiplier _ _ (Weight.signedSobolev_neg s) (fun _ => 1) 1 zero_le_one
    (by intro k; simp only [norm_one,mul_one,one_mul];
        exact Real.rpow_le_rpow_of_exponent_le (le_max_left (1:ℝ) |(k:ℝ)|) hst)
    (by intro k; simp)

theorem signedRealOrderInclusion_apply (s t : ℝ) (hst : s≤t)
    (a : fourierRealZeroSubmodule (Weight.signedSobolev t) p) (k : ℤ) :
    (signedRealOrderInclusion s t hst a).val.val.val k=a.val.val.val k := by
  rw [signedRealOrderInclusion,fourierRealZeroMultiplier_apply,one_mul]

theorem signedRealOrderInclusion_injective (s t : ℝ) (hst : s≤t) :
    Function.Injective (signedRealOrderInclusion (p:=p) s t hst) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have he := congrArg (fun z => z.val.val.val k) h
  simpa only [signedRealOrderInclusion_apply] using he

end NLS.WeightedCoeff
