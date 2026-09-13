import NLS.ZakharovShabat.ComplementaryResolventIdentity
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Analytic extension of the complementary inverse

Normalization at the strip center gives an entire bounded pencil. Its inverse
recovers the actual complementary inverse throughout the full closed strip,
including the resonant lattice point, and is analytic on an open neighborhood.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Entire normalization at the central parameter, acting as the identity on the resonant modes. -/
def complementaryNormalizedPencil (w : Weight) (n : ℤ) (z : ℂ) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w p :=
  1 + (z - (Real.pi : ℂ)*n) • complementaryFreeInverse w n _ (center_mem_resonantStrip n)

/-- Explicit inverse of the normalization on the closed strip. -/
theorem complementaryNormalizedPencil_mul (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    complementaryNormalizedPencil (p := p) w n z *
      (1 - (z-(Real.pi : ℂ)*n) • complementaryFreeInverse w n z hz) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply weightedPair_ext <;> intro k
  · change (f.fst.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z (-k)*f.fst.val k)) +
      (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) (-k) *
        (f.fst.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z (-k)*f.fst.val k))) = f.fst.val k
    linear_combination -(z-(Real.pi : ℂ)*n) * f.fst.val k *
      complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) (-k)
  · change (f.snd.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z k*f.snd.val k)) +
      (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) k *
        (f.snd.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z k*f.snd.val k))) = f.snd.val k
    linear_combination -(z-(Real.pi : ℂ)*n) * f.snd.val k *
      complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) k

/-- The explicit inverse also works on the left. -/
theorem mul_complementaryNormalizedPencil (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    (1 - (z-(Real.pi : ℂ)*n) • complementaryFreeInverse (p := p) w n z hz) *
      complementaryNormalizedPencil (p := p) w n z = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply weightedPair_ext <;> intro k
  · change (f.fst.val k + (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) (-k)*f.fst.val k)) -
      (z-(Real.pi : ℂ)*n) * (complementarySymbol n z (-k) *
        (f.fst.val k + (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) (-k)*f.fst.val k))) = f.fst.val k
    linear_combination -(z-(Real.pi : ℂ)*n) * f.fst.val k *
      complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) (-k)
  · change (f.snd.val k + (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) k*f.snd.val k)) -
      (z-(Real.pi : ℂ)*n) * (complementarySymbol n z k *
        (f.snd.val k + (z-(Real.pi : ℂ)*n) * (complementarySymbol n ((Real.pi : ℂ)*n) k*f.snd.val k))) = f.snd.val k
    linear_combination -(z-(Real.pi : ℂ)*n) * f.snd.val k *
      complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) k

/-- Every parameter in the full closed strip has invertible normalization. -/
theorem isUnit_complementaryNormalizedPencil (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    IsUnit (complementaryNormalizedPencil (p := p) w n z) :=
  ⟨⟨_, 1 - (z-(Real.pi : ℂ)*n) • complementaryFreeInverse w n z hz,
    complementaryNormalizedPencil_mul w n z hz, mul_complementaryNormalizedPencil (p := p) w n z hz⟩, rfl⟩

/-- Banach-algebra inversion agrees with the explicit complementary normalization inverse. -/
theorem inverse_complementaryNormalizedPencil (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    Ring.inverse (complementaryNormalizedPencil (p := p) w n z) =
      1 - (z-(Real.pi : ℂ)*n) • complementaryFreeInverse w n z hz := by
  calc
    _ = Ring.inverse (complementaryNormalizedPencil (p := p) w n z) *
        (complementaryNormalizedPencil (p := p) w n z * (1 - (z-(Real.pi : ℂ)*n) • complementaryFreeInverse w n z hz)) := by
      rw [complementaryNormalizedPencil_mul (p := p) w n z hz, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_complementaryNormalizedPencil (p := p) w n z hz), one_mul]

/-- A total domain-valued extension with no strip-membership argument. -/
def complementaryDomainExtension (w : Weight) (n : ℤ) (z : ℂ) :
    WeightedCoeffPair w p →L[ℂ] WeightedDomain w p :=
  (complementaryFreeDomainInverse w n _ (center_mem_resonantStrip n)).comp
    (Ring.inverse (complementaryNormalizedPencil (p := p) w n z))

/-- The extension is the actual domain inverse on every point of the closed strip. -/
theorem complementaryDomainExtension_eq (w : Weight) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    complementaryDomainExtension (p := p) w n z = complementaryFreeDomainInverse w n z hz := by
  rw [complementaryDomainExtension, inverse_complementaryNormalizedPencil (p := p) w n z hz]
  apply ContinuousLinearMap.ext
  intro f
  apply weightedPair_ext <;> intro k
  · change complementarySymbol n ((Real.pi : ℂ)*n) (-k) *
      (f.fst.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z (-k)*f.fst.val k)) =
        complementarySymbol n z (-k)*f.fst.val k
    linear_combination -f.fst.val k * complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) (-k)
  · change complementarySymbol n ((Real.pi : ℂ)*n) k *
      (f.snd.val k - (z-(Real.pi : ℂ)*n) * (complementarySymbol n z k*f.snd.val k)) =
        complementarySymbol n z k*f.snd.val k
    linear_combination -f.snd.val k * complementarySymbol_sub n z _ hz (center_mem_resonantStrip n) k

/-- The normalized pencil is entire in operator norm. -/
theorem analyticAt_complementaryNormalizedPencil (w : Weight) (n : ℤ) (z : ℂ) :
    AnalyticAt ℂ (complementaryNormalizedPencil (p := p) w n) z :=
  analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul analyticAt_const)

/-- Domain-valued analyticity at every invertible normalization. -/
theorem analyticAt_complementaryDomainExtension (w : Weight) (n : ℤ) (z : ℂ)
    (hz : IsUnit (complementaryNormalizedPencil (p := p) w n z)) :
    AnalyticAt ℂ (complementaryDomainExtension (p := p) w n) z := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _ hz).comp
    (analyticAt_complementaryNormalizedPencil (p := p) w n z)
  exact ((ContinuousLinearMap.compL ℂ (WeightedCoeffPair w p) (WeightedCoeffPair w p) (WeightedDomain w p))
    (complementaryFreeDomainInverse w n _ (center_mem_resonantStrip n))).analyticAt _ |>.comp hi

/-- Analyticity on a neighborhood of the entire closed strip, including its center and edges. -/
theorem analyticOnNhd_complementaryDomainExtension (w : Weight) (n : ℤ) :
    AnalyticOnNhd ℂ (complementaryDomainExtension (p := p) w n) (resonantStrip n) :=
  fun z hz => analyticAt_complementaryDomainExtension w n z (isUnit_complementaryNormalizedPencil (p := p) w n z hz)

end NLS.ZakharovShabat
