import NLS.ZakharovShabat.WeightedPotentialAnalytic
import NLS.ZakharovShabat.WeightedCorrection

/-!
# Joint analytic extensions of the even and full corrections

Banach-algebra inversion gives total extensions agreeing with the actual
shifted Neumann constructions. Their joint analytic domain contains every
closed-strip parameter satisfying the established small-square hypothesis.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual small-square hypothesis makes the even denominator invertible. -/
theorem isUnit_weightedEvenDenominator (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    IsUnit (1 - weightedPotentialInverse hp w φ n z hz ^ 2) :=
  ⟨⟨_, weightedEvenCorrection hp w φ n z hz h,
    weightedEvenCorrection_right hp w φ n z hz h, weightedEvenCorrection_left hp w φ n z hz h⟩, rfl⟩

/-- A total extension of the even inverse, with no proof-dependent arguments. -/
def weightedEvenExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  Ring.inverse (1 - weightedPotentialExtension hp w φ n z ^ 2)

/-- A total extension of the full correction by its squared factorization. -/
def weightedCorrectionExtension (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair w.toWeight p :=
  (1 + weightedPotentialExtension hp w φ n z) * weightedEvenExtension hp w φ n z

/-- The analytic even extension agrees with the actual Neumann inverse. -/
theorem weightedEvenExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedEvenExtension hp w φ n z = weightedEvenCorrection hp w φ n z hz h := by
  rw [weightedEvenExtension, weightedPotentialExtension_eq hp w φ n z hz]
  calc
    _ = Ring.inverse (1 - weightedPotentialInverse hp w φ n z hz ^ 2) *
        ((1 - weightedPotentialInverse hp w φ n z hz ^ 2) * weightedEvenCorrection hp w φ n z hz h) := by
      rw [weightedEvenCorrection_right, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ (isUnit_weightedEvenDenominator hp w φ n z hz h), one_mul]

/-- The analytic full extension agrees with the actual correction. -/
theorem weightedCorrectionExtension_eq (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    weightedCorrectionExtension hp w φ n z = weightedCorrection hp w φ n z hz h := by
  rw [weightedCorrectionExtension, weightedPotentialExtension_eq hp w φ n z hz,
    weightedEvenExtension_eq hp w φ n z hz h, weightedCorrection_formula]

/-- Joint analytic domain of the complementary corrections. -/
def weightedCorrectionDomain (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) :
    Set (WeightedCoeffPair w.toWeight p × ℂ) :=
  {s | IsUnit (complementaryNormalizedPencil (p := p) w.toWeight n s.2) ∧
    IsUnit (1 - weightedPotentialExtension hp w s.1 n s.2 ^ 2)}

/-- The existing shifted small-square condition lies in the joint analytic domain. -/
theorem mem_weightedCorrectionDomain (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    (φ,z) ∈ weightedCorrectionDomain hp w n := by
  refine ⟨isUnit_complementaryNormalizedPencil w.toWeight n z hz, ?_⟩
  rw [weightedPotentialExtension_eq hp w φ n z hz]
  exact isUnit_weightedEvenDenominator hp w φ n z hz h

/-- The even inverse is jointly analytic in operator norm. -/
theorem analyticAt_weightedEvenExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedEvenExtension hp w t.1 n t.2) s := by
  have hB : AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ =>
      1 - weightedPotentialExtension hp w t.1 n t.2 ^ 2) s :=
    analyticAt_const.sub ((analyticAt_weightedPotentialExtension hp w n s hs.1).pow 2)
  exact (analyticOnNhd_inverse (𝕜 := ℂ) _ hs.2).comp
    (f := fun t : WeightedCoeffPair w.toWeight p × ℂ => 1 - weightedPotentialExtension hp w t.1 n t.2 ^ 2) hB

/-- The full correction is jointly analytic in operator norm. -/
theorem analyticAt_weightedCorrectionExtension (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (s : WeightedCoeffPair w.toWeight p × ℂ) (hs : s ∈ weightedCorrectionDomain hp w n) :
    AnalyticAt ℂ (fun t : WeightedCoeffPair w.toWeight p × ℂ => weightedCorrectionExtension hp w t.1 n t.2) s :=
  (analyticAt_const.add (analyticAt_weightedPotentialExtension hp w n s hs.1)).mul
    (analyticAt_weightedEvenExtension hp w n s hs)

/-- The joint analytic domain is open, including around the closed strip boundaries. -/
theorem isOpen_weightedCorrectionDomain (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) :
    IsOpen (weightedCorrectionDomain hp w n) := by
  apply isOpen_iff_mem_nhds.mpr
  intro s hs
  have hA := ((analyticAt_complementaryNormalizedPencil (p := p) w.toWeight n s.2).comp
    (f := fun t : WeightedCoeffPair w.toWeight p × ℂ => t.2) analyticAt_snd).continuousAt
  have hB : ContinuousAt (fun t : WeightedCoeffPair w.toWeight p × ℂ =>
      1 - weightedPotentialExtension hp w t.1 n t.2 ^ 2) s :=
    (analyticAt_const.sub ((analyticAt_weightedPotentialExtension hp w n s hs.1).pow 2)).continuousAt
  exact Filter.inter_mem (hA.preimage_mem_nhds (Units.isOpen.mem_nhds hs.1))
    (hB.preimage_mem_nhds (Units.isOpen.mem_nhds hs.2))

end NLS.ZakharovShabat
