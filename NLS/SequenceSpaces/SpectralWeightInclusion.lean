import NLS.SequenceSpaces.SpectralWeight
import NLS.SequenceSpaces.WeightedPairMap

/-! # Norm-decreasing inclusions between spectral weights -/
noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forget part of a spectral weight while retaining the exact pair norm and coefficients. -/
def inclusionPair (w v : SpectralWeight) (h : ∀ k, v k ≤ w k) :
    WeightedCoeffPair w.toWeight p →L[ℂ] WeightedCoeffPair v.toWeight p :=
  WeightedCoeffPair.mapComponents w.toWeight v.toWeight
    (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h)
    (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h)

@[simp] theorem inclusionPair_fst (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (a : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (w.inclusionPair v h a).fst.val k = a.fst.val k := by simp [inclusionPair]

@[simp] theorem inclusionPair_snd (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (a : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (w.inclusionPair v h a).snd.val k = a.snd.val k := by simp [inclusionPair]

/-- Lowering the weight contracts the source finite-exponent pair norm. -/
theorem norm_inclusionPair_le (hp : p ≠ ⊤) (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (a : WeightedCoeffPair w.toWeight p) : ‖w.inclusionPair v h a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp w.toWeight v.toWeight
    (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h)
    (WeightedCoeff.inclusionCLM w.toWeight v.toWeight h) zero_le_one
    (fun a => by simpa using WeightedCoeff.norm_inclusionCLM_le w.toWeight v.toWeight h a)
    (fun a => by simpa using WeightedCoeff.norm_inclusionCLM_le w.toWeight v.toWeight h a) a

end NLS.SpectralWeight
