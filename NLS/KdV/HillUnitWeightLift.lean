import NLS.KdV.HillReduction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- Exact unweighted coefficient identification with the unit spectral weight. -/
def hillUnitWeightLift (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Coeff p ≃ₗᵢ[ℂ] WeightedCoeff SpectralWeight.one.toWeight p :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight p).symm

@[simp] theorem hillUnitWeightLift_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Coeff p) (k : ℤ) :
    (hillUnitWeightLift p a).val k = a k := by
  change a k/(SpectralWeight.one.toWeight k : ℂ) = a k
  simp only [SpectralWeight.one_apply,Complex.ofReal_one,div_one]

@[simp] theorem norm_hillUnitWeightLift (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Coeff p) :
    ‖hillUnitWeightLift p a‖ = ‖a‖ := (hillUnitWeightLift p).norm_map a

@[simp] theorem toCoeff_hillUnitWeightLift (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Coeff p) :
    SpectralWeight.one.toCoeff (hillUnitWeightLift p a) = a := by
  ext k
  simp only [SpectralWeight.toCoeff_apply,hillUnitWeightLift_apply]

@[simp] theorem hillUnitWeightLift_toCoeff (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff SpectralWeight.one.toWeight p) :
    hillUnitWeightLift p (SpectralWeight.one.toCoeff a) = a := by
  apply Subtype.ext
  funext k
  simp only [hillUnitWeightLift_apply,SpectralWeight.toCoeff_apply]

/-- The identification preserves the original convolution, without a weight factor. -/
theorem hillUnitWeightLift_convolution (q : Coeff 2) (a : Coeff 1) :
    hillUnitWeightLift 2 (Coeff.convolution q a) = SpectralWeight.one.convolution
      (hillUnitWeightLift 2 q) (hillUnitWeightLift 1 a) := by
  apply Subtype.ext
  funext k
  rw [hillUnitWeightLift_apply,← SpectralWeight.toCoeff_apply,
    SpectralWeight.toCoeff_convolution,toCoeff_hillUnitWeightLift,toCoeff_hillUnitWeightLift]

end NLS.KdV
