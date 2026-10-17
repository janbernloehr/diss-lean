import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDomain
import NLS.ZakharovShabat.SourceBirkhoffFourier

/-! # The actual weighted Jacobian in normalized coordinates

Isometric weight coordinates and the rectangular target equivalence
express the native weighted derivative on ordinary coefficient spaces.
Decoding gives exactly the original Jacobian; the same identity holds
for the free Fourier transform, including its reflected source component.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Express the actual native weighted derivative in normalized source and rectangular target coordinates. -/
def normalizedWeightedBirkhoffJacobian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) :
    CoeffPair p →L[ℂ] (Coeff p × Coeff p) :=
  (CoeffPair.toMax p).toContinuousLinearMap.comp
    ((sourcePairWeightCoordinates w).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a).comp
        (sourcePairWeightCoordinates w).symm.toContinuousLinearEquiv.toContinuousLinearMap))

@[simp] theorem normalizedWeightedBirkhoffJacobian_fst
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (w : SpectralWeight) (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (v : CoeffPair p) (n : ℤ) :
    (normalizedWeightedBirkhoffJacobian hp hp1 s w a v).1 n =
      (w (2*n) : ℂ)*(fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a
        ((sourcePairWeightCoordinates w).symm v)).fst.val n := rfl

@[simp] theorem normalizedWeightedBirkhoffJacobian_snd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (w : SpectralWeight) (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (v : CoeffPair p) (n : ℤ) :
    (normalizedWeightedBirkhoffJacobian hp hp1 s w a v).2 n =
      (w (2*n) : ℂ)*(fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a
        ((sourcePairWeightCoordinates w).symm v)).snd.val n := rfl

@[simp] theorem originalWeightedSourceCLM_coordinates_symm (w : SpectralWeight) (v : CoeffPair p) :
    originalWeightedSourceCLM w ((sourcePairWeightCoordinates w).symm v) = normalizedWeightedSource w v := by
  change normalizedWeightedSource w (sourcePairWeightCoordinates w ((sourcePairWeightCoordinates w).symm v)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Decoding the normalized weighted derivative recovers the actual unweighted derivative. -/
theorem normalizedWeightedBirkhoffJacobian_decode
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (ha : a ∈ D.originalWeightedComplexDomain w)
    (v : CoeffPair p) (n : ℤ) :
    (normalizedWeightedBirkhoffJacobian hp hp1 s w a v).1 n/(w (2*n) : ℂ) =
      (sourceBirkhoffJacobian hp hp1 s (originalWeightedSourceCLM w a) (normalizedWeightedSource w v)).1 n ∧
    (normalizedWeightedBirkhoffJacobian hp hp1 s w a v).2 n/(w (2*n) : ℂ) =
      (sourceBirkhoffJacobian hp hp1 s (originalWeightedSourceCLM w a) (normalizedWeightedSource w v)).2 n := by
  have hd := ((D.originalWeightedComplexDomain_spec w).2.2.2 a ha).2.2
  have hv := congrArg (fun L => L ((sourcePairWeightCoordinates w).symm v)) hd
  simp only [ContinuousLinearMap.comp_apply,originalWeightedSourceCLM_coordinates_symm] at hv
  constructor
  · rw [normalizedWeightedBirkhoffJacobian_fst,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
    simpa only [weightedBirkhoffTargetInclusion_fst,sourceBirkhoffJacobian] using congrArg (fun x => x.1 n) hv
  · rw [normalizedWeightedBirkhoffJacobian_snd,mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)]
    simpa only [weightedBirkhoffTargetInclusion_snd,sourceBirkhoffJacobian] using congrArg (fun x => x.2 n) hv
end SourceBirkhoffMapComplexData

/-- The free Fourier map commutes with decoding an even spectral weight. -/
theorem sourceBirkhoffFourier_decode (w : SpectralWeight) (v : CoeffPair p) (n : ℤ) :
    (sourceBirkhoffFourier v).1 n/(w (2*n) : ℂ) =
      (sourceBirkhoffFourier (normalizedWeightedSource w v)).1 n ∧
    (sourceBirkhoffFourier v).2 n/(w (2*n) : ℂ) =
      (sourceBirkhoffFourier (normalizedWeightedSource w v)).2 n := by
  constructor <;>
    simp only [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,
      normalizedWeightedSource_fst,normalizedWeightedSource_snd,mul_neg,SpectralWeight.apply_neg] <;> ring

end NLS.ZakharovShabat
