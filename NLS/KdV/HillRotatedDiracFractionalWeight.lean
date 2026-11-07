import NLS.KdV.HillRotatedDiracFractionalRegularity
import NLS.ZakharovShabat.SourceSection14WeightedMembership

/-! Normalized weighted coordinates of the identical fractional Dirac
source, with exact decoding and the full physical real form. -/
noncomputable section
open Complex NLS.WeightedCoeff NLS.ZakharovShabat
namespace NLS.KdV

def fractionalDiracWeightCoordinates (t : ℝ) :
    (WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) →L[ℂ] CoeffPair 2 :=
  (CoeffPair.toMax 2).symm.toContinuousLinearMap.comp
    ((weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap.prodMap
      (weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)

theorem fractionalDiracWeightCoordinates_fst (t : ℝ)
    (a : WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) (k : ℤ) :
    (fractionalDiracWeightCoordinates t a).fst k = (Weight.sobolev t k:ℂ)*a.1.val k := rfl

theorem fractionalDiracWeightCoordinates_snd (t : ℝ)
    (a : WeightedCoeff (Weight.sobolev t) 2 × WeightedCoeff (Weight.sobolev t) 2) (k : ℤ) :
    (fractionalDiracWeightCoordinates t a).snd k = (Weight.sobolev t k:ℂ)*a.2.val k := rfl

theorem normalizedWeightedSource_realType_of_decode_realType (w : SpectralWeight) (ψ : CoeffPair 2)
    (h : IsRealType (CoeffPair.toMax 2 (normalizedWeightedSource w ψ))) :
    IsRealType (CoeffPair.toMax 2 ψ) := by
  intro k
  have hh := h k
  change (normalizedWeightedSource w ψ).snd k =
    (starRingEnd ℂ) ((normalizedWeightedSource w ψ).fst (-k)) at hh
  simp only [normalizedWeightedSource_snd,normalizedWeightedSource_fst,mul_neg,
    SpectralWeight.apply_neg,map_div₀,Complex.conj_ofReal] at hh
  exact (div_left_inj' (w.toWeight.complex_ne_zero _)).mp hh

namespace HillProductEquationPatch

def rotatedDiracFractionalWeightCoordinates (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2) : CoeffPair 2 :=
  fractionalDiracWeightCoordinates (1-r) (P.rotatedDiracFractionalLift r hr hr1 q)

theorem analytic_rotatedDiracFractionalWeightCoordinates (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source) :
    AnalyticAt ℂ (P.rotatedDiracFractionalWeightCoordinates r hr hr1) q :=
  ((fractionalDiracWeightCoordinates (1-r)).analyticAt _).comp
    (P.analytic_rotatedDiracFractionalLift r hr hr1 q hq)

theorem rotatedDiracFractionalWeightCoordinates_decode (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source) :
    normalizedWeightedSource (sourceSobolevSpectralWeight (1-r) (by linarith))
        (P.rotatedDiracFractionalWeightCoordinates r hr hr1 q) =
      P.rotatedDiracSource (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext k
    change (normalizedWeightedSource _ _).fst k = _
    rw [normalizedWeightedSource_fst,rotatedDiracFractionalWeightCoordinates,fractionalDiracWeightCoordinates_fst,
      sourceSobolevSpectralWeight_even,mul_div_cancel_left₀ _ ((Weight.sobolev (1-r)).complex_ne_zero k)]
    exact (P.rotatedDiracFractionalLift_coefficients r hr hr1 q hq k).1
  · ext k
    change (normalizedWeightedSource _ _).snd k = _
    rw [normalizedWeightedSource_snd,rotatedDiracFractionalWeightCoordinates,fractionalDiracWeightCoordinates_snd,
      sourceSobolevSpectralWeight_even,mul_div_cancel_left₀ _ ((Weight.sobolev (1-r)).complex_ne_zero k)]
    exact (P.rotatedDiracFractionalLift_coefficients r hr hr1 q hq k).2

theorem rotatedDiracFractionalWeightCoordinates_real (P : HillProductEquationPatch)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (hq : sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q ∈ P.source)
    (hqreal : IsRealPeriodOneHminusOne (sobolevInclusion (show (-1:ℝ) ≤ -r by linarith) q)) :
    IsRealType (CoeffPair.toMax 2 (P.rotatedDiracFractionalWeightCoordinates r hr hr1 q)) := by
  apply normalizedWeightedSource_realType_of_decode_realType
    (sourceSobolevSpectralWeight (1-r) (by linarith))
  rw [P.rotatedDiracFractionalWeightCoordinates_decode r hr hr1 q hq]
  exact P.isRealType_rotatedDiracSource _ hq hqreal

end HillProductEquationPatch
end NLS.KdV
