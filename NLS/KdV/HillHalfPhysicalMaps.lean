import NLS.KdV.HillHalfNativeMaps
import NLS.KdV.SingularHillRieszContinuous

/-! The native half-denominator maps and their SAME actual physical L2 and
continuous outputs. Source probability Haar normalization is retained. -/
noncomputable section
open Set Metric MeasureTheory
namespace NLS.KdV
open NLS.Fourier

/-- The full native H1 lift has exactly the already constructed physical L2 image. -/
theorem hillHalfToH1_physicalL2 (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (a : Coeff 2) :
    singularHillL2DomainInclusion (hillHalfToH1 z a) = hillHalfDenominatorL2 z (l2Synthesis a) := by
  apply fourierBasis.repr.injective
  ext k
  rw [fourierBasis_repr,fourierBasis_repr,singularHillL2DomainInclusion_coefficient,
    hillHalfToH1_coefficient n hn z hz,hillHalfDenominatorL2_coefficient,
    hillHalfDenominatorBoundedSymbol_apply n hn z hz,LinearIsometryEquiv.symm_apply_apply]

/-- The full native H1 lift and the continuous-output half-denominator are
exactly the SAME physical continuous function, on ALL l2 inputs. -/
theorem hillHalfToH1_physicalContinuous (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (a : Coeff 2) :
    singularHillContinuousDomainInclusion (hillHalfToH1 z a) =
      hillHalfDenominatorToContinuous z (l2Synthesis a) := by
  apply ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ)
  change circleContinuousToLp 2 (singularHillContinuousDomainInclusion (hillHalfToH1 z a)) =
    circleContinuousToLp 2 (hillHalfDenominatorToContinuous z (l2Synthesis a))
  rw [singularHillContinuousDomainInclusion_toLp,hillHalfDenominatorToContinuous_toLp n hn z hz,
    hillHalfToH1_physicalL2 n hn z hz]

/-- The actual half-map on the ENTIRE native base agrees with the physical
L2 half-denominator on EVERY original periodic Hilbert input. -/
theorem hillHalfFromBase_physicalL2 (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ)) (F : CircleL2) :
    hillHalfFromBase z (singularHillL2BaseInclusion F) = l2Synthesis.symm (hillHalfDenominatorL2 z F) := by
  ext k
  rw [hillHalfFromBase_coefficient n hn z hz,singularHillL2BaseInclusion_coefficient]
  change _ = fourierBasis.repr (hillHalfDenominatorL2 z F) k
  rw [fourierBasis_repr,hillHalfDenominatorL2_coefficient,hillHalfDenominatorBoundedSymbol_apply n hn z hz]

end NLS.KdV
