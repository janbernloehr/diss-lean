import NLS.SequenceSpaces.FourierRealPhaseFlow
import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator

/-! Strong differentiation of arbitrary odd-frequency rotations on the
literal physical real Fourier form. The actual coefficient velocity must
belong to the SAME space; the rate need not be bounded. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem hasDerivAt_weightedPhaseFlow (w : Weight) (hp : p≠⊤)
    (freq : ℤ → ℝ) (a v : WeightedCoeff w p)
    (hv : ∀ k, v.val k=I*(freq k:ℂ)*a.val k) (time : ℝ) :
    HasDerivAt (fun t => phaseFlow w freq t a) (phaseFlow w freq time v) time := by
  have hd := Coeff.hasDerivAt_phaseFlow hp freq (weightIsometry w p a)
    (weightIsometry w p v) (fun k => by
      change (w k:ℂ)*v.val k=I*(freq k:ℂ)*((w k:ℂ)*a.val k)
      rw [hv]
      ring) time
  exact (((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd

theorem fourierRealZeroPhaseFlow_eq_projection (w : Weight) (hw : ∀ k, w (-k)=w k)
    (freq : ℤ → ℝ) (hf : ∀ k, freq (-k)=-freq k) (time : ℝ)
    (a : fourierRealZeroSubmodule w p) :
    fourierRealZeroFullProjection w hw (phaseFlow w freq time a.val.val)=
      fourierRealZeroPhaseFlow w freq hf time a :=
  fourierRealZeroFullProjection_inclusion w hw (fourierRealZeroPhaseFlow w freq hf time a)

theorem hasDerivAt_fourierRealZeroPhaseFlow (w : Weight) (hw : ∀ k, w (-k)=w k)
    (hp : p≠⊤) (freq : ℤ → ℝ) (hf : ∀ k, freq (-k)=-freq k)
    (a v : fourierRealZeroSubmodule w p)
    (hv : ∀ k, v.val.val.val k=I*(freq k:ℂ)*a.val.val.val k) (time : ℝ) :
    HasDerivAt (fun t => fourierRealZeroPhaseFlow w freq hf t a)
      (fourierRealZeroPhaseFlow w freq hf time v) time := by
  have hd := hasDerivAt_weightedPhaseFlow w hp freq a.val.val v.val.val hv time
  have hproj := @NLS.FunctionalAnalysis.hasDerivAt_clm_comp (WeightedCoeff w p) (fourierRealZeroSubmodule w p)
    inferInstance inferInstance inferInstance inferInstance (fourierRealZeroFullProjection (p:=p) w hw) _ _ time hd
  have he : (fun t => fourierRealZeroFullProjection w hw (phaseFlow w freq t a.val.val))=
      (fun t => fourierRealZeroPhaseFlow w freq hf t a) :=
    funext (fun t => fourierRealZeroPhaseFlow_eq_projection w hw freq hf t a)
  rw [he,fourierRealZeroPhaseFlow_eq_projection w hw freq hf time v] at hproj
  exact hproj

end NLS.WeightedCoeff
