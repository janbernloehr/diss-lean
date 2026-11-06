import NLS.KdV.HillReconstructionBounds
import NLS.KdV.HillAnalytic
import NLS.Fourier.ContinuousSynthesis

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



/-- Joint analyticity of the actual effective potential, also at periodic eigenvalues. -/
theorem analyticAt_hillEffectiveFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillEffectiveFamily w n) p := by
  have hq := (w.convolutionCLM.analyticAt p.1).comp
    ((ContinuousLinearMap.fst ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p)
  have hv : AnalyticAt ℂ (fun y : WeightedCoeff w.toWeight 2 × ℂ => hillModePotential w y.1 n) p :=
    SchurComplement.analyticAt_compCLM hq analyticAt_const
  exact SchurComplement.analyticAt_compCLM (analyticAt_hillInverseFamily w n hn p hz hcut) hv

/-- Proof-independent reconstruction of both corrected Fourier modes. -/
def hillReconstructionFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : (ℂ × ℂ) →L[ℂ] WeightedCoeff w.toWeight 1 :=
  hillModes w.toWeight n + (hillComplementFamily w.toWeight n p.2).comp
    (hillEffectiveFamily w n p)

theorem hillReconstructionFamily_eq (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) :
    hillReconstructionFamily w n p = hillReconstruct w p.1 n hn p.2 hz hcut := by
  unfold hillReconstructionFamily hillReconstruct hillEffectiveFamily hillEffectivePotential
  rw [hillComplementFamily_eq w.toWeight n hn p.2 hz, hillInverseFamily_eq w n hn p hz hcut]

theorem analyticAt_hillReconstructionFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillReconstructionFamily w n) p := by
  have hc := (analyticOnNhd_hillComplementFamily w.toWeight n hn p.2 hz).comp
    ((ContinuousLinearMap.snd ℂ (WeightedCoeff w.toWeight 2) ℂ).analyticAt p)
  exact analyticAt_const.add (SchurComplement.analyticAt_compCLM hc
    (analyticAt_hillEffectiveFamily w n hn p hz hcut))

/-- The actual continuous Fourier synthesis of the reconstructed modes. -/
def hillReconstructedCurveFamily (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : (ℂ × ℂ) →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  Fourier.continuousSynthesisCLM.comp (w.toCoeff.comp (hillReconstructionFamily w n p))

theorem analyticAt_hillReconstructedCurveFamily (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillReconstructedCurveFamily w n) p :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (SchurComplement.analyticAt_compCLM analyticAt_const
      (analyticAt_hillReconstructionFamily w n hn p hz hcut))

/-- Uniform physical-space error for arbitrary resonant amplitudes. -/
theorem norm_hillReconstructedCurve_error_le (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    ‖hillReconstructedCurveFamily w n p u -
      Fourier.continuousSynthesis (w.toCoeff (hillModes w.toWeight n u))‖ ≤
        (8*‖p.1‖/(n : ℝ))*(‖u.1‖+‖u.2‖) := by
  change ‖Fourier.continuousSynthesisCLM (w.toCoeff (hillReconstructionFamily w n p u)) -
    Fourier.continuousSynthesisCLM (w.toCoeff (hillModes w.toWeight n u))‖ ≤ _
  rw [← map_sub, ← map_sub, hillReconstructionFamily_eq w n hn p hz hcut]
  exact (Fourier.norm_continuousSynthesis_le _).trans
    (norm_hillReconstruct_error_le w p.1 n hn p.2 hz hcut u)

/-- Boundary evaluation of the two reconstructed modes, using the actual Fourier sum. -/
def hillReconstructionBoundaryRow (w : SpectralWeight) (n : ℕ)
    (p : WeightedCoeff w.toWeight 2 × ℂ) : (ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (0 : AddCircle (2 : ℝ))).comp (hillReconstructedCurveFamily w n p)

theorem analyticAt_hillReconstructionBoundaryRow (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ openHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) : AnalyticAt ℂ (hillReconstructionBoundaryRow w n) p :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (analyticAt_hillReconstructedCurveFamily w n hn p hz hcut)

/-- The free boundary row is exactly the sum of the two raw amplitudes. -/
theorem hillModes_boundary_value (w : SpectralWeight) (n : ℕ) (u : ℂ × ℂ) :
    Fourier.continuousSynthesis (w.toCoeff (hillModes w.toWeight n u)) 0 = u.1+u.2 := by
  have he : w.toCoeff (hillModes w.toWeight n u) =
      lp.single 1 (n : ℤ) u.1 + lp.single 1 (-(n : ℤ)) u.2 := by
    ext k
    simp [hillModes_apply, lp.single_apply, Pi.single_apply]
  rw [he]
  change Fourier.continuousSynthesisCLM (_+_) 0 = _
  rw [map_add]
  simp [Fourier.continuousSynthesisCLM_apply]

/-- Boundary traces inherit the same uniform summable error budget. -/
theorem norm_hillReconstructionBoundaryRow_error_le (w : SpectralWeight) (n : ℕ) (hn : 1 ≤ n)
    (p : WeightedCoeff w.toWeight 2 × ℂ) (hz : p.2 ∈ reducedHillStrip n)
    (hcut : 8*‖p.1‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    ‖hillReconstructionBoundaryRow w n p u - (u.1+u.2)‖ ≤
      (8*‖p.1‖/(n : ℝ))*(‖u.1‖+‖u.2‖) := by
  rw [← hillModes_boundary_value w n u]
  exact (ContinuousMap.norm_coe_le_norm
    (hillReconstructedCurveFamily w n p u -
      Fourier.continuousSynthesis (w.toCoeff (hillModes w.toWeight n u))) 0).trans
        (norm_hillReconstructedCurve_error_le w n hn p hz hcut u)

end NLS.KdV
