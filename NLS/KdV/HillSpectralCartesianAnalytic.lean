import NLS.KdV.HillSummedRegularCorrectionAnalytic
import NLS.KdV.HillOwnAmplitudeAnalytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillSpectralCartesian_analytic_extension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff r.val)=hillSpectralCartesian r.val r.property.1 r.property.2 n hn := by
  obtain ⟨A,hA,hmatchA⟩ := exists_hillOwnCartesianAmplitude_analytic_extension q hq hr n hn
  obtain ⟨S,hS,hmatchS⟩ := exists_hillSummedRegularAbelianCorrection_analytic_extension h0q h0r q hq hr n hn
  let Z : Coeff 2 → ℂ := fun p => A p*Complex.exp (I*S p)
  have hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) :=
    hA.mul (analyticAt_const.mul hS).cexp'
  refine ⟨Z,hZ,?_⟩
  filter_upwards [hmatchA,hmatchS] with r hrA hrS
  dsimp only [Z]
  rw [hrA,hrS,hillSpectralCartesian_eq_ownAmplitude_mul_correction]

end NLS.KdV
