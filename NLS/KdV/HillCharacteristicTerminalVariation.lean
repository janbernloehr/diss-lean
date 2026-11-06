import NLS.KdV.HillIsospectralGapInvariants
import NLS.ComplexAnalysis.CosineTerminalVariation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual complex cosine terminal equation gives the energy
variation in every isospectral direction, including sine-zero endpoints. -/
theorem hillCharacteristicCosineTerminal_isospectral_fderiv
    (k : ℕ) (hk : 1≤k) (d μ ε : Coeff 2 → ℂ)
    (hd : AnalyticAt ℂ d (SpectralWeight.one.toCoeff q))
    (hμ : AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q))
    (hε : AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q))
    (hdne : d (SpectralWeight.one.toCoeff q)≠0)
    (hdsq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), d p^2=hillLocalGapSquare q hq hr k p/4)
    (heq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      cosineGapPoint (hillLocalGapMidpoint q hq hr k p) (d p) (ε p)=μ p)
    (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ μ (SpectralWeight.one.toCoeff q)) h=
      -(d (SpectralWeight.one.toCoeff q)*Complex.sin (ε (SpectralWeight.one.toCoeff q)))*
        ((fderiv ℂ ε (SpectralWeight.one.toCoeff q)) h) := by
  obtain ⟨U,_,hpU,hM,_,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr k hk
  apply cosineTerminal_fderiv_of_stationary_gap (hillLocalGapMidpoint q hq hr k) d μ ε _ h
    (hM _ hpU) hd hμ hε heq
    (hillLocalGapSymmetricData_isospectral_fderiv q hq hr k hk h hiso).1
    (hillGapHalfLength_isospectral_fderiv q hq hr k hk d hd hdne hdsq h hiso)

end NLS.KdV
