import NLS.KdV.HillOpenRegularEndpointCotangents
import NLS.KdV.HillClosedRegularCotangents

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Every periodic physical Dirichlet terminal, open or collapsed, has an actual
regular-correction germ with its physical cotangent in the genuine norming span. -/
theorem exists_hillRegularAbelianCorrection_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ C : Coeff 2 → ℂ, ∃ c : ℂ,
      AnalyticAt ℂ C (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) ∧
      ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
        SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
        (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
          c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  by_cases hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k=0
  · obtain ⟨C,c,hC,hCreal,hCD⟩ := exists_hillRegularAbelianCorrection_closed_norming_cotangent h0q h0r q n k hn hk hgap
    exact ⟨C,c,hC,hCreal,fun h _ => hCD (SpectralWeight.one.toCoeff h)⟩
  · exact exists_hillRegularAbelianCorrection_open_endpoint_norming_cotangent h0q h0r q n k hn hk hgap hlog

/-- At every periodic terminal the cotangent of any actual physically matched
analytic regular-correction germ is intrinsic on the original source tangent space. -/
theorem hillRegularAbelianCorrectionGerm_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) :
    ∃ c : ℂ, ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  obtain ⟨C,c,hC,hCreal,hCD⟩ := exists_hillRegularAbelianCorrection_endpoint_norming_cotangent h0q h0r q n k hn hk hlog
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=C (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGreal,hCreal] with p hpG hpC
    exact hpG.trans hpC.symm
  refine ⟨c,?_⟩
  intro h heven
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    G C hG hC heq h heven).trans (hCD h heven)

end NLS.KdV
