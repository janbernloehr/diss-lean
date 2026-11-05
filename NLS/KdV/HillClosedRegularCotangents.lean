import NLS.KdV.HillClosedGapEndpointCotangent
import NLS.KdV.HillGlobalRegularCorrection
import NLS.KdV.HillPhysicalGermDerivativeUniqueness

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

/-- At a collapsed source gap the actual globally defined regular correction
has a constructed analytic physical germ with a genuine log-norming cotangent. -/
theorem exists_hillRegularAbelianCorrection_closed_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k=0) :
    ∃ C : Coeff 2 → ℂ, ∃ c : ℂ,
      AnalyticAt ℂ C (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        C (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) ∧
      ∀ h : Coeff 2,
        (fderiv ℂ C (SpectralWeight.one.toCoeff q.val)) h=
          c*hillPhysicalDirectionPairing h (hillLogNormingGradientCurve q k hk) := by
  have hc : hillRealLabels q.val q.property.1 q.property.2 (2*k-1)=hillRealLabels q.val q.property.1 q.property.2 (2*k) := by
    dsimp only [hillRealGapHalfLength] at hgap
    linarith
  obtain ⟨C,hC,_,hphysical,c,hder⟩ := exists_hillRegularAbelian_closed_gap_norming_cotangent
    q.val q.property.1 q.property.2 h0q h0r n k hn hk hc
  refine ⟨C,c,hC,?_,hder⟩
  filter_upwards [hphysical] with p hp
  by_cases hc' : hillRealGapHalfLength p.val p.property.1 p.property.2 k=0
  · rw [hillRegularAbelianCorrection_closed p.val p.property.1 p.property.2 n hn k hk hc']
    exact hp.2.1 hc'
  · have hspec := hillDirichletSelectedRealAngle_spec p.val p.property.1 p.property.2 k hk hc'
    rw [hillRegularAbelianCorrection,dif_neg hc']
    exact hp.2.2 hc' _ hspec.2.1 hspec.2.2

/-- The collapsed-gap regular-correction cotangent is intrinsic to its actual
physical germ on every original even source direction. -/
theorem hillRegularAbelianCorrectionGerm_closed_norming_cotangent
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k=0)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) :
    ∃ c : ℂ, ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  obtain ⟨C,c,hC,hCreal,hCD⟩ := exists_hillRegularAbelianCorrection_closed_norming_cotangent h0q h0r q n k hn hk hgap
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=C (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGreal,hCreal] with p hpG hpC
    exact hpG.trans hpC.symm
  refine ⟨c,?_⟩
  intro h heven
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    G C hG hC heq h heven).trans (hCD (SpectralWeight.one.toCoeff h))

end NLS.KdV
