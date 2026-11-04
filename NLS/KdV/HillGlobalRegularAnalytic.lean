import NLS.KdV.HillGlobalRegularCorrection
import NLS.KdV.HillDirichletAbelianIntegralAnalytic
import NLS.KdV.HillClosedGapAbelianCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillRegularAbelianCorrection_analytic_open_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k ≠ 0) :
    ∃ C : Coeff 2 → ℂ, AnalyticAt ℂ C (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        C (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  obtain ⟨B,ε,e,hB,hε,_,_,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_analytic_open_gap_extension q hq hr h0q h0r n k hn hk hgap
  let C : Coeff 2 → ℂ := fun p => B p-(if k=n then 1 else 0)*(ε p-(Real.pi:ℂ))
  have hC : AnalyticAt ℂ C (SpectralWeight.one.toCoeff q) :=
    hB.sub (analyticAt_const.mul (hε.sub analyticAt_const))
  refine ⟨C,hC,?_⟩
  filter_upwards [hphysical] with p hp
  let P := SpectralWeight.one.toCoeff p.val
  have hreal : ε P = ((ε P).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (show (ε P).im = 0 from hp.2.1)
  have hpoint : cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
      (hillRealGapHalfLength p.val p.property.1 p.property.2 k) ((ε P).re : ℂ) =
        (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) := by
    have hh := hp.2.2.1
    change cosineGapPoint _ _ (ε P) = _ at hh
    rw [hreal] at hh
    exact hh
  have hsin : Complex.sin ((ε P).re : ℂ) = hillDirichletGapSine p.val p.property.1 p.property.2 k hk := by
    have hh := hp.2.2.2.1
    change Complex.sin (ε P) = _ at hh
    rw [hreal] at hh
    exact hh
  rw [hillRegularAbelianCorrection_eq_of_terminal p.val p.property.1 p.property.2 n k hn hk hp.1 _ hpoint hsin]
  change B P-(if k=n then 1 else 0)*(ε P-(Real.pi:ℂ)) = _
  rw [hp.2.2.2.2.1]
  change hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k (ε P) =
    hillRegularAbelianPrimitive p.val p.property.1 p.property.2 n hn k ((ε P).re : ℂ)
  rw [hreal]
  simp only [ofReal_re]

theorem exists_hillRegularAbelianCorrection_analytic_closed_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hgap : hillRealGapHalfLength q hq hr k = 0) :
    ∃ C : Coeff 2 → ℂ, AnalyticAt ℂ C (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        C (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  have hc : hillRealLabels q hq hr (2*k-1) = hillRealLabels q hq hr (2*k) := by
    dsimp only [hillRealGapHalfLength] at hgap
    linarith
  obtain ⟨C,hC,_,hphysical⟩ := exists_hillRegularAbelian_analytic_closed_gap_correction q hq hr h0q h0r n k hn hk hc
  refine ⟨C,hC,?_⟩
  filter_upwards [hphysical] with p hp
  by_cases hc' : hillRealGapHalfLength p.val p.property.1 p.property.2 k = 0
  · rw [hillRegularAbelianCorrection_closed p.val p.property.1 p.property.2 n hn k hk hc']
    exact hp.2.1 hc'
  · have hspec := hillDirichletSelectedRealAngle_spec p.val p.property.1 p.property.2 k hk hc'
    rw [hillRegularAbelianCorrection,dif_neg hc']
    exact hp.2.2 hc' _ hspec.2.1 hspec.2.2

theorem exists_hillRegularAbelianCorrection_analytic_extension
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    ∃ C : Coeff 2 → ℂ, AnalyticAt ℂ C (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        C (SpectralWeight.one.toCoeff p.val) = hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  by_cases hgap : hillRealGapHalfLength q hq hr k = 0
  · exact exists_hillRegularAbelianCorrection_analytic_closed_extension q hq hr h0q h0r n k hn hk hgap
  · exact exists_hillRegularAbelianCorrection_analytic_open_extension q hq hr h0q h0r n k hn hk hgap

end NLS.KdV
