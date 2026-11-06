import NLS.KdV.HillProjectedKernelCharts
import NLS.KdV.HillPhaseSeriesDerivativeAssembly
import NLS.KdV.HillPhaseSeriesPhysicalMatching
import NLS.KdV.HillPrimitiveCorrectionMatching
import NLS.KdV.HillPrimitivePartialSumVariations
import NLS.KdV.HillClosedGapAbelianCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual full infinite physical phase has an analytic local lift
with its exact signed physical action-source derivative on the regular
terminal locus. The full normally convergent series is differentiated. -/
theorem exists_hillFullPhysicalPhase_regular_source_variation
    (n : ℕ) (hn : 1≤n)
    (hreg : ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr (j+1) (by omega))≠0) :
    ∃ Θ : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ, ∃ ε : Coeff 2 → ℂ,
      AnalyticAt ℂ Θ q ∧ AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 n)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 n) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 n hn ∧
        Θ p.val=hillSummedRegularAbelianCorrection p.val p.property.1 p.property.2 n hn+
          ε (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ Θ q) (hillPhysicalMomentHamiltonianSource q hq hr k hk 0)=
          -(if k=n then 1 else 0 : ℂ) := by
  obtain ⟨B,ε,e,hdata,hpartial⟩ :=
    exists_hillPhysicalPrimitive_partial_sum_source_variations q hq hr h0q h0r n hn hreg
  have hgap (j : ℕ) : hillRealGapHalfLength q hq hr (j+1)≠0 := by
    intro hz
    exact hreg j (hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr (j+1) (by omega) hz)
  have hB (j : ℕ) : AnalyticAt ℂ (B j) (SpectralWeight.one.toCoeff q) := (hdata j).1
  have hmatch (j : ℕ) : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      B j (SpectralWeight.one.toCoeff p.val)=hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn (j+1) (by omega)+
        (if j+1=n then 1 else 0)*(ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) :=
    eventually_hillPrimitive_eq_regularCorrection_of_terminal q hq hr n (j+1) hn (by omega) (hgap j)
      (B j) (ε j) (hdata j).2.2.2.2
  obtain ⟨U,V,N,M,hU,hqU,hV,hqV,hN,_,_,β,hβ,hzero,hbound,hβreal⟩ :=
    exists_hillHighRegularCorrection_weightOne_normal_charts q hq hr h0q h0r n hn
  let Θ : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ := fun p =>
    (∑ j∈hillPhaseFiniteHead N n,B j (SpectralWeight.one.toCoeff p))+(∑' j : ℕ,β j p)
  have hD := hillPrimitiveSeries_fderiv_of_normal_tail q hq hr n N hn hN U hU hqU V hV hqV
    β hβ hzero M hbound hβreal B ε hB hmatch hpartial
  have hphase := eventually_hillPhaseSeries_eq_full_physical_phase q hq hr h0q h0r n N hn hN V hV hqV
    β hzero hβreal B ε hmatch
  have hni : n-1+1=n := by omega
  have hown := (hdata (n-1)).2.2.2.2
  simp only [hni] at hown
  have hgapn : hillRealGapHalfLength q hq hr n≠0 := by simpa only [hni] using hgap (n-1)
  have hgn : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillRealGapHalfLength p.val p.property.1 p.property.2 n≠0 :=
    (continuous_hillRealGapHalfLength n).continuousAt.eventually_ne hgapn
  refine ⟨Θ,ε (n-1),hD.1,(hdata (n-1)).2.1,?_,hD.2⟩
  filter_upwards [hphase,hown,hgn] with p hpPhase hpOwn hpGap
  have hi : (ε (n-1) (SpectralWeight.one.toCoeff p.val)).im=0 :=
    hillDirichlet_angle_im_eq_zero p.val p.property.1 p.property.2 n hn hpGap _ hpOwn.1 hpOwn.2.1
  exact ⟨hpGap,hi,hpOwn.1,hpOwn.2.1,hpPhase⟩

end NLS.KdV
