import NLS.KdV.HillFullRegularPhaseVariation
import NLS.KdV.HillActionAmplitudeSources
import NLS.KdV.HillSpectralCartesianTerminal
import NLS.KdV.HillSpectralCartesianAnalytic
import NLS.ComplexAnalysis.ActionPhaseSourceVariation

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

/-- Every analytic germ matching the actual physical Cartesian coordinate has
this exact action-source derivative on the regular terminal locus. -/
theorem hillSpectralCartesianGerm_regular_actionSource_fderiv
    (n : ℕ) (hn : 1≤n)
    (hreg : ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr (j+1) (by omega))≠0)
    (Z : Coeff 2 → ℂ) (hZ : AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q))
    (hZreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      Z (SpectralWeight.one.toCoeff p.val)=hillSpectralCartesian p.val p.property.1 p.property.2 n hn) :
    ∀ k : ℕ, ∀ hk : 1≤k,
      (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
        (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0))=
          -I*(if k=n then 1 else 0 : ℂ)*hillSpectralCartesian q hq hr n hn := by
  obtain ⟨Θ,ε,hΘ,_,hphysical,hsource⟩ :=
    exists_hillFullPhysicalPhase_regular_source_variation q hq hr h0q h0r n hn hreg
  have hgap := hphysical.self_of_nhds.1
  let P : WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ] Coeff 2 := SpectralWeight.one.toCoeff
  let A : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ := fun p => hillLocalActionAmplitude q hq hr n (P p)
  have hAcoef := analyticAt_hillLocalActionAmplitude q hq hr n hn hgap
  have hA : AnalyticAt ℂ A q := hAcoef.comp (f := P) (P.analyticAt q)
  let F : WeightedCoeff SpectralWeight.one.toWeight 2 → ℂ := fun p => A p*Complex.exp (I*Θ p)
  have hF : AnalyticAt ℂ F q := hA.mul (analyticAt_const.mul hΘ).cexp'
  have hFreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F p.val=hillSpectralCartesian p.val p.property.1 p.property.2 n hn := by
    filter_upwards [hphysical,eventually_hillLocalActionAmplitude_eq_physical q hq hr n hn] with p hp hAmp
    have he : ε (P p.val)=((ε (P p.val)).re : ℂ) := by
      apply Complex.ext
      · simp only [ofReal_re]
      · change (ε (P p.val)).im=0
        exact hp.2.1
    have ht := hillSpectralCartesian_eq_abelian_terminal p.val p.property.1 p.property.2 n hn hp.1
      (ε (P p.val)).re (by simpa only [←he] using hp.2.2.1) (by simpa only [←he] using hp.2.2.2.1)
    dsimp only [F,A,P]
    rw [hAmp,hp.2.2.2.2,ht]
    congr 2
    rw [←he]
    ring
  have hZpull : AnalyticAt ℂ (Z ∘ P) q := hZ.comp (f := P) (P.analyticAt q)
  have hreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      (Z ∘ P) p.val=F p.val := by
    filter_upwards [hZreal,hFreal] with p hpZ hpF
    exact hpZ.trans hpF.symm
  intro k hk
  let h := hillPhysicalMomentHamiltonianSource q hq hr k hk 0
  have heven : P h∈Coeff.paritySubspace 0 := hillEnergyContourHamiltonianSource_mem_even _ _ _ _ _ _
  have hsame := hillPhysicalGerm_fderiv_eq_of_eventuallyEq q hq hr (Z ∘ P) F hZpull hF hreal h heven
  have hDZ := hZ.differentiableAt.hasFDerivAt.comp q P.hasFDerivAt
  change HasFDerivAt (Z ∘ P) _ q at hDZ
  rw [hDZ.fderiv,ContinuousLinearMap.comp_apply] at hsame
  have hAzero : (fderiv ℂ A q) h=0 := by
    have hd := hAcoef.differentiableAt.hasFDerivAt.comp q P.hasFDerivAt
    change HasFDerivAt A _ q at hd
    rw [hd.fderiv,ContinuousLinearMap.comp_apply]
    exact hillLocalActionAmplitude_physicalActionSource_fderiv q hq hr n k hn hk hgap
  calc
    _ = (fderiv ℂ F q) h := hsame
    _ = -I*(if k=n then 1 else 0 : ℂ)*F q :=
      actionPhase_fderiv_of_stationary_amplitude A Θ q h _ hA hΘ hAzero (hsource k hk)
    _ = _ := by rw [hFreal.self_of_nhds]

/-- An actual analytic physical Cartesian germ with all regular action rotations. -/
theorem exists_hillSpectralCartesian_regular_actionSource_variations
    (n : ℕ) (hn : 1≤n)
    (hreg : ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr (j+1) (by omega))≠0) :
    ∃ Z : Coeff 2 → ℂ, AnalyticAt ℂ Z (SpectralWeight.one.toCoeff q) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        Z (SpectralWeight.one.toCoeff p.val)=hillSpectralCartesian p.val p.property.1 p.property.2 n hn) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ Z (SpectralWeight.one.toCoeff q))
          (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk 0))=
            -I*(if k=n then 1 else 0 : ℂ)*hillSpectralCartesian q hq hr n hn := by
  obtain ⟨Z,hZ,hZreal⟩ := exists_hillSpectralCartesian_analytic_extension h0q h0r q hq hr n hn
  exact ⟨Z,hZ,hZreal,hillSpectralCartesianGerm_regular_actionSource_fderiv q hq hr h0q h0r n hn hreg Z hZ hZreal⟩

end NLS.KdV
