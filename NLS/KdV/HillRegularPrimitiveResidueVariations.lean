import NLS.KdV.HillCharacteristicDirichletPrimitives
import NLS.KdV.HillCharacteristicTerminalVariation
import NLS.KdV.HillDirichletTerminalNormalization
import NLS.KdV.HillHamiltonianDirichletSourceFlows

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

/-- A genuine physical Dirichlet-evaluated Abelian primitive germ has
exactly the checked action-residue source variation on a nonzero terminal
sheet. The same germ works for every physical moment source at once. -/
theorem exists_hillDirichletPrimitive_regular_physical_source_variations
    (n j : ℕ) (hn : 1≤n) (hj : 1≤j) (hgap : hillRealGapHalfLength q hq hr j≠0)
    (hreg : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr j hj)≠0) :
    ∃ B ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      ε (SpectralWeight.one.toCoeff q)=e ∧
      e∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 j≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 j)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 j) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 j hj : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 j hj ∧
        B (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn j
          (ε (SpectralWeight.one.toCoeff p.val)) ∧ (B (SpectralWeight.one.toCoeff p.val)).im=0) ∧
      ∀ k : ℕ, ∀ hk : 1≤k, ∀ m : ℕ,
        (fderiv ℂ B (SpectralWeight.one.toCoeff q))
          (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk m))=
          hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr j hj)*
            hillPhysicalMomentDirichletResidue (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k j hj m := by
  obtain ⟨B,d,μ,S,ε,e,hB,hd,hμ,hS,hε,hd0,hμ0,hS0,hε0,he,hpoint,hsin,hcomplex,hphysical,hBvar⟩ :=
    exists_hillDirichletAbelianIntegral_characteristic_open_gap_extension q hq hr h0q h0r n j hn hj hgap
  refine ⟨B,ε,e,hB,hε,hε0,he,hphysical,?_⟩
  intro k hk m
  let h := SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk m)
  have hiso : ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) h=0 :=
    hillPhysicalMomentHamiltonianSource_isospectral q hq hr k hk m
  have hdne : d (SpectralWeight.one.toCoeff q)≠0 := by
    rw [hd0]
    exact ofReal_ne_zero.mpr hgap
  have hdsq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), d p^2=hillLocalGapSquare q hq hr j p/4 :=
    hcomplex.mono (fun _ hp => hp.2.1)
  have hroot : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), hillL2DirichletCharacteristic p (μ p)=0 :=
    hcomplex.mono (fun _ hp => hp.2.2.1)
  have heq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      cosineGapPoint (hillLocalGapMidpoint q hq hr j p) (d p) (ε p)=μ p :=
    hcomplex.mono (fun _ hp => hp.2.2.2.1)
  have hv := hillCharacteristicCosineTerminal_isospectral_fderiv q hq hr j hj d μ ε hd hμ hε hdne hdsq heq h hiso
  rw [hd0,hε0] at hv
  change (fderiv ℂ B (SpectralWeight.one.toCoeff q)) h=_
  rw [hBvar h hiso,hillDirichletCosineDifferential_regular_terminal_variation q hq hr n j hn hj hgap e
    ((fderiv ℂ ε (SpectralWeight.one.toCoeff q)) h) ((fderiv ℂ μ (SpectralWeight.one.toCoeff q)) h)
    hpoint hsin hv hreg]
  rw [hillDirichletBranch_physicalMomentHamiltonianSource_fderiv (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
    k j hk hj m μ hμ hμ0 hroot]
  rw [← mul_assoc,div_mul_cancel₀ _ hreg]

end NLS.KdV
