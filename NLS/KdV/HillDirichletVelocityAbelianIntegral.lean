import NLS.KdV.HillDirichletVelocityData
import NLS.KdV.HillTraceStationaryAbelianPrimitive

/-! # Actual Abelian integral variation from Dirichlet first derivatives -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

/-- Genuine analytic sheeted Dirichlet Abelian integrals have the exact
normalized-numerator kernel, including its filled spectral diagonal and
terminal bandedges. The entire actual source contribution was proved zero;
the remaining terminal contribution is now evaluated. -/
theorem exists_hillDirichletAbelianIntegral_velocity_variation
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hgap : hillRealGapHalfLength q hq hr k≠0) :
    ∃ B ε : Coeff 2 → ℂ, ∃ e : ℂ,
      AnalyticAt ℂ B (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q) ∧
      ε (SpectralWeight.one.toCoeff q)=e ∧ e∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
      (∀ (V : Coeff 2) (K : ℂ),
        HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V K →
        (fderiv ℂ B (SpectralWeight.one.toCoeff q)) V=
          hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)*K) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        hillRealGapHalfLength p.val p.property.1 p.property.2 k≠0 ∧
        (ε (SpectralWeight.one.toCoeff p.val)).im=0 ∧
        cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
          (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val))=
            (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
        Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk ∧
        B (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k
          (ε (SpectralWeight.one.toCoeff p.val)) ∧ (B (SpectralWeight.one.toCoeff p.val)).im=0 := by
  obtain ⟨B,ε,e,hB,hε,hε0,he,hdecomp,hphysical⟩ :=
    exists_hillDirichletAbelianIntegral_trace_stationary_source_decomposition q hq hr h0q h0r n k hn hk hgap
  have hterminal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 k)
        (hillRealGapHalfLength p.val p.property.1 p.property.2 k) (ε (SpectralWeight.one.toCoeff p.val))=
          (hillDirichletEnergy p.val p.property.1 p.property.2 k hk : ℂ) ∧
      Complex.sin (ε (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk :=
    hphysical.mono (fun _ hp => ⟨hp.2.2.1,hp.2.2.2.1⟩)
  have hpoint := (Filter.Eventually.self_of_nhds (x := (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) hterminal).1
  rw [hε0] at hpoint
  have hball := hillRealGapSegment_subset_intrinsic_contour_ball q hq hr k hk
    (ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q hq hr (by omega : 2*k-1≤2*k))
      (hillDirichletEnergy_mem_gap q hq hr k hk))
  have hUne := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk (hillDirichletEnergy q hq hr k hk)
    (hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk (ball_subset_closedBall hball))
  refine ⟨B,ε,e,hB,hε,hε0,he,?_,hphysical⟩
  intro V K hv
  rw [hdecomp V hv.trace_stationary,HillDirichletVelocityData.terminal_angle (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk hgap ε hε.differentiableAt hterminal V K hv]
  unfold hillAbelianCosineDifferential
  rw [hpoint]
  field_simp [hUne]
  simp only [I_sq]
  ring

end NLS.KdV
