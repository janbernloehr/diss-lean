import NLS.KdV.HillOwnModelIntegrability
import NLS.KdV.HillCosineSourceIntegrability
import NLS.ZakharovShabat.SourceEtaPrescribedRepresentative
import NLS.ZakharovShabat.SourceAngularOriginalEtaAnalytic

noncomputable section
set_option autoImplicit false
open Set Complex Metric MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

/-- The CONSTRUCTED original own frequency integral realizes the actual
analytic eta phase ACROSS THE INTERIOR CUT. Every model-integrability,
normalization, source-chart and sheet condition is discharged; no
outside-gap admissibility is asserted for this gap-interior path. -/
theorem originalOwnSourceIntegral_exp_two_I_eq_eta_phase
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
    let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
    Complex.exp (2*I*sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots
      (sourceAngularRootSheet (by simp) w) ψ γ)=
        sourceAngularEtaAnalyticPhase (by norm_num) (by norm_num) ((n:ℕ):ℤ) P.family.roots ψ := by
  dsimp only
  let a := hillOriginalHminusSource q.val
  let ψ := P.dirichletSource a
  let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ (n:ℕ)
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n n.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift n hgap
  have hrealA := hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)
  have hψ : ψ∈P.family.domain := (P.mem_sourceBetaDomain_of_real a hq hrealA).2
  have hz : P.dirichletFrequency (n:ℕ) a≠0 := by
    intro he
    have hp := P.originalCosineFrequencyPath_re_pos q hq hreal houtside c hshift n hgap 1
    rw [Path.extend_one,← P.dirichletFrequency_eq_sourcePhase,he,zero_re] at hp
    exact lt_irrefl 0 hp
  have hwp : w=sourceAntiDiscriminantCandidate (by simp) (by norm_num) ψ μ :=
    (P.dirichletSheet_eq_original q hq hreal houtside c hshift n).symm.trans
      (P.dirichletSheet_eq_sourcePhase n a hq hz)
  have hbase := sourceAngularRootSheet_dirichlet_base (by simp) (by norm_num) ψ (n:ℕ)
    (by rw [← hwp];exact hw)
  dsimp only at hbase
  rw [← hwp] at hbase
  have hμgap : μ∈sourcePeriodicSegment (by simp) (by norm_num) ψ (n:ℕ) := by
    simpa only [Path.extend_one] using
      P.originalCosineFrequencyPath_mem_sourceGap q hq hreal houtside c hshift n hgap 1
  have hnLeft := (sourceAngularRootSheet_point_ne_periodic_endpoints (by simp) (by norm_num)
    ψ (n:ℕ) w μ hw hbase.1).1
  have hsourceGap : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ)
      (periodOnePotential_mem _) (n:ℕ)≠0 := by
    intro hc
    have hRL := sub_eq_zero.mp hc
    have hm : μ=canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem _) (n:ℕ) := by
      simpa only [sourcePeriodicSegment,hRL,segment_same,mem_singleton_iff] using hμgap
    exact hnLeft hm
  obtain ⟨V,U,d,T,r,R,z₀,ρ,δ,ε,hψU,_,_,D,_⟩ := H.eta_original_analytic_chart ψ hψ (n:ℕ) hsourceGap
  have hψV := D.angle.source_subset hψU
  have hb : μ∈sourceAngularRegularSheetDisc (by simp) ψ (d (n:ℕ)) r w :=
    ⟨D.annulus.gap_enclosed ψ hψV hμgap,hbase.1⟩
  have hsheet := P.originalCosineFrequencyPath_sheet_resolution q hq hreal houtside c hshift n hgap hw
  have hInt := P.originalCosineFrequencyPath_source_curveIntegrable q hq hreal houtside c hshift
    ((n:ℕ):ℤ) n hgap hw
  exact D.exp_two_I_prescribed_pathIntegral_eq_phase ψ hψU w hw hb (hbase.2.trans hwp) γ
    (P.contDiffOn_originalCosineFrequencyPath q hq hreal houtside c hshift n hgap)
    (fun t ht => ⟨D.annulus.gap_enclosed ψ hψV
      (P.originalCosineFrequencyPath_mem_sourceGap q hq hreal houtside c hshift n hgap t),(hsheet t ht).1⟩)
    hInt.1 (P.originalCosineFrequencyPath_eta_model_curveIntegrable q hq hreal houtside c hshift H n hgap hw)

end NLS.KdV.HillHminusPsiChart
