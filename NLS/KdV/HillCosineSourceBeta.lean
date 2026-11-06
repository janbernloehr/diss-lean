import NLS.KdV.HillCosineSourceIntegrability
import NLS.KdV.HillHminusDirichletSourceBetaSeries
import NLS.ZakharovShabat.SourceAngularPairedPrimitives

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)

/-- Actual constructed paired source primitives evaluate the CONSTRUCTED
original frequency paths. All source disc, sheet and individual
integrability conditions are DISCHARGED, including the singular start. -/
theorem originalCosineFrequencyPath_integral_eq_beta_pair
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n k : ℕ+) (hkn : k≠n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hw : hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)≠0) :
    let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
      (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
    let ψ := P.dirichletSource (hillOriginalHminusSource q.val)
    let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
    sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w) ψ γ+
      sourceAngularPathIntegral ((n:ℕ):ℤ) P.family.roots (sourceAngularRootSheet (by simp) w) ψ
        (γ.map continuous_neg)=
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) ((k:ℕ):ℤ) P.family.roots ψ+
        sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((k:ℕ):ℤ)) P.family.roots ψ := by
  dsimp only
  let a := hillOriginalHminusSource q.val
  let ψ := P.dirichletSource a
  let w := hillDirichletSheetRoot (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)
  let γ := P.originalCosineFrequencyPath q hq hreal houtside c hshift k hgap
  have hrealA := hreal a hq.1 (hillOriginalHminusSource_real q.val q.property.2)
  have hψ : ψ∈P.family.domain := (P.mem_sourceBetaDomain_of_real a hq hrealA).2
  have hz : P.dirichletFrequency (k:ℕ) a≠0 := by
    intro he
    have hp := P.originalCosineFrequencyPath_re_pos q hq hreal houtside c hshift k hgap 1
    rw [Path.extend_one,← P.dirichletFrequency_eq_sourcePhase,he,zero_re] at hp
    exact lt_irrefl 0 hp
  have hwp : w=sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (k:ℕ) ψ :=
    (P.dirichletSheet_eq_original q hq hreal houtside c hshift k).symm.trans
      (P.dirichletSheet_eq_sourcePhase k a hq hz)
  have hwn : w=sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet (-((k:ℕ):ℤ)) ψ :=
    (P.dirichletSheet_eq_original q hq hreal houtside c hshift k).symm.trans
      (P.dirichletSheet_eq_negative_sourcePhase k a hq hrealA hz)
  have hmn : ((k:ℕ):ℤ)≠(n:ℕ) := by exact_mod_cast (show (k:ℕ)≠(n:ℕ) from fun h => hkn (Subtype.ext h))
  have hneg : -((k:ℕ):ℤ)≠(n:ℕ) := by have := k.pos;have := n.pos;omega
  obtain ⟨D⟩ := H.nonempty_pairedDirichletPrimitives ψ hψ ((n:ℕ):ℤ) ((k:ℕ):ℤ) hmn hneg
    (by rw [← hwp];exact hw) (by rw [← hwn];exact hw)
  have hμ : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ (-((k:ℕ):ℤ))=
      -canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ (k:ℕ) := by
    rw [← P.dirichletFrequency_eq_sourcePhase,← P.dirichletFrequency_eq_sourcePhase]
    exact P.dirichletFrequency_neg_of_real a hrealA (k:ℕ)
  have hpair := D.pathIntegral_eq_beta_pair (P.sourcePhase_periodic_endpoint_reflection a) hμ
    (hwn.symm.trans hwp) γ (P.contDiffOn_originalCosineFrequencyPath q hq hreal houtside c hshift k hgap)
  rw [← hwp] at hpair
  have hsheet := P.originalCosineFrequencyPath_sheet_resolution q hq hreal houtside c hshift k hgap hw
  have hInt := P.originalCosineFrequencyPath_source_curveIntegrable q hq hreal houtside c hshift
    ((n:ℕ):ℤ) k hgap hw
  apply hpair _ _ hInt.1 hInt.2
  · intro t ht
    exact ⟨D.positive_data.gap_enclosed
      (P.originalCosineFrequencyPath_mem_sourceGap q hq hreal houtside c hshift k hgap t),
        (hsheet t ht).1⟩
  · intro t ht
    exact ⟨D.negative_data.gap_enclosed
      (P.originalCosineFrequencyPath_neg_mem_sourceGap q hq hreal houtside c hshift k hgap t),
        (hsheet t ht).2.1⟩

end NLS.KdV.HillHminusPsiChart
