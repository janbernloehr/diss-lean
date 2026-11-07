import NLS.KdV.PhysicalSharpDiagonalCancellation

/-! Every renormalized scalar correction is analytic on ONE common
complex parameter neighborhood, with all actual higher actions retained. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {t : ℝ} {ht : 0≤t} {J : E →L[ℂ] PeriodOneHminusOne}

theorem PhysicalFrequencyParameterization.exists_analytic_renormalized_domain
    (A : PhysicalFrequencyParameterization E t ht J) (q : E) (hq : q∈A.domain)
    (hqr : IsRealPeriodOneHminusOne (J q)) :
    ∃ U : Set E, IsOpen U ∧ q∈U ∧ U⊆A.domain ∧
      ∀ n : ℕ+, AnalyticOnNhd ℂ (A.renormalizedCorrection n) U := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  let Φ := fun a => L (A.normalizedSource a)
  have hΦ : AnalyticOnNhd ℂ Φ A.domain := fun a ha =>
    (L.analyticAt _).comp (A.analytic_source a ha)
  let S := sourceComplexHigherActionDomain (p := 2) (by norm_num) (by norm_num)
  have hS : IsOpen S := isOpen_sourceComplexHigherActionDomain (by norm_num) (by norm_num)
  have hqS : Φ q∈S := realType_subset_sourceComplexHigherActionDomain (by norm_num) (by norm_num)
    (normalizedWeightedSource_realType (sourceSobolevSpectralWeight t ht)
      (A.normalizedSource q) (A.real_source q hq hqr))
  let U := A.domain∩Φ ⁻¹' S
  have hU : IsOpen U := hΦ.continuousOn.isOpen_inter_preimage A.domain_open hS
  refine ⟨U,hU,⟨hq,hqS⟩,inter_subset_left,?_⟩
  intro n a ha
  have hc := (A.physical.analytic_correction n _ (A.domain_subset ha.1)).comp (J.analyticAt a)
  have hact := (analyticOnNhd_sourceComplexHigherAction (by norm_num) (by norm_num) (n:ℤ) 1
    (Φ a) ha.2).comp (hΦ a ha.1)
  apply (hc.add ((analyticAt_const (v := (12:ℂ))).mul hact)).congr
  filter_upwards [A.domain_open.mem_nhds ha.1] with b hb
  dsimp only [PhysicalFrequencyParameterization.renormalizedCorrection,Φ,Function.comp_apply,Pi.add_apply,Pi.mul_apply]
  rw [A.source_identity b hb]

end NLS.KdV
