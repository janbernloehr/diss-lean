import NLS.ZakharovShabat.SourceEquation2_18
import NLS.ZakharovShabat.SourceGapCosineMeanDomain

/-!
# The action's cosine representation on the original complex domain

The regular numerator is analytic through the selected gap. Its cosine
mean depends analytically on the midpoint and squared gap, without any
choice of analytic endpoint labels. Real-source agreement then continues
throughout the original connected domain.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Retrieve the unchanged-domain critical-offset data. -/
theorem SourceEquation2_18Data.criticalOffsets
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) : SourceLemma10_10Data hp hp1 W :=
  H.previous.previous.previous.previous.previous.previous.previous.previous

/-- The regular numerator in the recentered action formula. -/
def sourceActionChiNumerator (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × CoeffPair p) : ℂ :=
  (canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n-t.1)^2 *
    sourceActionChi hp hp1 n t.2 t.1

/-- The entire actual segment avoids every other gap on the unchanged domain. -/
theorem SourceEquation2_18Data.segment_subset_omitted
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourcePeriodicSegment hp hp1 ψ n ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  have h2 := H.criticalOffsets.previous.previous.previous.roots.roots.symmetric
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := h2.isolation ψ hψ
  exact fun _ hz => hD.disk_subset_omittedDomain ψ hψV n (hD.gap ψ hψV n hz)

/-- The unnormalized cosine integral is analytic at every complex source in W. -/
theorem SourceEquation2_18Data.chiCosineMean_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceGapCosineMean hp hp1 n (sourceActionChiNumerator hp hp1 n)) W := by
  have h6 := H.criticalOffsets.previous.previous.previous
  have h2 := h6.roots.roots.symmetric
  apply analyticOnNhd_sourceGapCosineMean_of_segment hp hp1 n W _
    (h6.roots.joint n).1 _ (h2.midpoint n) (h2.squared_gap n) (fun ψ hψ => H.segment_subset_omitted ψ hψ n)
  intro t ht
  exact (((((h2.simplicity.critical t.2 ht.1 n).1).comp
    (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd).sub analyticAt_fst).pow 2).mul (H.joint n t ht)

/-- Agreement with the real action includes the collapsed-gap case. -/
theorem SourceEquation2_18Data.action_eq_chiCosineMean_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hr : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = (2/(Real.pi:ℂ))*
      sourceGapCosineMean hp hp1 n (sourceActionChiNumerator hp hp1 n) ψ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let a := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  by_cases hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  · have hδ : δ ≠ 0 := sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hr n hopen
    calc
      sourceIndexedAction hp hp1 n ψ = (2/(Real.pi:ℂ))*(δ^2 *
          ∫ θ in (0:ℝ)..Real.pi, ((a-τ)/δ-(Real.cos θ:ℂ))^2 *
            (Complex.I*sourceCriticalRootRatioExtension hp hp1 n ψ (τ+δ*(Real.cos θ:ℂ)))) := by
        rw [sourceIndexedAction_eq_sourceRealAction hp hp1 n ψ hr,
          ← sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hr,
          sourceComplexAction_eq_upper_cosineBoundaryIntegral hp hp1 ψ hr n hopen,
          ← sourceAction_upper_cosineBoundaryIntegral_recenter hp hp1 ψ hr n hopen a.re,
          sourceAction_upper_cosineBoundaryIntegral_critical_model hp hp1 ψ hr n hopen]
        dsimp only [a,τ,δ]
        ring
      _ = _ := by
        congr 1
        rw [← intervalIntegral.integral_const_mul]
        unfold sourceGapCosineMean parametricCosineMean
        apply intervalIntegral.integral_congr
        intro θ _
        have hz : τ+δ*(Real.cos θ:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n :=
          sourceStandardRootGapSegment_subset_omittedDomain_of_realType hp hp1 ψ hr n
            ⟨Real.cos θ,⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩,rfl⟩
        change δ^2 * (((a-τ)/δ-(Real.cos θ:ℂ))^2 *
          (Complex.I*sourceCriticalRootRatioExtension hp hp1 n ψ (τ+δ*(Real.cos θ:ℂ)))) =
            (a-(τ+δ*(Real.cos θ:ℂ)))^2*sourceActionChi hp hp1 n ψ (τ+δ*(Real.cos θ:ℂ))
        rw [sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n _ hz]
        field_simp
        simp [Complex.I_sq]
        ring
  · have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
    have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hr) n
    have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 := by
      apply sub_eq_zero.mpr
      exact Complex.ext (le_antisymm (not_lt.mp hopen) hle) (him.2.trans him.1.symm)
    have hδ : δ = 0 := by simp only [δ,sourceStandardRootHalfGap,hgap,zero_div]
    have ha : a = τ := H.criticalOffsets.critical_eq_midpoint_of_gap_zero ψ hψ n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
    rw [H.previous.collapsed ψ hψ n hgap]
    change 0 = (2/(Real.pi:ℂ))*(∫ θ in (0:ℝ)..Real.pi,
      (a-(τ+δ*(Real.cos θ:ℂ)))^2*sourceActionChi hp hp1 n ψ (τ+δ*(Real.cos θ:ℂ)))
    simp only [hδ,zero_mul,add_zero,ha,sub_self,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      intervalIntegral.integral_zero,mul_zero]

/-- Real agreement determines the action on the entire original connected W. -/
theorem SourceEquation2_18Data.action_eq_chiCosineMean
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (hWc : IsPreconnected W)
    (hR : realTypeSourceLocus p ⊆ W) (n : ℤ) :
    EqOn (sourceIndexedAction hp hp1 n) (fun ψ => (2/(Real.pi:ℂ))*
      sourceGapCosineMean hp hp1 n (sourceActionChiNumerator hp hp1 n) ψ) W := by
  have hA := H.previous.previous.analytic n
  have hB : AnalyticOnNhd ℂ (fun ψ => (2/(Real.pi:ℂ))*
      sourceGapCosineMean hp hp1 n (sourceActionChiNumerator hp hp1 n) ψ) W :=
    fun ψ hψ => analyticAt_const.mul (H.chiCosineMean_analytic n ψ hψ)
  have h0 : (0 : CoeffPair p) ∈ W := hR (by simp [realTypeSourceLocus])
  obtain ⟨U,hU,h0U,_,he⟩ := exists_local_eqOn_of_eqOn_realType hp (0 : CoeffPair p)
    (by simp) W W hW hW h0 h0 _ _ hA.differentiableOn hB.differentiableOn
    (fun ψ hψ hr => H.action_eq_chiCosineMean_real ψ hψ.1 hr n)
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB hWc h0
    (Filter.mem_of_superset (hU.mem_nhds h0U) he)

end NLS.ZakharovShabat
