import NLS.ZakharovShabat.SourceAngularOriginalEtaIntegral
import NLS.ZakharovShabat.SourceAngularEtaImproperRemainder

/-!
# One improper eta remainder on each original disk

The original normalized primitive gives the same terminal remainder for
every admissible interior C¹ path. At a periodic terminal this remainder
is zero, independently of the continued root sign.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The remainder is independent of every admissible path and its continuation. -/
theorem eta_original_common_improper_remainder (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈ ball (P.center:ℂ) P.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
    ∃ B : ℂ, ∀ Q : ℂ × CoeffPair p → ℂ,
      ∀ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) μ,
      SourceAngularAdmissiblePathRootData hp hp1 n ψ (P.center:ℂ) P.radius Q γ →
      (w ≠ 0 → Q (μ,ψ) = w) → ContDiffOn ℝ 1 γ.extend (Ioo 0 1) →
      Tendsto (fun u : ℝ × ℝ =>
        truncatedPathIntegral (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2 -
          truncatedPathIntegral (sourceAngularEtaPathModelIntegrand hp hp1 n ψ Q) γ u.1 u.2)
        ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 B) := by
  intro μ w
  by_cases hw : w ≠ 0
  · obtain ⟨F,E,hE⟩ := H.eta_original_sheet_primitive ψ hψ n P hgap w hw
    have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ n hw
    refine ⟨E μ,?_⟩
    intro Q γ hQ hnorm hγ
    obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign P.closedBall_subset_omittedDomain
    exact hQ.improper_remainder_limit s P.closedBall_subset_omittedDomain
      (H.angular_endpoint_data ψ hψ n) F hE.hasDerivAt_exterior hE.tendsto_left_exterior
      κ hκ hfixed (E μ)
      (hQ.signed_primitive_terminal_limit hE P.closedBall_subset_omittedDomain hw
        ⟨hμ,hbase.1⟩ ((hnorm hw).trans hbase.2.symm) κ hκ hfixed) hγ
  · obtain ⟨F,E,hE⟩ := H.eta_original_sheet_primitive ψ hψ n P hgap 1 one_ne_zero
    have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ n
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) (not_ne_iff.mp hw)
    have hboundary : Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n] μ) (𝓝 0) := by
      simp only [mem_insert_iff,mem_singleton_iff] at hend
      rcases hend with h | h
      · simpa only [μ,h] using hE.tendsto_left_exterior
      · simpa only [μ,h] using hE.tendsto_right_exterior
    refine ⟨0,?_⟩
    intro Q γ hQ _ hγ
    obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign P.closedBall_subset_omittedDomain
    have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ))
        (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ n] μ) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [Path.extend_one] using
          (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
        exact hQ.interior t ht
    have hl : Tendsto ((fun z => κ*F z) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 0) := by
      simpa only [Function.comp_def,mul_zero] using (hboundary.comp hγend).const_mul κ
    exact hQ.improper_remainder_limit s P.closedBall_subset_omittedDomain
      (H.angular_endpoint_data ψ hψ n) F hE.hasDerivAt_exterior hE.tendsto_left_exterior
      κ hκ hfixed 0 hl hγ

end SourceLemma12_12Data
end NLS.ZakharovShabat
