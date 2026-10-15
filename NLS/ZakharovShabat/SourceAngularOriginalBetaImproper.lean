import NLS.ZakharovShabat.SourceAngularOriginalBetaValues
import NLS.ZakharovShabat.SourceAngularBetaImproperPath

/-!
# Original beta values along arbitrary admissible paths

On the same domain and root family from Lemma 12.12, every admissible
interior C¹ path with the prescribed terminal root has a genuine improper
integral equal to beta. This includes collapsed gaps and either sign at
periodic terminals. No integrability or primitive hypothesis is supplied.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both periodic endpoints give zero on either continued sheet. -/
theorem beta_original_periodic_terminal_improper_limit (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    {b : ℂ} (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 0) := by
  obtain ⟨F,A,hF,hA,hB⟩ := H.angular_original_endpoint_primitive ψ hψ n m hmn P
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign P.closedBall_subset_omittedDomain
  have hbF : Tendsto F (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m] b) (𝓝 A) := by
    simp only [mem_insert_iff,mem_singleton_iff] at hb
    rcases hb with rfl | rfl
    · exact hA
    · exact hB
  have hγend : Tendsto γ.extend (𝓝[<] (1:ℝ))
      (𝓝[ball (P.center:ℂ) P.radius \ sourcePeriodicSegment hp hp1 ψ m] b) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Path.extend_one] using
        (γ.continuous_extend.continuousAt (x := (1:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0:ℝ) < 1)] with t ht
      exact hQ.interior t ht
  have hend : Tendsto ((fun z => κ*(F z-A)) ∘ γ.extend) (𝓝[<] (1:ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,mul_zero] using
      ((hbF.comp hγend).sub (tendsto_const_nhds (x := A))).const_mul κ
  exact hQ.tendsto_truncatedIntegral_of_signed_primitive_limits P.closedBall_subset_omittedDomain n s F A hF hA κ hκ hfixed 0 hend hγ

/-- The actual truncated integral tends to the original beta, independently at both ends. -/
theorem beta_original_improper_limit (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    Tendsto (fun u : ℝ × ℝ => truncatedPathIntegral
      (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ u.1 u.2)
      ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (sourceAngularBeta hp hp1 n m s ψ)) := by
  by_cases hw : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0
  · obtain ⟨F,A,E,hE⟩ := H.beta_original_dirichlet_primitive ψ hψ n m hmn P hμ hw
    rw [hE.beta_eq_terminal]
    exact hE.primitive.admissible_improper_limit P.closedBall_subset_omittedDomain hw
      hE.terminal_mem Q γ hQ ((hnorm hw).trans hE.terminal_sheet_value.symm) hγ
  · have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ m
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) (not_ne_iff.mp hw)
    rw [sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ
      (by simpa only [SourceAngularDirichletTerminalIsEndpoint,mem_insert_iff,mem_singleton_iff] using hend)]
    exact H.beta_original_periodic_terminal_improper_limit ψ hψ n m hmn P hend Q γ hQ hγ

/-- The limit-defined beta integral equals the established source value. -/
theorem beta_original_improperIntegral_eq_value (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Ioo 0 1)) :
    improperPathIntegral (fun z => sourceAngularIntegrand n s Q (z,ψ)) γ =
      sourceAngularBeta hp hp1 n m s ψ :=
  (H.beta_original_improper_limit ψ hψ n m hmn P hμ Q γ hQ hnorm hγ).limUnder_eq

end SourceLemma12_12Data
end NLS.ZakharovShabat
