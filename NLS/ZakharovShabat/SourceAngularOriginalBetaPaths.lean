import NLS.ZakharovShabat.SourceAngularOriginalCollapsedPrimitive
import NLS.ZakharovShabat.SourceAngularBetaAdmissiblePath
import NLS.ZakharovShabat.SourceAngularEtaAdmissiblePathPeriod

/-!
# Beta path independence on the original domain and disks

The terminal anti-discriminant fixes the continued root only at a
regular Dirichlet endpoint. At a periodic endpoint either sign gives
zero. These assertions include collapsed complex gaps and comparisons
between different original disks; no primitive is assumed by callers.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- A collapsed selected gap makes every C¹ admissible beta path integrable. -/
theorem beta_original_collapsed_curveIntegrable (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    {b : ℂ} (hb : b ∈ ball (P.center:ℂ) P.radius)
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) :
    CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ := by
  obtain ⟨κ,hκ,hfixed⟩ := hQ.exists_fixed_sign P.closedBall_subset_omittedDomain
  let f := sourceAngularCollapsedIntegrand hp hp1 n m s ψ
  have hint := sourceAngularCollapsedIntegrand_curveIntegrable hp hp1 n m s ψ
    (H.angular_endpoint_data ψ hψ m) (ball (P.center:ℂ) P.radius)
    (fun _ hz => P.closedBall_subset_omittedDomain (ball_subset_closedBall hz)) γ hγ (by
      intro t
      simpa only [Path.extend_apply γ t.property] using
        hQ.path_mem_ball (P.gap (left_mem_segment ℝ _ _)) hb t t.property)
  have hω : holomorphicOneForm (fun z => κ*f z) = κ • holomorphicOneForm f := by
    funext z
    exact mul_smul κ (f z) (ContinuousLinearMap.id ℂ ℂ)
  have hintκ : CurveIntegrable (holomorphicOneForm (fun z => κ*f z)) γ := by
    rw [hω]
    exact hint.smul
  apply (curveIntegrable_holomorphicOneForm_congr_interior _ (fun z => κ*f z) γ ?_).mpr hintκ
  intro t ht
  have hc := H.angular_extension.angular_collapsed_integrand_eq_canonical ψ hψ n m hmn hgap
    (γ.extend t) (hQ.interior_mem_canonicalRootDomain P.closedBall_subset_omittedDomain t ht)
  change sourceAngularIntegrand n s Q (γ.extend t,ψ) = κ*f (γ.extend t)
  dsimp only [f]
  rw [← hc]
  dsimp only [sourceAngularIntegrand]
  rw [hfixed t ht]
  rcases hκ with rfl | rfl <;> simp only [one_mul,neg_one_mul,div_neg]

/-- Every integrable admissible root continuation between periodic endpoints
has zero off-diagonal integral, including collapsed gaps and either sign. -/
theorem beta_original_periodic_terminal_zero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    {b : ℂ} (hb : b ∈ ({canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m} : Set ℂ))
    (Q : ℂ × CoeffPair p → ℂ)
    (γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b)
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    sourceAngularPathIntegral n s Q ψ γ = 0 := by
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
  exact hQ.pathIntegral_eq_of_signed_primitive_limits n s F A hF hA κ hκ hfixed 0 hend hγ hint

/-- The actual Dirichlet beta integral is independent of path, continued root,
and original isolating disk. At periodic terminals normalization is unnecessary. -/
theorem beta_original_dirichlet_path_independent (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P P' : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (hμ' : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P'.center:ℂ) P'.radius)
    (Q Q' : ℂ × CoeffPair p → ℂ)
    (γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hQ : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ)
    (hQ' : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P'.center:ℂ) P'.radius Q' κ)
    (hnorm : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hnorm' : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0 →
      Q' (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
        sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) (hκ : ContDiffOn ℝ 1 κ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ)
    (hint' : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q' (z,ψ))) κ) :
    sourceAngularPathIntegral n s Q ψ γ = sourceAngularPathIntegral n s Q' ψ κ := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
  by_cases hw : w ≠ 0
  · have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
    obtain ⟨F,A,E,hE⟩ := H.angular_original_sheet_primitive_all_gaps ψ hψ n m hmn P w hw
    obtain ⟨G,B,J,hJ⟩ := H.angular_original_sheet_primitive_all_gaps ψ hψ n m hmn P' w hw
    rw [hE.admissible_pathIntegral_eq_value P.closedBall_subset_omittedDomain hw ⟨hμ,hbase.1⟩
      Q γ hQ ((hnorm hw).trans hbase.2.symm) hγ hint,
      hJ.admissible_pathIntegral_eq_value P'.closedBall_subset_omittedDomain hw ⟨hμ',hbase.1⟩
        Q' κ hQ' ((hnorm' hw).trans hbase.2.symm) hκ hint']
    exact hE.dirichlet_terminal_eq hJ P.gap P'.gap hw hw ⟨hμ,hbase.1⟩ ⟨hμ',hbase.1⟩ hbase.2 hbase.2
  · have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ m
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) (not_ne_iff.mp hw)
    rw [H.beta_original_periodic_terminal_zero ψ hψ n m hmn P hend Q γ hQ hγ hint,
      H.beta_original_periodic_terminal_zero ψ hψ n m hmn P' hend Q' κ hQ' hκ hint']

end SourceLemma12_12Data
end NLS.ZakharovShabat
