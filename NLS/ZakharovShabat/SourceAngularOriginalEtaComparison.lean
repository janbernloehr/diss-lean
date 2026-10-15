import NLS.ZakharovShabat.SourceAngularOriginalEndpointIntegrals

/-!
# Eta path comparison across different original disks

A common transverse path in the convex intersection of two original disks
has the prescribed terminal root and integrable actual and model forms.
Comparing each given path to this common path gives an integer 2π period
without requiring either disk to contain the other.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Two original disks have a common normalized integrable Dirichlet path. -/
theorem original_dirichlet_common_integral_path (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (P P' : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (hμ' : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P'.center:ℂ) P'.radius) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P'.center:ℂ) P'.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
        Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ ∧
        CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ := by
  let S := ball (P.center:ℂ) P.radius ∩ ball (P'.center:ℂ) P'.radius
  obtain ⟨Q,γ,hQ,hγ,hnorm,hmem,k,hk,hsep⟩ := P.exists_admissible_path_root_in_open_convex
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) S (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)) (fun _ h => h.1)
    ⟨P.gap (left_mem_segment ℝ _ _),P'.gap (left_mem_segment ℝ _ _)⟩ ⟨hμ,hμ'⟩
    _ (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m)
  have hQ' : SourceAngularAdmissiblePathRootData hp hp1 m ψ (P'.center:ℂ) P'.radius Q γ :=
    ⟨hQ.continuous_root,hQ.square_root,fun t ht =>
      ⟨(hmem t (Ioo_subset_Icc_self ht)).2,(hQ.interior t ht).2⟩⟩
  obtain ⟨ha,hm⟩ := hQ.transverse_actual_and_model_curveIntegrable P γ
    (H.angular_endpoint_data ψ hψ m) hμ hgap hγ k hk hsep s
  exact ⟨Q,γ,hQ,hQ',hγ,hnorm,ha m,hm⟩

/-- Every normalized integrable original-disk eta path has the same class modulo 2π,
including when the paths use different disks or end at a periodic endpoint. -/
theorem eta_original_dirichlet_path_periods_across_circles
    (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (P P' : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (hμ' : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P'.center:ℂ) P'.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
    let w := sourceAntiDiscriminantCandidate hp hp1 ψ μ
    ∀ Q Q' : ℂ × CoeffPair p → ℂ,
    ∀ γ κ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) μ,
      SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ →
      SourceAngularAdmissiblePathRootData hp hp1 m ψ (P'.center:ℂ) P'.radius Q' κ →
      (w ≠ 0 → Q (μ,ψ) = w) → (w ≠ 0 → Q' (μ,ψ) = w) →
      ContDiffOn ℝ 1 γ.extend (Icc 0 1) → ContDiffOn ℝ 1 κ.extend (Icc 0 1) →
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ →
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q' (z,ψ))) κ →
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ →
      CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q')) κ →
      ∃ k : ℤ, sourceAngularPathIntegral m s Q ψ γ-sourceAngularPathIntegral m s Q' ψ κ =
        k*(2*Real.pi) := by
  intro μ w Q Q' γ κ hQ hQ' hnorm hnorm' hγ hκ hi hi' hm hm'
  obtain ⟨Q₀,γ₀,hQ₀,hQ₀',hγ₀,hnorm₀,hi₀,hm₀⟩ :=
    H.original_dirichlet_common_integral_path ψ hψ m P P' hgap hμ hμ'
  obtain ⟨k,hk⟩ := H.eta_original_dirichlet_path_periods ψ hψ m P hgap hμ
    Q Q₀ γ γ₀ hQ hQ₀ hnorm (fun _ => hnorm₀) hγ hγ₀ hi hi₀ hm hm₀
  obtain ⟨l,hl⟩ := H.eta_original_dirichlet_path_periods ψ hψ m P' hgap hμ'
    Q' Q₀ κ γ₀ hQ' hQ₀' hnorm' (fun _ => hnorm₀) hκ hγ₀ hi' hi₀ hm' hm₀
  refine ⟨k-l,?_⟩
  push_cast
  linear_combination hk-hl

end SourceLemma12_12Data
end NLS.ZakharovShabat
