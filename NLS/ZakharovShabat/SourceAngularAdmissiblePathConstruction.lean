import NLS.ComplexAnalysis.QuadraticBezierAdmissible
import NLS.ComplexAnalysis.CanonicalRootPathExtension
import NLS.ZakharovShabat.SourceAngularOriginalBetaValues

/-!
# Constructed admissible paths and continued angular roots

Every original disk contains a smooth path from its left periodic
endpoint to any terminal in the disk, with interior avoiding the gap.
A continuously continued root takes any prescribed valid terminal value.
The paths have a quantitative transverse bound at both periodic endpoints,
including when the terminal is periodic or the selected gap collapses.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An open convex subset of an original disk admits a smooth path with a prescribed root. -/
theorem SourceCriticalRootPeriodCircle.exists_admissible_path_root_in_open_convex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) (b : ℂ)
    (S : Set ℂ) (hS : IsOpen S) (hconv : Convex ℝ S)
    (hsub : S ⊆ ball (P.center:ℂ) P.radius)
    (ha : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ∈ S)
    (hb : b ∈ S) (w : ℂ)
    (hw : sourceAngularRadicand hp (b,ψ) = w^2) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b,
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧ Q (b,ψ) = w ∧
        (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ S) ∧
        ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t*(1-t) ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ ∧
          k*t*(1-t) ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  obtain ⟨γ,hγ,hmem,k,hk,hsep⟩ :=
    exists_bezier_admissible_path_in_open_convex a r b S hS hconv ha hb
  have hball (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) := hsub (hmem t ht)
  let F : ℂ → ℂ := fun z => sourceAngularRadicand hp (z,ψ)
  have hF : AnalyticOnNhd ℂ F univ := by
    intro z _
    exact (analyticOnNhd_sourceAngularRadicand hp hp1 (z,ψ) (mem_univ _)).comp
      (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)
  have ha : a ∉ sourceCanonicalRootDomain hp hp1 ψ :=
    fun h => h m (left_mem_segment ℝ _ _)
  have hFa : F a = 0 := by
    dsimp only [F,sourceAngularRadicand,a]
    rw [canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem ψ) m]
    simp
  have hγD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ := by
    intro j
    by_cases hj : j = m
    · subst j; exact (hsep t ht).1
    · exact P.closedBall_subset_omittedDomain (ball_subset_closedBall (hball t (Ioo_subset_Icc_self ht))) j hj
  obtain ⟨q,hq,hsq,_,hqb,_⟩ := exists_continuous_canonical_path_root F
    (sourceCanonicalRoot hp hp1 ψ) (sourceCanonicalRootDomain hp hp1 ψ) hF
    (sourceCanonicalRoot_analyticOnNhd hp hp1 ψ).continuousOn
    (fun z hz => sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 ψ z hz)
    γ ha hFa hγD w hw
  let Q : ℂ × CoeffPair p → ℂ := fun u => q u.1
  refine ⟨Q,γ,?_,hγ,hqb,hmem,k,hk,fun t ht => (hsep t ht).2⟩
  apply sourceAngularAdmissiblePathRootData_of_continuousOn hp hp1 m ψ _ _ Q γ hq hsq
  exact fun t ht => ⟨hball t (Ioo_subset_Icc_self ht),(hsep t ht).1⟩

/-- An original disk admits an actual smooth path with a prescribed continued root. -/
theorem SourceCriticalRootPeriodCircle.exists_admissible_path_root
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) (b : ℂ)
    (hb : b ∈ ball (P.center:ℂ) P.radius) (w : ℂ)
    (hw : sourceAngularRadicand hp (b,ψ) = w^2) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m) b,
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧ Q (b,ψ) = w ∧
        (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ ball (P.center:ℂ) P.radius) ∧
        ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t*(1-t) ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ ∧
          k*t*(1-t) ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ :=
  P.exists_admissible_path_root_in_open_convex b (ball (P.center:ℂ) P.radius)
    isOpen_ball (convex_ball _ _) (Subset.refl _) (P.gap (left_mem_segment ℝ _ _)) hb w hw

/-- The actual anti-discriminant supplies the terminal normalization, including zero values. -/
theorem SourceCriticalRootPeriodCircle.exists_dirichlet_admissible_path_root
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {m : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
        Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ ball (P.center:ℂ) P.radius) ∧
        ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
          k*t*(1-t) ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ ∧
          k*t*(1-t) ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-γ.extend t‖ :=
  P.exists_admissible_path_root _ hμ _
    (sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ m)

end NLS.ZakharovShabat
