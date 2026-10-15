import NLS.ZakharovShabat.SourceSection13OriginalDomain
import NLS.ZakharovShabat.SourceAngularBeta

/-!
# Actual beta values on the retained complex domain

The original-disk primitives give a unique beta value at every complex
source, including collapsed gaps and periodic Dirichlet terminals. Every
integrable admissible path with the prescribed terminal sheet evaluates
to this value. Curve integrability remains explicit for open gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual Dirichlet sheet has a normalized primitive on each original disk. -/
theorem beta_original_dirichlet_primitive (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius)
    (hw : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0) :
    ∃ F : ℂ → ℂ, ∃ A : ℂ, ∃ E : ℂ → ℂ,
      SourceAngularDirichletPrimitiveData hp hp1 n m s ψ (P.center:ℂ) P.radius F A E := by
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
  obtain ⟨F,A,E,hE⟩ := H.angular_original_sheet_primitive_all_gaps ψ hψ n m hmn P _ hw
  exact ⟨F,A,E,⟨P.gap,hw,hE,⟨hμ,hbase.1⟩,hbase.2⟩⟩

/-- The primitive definition gives exactly one beta value throughout the original W. -/
theorem beta_original_value_unique (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n) :
    ∃! b : ℂ, b ∈ sourceAngularBetaValues hp hp1 n m s ψ := by
  classical
  by_cases hend : SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ m
  · simpa only [sourceAngularBetaValues,if_pos hend,mem_singleton_iff] using
      (show ∃! b : ℂ, b = 0 from ⟨0,rfl,fun _ h => h⟩)
  · obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
    have hleft : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m :=
      fun h => hend (Or.inl h)
    have hright : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ≠
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m :=
      fun h => hend (Or.inr h)
    have hw := sourceDirichletAntiDiscriminant_ne_zero_of_mem_omittedDomain hp hp1 ψ m
      ((P m).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ m))) hleft hright
    obtain ⟨F,A,E,hE⟩ := H.beta_original_dirichlet_primitive ψ hψ n m hmn (P m) (hμ m) hw
    simp only [sourceAngularBetaValues,if_neg hend]
    refine ⟨E (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),⟨_,_,F,A,E,hE,rfl⟩,?_⟩
    rintro b ⟨d,R,G,B,J,hJ,hb⟩
    exact hb.symm.trans (hJ.terminal_eq hE)

/-- The chosen beta is a value of an actual normalized primitive. -/
theorem beta_original_mem_values (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n) :
    sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ :=
  Classical.epsilon_spec (H.beta_original_value_unique ψ hψ n m hmn).exists

/-- Every integrable admissible path computes the original-domain beta value. -/
theorem beta_original_pathIntegral_eq_value (H : SourceLemma12_12Data hp hp1 W₀ W s)
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
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hint : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ) :
    sourceAngularPathIntegral n s Q ψ γ = sourceAngularBeta hp hp1 n m s ψ := by
  by_cases hw : sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0
  · obtain ⟨F,A,E,hE⟩ := H.beta_original_dirichlet_primitive ψ hψ n m hmn P hμ hw
    exact (hE.primitive.admissible_pathIntegral_eq_value P.closedBall_subset_omittedDomain hw
      hE.terminal_mem Q γ hQ ((hnorm hw).trans hE.terminal_sheet_value.symm) hγ hint).trans
        hE.beta_eq_terminal.symm
  · have hend := sourceDirichletRoot_mem_periodicEndpoints_of_antiDiscriminant_eq_zero hp hp1 ψ m
      (P.closedBall_subset_omittedDomain (ball_subset_closedBall hμ)) (not_ne_iff.mp hw)
    rw [H.beta_original_periodic_terminal_zero ψ hψ n m hmn P hend Q γ hQ hγ hint]
    exact (sourceAngularBeta_eq_zero_of_endpoint hp hp1 n m s ψ
      (by simpa only [SourceAngularDirichletTerminalIsEndpoint,mem_insert_iff,mem_singleton_iff] using hend)).symm

end SourceLemma12_12Data
end NLS.ZakharovShabat
