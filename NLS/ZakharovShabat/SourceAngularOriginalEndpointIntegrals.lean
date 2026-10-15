import NLS.ZakharovShabat.SourceAngularTransversePathIntegrability

/-!
# Constructed endpoint integrals throughout the original domain

The original disk supplies one smooth path and continuously continued
root normalized by the actual Dirichlet anti-discriminant. Every
off-diagonal angular integrand is integrable on that path and evaluates
to the unique analytic beta. At open gaps the diagonal integrand and its
eta model are also integrable. At collapsed gaps the original removable
extension supplies off-diagonal integrability.
-/

noncomputable section
open Set Metric Complex Filter Topology MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One constructed path in any original disk realizes every off-diagonal beta.
The eta and model integrals also exist whenever the selected gap is open. -/
theorem original_dirichlet_integral_path (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (m : ℤ)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
        Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        (∀ n : ℤ, m ≠ n →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ ∧
          sourceAngularPathIntegral n s Q ψ γ = sourceAngularBeta hp hp1 n m s ψ) ∧
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
            canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m →
          CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand m s Q (z,ψ))) γ ∧
          CurveIntegrable (holomorphicOneForm (sourceAngularEtaPathModelIntegrand hp hp1 m ψ Q)) γ) := by
  obtain ⟨Q,γ,hQ,hγ,hnorm,_,k,hk,hsep⟩ := P.exists_dirichlet_admissible_path_root hμ
  have hactual (n : ℤ) (hmn : m ≠ n) :
      CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ := by
    by_cases hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
    · exact (hQ.transverse_actual_and_model_curveIntegrable P γ (H.angular_endpoint_data ψ hψ m)
        hμ hgap hγ k hk hsep s).1 n
    · have he := not_ne_iff.mp hgap
      have hg : sourcePeriodicGapDisplacement hp hp1 ψ m = 0 := by
        simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,he,sub_self]
      exact H.beta_original_collapsed_curveIntegrable ψ hψ n m hmn P hg hμ Q γ hQ hγ
  refine ⟨Q,γ,hQ,hγ,hnorm,?_,?_⟩
  · intro n hmn
    exact ⟨hactual n hmn,H.beta_original_pathIntegral_eq_value ψ hψ n m hmn P hμ Q γ hQ
      (fun _ => hnorm) hγ (hactual n hmn)⟩
  · intro hgap
    obtain ⟨ha,hm⟩ := hQ.transverse_actual_and_model_curveIntegrable P γ (H.angular_endpoint_data ψ hψ m)
      hμ hgap hγ k hk hsep s
    exact ⟨ha m,hm⟩

/-- Every beta is a genuine improper integral along a constructed original-disk path.
Neither a path nor an integrability premise is supplied by the caller. -/
theorem beta_original_exists_improper_integral (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m ∈ ball (P.center:ℂ) P.radius) :
    ∃ Q : ℂ × CoeffPair p → ℂ,
      ∃ γ : Path (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m),
        SourceAngularAdmissiblePathRootData hp hp1 m ψ (P.center:ℂ) P.radius Q γ ∧
        ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
        Q (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m,ψ) =
          sourceAntiDiscriminantCandidate hp hp1 ψ (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ∧
        CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ ∧
        Tendsto (fun u : ℝ × ℝ => ∫ t in u.1..u.2,
          curveIntegralFun (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ t)
          ((𝓝[>] (0:ℝ)) ×ˢ (𝓝[<] (1:ℝ))) (𝓝 (sourceAngularBeta hp hp1 n m s ψ)) := by
  obtain ⟨Q,γ,hQ,hγ,hnorm,hint,_⟩ := H.original_dirichlet_integral_path ψ hψ m P hμ
  obtain ⟨hi,he⟩ := hint n hmn
  refine ⟨Q,γ,hQ,hγ,hnorm,hi,?_⟩
  have hl := tendsto_curveIntegral_truncations
    (holomorphicOneForm (fun z => sourceAngularIntegrand n s Q (z,ψ))) γ hi
  change Tendsto _ _ (𝓝 (sourceAngularPathIntegral n s Q ψ γ)) at hl
  rwa [he] at hl

end SourceLemma12_12Data
end NLS.ZakharovShabat
