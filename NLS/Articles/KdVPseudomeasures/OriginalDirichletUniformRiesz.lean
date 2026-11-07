import NLS.Articles.KdVPseudomeasures.OriginalDirichletSourceCircles

/-! Actual simple Dirichlet projections on all sufficiently high literal
source circles, uniformly in the original complex H^-1 norm topology.
No validity, isolation, rank or projection hypotheses are supplied. -/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- On ONE open original H^-1 neighborhood, EVERY high source Pi_(n,q)
is the actual bounded physical L2 idempotent with exactly one normalized
native eigenfunction line as its FULL range. Its actual coefficient gives
the projected residual nu*(mu_n-lambda), uniformly at the same source indices.
This proves the contour/operator input to (31), without a quantitative C.4
comparison or the source overlap lower bound (32). -/
theorem exists_uniform_originalDirichletRiesz_normalized_range_and_residual
    (q : OriginalComplexHminusOnePotential) :
    ∃ N : ℕ, ∃ U : Set (FourierLebesgueSpace (2:ℝ) (-1) 2),
      0 < N ∧ IsOpen U ∧ q.val ∈ U ∧
      ∀ a : OriginalComplexHminusOnePotential, a.val ∈ U →
        ∀ n : ℕ+, N < (n:ℕ) →
          IsIdempotentElem (originalDirichletRieszProjection a n) ∧
          ∃ g : UnitDirichletH1,
            singularDirichletOperator a.val g =
              originalComplexDirichletLabels a n • singularDirichletDomainInclusion g ∧
            ‖unitDirichletL2Inclusion g‖ = 1 ∧
            (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
            (originalDirichletRieszProjection a n).range =
              Submodule.span ℂ {unitDirichletL2Inclusion g} ∧
            Module.finrank ℂ (originalDirichletRieszProjection a n).range = 1 ∧
            ∀ G : UnitDirichletH1, ∀ lambda : ℂ, ∃ nu : ℂ,
              originalDirichletRieszProjection a n (unitDirichletL2Inclusion G) =
                nu • unitDirichletL2Inclusion g ∧
              originalDirichletBaseRieszProjection a n
                (singularDirichletOperator a.val G-lambda • singularDirichletDomainInclusion G) =
                  (nu*(originalComplexDirichletLabels a n-lambda)) • singularDirichletDomainInclusion g ∧
              ‖nu‖ ≤ ‖originalDirichletRieszProjection a n‖*‖unitDirichletL2Inclusion G‖ := by
  obtain ⟨N,U,hN,hU,hq,_,hcircles⟩ :=
    exists_uniform_originalComplexDirichlet_sourceCircles q
  refine ⟨N,U,hN,hU,hq,?_⟩
  intro a ha n hn
  obtain ⟨hc,hl,hiso,hm⟩ := hcircles a ha n hn
  have honly (z : ℂ) (hz : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
      (hs : z ∈ singularDirichletSpectrum a.val) : z = originalComplexDirichletLabels a n :=
    (hiso z (ball_subset_closedBall hz)).mp hs
  obtain ⟨g,hg,hnorm,hint,hrange⟩ :=
    exists_originalDirichletRiesz_normalized_generator a n hc hl honly hm
  have hne : unitDirichletL2Inclusion g ≠ 0 := by
    intro he
    rw [he,norm_zero] at hnorm
    norm_num at hnorm
  refine ⟨isIdempotentElem_originalDirichletRieszProjection a n hc,
    g,hg,hnorm,hint,hrange,?_,?_⟩
  · rw [hrange]
    exact finrank_span_singleton hne
  · intro G lambda
    exact exists_originalDirichletRiesz_projected_residual_amplitude a n hc hl honly hm
      g hg hnorm G lambda

end NLS.Articles.KdVPseudomeasures
