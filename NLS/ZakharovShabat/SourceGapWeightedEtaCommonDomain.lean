import NLS.ZakharovShabat.SourceGapWeightedEtaAngle

/-! # A common analytic domain for all gap-weighted eta coordinates

The actual normalized psi family and annular charts supply one complex
neighborhood of the whole real source locus on which every signed
coordinate is analytic, including at collapsed gaps. The index-uniform
estimate of Lemma 15.1 is a separate remaining assertion.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real collapsed gaps give zero for both coordinates. At complex
collapsed gaps only their product must vanish, so real type is essential. -/
theorem sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (σ : ℂ) : sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ = 0 := by
  have hτ := sourceDirichletRoot_eq_midpoint_of_real_collapsed_gap hp hp1 ψ hreal n
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  change canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n =
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n at hτ
  have hs := sourceDirichletEtaSineNumerator_sq_add hp hp1 n ψ hμ
  rw [hτ, hgap, sub_self] at hs
  have hb : sourceDirichletEtaSineNumerator hp hp1 n ψ = 0 := sq_eq_zero_iff.mp (by simpa using hs)
  simp only [sourceGapWeightedEtaCoordinate, hτ, hb, sub_self, mul_zero, add_zero, zero_mul]

/-- The analyticity assertion in Lemma 15.1, on an actually constructed
common neighborhood, together with the exact product identity.
Uniform estimates and sequence-valued assembly are not asserted here. -/
theorem exists_sourceGapWeightedEta_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        (∀ n : ℤ, ∀ σ : ℂ, AnalyticOnNhd ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) W) ∧
        (∀ ψ ∈ W, ∀ n : ℤ,
          sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ * sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ =
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) ∧
        (∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ,
          canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
          ∀ σ : ℂ, sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ = 0) := by
  obtain ⟨W₀,B,W,_,_,_,_,_,_,hW,hWreal,hWB,s,D,hcharts⟩ :=
    exists_sourceAngular_eta_remainder_cauchy_common_domain hp hp1
  refine ⟨W₀,B,W,hW,hWreal,hWB,s,D,?_,?_,?_⟩
  · intro n σ φ hφ
    obtain ⟨V,c,T,r,R,z₀,ρ,hφV,hVW,hrρ,hρR,C,_⟩ := hcharts φ hφ n
    exact C.analyticOnNhd_gapWeightedEtaCoordinate ρ hrρ hρR
      ((D.roots_analytic .dirichlet n).mono (hVW.trans hWB))
      (fun ψ hψ => (D.symmetric_analytic ψ (hWB (hVW hψ)) n).1) σ φ hφV
  · intro ψ hψ n
    obtain ⟨V,c,T,r,R,z₀,ρ,hψV,_,_,_,C,_⟩ := hcharts ψ hψ n
    exact sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
      (((C.disc_family ψ hψV).contour_family.2 n).2.2.1
        (Metric.ball_subset_closedBall ((C.disc_family ψ hψV).dirichlet_mem_ball n)))
  · intro ψ hψ hreal n hgap σ
    obtain ⟨V,c,T,r,R,z₀,ρ,hψV,_,_,_,C,_⟩ := hcharts ψ hψ n
    exact sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap hp hp1 n s ψ hreal
      (((C.disc_family ψ hψV).contour_family.2 n).2.2.1
        (Metric.ball_subset_closedBall ((C.disc_family ψ hψV).dirichlet_mem_ball n))) hgap σ

end NLS.ZakharovShabat
