import NLS.ZakharovShabat.SourceGapWeightedEtaUniformBound
import NLS.ZakharovShabat.SourceGapWeightedEtaCommonDomain

/-! # Lemma 15.1 on a common complex neighborhood

The actual coordinates are analytic through collapsed gaps and have
the required locally uniform bound, uniformly in the gap index. The
union of the constructed neighborhoods transfers the bound from real
centers to every complex point of one common domain. The original
open-gap exponential formula is supplied by `SourceGapWeightedEtaAngle`.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Lemma 15.1: a common neighborhood carrying analytic coordinates
and a locally uniform estimate with one constant for every index and
both signs. The exact product and real collapsed-gap vanishing persist. -/
theorem exists_sourceGapWeightedEta_lemma15_1
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ B ∧
      ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
        SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s ∧
        (∀ n : ℤ, ∀ σ : ℂ, AnalyticOnNhd ℂ (sourceGapWeightedEtaCoordinate hp hp1 n s σ) W) ∧
        (∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
          ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n : ℤ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
            ‖sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ‖ ≤ C *
              (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ +
                ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
                  sourceStandardRootMidpoint hp hp1 ψ n‖)) ∧
        (∀ ψ ∈ W, ∀ n : ℤ,
          sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ * sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ =
            (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) ∧
        (∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ,
          canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 →
          ∀ σ : ℂ, sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ = 0) := by
  classical
  obtain ⟨W₀,B,V,_,_,_,hB,hBreal,hBW₀,hV,hVreal,hVB,s,D,hcharts⟩ :=
    exists_sourceAngular_eta_remainder_cauchy_common_domain hp hp1
  have hlocal (φ : realTypeSourceLocus p) :=
    D.exists_local_uniform_gapWeightedEtaCoordinate_bound hB hBW₀ φ.val (hBreal φ.property) φ.property
  choose U hU hφU _ C hC hbound using hlocal
  let W := ⋃ φ : realTypeSourceLocus p, U φ ∩ V
  have hW : IsOpen W := isOpen_iUnion (fun φ => (hU φ).inter hV)
  have hWV : W ⊆ V := iUnion_subset (fun _ => inter_subset_right)
  have hrealW : realTypeSourceLocus p ⊆ W := by
    intro φ hφ
    exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩,hVreal hφ⟩
  refine ⟨W₀,B,W,hW,hrealW,hWV.trans hVB,s,D,?_,?_,?_,?_⟩
  · intro n σ φ hφ
    obtain ⟨A,c,T,r,R,z₀,ρ,hφA,hAV,hrρ,hρR,E,_⟩ := hcharts φ (hWV hφ) n
    exact E.analyticOnNhd_gapWeightedEtaCoordinate ρ hrρ hρR
      ((D.roots_analytic .dirichlet n).mono (hAV.trans hVB))
      (fun ψ hψ => (D.symmetric_analytic ψ (hVB (hAV hψ)) n).1) σ φ hφA
  · intro φ hφ
    obtain ⟨a,ha⟩ := mem_iUnion.mp hφ
    exact ⟨U a ∩ W,(hU a).inter hW,⟨ha.1,hφ⟩,inter_subset_right,C a,hC a,
      fun ψ hψ n σ hσ => hbound a ψ hψ.1 n σ hσ⟩
  · intro ψ hψ n
    obtain ⟨A,c,T,r,R,z₀,ρ,hψA,_,_,_,E,_⟩ := hcharts ψ (hWV hψ) n
    exact sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
      (((E.disc_family ψ hψA).contour_family.2 n).2.2.1
        (ball_subset_closedBall ((E.disc_family ψ hψA).dirichlet_mem_ball n)))
  · intro ψ hψ hreal n hgap σ
    obtain ⟨A,c,T,r,R,z₀,ρ,hψA,_,_,_,E,_⟩ := hcharts ψ (hWV hψ) n
    exact sourceGapWeightedEtaCoordinate_eq_zero_of_real_collapsed_gap hp hp1 n s ψ hreal
      (((E.disc_family ψ hψA).contour_family.2 n).2.2.1
        (ball_subset_closedBall ((E.disc_family ψ hψA).dirichlet_mem_ball n))) hgap σ

end NLS.ZakharovShabat
