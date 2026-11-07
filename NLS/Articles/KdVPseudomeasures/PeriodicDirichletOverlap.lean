import NLS.Articles.KdVPseudomeasures.EndpointDirichletProjectionConvergence
import NLS.Articles.KdVPseudomeasures.PeriodicDirichletBoundaryVector
import NLS.Articles.KdVPseudomeasures.PeriodicEndpointProjectionConvergence
import NLS.KdV.PeriodicDirichletProjectionError

/-! Source overlap (32) for ACTUAL normalized boundary-zero spectral
vectors and their identical native interval restrictions. All source norm
ball cutoffs precede the potential, index, vectors and normalized generator. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ZakharovShabat

/-- Every normalized zero-boundary vector in the ENTIRE actual high
periodic spectral range has interval projection error less than one half.
This includes complex associated vectors and every faithful native interval
restriction; neither projection convergence nor an overlap is a premise. -/
theorem exists_uniform_sourcePeriodicDirichlet_projection_error
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
      ∀ G : FourierLebesgueSpace (2:ℝ) 1 2, ∀ g : UnitDirichletH1,
        ‖singularHillL2DomainInclusion G‖ = 1 → ‖unitDirichletL2Inclusion g‖ = 1 →
        singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
          (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range →
        singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ)) = 0 →
        (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
          singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) →
        ‖originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n
          (unitDirichletL2Inclusion g)-unitDirichletL2Inclusion g‖ < 1/2 := by
  obtain ⟨NP,hNP,hP⟩ := exists_uniform_sourceEndpointPeriodicProjection_sub_free_small r hr R
    (epsilon := 1/16) (by norm_num)
  obtain ⟨ND,_,hD⟩ := exists_uniform_sourceEndpointDirichletProjection_sub_free_small r hr R
    (epsilon := 1/16) (by norm_num)
  obtain ⟨NC,_,hC⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  obtain ⟨NF,_,hF⟩ := exists_periodicDirichlet_projection_error_bound
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨NL,hNL⟩ := eventually_atTop.mp (hl.eventually_gt_atTop (1:ℝ))
  let N := max Nmin (max NP (max ND (max NC (max (NF+1) NL))))
  refine ⟨N,by dsimp [N];omega,by dsimp [N];omega,?_⟩
  intro q hq hp n hn G g hGn hgn hG hG0 hsame
  have hnP : NP ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnD : ND ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnC : NC ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnF : NF < (n:ℕ) := by dsimp [N] at hn;omega
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hc := (hC q hq n hnC).1
  have hfixed := singularHillContinuousRieszProjection_fixed_of_physical_range _ _ _
    (by exact_mod_cast n.property) hc G hG
  have hfree : singularHillContinuousRieszProjection 0 (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) =
      hillFreeContinuousModeProjection (n:ℕ) := by
    rw [← freeHillValue_natCast_complex]
    exact hillContinuousRieszProjection_zero_eq_modes (n:ℕ) n.property (hNL (n:ℕ) hnL)
  have happrox : ‖singularHillContinuousDomainInclusion G-
      hillFreeContinuousModeProjection (n:ℕ) (singularHillL2DomainInclusion G)‖ < 1/16 := by
    have he := (singularHillContinuousRieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-singularHillContinuousRieszProjection 0
        (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).le_opNorm (singularHillL2DomainInclusion G)
    rw [sub_apply,hfixed,hfree,hGn,mul_one] at he
    have hp := (hP q hq n hnP).1
    rw [hfree] at hp
    exact he.trans_lt hp
  have hrestrict : circleUnitContinuousRestriction (singularHillContinuousDomainInclusion G) =
      unitDirichletContinuousInclusion g := by
    apply ContinuousMap.ext
    intro x
    exact (hsame x.val x.property).symm
  have hb := hF n hnF (sourceComplexHminusOne r hr q)
    (singularHillContinuousDomainInclusion G) (singularHillL2DomainInclusion G) hG0
  dsimp only at hb
  rw [hrestrict,unitIntervalContinuousToLp_two_dirichlet,hgn] at hb
  have hd := (hD q hq hp n hnD).2.2
  change ‖singularDirichletL2RieszProjection (sourceComplexHminusOne r hr q)
    (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)-singularDirichletL2RieszProjection 0
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)‖ < 1/16 at hd
  change ‖singularDirichletL2RieszProjection (sourceComplexHminusOne r hr q)
    (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) (unitDirichletL2Inclusion g)-unitDirichletL2Inclusion g‖ < 1/2
  linarith

/-- Source (32), with its exact final constants, for ANY normalized actual
Dirichlet eigenfunction and ANY unit zero-boundary periodic spectral vector.
The full complex operator domains and the same physical interval are used. -/
theorem exists_uniform_sourcePeriodicDirichlet_overlap
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
      ∀ G : FourierLebesgueSpace (2:ℝ) 1 2, ∀ g : UnitDirichletH1,
        ‖singularHillL2DomainInclusion G‖ = 1 → ‖unitDirichletL2Inclusion g‖ = 1 →
        singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
          (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range →
        singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ)) = 0 →
        (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
          singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) →
      ∀ v : UnitDirichletH1,
        singularDirichletOperator (sourceComplexHminusOne r hr q) v =
          originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) n •
            singularDirichletDomainInclusion v →
        ‖unitDirichletL2Inclusion v‖ = 1 →
        ∃ nu : ℂ, originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n
          (unitDirichletL2Inclusion g) = nu • unitDirichletL2Inclusion v ∧
          (1/2:ℝ) ≤ ‖nu‖ ∧ ‖nu‖ ≤ 3/2 := by
  obtain ⟨NE,hNE,hmin,herror⟩ := exists_uniform_sourcePeriodicDirichlet_projection_error r hr R Nmin
  obtain ⟨NC,_,hcircles⟩ := exists_uniform_sourceEndpointDirichlet_sourceCircles r hr R
  refine ⟨max NE NC,hNE.trans (le_max_left _ _),hmin.trans (le_max_left _ _),?_⟩
  intro q hq hp n hn G g hGn hgn hG hG0 hsame v hv hvn
  let a := sourceOriginalComplexPotential r hr q hp
  obtain ⟨hc,hl,hiso,hm⟩ := hcircles q hq hp n ((le_max_right _ _).trans hn)
  have honly (z : ℂ) (hz : z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
      (hs : z ∈ singularDirichletSpectrum a.val) : z = originalComplexDirichletLabels a n :=
    (hiso z (ball_subset_closedBall hz)).mp hs
  obtain ⟨nu,hnu,_⟩ := exists_singularDirichletL2Riesz_amplitude_bound a.val _ _
    (by exact_mod_cast n.property) hc _ hl honly hm v hv hvn (unitDirichletL2Inclusion g)
  have he := herror q hq hp n ((le_max_left _ _).trans hn) G g hGn hgn hG hG0 hsame
  change ‖singularDirichletL2RieszProjection a.val _ _ (unitDirichletL2Inclusion g)-
    unitDirichletL2Inclusion g‖ < 1/2 at he
  rw [hnu] at he
  have hu := norm_sub_norm_le (nu • unitDirichletL2Inclusion v) (unitDirichletL2Inclusion g)
  have hd := norm_sub_norm_le (unitDirichletL2Inclusion g) (nu • unitDirichletL2Inclusion v)
  rw [norm_smul,hvn,hgn,mul_one] at hu hd
  rw [norm_sub_rev] at hd
  exact ⟨nu,hnu,by linarith,by linarith⟩

/-- Actual boundary vectors with the source overlap exist at one common
original endpoint ball cutoff. The SAME stronger original distribution and
the exact physical norm one in both intervals are retained. -/
theorem exists_uniform_source_boundaryVector_with_Dirichlet_overlap
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ n : ℕ+, N ≤ (n:ℕ) →
      ∃ G : FourierLebesgueSpace (2:ℝ) 1 2, ∃ g : UnitDirichletH1,
        ‖singularHillL2DomainInclusion G‖ = 1 ∧ ‖unitDirichletL2Inclusion g‖ = 1 ∧
        singularHillL2DomainInclusion G ∈ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
          (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range ∧
        singularHillContinuousDomainInclusion G (0 : AddCircle (2:ℝ)) = 0 ∧
        singularHillContinuousDomainInclusion G ((1:ℝ) : AddCircle (2:ℝ)) = 0 ∧
        (∀ x ∈ Icc (0:ℝ) 1, unitDirichletRepresentative g x =
          singularHillContinuousDomainInclusion G (x : AddCircle (2:ℝ))) ∧
        (∃ u : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val = G.val) ∧
        ∀ v : UnitDirichletH1,
          singularDirichletOperator (sourceComplexHminusOne r hr q) v =
            originalComplexDirichletLabels (sourceOriginalComplexPotential r hr q hp) n •
              singularDirichletDomainInclusion v →
          ‖unitDirichletL2Inclusion v‖ = 1 →
          ∃ nu : ℂ, originalDirichletRieszProjection (sourceOriginalComplexPotential r hr q hp) n
            (unitDirichletL2Inclusion g) = nu • unitDirichletL2Inclusion v ∧
            (1/2:ℝ) ≤ ‖nu‖ ∧ ‖nu‖ ≤ 3/2 := by
  obtain ⟨NO,hNO,hmin,hO⟩ := exists_uniform_sourcePeriodicDirichlet_overlap r hr R Nmin
  obtain ⟨N,hN,hON,hB⟩ := exists_uniform_sourcePeriodicDirichletBoundaryVector r hr R NO
  refine ⟨N,hN,hmin.trans hON,?_⟩
  intro q hq hp n hn
  obtain ⟨G,g,hGn,hgn,hG,hG0,hG1,_,hsame,hstrong⟩ := hB q hq hp n hn
  exact ⟨G,g,hGn,hgn,hG,hG0,hG1,hsame,hstrong,
    hO q hq hp n (hON.trans hn) G g hGn hgn hG hG0 hsame⟩

end NLS.Articles.KdVPseudomeasures
