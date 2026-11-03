import NLS.Articles.KdVPseudomeasures.OriginalPeriodicRiesz
import NLS.Articles.KdVPseudomeasures.SpectralComplexPairs
import NLS.KdV.PseudomeasureSourceCircles

/-! Uniform source periodic circles and actual physical rank two, on each
ball in the EXACT original complex endpoint norm. A single cutoff precedes
the potential and all later ORIGINAL positive indices. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual original H-minus-one distribution of a physically period-one
complex endpoint source, with no reality or mean-zero condition added. -/
def sourceOriginalComplexPotential (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) : OriginalComplexHminusOnePotential :=
  ⟨sourceComplexHminusOne r hr q,by rw [sourceComplexHminusOne_val];exact hp⟩

/-- The article adapter retains the entire original source distribution. -/
theorem sourceOriginalComplexPotential_distribution (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    (sourceOriginalComplexPotential r hr q hp).val.val = q.val :=
  sourceComplexHminusOne_val r hr q

/-- Any actual complex source pair supplies the literal source circle and
physical rank two, independently of which high-pair construction was used. -/
theorem SourceHillComplexPair.sourceCircle_rank_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ+) (p : SourceHillComplexPair r hr q n) :
    sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
      singularHillResolventSet (sourceComplexHminusOne r hr q) ∧
    Module.finrank ℂ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range = 2 := by
  have hc := p.sourceCircle_resolvent r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
  have hk := p.sourceCircle_physical_rank r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q) n.property
  change sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) ⊆ singularHillResolventSet
    (endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q)) at hc
  rw [sourceEndpointCoefficients_HminusOne_complex r hr q,freeHillValue_natCast_complex] at hc hk
  exact ⟨hc,hk⟩

/-- Every source-small high strip supplies the literal periodic resolvent
circle and ACTUAL physical L2 rank TWO, including coincident complex roots. -/
theorem sourcePeriodicCircle_rank_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (n : ℕ+)
    (hs : endpointHillConstant r*((n:ℕ):ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
      singularHillResolventSet (sourceComplexHminusOne r hr q) ∧
    Module.finrank ℂ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
      (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range = 2 :=
  SourceHillComplexPair.sourceCircle_rank_two r hr q n
    (sourceHillComplexPair r hr (n:ℕ) n.property q hs)

/-- ONE cutoff before EVERY original complex endpoint potential in the
specified original norm ball gives valid literal source circles and rank two. -/
theorem exists_uniform_sourcePeriodicCircle_rank_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
          singularHillResolventSet (sourceComplexHminusOne r hr q) ∧
        Module.finrank ℂ (singularHillL2RieszProjection (sourceComplexHminusOne r hr q)
          (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range = 2 := by
  obtain ⟨N,hN,hcut⟩ := exists_endpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn
  apply sourcePeriodicCircle_rank_two r hr q n
  exact (mul_le_mul_of_nonneg_left hq (mul_nonneg (endpointHillConstant_pos r hr.2).le
    (Real.rpow_nonneg (by positivity) _))).trans (hcut (n:ℕ) hn)

/-- The SAME literal periodic projection on physically period-one original
sources has rank TWO, uniformly on every original endpoint norm ball. -/
theorem exists_uniform_originalPeriodicCircle_rank_two (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
        ∀ n : ℕ+, N ≤ (n:ℕ) →
          sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆
            singularHillResolventSet (sourceOriginalComplexPotential r hr q hp).val ∧
          Module.finrank ℂ (originalPeriodicRieszProjection
            (sourceOriginalComplexPotential r hr q hp) n).range = 2 := by
  obtain ⟨N,hN,hcircle⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  exact ⟨N,hN,fun q hq hp n hn => hcircle q hq n hn⟩

end NLS.Articles.KdVPseudomeasures
