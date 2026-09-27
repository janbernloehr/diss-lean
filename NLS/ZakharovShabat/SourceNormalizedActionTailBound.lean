import NLS.ZakharovShabat.SourceNormalizedActionEstimate
import NLS.ZakharovShabat.SourceSingleRootQuotientTailLimit
import NLS.ZakharovShabat.SourceTailIsolation
import NLS.ZakharovShabat.CriticalMidpointOffset

/-!
# Product-tail control on the normalized action path

The complementary factor in the normalized action is the deleted
single-root quotient product. A tail estimate for that product is
already available on isolating discs. This file transports the bound
to every point of the cosine-parametrized selected gap, locally
uniformly in the source and for all sufficiently large indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit product-tail majorant for the complementary factor. -/
def sourceNormalizedActionFactorTailMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (C : ℝ) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  Real.exp (C *
      ‖canonicalCriticalMidpointOffset hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ)‖ *
        ‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ +
      (C^2/2) * ∑' m : ℤ,
        sourceSquaredGapReciprocalTerm hp hp1 ψ n m) - 1

/-- Near every real-type source, the complementary factor is bounded
along each entire selected gap by the deleted-product tail majorant
for all sufficiently large signed indices. -/
theorem exists_local_sourceNormalizedAction_factor_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
        ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
          ∀ θ : ℝ,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n +
                sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)) - 1‖ ≤
              sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
  obtain ⟨N,ε,hε,hεmax,V₁,hV₁open,_,hφV₁,C,hC,K₁,hbound⟩ :=
    exists_local_uniform_sourceSingleRootQuotientJointProduct_tail_bound
      hp hp1 hp φ hφ
  obtain ⟨N₂,V₂,hV₂open,hφV₂,htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  let V := V₁ ∩ V₂
  let K := max K₁ (max (N+1) (N₂+1))
  refine ⟨V,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,C,hC,K,?_⟩
  intro ψ hψ n hn θ
  have hK₁ : K₁ ≤ n.natAbs := by dsimp [K] at hn; omega
  have hN : N < n.natAbs := by dsimp [K] at hn; omega
  have hN₂ : N₂ < n.natAbs := by dsimp [K] at hn; omega
  let z := sourceStandardRootMidpoint hp hp1 ψ n +
    sourceStandardRootHalfGap hp hp1 ψ n * (Real.cos θ:ℂ)
  have hend := htail ψ hψ.2 n hN₂
  have hconv : Convex ℝ (refinedResonantDisk n) := by
    unfold refinedResonantDisk
    exact convex_ball _ _
  have hsegment : sourcePeriodicSegment hp hp1 ψ n ⊆
      refinedResonantDisk n := by
    change segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) ⊆ refinedResonantDisk n
    exact hconv.segment_subset hend.1 hend.2.1
  have hzseg : z ∈ sourcePeriodicSegment hp hp1 ψ n :=
    sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n (Real.cos θ)
      (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
  have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    simpa [sourceIsolatingDisc, not_le.mpr hN] using hsegment hzseg
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let α : Coeff p := canonicalCriticalMidpointOffset hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m := by
    simp only [a,α,displacedRoots,canonicalCriticalDisplacement_apply,
      canonicalCriticalMidpointOffset_apply]
    ring
  have hproduct := hbound ψ hψ.1 n hK₁ a α hα z hzdisc
  have hfactor : I * sourceCriticalRootRatioExtension hp hp1 n ψ z =
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by
    change I * (-I *
      sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) = _
    calc
      I * (-I * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) =
          -(I^2) * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by ring
      _ = _ := by simp [Complex.I_sq]
  change ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤ _
  rw [hfactor]
  exact hproduct

/-- The action quotient itself satisfies the explicit product-tail
estimate on every sufficiently distant open real-type gap in one
neighborhood of a real-type base source. -/
theorem exists_local_sourceRawNormalizedAction_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
        ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
          ∀ n : ℤ, K ≤ n.natAbs →
            (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) n).re <
              (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) n).re →
            ‖4 * sourceRawNormalizedAction hp hp1 n ψ - 1‖ ≤
              8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 +
              2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 *
                  sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
  obtain ⟨V,hVopen,hφV,C,hC,K,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_tail_bound hp hp1 φ hφ
  refine ⟨V,hVopen,hφV,C,hC,K,?_⟩
  intro ψ hψ hreal n hn hopen
  exact norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
    hp hp1 ψ hreal n hopen
    (sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n)
    (hfactor ψ hψ n hn)

end NLS.ZakharovShabat
