import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.CriticalOffsetCoefficientCollapsedGap

/-!
# Critical midpoint coefficients on complex source isolating discs

The deleted periodic product is nonzero in the indexed isolating disc.
At a collapsed complex gap, the common endpoint is a critical point;
disjoint cluster discs identify it with that index's canonical
critical root. The quadratic offset coefficient is therefore nonzero
at every index throughout a local complex source neighborhood.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- In a disjoint source isolating family, a collapsed periodic pair
has its indexed canonical critical root at the common endpoint. -/
theorem sourceCriticalPoint_eq_of_collapsed_isolatingGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ)
    (hcollapsed : canonicalPeriodicLeft hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicRight hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) :
    canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicLeft hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  let a := canonicalPeriodicLeft hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hcrit : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) a = 0 :=
    canonicalPeriodicLeft_critical_of_eq_right hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n hcollapsed
  obtain ⟨m,hm⟩ :=
    (canonicalCriticalPoints_exhaustive hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) a).mp hcrit
  have hmn : m = n := by
    by_contra hne
    have han : a ∈ sourceIsolatingDisc hp hp1 φ N ε n :=
      hcluster n (Or.inl rfl)
    have ham : a ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
      rw [← hm]
      exact hcluster m (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hne)) han ham
  subst m
  exact hm

/-- The coefficient of the exact critical midpoint identity is
nonzero for every index of a complex source with disjoint clusters. -/
theorem sourceCriticalOffsetCoefficient_ne_zero_of_isolating
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    canonicalCriticalOffsetCoefficient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 := by
  let v := periodOnePotential ψ
  let hv := periodOnePotential_mem ψ
  let c := canonicalCriticalPoints hp hp1 v hv n
  have hcdisc : c ∈ sourceIsolatingDisc hp hp1 φ N ε n :=
    hcluster n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hprod : canonicalDeletedPeriodicProduct hp hp1 v hv n c ≠ 0 :=
    canonicalDeletedPeriodicProduct_ne_zero_on_sourceIsolatingDisc
      hp hp1 φ ψ N ε hcluster hdisjoint n c hcdisc
  by_cases hgap : canonicalPeriodicGap hp hp1 v hv n = 0
  · have hcollapsed : canonicalPeriodicLeft hp hp1 v hv n =
        canonicalPeriodicRight hp hp1 v hv n := by
      unfold canonicalPeriodicGap at hgap
      exact (sub_eq_zero.mp hgap).symm
    have hc := sourceCriticalPoint_eq_of_collapsed_isolatingGap
      hp hp1 φ ψ N ε hcluster hdisjoint n hcollapsed
    have hmid : canonicalPeriodicMidpoint hp hp1 v hv n =
        canonicalPeriodicLeft hp hp1 v hv n := by
      unfold canonicalPeriodicMidpoint
      rw [← hcollapsed]
      ring
    have hzero : canonicalCriticalMidpointOffset hp hp1 v hv n = 0 := by
      rw [canonicalCriticalMidpointOffset_apply]
      change canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n -
          canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) n = 0
      rw [hc, hmid]
      ring
    have hcoef : canonicalCriticalOffsetCoefficient hp hp1 v hv n =
        2*canonicalDeletedPeriodicProduct hp hp1 v hv n c := by
      simp only [canonicalCriticalOffsetCoefficient, hzero, zero_mul, add_zero]
      rfl
    rw [hcoef]
    exact mul_ne_zero (by norm_num) hprod
  · exact canonicalCriticalOffsetCoefficient_ne_zero_of_gap_and_product
      hp hp1 v hv n hgap hprod

/-- The exact squared-gap critical-root formula holds at every index
of a complex source in a disjoint isolating family. -/
theorem sourceCriticalPoints_midpoint_gap_sq_of_isolating
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (N : ℕ) (ε : ℝ)
    (hcluster : ∀ m : ℤ, sourceSpectralCluster hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ N ε m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ N ε i)
        (sourceIsolatingDisc hp hp1 φ N ε j))
    (n : ℤ) :
    canonicalCriticalPoints hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
      canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
        canonicalCriticalGapQuotient hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  simpa only [sourcePeriodicGapDisplacement_apply,
      canonicalCriticalMidpointOffset_apply, canonicalCriticalGapQuotient] using
    canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n
      (sourceCriticalOffsetCoefficient_ne_zero_of_isolating
        hp hp1 φ ψ N ε hcluster hdisjoint n)

/-- On the connected almost-real source domain, the critical
midpoint coefficient is nonzero and the exact squared-gap formula
holds at every signed index, including collapsed complex gaps. -/
theorem exists_global_sourceCriticalPoints_midpoint_gap_sq_exact
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        canonicalCriticalOffsetCoefficient hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 ∧
        canonicalCriticalPoints hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
          canonicalPeriodicMidpoint hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
          (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
            canonicalCriticalGapQuotient hp hp1
              (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  obtain ⟨W,hWopen,hWconn,hreal,hlocal⟩ :=
    exists_global_source_isolating_neighborhood hp hp1
  refine ⟨W,hWopen,hWconn,hreal,?_⟩
  intro ψ hψ n
  obtain ⟨V,_,_,hψV,_,φ,N,ε,_,_,hcluster,_,hdisjoint⟩ := hlocal ψ hψ
  exact ⟨sourceCriticalOffsetCoefficient_ne_zero_of_isolating
      hp hp1 φ ψ N ε (hcluster ψ hψV) hdisjoint n,
    sourceCriticalPoints_midpoint_gap_sq_of_isolating
      hp hp1 φ ψ N ε (hcluster ψ hψV) hdisjoint n⟩

end NLS.ZakharovShabat
