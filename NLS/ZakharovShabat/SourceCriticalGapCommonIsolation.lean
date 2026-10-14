import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceStandardRootOmittedCommonDomain
import NLS.ZakharovShabat.CriticalOffsetCoefficientCollapsedGap

/-!
# Critical midpoint coefficients on the original common isolating family

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
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

/-- In a disjoint source isolating family, a collapsed periodic pair
has its indexed canonical critical root at the common endpoint. -/
theorem SourceIsolatingNeighborhoods.criticalPoint_eq_of_collapsedGap
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
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
    have han : a ∈ D n :=
      h.cluster ψ hψ n (Or.inl rfl)
    have ham : a ∈ D m := by
      rw [← hm]
      exact h.cluster ψ hψ m (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    exact Set.disjoint_left.mp (h.disjoint n m (Ne.symm hne)) han ham
  subst m
  exact hm

/-- The coefficient of the exact critical midpoint identity is
nonzero for every index of a complex source with disjoint clusters. -/
theorem SourceIsolatingNeighborhoods.criticalOffsetCoefficient_ne_zero
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (n : ℤ) :
    canonicalCriticalOffsetCoefficient hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 := by
  let v := periodOnePotential ψ
  let hv := periodOnePotential_mem ψ
  let c := canonicalCriticalPoints hp hp1 v hv n
  have hcdisc : c ∈ D n :=
    h.cluster ψ hψ n (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have hprod : canonicalDeletedPeriodicProduct hp hp1 v hv n c ≠ 0 :=
    canonicalDeletedPeriodicProduct_ne_zero_on_sourceOmittedDomain
      hp hp1 ψ n c (h.disk_subset_omittedDomain ψ hψ n hcdisc)
  by_cases hgap : canonicalPeriodicGap hp hp1 v hv n = 0
  · have hcollapsed : canonicalPeriodicLeft hp hp1 v hv n =
        canonicalPeriodicRight hp hp1 v hv n := by
      unfold canonicalPeriodicGap at hgap
      exact (sub_eq_zero.mp hgap).symm
    have hc := h.criticalPoint_eq_of_collapsedGap ψ hψ n hcollapsed
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
theorem SourceIsolatingNeighborhoods.criticalPoints_midpoint_gap_sq
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
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
      (h.criticalOffsetCoefficient_ne_zero ψ hψ n)

end NLS.ZakharovShabat
