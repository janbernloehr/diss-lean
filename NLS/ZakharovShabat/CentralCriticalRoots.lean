import NLS.ZakharovShabat.DiscriminantCriticalDistribution
import NLS.SequenceSpaces.FiniteEnumeration

/-!
# Central critical points with their analytic multiplicities

The central analytic count gives exactly one slot per free index in [-N,N].
The enumeration retains all repeated roots and has a uniform displacement
bound determined only by the central radius and cutoff.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Critical-point multiplicities have finite support in the central disc. -/
theorem hasFiniteSupport_centralCriticalOrder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) :
    (fun z : ℂ => if z ∈ closedBall 0 (centralCircleRadius N) then
      analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z else 0).HasFiniteSupport :=
  (finite_discriminant_criticalPoints_of_isCompact hp hp1 φ hφ
    (isCompact_closedBall 0 (centralCircleRadius N))).subset (analyticZeroCount_support_subset _ _)

/-- The actual central critical roots, with each analytic multiplicity retained. -/
def centralCriticalRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) : Multiset ℂ :=
  analyticZeroMultiset (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius N))
    (hasFiniteSupport_centralCriticalOrder hp hp1 φ hφ N)

/-- The cardinality is exactly the central analytic zero count. -/
theorem card_centralCriticalRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) :
    (centralCriticalRoots hp hp1 φ hφ N).card =
      analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius N)) :=
  card_analyticZeroMultiset _ _ _

/-- Every point occurs with exactly its analytic order in the central disc. -/
theorem count_centralCriticalRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (z : ℂ) :
    (centralCriticalRoots hp hp1 φ hφ N).count z =
      if z ∈ closedBall 0 (centralCircleRadius N) then analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z else 0 :=
  count_analyticZeroMultiset _ _ _ z

/-- The multiset contains precisely the actual central critical points. -/
theorem mem_centralCriticalRoots (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (z : ℂ) :
    z ∈ centralCriticalRoots hp hp1 φ hφ N ↔
      z ∈ closedBall 0 (centralCircleRadius N) ∧ deriv (canonicalDiscriminant hp φ) z = 0 := by
  constructor
  · exact mem_analyticZeroMultiset_imp _ _ _
  · rintro ⟨hz, hz0⟩
    apply Multiset.count_pos.mp
    rw [count_centralCriticalRoots, if_pos hz]
    exact analyticOrderNatAt_pos_of_zero (analyticOnNhd_discriminant_derivative hp hp1 φ hφ z (mem_univ _))
      (analyticOrderAt_discriminant_derivative_ne_top hp hp1 φ hφ z) hz0

/-- A count of 2N+1 labels all central roots on [-N,N], retaining multiplicities. -/
theorem exists_centralCriticalLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ)
    (hc : analyticZeroCount (deriv (canonicalDiscriminant hp φ)) (closedBall 0 (centralCircleRadius N)) = 2*N+1) :
    ∃ ξ : ℤ → ℂ, (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N := by
  apply NLS.exists_finset_multiset_enumeration
  rw [card_centralCriticalRoots, hc, Int.card_Icc]
  omega

/-- Each central label has a cutoff-only displacement bound. -/
theorem norm_centralCriticalLabel_displacement_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (ξ : ℤ → ℂ)
    (hξ : (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n} : Multiset ℂ)) = centralCriticalRoots hp hp1 φ hφ N)
    (n : ℤ) (hn : n.natAbs ≤ N) :
    ‖ξ n-(Real.pi : ℂ)*n‖ ≤ centralCircleRadius N+Real.pi*N := by
  have hns : n ∈ Finset.Icc (-(N : ℤ)) N := by simp only [Finset.mem_Icc]; omega
  have hmem : ξ n ∈ centralCriticalRoots hp hp1 φ hφ N := by
    rw [← hξ]
    simp only [Multiset.mem_sum, Multiset.mem_singleton]
    exact ⟨n, hns, rfl⟩
  have hz : ‖ξ n‖ ≤ centralCircleRadius N := by simpa using ((mem_centralCriticalRoots hp hp1 φ hφ N _).mp hmem).1
  have hf : ‖(Real.pi : ℂ)*n‖ ≤ Real.pi*N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast hn
  exact (norm_sub_le _ _).trans (add_le_add hz hf)

end NLS.ZakharovShabat
