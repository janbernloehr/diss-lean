import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.ZakharovShabat.DiscriminantRolle

/-!
# Repeated complete endpoints and criticality

A coincident pair contributes two occurrences to the full central multiset
at a sufficiently large cutoff. Hence its original algebraic multiplicity
is at least two, also when the pair was initially distant.
-/

noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A collapsed pair in any complete labeling has original algebraic multiplicity at least two. -/
theorem PeriodicEndpointLabeling.multiplicity_ge_two_of_eq
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (n : ℤ) (he : ξ n = η n) :
    2 ≤ periodicAlgebraicMultiplicity hp φ (ξ n) := by
  let K := max N n.natAbs
  have hc := h.central_at_larger_cutoff K (le_max_left _ _)
  have hn : n.natAbs ≤ K := le_max_right _ _
  have hnmem : n ∈ Finset.Icc (-(K : ℤ)) K := by simp only [Finset.mem_Icc]; omega
  have hs := (hc.root_iff (ξ n)).mp ⟨n,hn,Or.inl rfl⟩
  have hpair : ({ξ n,η n} : Multiset ℂ).count (ξ n) = 2 := by rw [← he]; simp
  calc
    2 = ({ξ n,η n} : Multiset ℂ).count (ξ n) := hpair.symm
    _ ≤ ∑ i ∈ Finset.Icc (-(K : ℤ)) K, ({ξ i,η i} : Multiset ℂ).count (ξ n) :=
      Finset.single_le_sum (f := fun i => ({ξ i,η i} : Multiset ℂ).count (ξ n))
        (fun _ _ => Nat.zero_le _) hnmem
    _ = periodicAlgebraicMultiplicity hp φ (ξ n) := by rw [hc.count_eq,if_pos hs]

/-- A collapsed pair in an even potential is a discriminant critical point, without a real-type assumption. -/
theorem PeriodicEndpointLabeling.critical_of_eq
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p) (heven : φ ∈ pairParitySubspace 0)
    (n : ℤ) (he : ξ n = η n) : deriv (canonicalDiscriminant hp φ) (ξ n) = 0 :=
  discriminant_derivative_eq_zero_of_multiplicity_ge_two hp hp1 φ heven (ξ n)
    ((h.exhaustive _).mpr ⟨n,Or.inl rfl⟩) (h.multiplicity_ge_two_of_eq n he)

end NLS.ZakharovShabat
