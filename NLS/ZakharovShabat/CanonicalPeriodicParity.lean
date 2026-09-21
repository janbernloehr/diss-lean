import NLS.ZakharovShabat.CanonicalPeriodicLevels
import NLS.ZakharovShabat.PeriodicParityFilters

/-!
# Exact central parity of the canonical ordered endpoints

Discriminant levels identify the parity of every canonical index.
Filtering the complete central enumeration then recovers both original
parity multisets, including their exact algebraic multiplicities.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A full central enumeration whose endpoints have the prescribed levels retains both exact parity multisets. -/
theorem CentralPeriodicLabeling.toParity_of_discriminant_levels
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CentralPeriodicLabeling hp φ N ξ η) (hp1 : 1 < p) (heven : φ ∈ pairParitySubspace 0)
    (hl : ∀ n : ℤ,
      canonicalDiscriminant hp φ (ξ n) = (if n % 2 = 0 then 2 else -2) ∧
      canonicalDiscriminant hp φ (η n) = (if n % 2 = 0 then 2 else -2)) :
    CentralParityLabeling hp φ N ξ η := by
  have he (r : ℤ) (hr : r = 0 ∨ r = 1) :
      centralParityRoots hp φ N r = ∑ n ∈ centralParityIndices N r, ({ξ n,η n} : Multiset ℂ) := by
    rw [centralParityRoots_eq_filter_discriminant hp hp1 φ heven N r hr, ← h.roots]
    let F : Multiset ℂ →+ Multiset ℂ := {
      toFun := fun m => m.filter (fun z => canonicalDiscriminant hp φ z = (if r % 2 = 0 then 2 else -2))
      map_zero' := by simp
      map_add' := fun a b => by simp }
    change F (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({ξ n,η n} : Multiset ℂ)) = _
    rw [map_sum]
    unfold centralParityIndices
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    change (({ξ n,η n} : Multiset ℂ).filter
      (fun z => canonicalDiscriminant hp φ z = (if r % 2 = 0 then 2 else -2))) = _
    rcases hr with rfl | rfl <;> by_cases hn : n % 2 = 0
    · norm_num [Multiset.insert_eq_cons,Multiset.filter_singleton,(hl n).1,(hl n).2,hn]
    · have hn1 : n % 2 = 1 := by omega
      norm_num [Multiset.insert_eq_cons,Multiset.filter_singleton,(hl n).1,(hl n).2,hn1]
    · norm_num [Multiset.insert_eq_cons,Multiset.filter_singleton,(hl n).1,(hl n).2,hn]
    · have hn1 : n % 2 = 1 := by omega
      norm_num [Multiset.insert_eq_cons,Multiset.filter_singleton,(hl n).1,(hl n).2,hn1]
  exact ⟨(he 0 (Or.inl rfl)).symm,(he 1 (Or.inr rfl)).symm⟩

/-- Every complete ordered real-type endpoint labeling has the exact central parity labeling. -/
theorem PeriodicEndpointLabeling.centralParity_of_ordered_realType
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p) (heven : φ ∈ pairParitySubspace 0)
    (hreal : IsRealType φ) (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)) :
    CentralParityLabeling hp φ N ξ η := by
  obtain ⟨hx,hy⟩ := h.eq_canonicalPeriodicEndpoints hp1 heven hw hc
  apply h.central.toParity_of_discriminant_levels hp1 heven
  intro n
  rw [hx,hy]
  exact canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ heven hreal n

/-- The canonical endpoint coordinates realize the exact central parity multisets at their chosen cutoff. -/
theorem canonicalPeriodicEndpoints_centralParity (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    CentralParityLabeling hp φ (canonicalPeriodicCutoff hp hp1 φ heven)
      (canonicalPeriodicLeft hp hp1 φ heven) (canonicalPeriodicRight hp hp1 φ heven) :=
  (canonicalPeriodicEndpoints_spec hp hp1 φ heven).1.centralParity_of_ordered_realType hp1 heven hreal
    (canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 (canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.2

end NLS.ZakharovShabat
