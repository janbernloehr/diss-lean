import NLS.ZakharovShabat.CentralParityLabeling
import NLS.ZakharovShabat.PeriodicSpectralProductExistence

/-!
# Complete actual periodic pairs with central parity labels

Splicing finite central labels into the distant counted eigenvalue pairs
preserves ℓp displacements. The result records the original central parity
multiplicities and every distant pair, without free artificial central roots.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Replace only the central indices of a sequence by prescribed root labels. -/
def spliceCentralRoots (N : ℕ) (α ξ : ℤ → ℂ) (n : ℤ) : ℂ :=
  if N < n.natAbs then ξ n else α n

/-- Finite central replacement preserves the displacement class, at every exponent. -/
theorem memℓp_spliceCentralRoots {p : ℝ≥0∞} (N : ℕ) (α ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    Memℓp (fun n => spliceCentralRoots N α ξ n-(Real.pi : ℂ)*n) p := by
  have hs : Set.Finite {n | spliceCentralRoots N α ξ n-ξ n ≠ 0} := by
    apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
    intro n hn
    have hlow : n.natAbs ≤ N := by
      by_contra h
      exact hn (by simp [spliceCentralRoots, show N < n.natAbs by omega])
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hm : Memℓp (fun n => spliceCentralRoots N α ξ n-ξ n) p :=
    (memℓp_zero hs).of_exponent_ge zero_le
  have he : (fun n => spliceCentralRoots N α ξ n-(Real.pi : ℂ)*n) =
      (fun n => spliceCentralRoots N α ξ n-ξ n) + (fun n => ξ n-(Real.pi : ℂ)*n) := by
    funext n
    dsimp
    ring
  rw [he]
  exact hm.add hξ

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Splicing leaves the entire central root multiset unchanged. -/
theorem CentralParityLabeling.splice {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {α β : ℤ → ℂ}
    (h : CentralParityLabeling hp φ N α β) (ξ η : ℤ → ℂ) :
    CentralParityLabeling hp φ N (spliceCentralRoots N α ξ) (spliceCentralRoots N β η) := by
  have he (r : ℤ) : (∑ n ∈ centralParityIndices N r,
      ({spliceCentralRoots N α ξ n, spliceCentralRoots N β η n} : Multiset ℂ)) =
        ∑ n ∈ centralParityIndices N r, ({α n, β n} : Multiset ℂ) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hi := (Finset.mem_filter.mp hn).1
    have hlow : ¬ N < n.natAbs := by simp only [Finset.mem_Icc] at hi; omega
    simp only [spliceCentralRoots, if_neg hlow]
  exact ⟨(he 0).trans h.even, (he 1).trans h.odd⟩

/-- Complete actual root sequences retain central parity multiplicities and distant counted pairs. -/
structure CompletePeriodicParityPairs (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ) : Prop where
  counting : PeriodicCountingData hp (weightedBaseToPair w φ) N
  even_potential : weightedBaseToPair w φ ∈ pairParitySubspace 0
  left_displacement : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p
  right_displacement : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p
  central : CentralParityLabeling hp (weightedBaseToPair w φ) N ξ η
  distant : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)

/-- Counted distant pairs can be completed by actual central roots in both parity sectors. -/
theorem exists_completePeriodicParityPairs (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (hφ : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    ∃ α β : ℤ → ℂ, CompletePeriodicParityPairs hp w φ N α β ∧
      ∀ n : ℤ, N < n.natAbs → α n = ξ n ∧ β n = η n := by
  obtain ⟨a,b,hab⟩ := exists_centralParityLabeling hp _ hφ N hc
  refine ⟨spliceCentralRoots N a ξ, spliceCentralRoots N b η,
    ⟨hc, hφ, memℓp_spliceCentralRoots N a ξ hξ, memℓp_spliceCentralRoots N b η hη,
      hab.splice ξ η, ?_⟩, ?_⟩
  · intro n hn
    simpa only [spliceCentralRoots, if_pos hn] using hr n hn
  · intro n hn
    simp only [spliceCentralRoots, if_pos hn, and_self]

/-- Actual displacement estimates supply complete parity pairs on one potential neighborhood. -/
theorem exists_uniform_completePeriodicParityPairs (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∀ N : ℕ, N₀ ≤ N → ∃ ξ η : ℤ → ℂ, CompletePeriodicParityPairs hp w ψ N ξ η := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,h⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven N hN
  obtain ⟨ξ,η,hξ,hη,hr,hd⟩ := h ψ hψ
  obtain ⟨α,β,hab,_⟩ := exists_completePeriodicParityPairs hp w ψ heven N (hd N hN).1
    ξ η hξ hη (fun n hn => hr n (by omega))
  exact ⟨α,β,hab⟩

end NLS.ZakharovShabat
