import NLS.ZakharovShabat.PeriodicGapSummability
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds
import NLS.ZakharovShabat.DiscriminantPairFactorization

/-! # Weighted gap estimates for the canonical endpoint labels

The intrinsic contour squared gap equals the square of the canonical ordered
endpoint gap outside one common central block. This transports the weighted
spectral estimate without making a continuous choice of the two roots.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ordering the actual counted pairs leaves every distant squared gap unchanged. -/
theorem CompletePeriodicParityPairs.canonical_squaredGap
    {hp : p ≠ ⊤} {w : SpectralWeight} {φ : WeightedCoeffPair w.toWeight p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : CompletePeriodicParityPairs hp w φ N ξ η)
    (hp1 : 1 < p) (n : ℤ) (hn : N < n.natAbs) :
    periodicSquaredGap hp (weightedBaseToPair w φ) n =
      (canonicalPeriodicGap hp hp1 (weightedBaseToPair w φ) h.even_potential n)^2 := by
  classical
  obtain ⟨α,β,hl,hw,hs,hpairs⟩ := h.toEndpoints.exists_ordered
  obtain ⟨hα,hβ⟩ := hl.eq_canonicalPeriodicEndpoints hp1 h.even_potential hw hs
  have hm := congrArg Multiset.toFinset (hpairs n hn)
  have he : ({α n,β n} : Set ℂ) = {ξ n,η n} := by
    simpa using
      congrArg (fun s : Finset ℂ => (s : Set ℂ)) hm
  rw [(h.distant n hn).squaredGap_eq]
  change _ = (canonicalPeriodicRight hp hp1 _ _ n - canonicalPeriodicLeft hp hp1 _ _ n)^2
  rw [← hα, ← hβ]
  rcases Set.pair_eq_pair_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy]; ring
  · rw [hx,hy]

/-- One open weighted neighborhood identifies all distant canonical squared gaps with
intrinsic contour invariants, including at collapsed gaps. -/
theorem exists_uniform_canonical_squaredGap_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ heven : weightedBaseToPair w ψ ∈ pairParitySubspace 0,
      ∀ n : ℤ, N < n.natAbs → periodicSquaredGap hp (weightedBaseToPair w ψ) n =
        (canonicalPeriodicGap hp hp1 (weightedBaseToPair w ψ) heven n)^2 := by
  obtain ⟨N,hN,U,ho,_,hφ,_,hh⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨N,hN,U,ho,hφ,?_⟩
  intro ψ hψ heven n hn
  obtain ⟨ξ,η,h⟩ := hh ψ hψ heven N le_rfl
  exact h.canonical_squaredGap hp1 n hn

/-- Weighted gap power estimates apply to the actual canonical source labels on a
common neighborhood and at every sufficiently large cutoff. -/
theorem exists_uniform_canonicalWeightedGapSummability (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ φ ∈ U ∧ ∀ ψ ∈ U, ∀ heven : weightedBaseToPair w ψ ∈ pairParitySubspace 0,
      ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then
          (w (2*n))^p.toReal * ‖canonicalPeriodicGap hp hp1
            (weightedBaseToPair w ψ) heven n‖^p.toReal else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then
          (w (2*n))^p.toReal * ‖canonicalPeriodicGap hp hp1
            (weightedBaseToPair w ψ) heven n‖^p.toReal else 0) ≤ rootGapBudget w ψ N := by
  obtain ⟨Ng,hNg,U,ho,_,hφ,_,hg⟩ := exists_uniform_periodicGapSummability hp hp1 w φ
  obtain ⟨Nc,_,V,hV,hφV,hc⟩ := exists_uniform_canonical_squaredGap_eq hp hp1 w φ
  refine ⟨max Ng (Nc+1),by omega,U ∩ V,ho.inter hV,⟨hφ,hφV⟩,?_⟩
  intro ψ hψ heven N hN
  have he : periodicGapPowerTail hp w ψ N = fun n : ℤ => if N ≤ n.natAbs then
      (w (2*n))^p.toReal * ‖canonicalPeriodicGap hp hp1
        (weightedBaseToPair w ψ) heven n‖^p.toReal else 0 := by
    funext n
    unfold periodicGapPowerTail
    by_cases hn : N ≤ n.natAbs
    · rw [if_pos hn, if_pos hn, hc ψ hψ.2 heven n (by omega), norm_sq_rpow_half]
    · rw [if_neg hn, if_neg hn]
  simpa only [he] using hg ψ hψ.1 N (by omega)

end NLS.ZakharovShabat
