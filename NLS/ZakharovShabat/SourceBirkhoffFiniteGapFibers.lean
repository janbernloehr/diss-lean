import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport

/-! # Finite-gap approximation of Birkhoff collisions

Two distinct sources with the same output have disjoint local inverse
branches. Truncating that common output and using both branches produces
distinct finite-gap sources in any prescribed neighborhoods. Consequently
global injectivity is equivalent to injectivity on the finite-gap locus.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Every collision can be approximated, in independently prescribed
neighborhoods, by distinct finite-gap preimages of a common finite output. -/
theorem exists_finiteGap_collision_mem_open
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ ψ : realTypeSourceSubmodule p) (hne : φ ≠ ψ)
    (heq : sourceRealBirkhoffMap hp hp1 s φ = sourceRealBirkhoffMap hp hp1 s ψ)
    (U V : Set (realTypeSourceSubmodule p)) (hU : IsOpen U) (hV : IsOpen V)
    (hφ : φ ∈ U) (hψ : ψ ∈ V) :
    ∃ S : Finset ℤ, ∃ φ' ψ' : realTypeSourceSubmodule p,
      φ' ∈ U ∧ ψ' ∈ V ∧ φ' ≠ ψ' ∧
      φ' ∈ sourceFiniteGapLocus hp hp1 ∧ ψ' ∈ sourceFiniteGapLocus hp hp1 ∧
      sourceRealBirkhoffMap hp hp1 s φ' =
        RealCoeff.truncatePair S (sourceRealBirkhoffMap hp hp1 s φ) ∧
      sourceRealBirkhoffMap hp hp1 s ψ' =
        RealCoeff.truncatePair S (sourceRealBirkhoffMap hp hp1 s φ) := by
  obtain ⟨g, hg, hgφ, _, hrightg, _⟩ := D.proposition17_1 φ
  obtain ⟨k, hk, hkψ, _, hrightk, _⟩ := D.proposition17_1 ψ
  rw [← heq] at hk hkψ hrightk
  let z := sourceRealBirkhoffMap hp hp1 s φ
  let T := fun S : Finset ℤ => RealCoeff.truncatePair S z
  have ht : Tendsto T atTop (𝓝 z) := RealCoeff.tendsto_truncatePair hp z
  have hgT : Tendsto (fun S => g (T S)) atTop (𝓝 φ) := by
    have h := hg.continuousAt.tendsto.comp ht
    rw [hgφ] at h
    exact h
  have hkT : Tendsto (fun S => k (T S)) atTop (𝓝 ψ) := by
    have h := hk.continuousAt.tendsto.comp ht
    rw [hkψ] at h
    exact h
  have hdistinct : ∀ᶠ S in atTop, g (T S) ≠ k (T S) := by
    simpa only [sub_ne_zero] using (hgT.sub hkT).eventually_ne (sub_ne_zero.mpr hne)
  obtain ⟨S, hgu, hkv, hneq, hgr, hkr⟩ :=
    ((hgT.eventually (hU.mem_nhds hφ)).and
      ((hkT.eventually (hV.mem_nhds hψ)).and
        (hdistinct.and ((ht.eventually hrightg).and (ht.eventually hrightk))))).exists
  exact ⟨S, g (T S), k (T S), hgu, hkv, hneq,
    D.finiteGap_of_real_map_eq_truncatePair _ S z hgr,
    D.finiteGap_of_real_map_eq_truncatePair _ S z hkr, hgr, hkr⟩

/-- It suffices, and is necessary, to prove injectivity on actual finite-gap sources. -/
theorem real_map_injective_iff_injOn_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) ↔
      Set.InjOn (sourceRealBirkhoffMap hp hp1 s) (sourceFiniteGapLocus hp hp1) := by
  constructor
  · intro hi
    exact hi.injOn
  · intro hi φ ψ heq
    by_contra hne
    obtain ⟨S, φ', ψ', _, _, hneq, hfφ, hfψ, hφ', hψ'⟩ :=
      D.exists_finiteGap_collision_mem_open φ ψ hne heq univ univ
        isOpen_univ isOpen_univ (mem_univ _) (mem_univ _)
    exact hneq (hi hfφ hfψ (hφ'.trans hψ'.symm))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
