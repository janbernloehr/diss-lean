import NLS.ZakharovShabat.SourceIndexedHigherActionAsymptotic

/-! # Higher actions and the original periodic endpoints

The first asymptotic comparison displayed in Section 23 holds for either
original periodic endpoint. More generally it holds for any sample in
each actual periodic segment, with no division by an action at a closed gap.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Higher actions are asymptotic to any actual gap sample raised to the
spectral power, times the ordinary action, along both integer tails. -/
theorem sourceIndexedHigherAction_asymptotic_gapSample
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (k : ℕ) (ρ : ℤ → ℂ)
    (hρ : ∀ n, ρ n ∈ sourcePeriodicSegment hp hp1 φ.val n) :
    Asymptotics.IsEquivalent cofinite
      (fun n : ℤ => sourceIndexedHigherAction hp hp1 n k φ.val)
      (fun n : ℤ => (ρ n)^k * sourceIndexedAction hp hp1 n φ.val) := by
  have hs : Asymptotics.IsEquivalent cofinite (fun n : ℤ => (ρ n)^k)
      (fun n : ℤ => ((Real.pi : ℂ)*n)^k) :=
    Asymptotics.isEquivalent_of_tendsto_one
      (sourceGapSample_power_ratio_tendsto hp hp1 φ.val ρ hρ k)
  exact (sourceIndexedHigherAction_asymptotic hp hp1 φ k).trans
    (hs.mul (Asymptotics.IsEquivalent.refl
      (u := fun n : ℤ => sourceIndexedAction hp hp1 n φ.val) (l := cofinite))).symm

/-- The literal comparison with the left periodic endpoint, including
closed gaps. Spectral power k denotes printed action level k+1. -/
theorem sourceIndexedHigherAction_asymptotic_leftEndpoint
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (k : ℕ) :
    Asymptotics.IsEquivalent cofinite
      (fun n : ℤ => sourceIndexedHigherAction hp hp1 n k φ.val)
      (fun n : ℤ =>
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val)
          (periodOnePotential_mem φ.val) n)^k * sourceIndexedAction hp hp1 n φ.val) :=
  sourceIndexedHigherAction_asymptotic_gapSample hp hp1 φ k _
    (fun _ => left_mem_segment ℝ _ _)

/-- The literal comparison with the right periodic endpoint, including
closed gaps and both tails, for every natural spectral power. -/
theorem sourceIndexedHigherAction_asymptotic_rightEndpoint
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (k : ℕ) :
    Asymptotics.IsEquivalent cofinite
      (fun n : ℤ => sourceIndexedHigherAction hp hp1 n k φ.val)
      (fun n : ℤ =>
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val)
          (periodOnePotential_mem φ.val) n)^k * sourceIndexedAction hp hp1 n φ.val) :=
  sourceIndexedHigherAction_asymptotic_gapSample hp hp1 φ k _
    (fun _ => right_mem_segment ℝ _ _)

end NLS.ZakharovShabat
