import NLS.SequenceSpaces.WeightedPhaseFlow

/-! # Joint native continuity for coordinatewise continuous real frequencies -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem continuous_phaseFlow_family {X : Type*} [TopologicalSpace X]
    (w : Weight) (hp : p≠⊤) (ω : X → ℤ → ℝ) (z : X → WeightedCoeff w p)
    (hω : ∀ n, Continuous (fun x => ω x n)) (hz : Continuous z) :
    Continuous (fun x : ℝ × X => phaseFlow w (ω x.2) x.1 (z x.2)) := by
  exact (weightIsometry w p).symm.continuous.comp
    (Coeff.continuous_phaseMultiply_family hp
      (fun x : ℝ × X => fun n => x.1*ω x.2 n)
      (fun x => weightIsometry w p (z x.2))
      (fun n => continuous_fst.mul ((hω n).comp continuous_snd))
      ((weightIsometry w p).continuous.comp (hz.comp continuous_snd)))

end NLS.WeightedCoeff
