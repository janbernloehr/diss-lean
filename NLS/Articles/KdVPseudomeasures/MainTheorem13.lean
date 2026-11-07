import NLS.Articles.KdVPseudomeasures.MainTheorem11

/-! Original Theorem 1.3. Every bounded invariant subset has its
literal physical Wiener weak-star subspace topology. The target is
the full compact-open space of continuous trajectories valued in
that same subset; closedness is not assumed. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def sourceTheorem1_3Statement : Prop :=
  ∀ (s : ℝ) (hs : -(1 / 2 : ℝ) < s ∧ s ≤ 0),
    let hr := admissiblePredualOrder_neg_of_sourceRange s hs
    ∀ (V : Set (WeakStarPotential (-s))) (_hb : PotentialNormBounded (-s) V)
      (hV : HillEndpointKdVInvariant (-s) hr V) (T : ℝ), 0 < T →
        Continuous (hillEndpointWeakStarKdVTrajectoryOn (-s) hr V hV T)

theorem sourceTheorem1_3 : sourceTheorem1_3Statement := by
  intro s hs
  dsimp only
  intro V hb hV T _
  exact continuous_hillEndpointWeakStarKdVTrajectoryOn (-s)
    (admissiblePredualOrder_neg_of_sourceRange s hs) V hb hV T

end NLS.Articles.KdVPseudomeasures
