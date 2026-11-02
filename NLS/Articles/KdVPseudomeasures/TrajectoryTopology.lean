import NLS.SequenceSpaces.WeightedWeakStarLowerTopology

/-!
# H-minus-one trajectory topology on bounded pseudomeasure sets

For s > -1/2 the exact threshold (s-(-1))*2 > 1 is satisfied. Thus the
H-minus-one coefficient norm trajectory topology equals the weak-star
endpoint trajectory topology on every norm-bounded subset. This supplies the
topological transfer in Theorem 1.3; it does not construct the physical KdV
solution map or prove its invariance and H-minus-one continuity.
-/
noncomputable section
open Set Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- The strict source range yields the Hilbert embedding threshold exactly. -/
theorem hminusOne_threshold (s : ℝ) (hs : -(1:ℝ)/2 < s) :
    1 < (-(-s)-(-1))*(2:ℝ≥0∞).toReal := by
  norm_num
  linarith

/-- Actual continuous lower Hilbert realization on a bounded endpoint subset. -/
def hminusOneMapOn (s : ℝ) (hs : -(1:ℝ)/2 < s)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev (-s)) 1)))
    (hb : Bornology.IsBounded V) :
    C(V, WeightedCoeff (Weight.sobolev (-1)) 2) :=
  WeightedCoeff.lowerWeakStarMapOn (-s) (-1) (by norm_num)
    (hminusOne_threshold s hs) V hb

/-- On every bounded invariant target V, the full compact-time weak-star
trajectory topology is exactly the one induced by H-minus-one trajectories.
Invariance is used when constructing a trajectory with codomain V; the
present topological statement holds for every bounded V. -/
theorem continuous_trajectory_iff_hminusOne (s : ℝ) (hs : -(1:ℝ)/2 < s)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev (-s)) 1)))
    (hb : Bornology.IsBounded V) (T : ℝ)
    {X : Type*} [TopologicalSpace X]
    (S : X → C(Icc (-T) T,V)) :
    Continuous S ↔ Continuous (fun x => (hminusOneMapOn s hs V hb).comp (S x)) :=
  WeightedCoeff.continuous_weakStarTrajectory_iff_lower (-s) (-1) (by norm_num)
    (hminusOne_threshold s hs) V hb S

end NLS.Articles.KdVPseudomeasures
