import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets

/-!
# Compact feasibility of closed physical constraints

Finite consistency is tested within one specified original endpoint norm
ball. The resulting potential satisfies every constraint and the same
bound, together with all original physical restrictions.
-/
noncomputable section
open Set Filter Topology
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- Arbitrary closed constraints with uniformly bounded finite realizations
have one physical realization of the entire family. -/
theorem exists_source_mem_all_of_finite_constraints (r R : ℝ)
    {ι : Type*} (C : ι → Set (WeakStarPotential r)) (hc : ∀ i, IsClosed (C i))
    (hf : ∀ J : Finset ι, ∃ q : WeakStarPotential r,
      ‖q.toPotential.val‖ ≤ R ∧ ∀ i ∈ J, q ∈ C i) :
    ∃ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R ∧ ∀ i, q ∈ C i := by
  have hn := (isCompact_sourceNormBall r R).inter_iInter_nonempty C hc (fun J => by
    obtain ⟨q, hq, hC⟩ := hf J
    exact ⟨q, hq, mem_iInter.mpr fun i => mem_iInter.mpr fun hi => hC i hi⟩)
  obtain ⟨q, hq, hC⟩ := hn
  exact ⟨q, hq, fun i => mem_iInter.mp hC i⟩

/-- An inconsistent family of closed constraints is already inconsistent
for finitely many constraints within the same endpoint norm ball. -/
theorem exists_finite_source_constraints_obstruction (r R : ℝ)
    {ι : Type*} (C : ι → Set (WeakStarPotential r)) (hc : ∀ i, IsClosed (C i))
    (hn : ¬ ∃ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R ∧ ∀ i, q ∈ C i) :
    ∃ J : Finset ι, ¬ ∃ q : WeakStarPotential r,
      ‖q.toPotential.val‖ ≤ R ∧ ∀ i ∈ J, q ∈ C i := by
  by_contra! h
  exact hn (exists_source_mem_all_of_finite_constraints r R C hc h)

/-- Finite consistency of closed Fourier constraints produces one original
physical potential satisfying every prescribed coefficient constraint. -/
theorem exists_source_coefficients_of_finite_constraints (r R : ℝ)
    (C : ℤ → Set ℂ) (hc : ∀ n, IsClosed (C n))
    (hf : ∀ J : Finset ℤ, ∃ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R ∧
      ∀ n ∈ J, q.toPotential.val.val (mode (-n)) ∈ C n) :
    ∃ q : WeakStarPotential r, ‖q.toPotential.val‖ ≤ R ∧
      ∀ n, q.toPotential.val.val (mode (-n)) ∈ C n :=
  exists_source_mem_all_of_finite_constraints r R
    (fun n => {q | q.toPotential.val.val (mode (-n)) ∈ C n})
    (fun n => (hc n).preimage (continuous_sourceCoefficient r n)) hf

/-- A decreasing family of nonempty weak-star closed physical sets has a
common point if the first set is bounded in the original endpoint norm. -/
theorem exists_source_mem_all_of_antitone (r : ℝ)
    (C : ℕ → Set (WeakStarPotential r)) (hc : ∀ n, IsClosed (C n))
    (hd : Antitone C) (hn : ∀ n, (C n).Nonempty)
    (hb : PotentialNormBounded r (C 0)) : ∃ q, ∀ n, q ∈ C n := by
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n => hd (Nat.le_succ n)) hn
    ((isCompact_source_iff_bounded_closed r _).mpr ⟨hb, hc 0⟩) hc
  exact ⟨q, fun n => mem_iInter.mp hq n⟩

/-- Every nonempty weak-star closed physical set contains a potential of
least original endpoint norm; no boundedness of the whole set is needed. -/
theorem exists_source_norm_minimizer_on_closed (r : ℝ)
    (A : Set (WeakStarPotential r)) (hc : IsClosed A) (hn : A.Nonempty) :
    ∃ a ∈ A, ∀ q ∈ A, ‖a.toPotential.val‖ ≤ ‖q.toPotential.val‖ := by
  obtain ⟨q₀, hq₀⟩ := hn
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ ‖q₀.toPotential.val‖} ∩ A
  have hk : IsCompact K := (isCompact_sourceNormBall r _).inter_right hc
  obtain ⟨a, ha, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (show K.Nonempty from ⟨q₀, (show ‖q₀.toPotential.val‖ ≤ ‖q₀.toPotential.val‖ from le_rfl), hq₀⟩) hk
      ((lowerSemicontinuous_sourceNorm r).lowerSemicontinuousOn K)
  refine ⟨a, ha.2, fun q hq => ?_⟩
  by_cases hle : ‖q.toPotential.val‖ ≤ ‖q₀.toPotential.val‖
  · exact hmin ⟨hle, hq⟩
  · exact ha.1.trans (le_of_not_ge hle)

end NLS.Articles.KdVPseudomeasures
