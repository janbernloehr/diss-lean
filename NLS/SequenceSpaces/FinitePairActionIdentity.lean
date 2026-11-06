import NLS.SequenceSpaces.FiniteCenterBall
import NLS.SequenceSpaces.QuadraticActionsExponent

/-! # Equal-action finite truncations determine continuous pair values -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

theorem quadraticActionsExponent_truncatePair (S : Finset ℤ) (z : Coeff p × Coeff p) :
    quadraticActionsExponent (q := q) (truncatePair S z) = truncate S (quadraticActionsExponent z) := by
  ext k
  simp only [quadraticActionsExponent_apply,truncatePair,truncate_apply]
  split_ifs <;> simp

/-- Both points are truncated at the same finite set, preserving their
equal actions and real form while eventually entering their own domains. -/
theorem eq_of_finite_pair_action_agreement (hp : p ≠ ⊤)
    (U V : Set (Coeff p × Coeff p)) (hU : IsOpen U) (hV : IsOpen V)
    (f g : (Coeff p × Coeff p) → ℂ)
    (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (he : ∀ S : Finset ℤ, ∀ z ∈ U, ∀ w ∈ V,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ k, k ∉ S → z.1 k=0 ∧ z.2 k=0) →
      (∀ k, k ∉ S → w.1 k=0 ∧ w.2 k=0) →
      quadraticActionsExponent (q := q) w = quadraticActionsExponent z → f z=g w)
    (z : Coeff p × Coeff p) (hz : z ∈ U) (w : Coeff p × Coeff p) (hw : w ∈ V)
    (hzr : z ∈ realPairLocus p) (hwr : w ∈ realPairLocus p)
    (ha : quadraticActionsExponent (q := q) w = quadraticActionsExponent z) : f z=g w := by
  have ht := tendsto_truncatePair hp z
  have hs := tendsto_truncatePair hp w
  have hfu := (hf.continuousAt (hU.mem_nhds hz)).tendsto.comp ht
  have hgv := (hg.continuousAt (hV.mem_nhds hw)).tendsto.comp hs
  have heq : (fun S => f (truncatePair S z)) =ᶠ[atTop] (fun S => g (truncatePair S w)) := by
    filter_upwards [ht (hU.mem_nhds hz), hs (hV.mem_nhds hw)] with S hSz hSw
    apply he S _ hSz _ hSw (truncatePair_mem_realPairLocus S z hzr)
      (truncatePair_mem_realPairLocus S w hwr)
    · intro k hk
      simp only [truncatePair,truncate_apply,if_neg hk,and_self]
    · intro k hk
      simp only [truncatePair,truncate_apply,if_neg hk,and_self]
    · rw [quadraticActionsExponent_truncatePair,quadraticActionsExponent_truncatePair,ha]
  exact tendsto_nhds_unique hfu (hgv.congr' heq.symm)

end NLS.Coeff
