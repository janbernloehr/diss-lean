import NLS.SequenceSpaces.WeightedRealInclusion
import NLS.SequenceSpaces.RealCoeffTruncation
import NLS.SequenceSpaces.RealActionReduction

/-! # Finite truncation in native weighted real spaces

The raw real coefficients are cut off at the same finite indices in both
components. Convergence holds in the original weighted norm. Forgetting a
weight bounded below by one commutes with the truncation exactly.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedRealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Cut off a native weighted real sequence at a finite raw index set. -/
def truncate (w : Weight) (S : Finset ℤ) (a : WeightedRealCoeff w p) : WeightedRealCoeff w p :=
  WeightedCoeff.reCLM w p (WeightedCoeff.truncate w p S a.val)

/-- Complex inclusion is the same coefficient cutoff, with no projection error. -/
theorem truncate_complex (w : Weight) (S : Finset ℤ) (a : WeightedRealCoeff w p) :
    (truncate w S a).val = WeightedCoeff.truncate w p S a.val := by
  apply WeightedCoeff.complexCLM_reCLM
  intro n
  rw [WeightedCoeff.truncate_apply]
  split_ifs
  · exact im_eq_zero w p a n
  · rfl

@[simp] theorem truncate_apply (w : Weight) (S : Finset ℤ) (a : WeightedRealCoeff w p) (n : ℤ) :
    (truncate w S a).val.val n = if n ∈ S then a.val.val n else 0 := by
  rw [truncate_complex,WeightedCoeff.truncate_apply]

/-- Native weighted real truncations converge at every finite Banach exponent. -/
theorem tendsto_truncate (w : Weight) (hp : p ≠ ⊤) (a : WeightedRealCoeff w p) :
    Tendsto (fun S : Finset ℤ => truncate w S a) atTop (𝓝 a) := by
  have he : WeightedCoeff.reCLM w p a.val = a := by
    apply Subtype.ext
    exact WeightedCoeff.complexCLM_reCLM w p a.val
      ((WeightedCoeff.mem_realSubmodule_iff w p a.val).mp a.property)
  have h := ((WeightedCoeff.reCLM w p).continuous.tendsto a.val).comp
    (WeightedCoeff.tendsto_truncate w p hp a.val)
  simpa only [truncate,Function.comp_def,he] using h

/-- Forgetting the weight preserves the finite raw cutoff. -/
theorem forget_truncate (w : Weight) (hw : ∀ n, 1 ≤ w n)
    (S : Finset ℤ) (a : WeightedRealCoeff w p) :
    forgetWeightCLM w hw (truncate w S a) = RealCoeff.truncate S (forgetWeightCLM w hw a) := by
  apply lp.ext
  funext n
  simp only [forgetWeightCLM_apply,truncate_apply,RealCoeff.truncate_apply]
  split_ifs <;> rfl

/-- Cut off both native weighted real components at the same finite set. -/
def truncatePair (w : Weight) (S : Finset ℤ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) :=
  WithLp.toLp p (truncate w S z.fst,truncate w S z.snd)

@[simp] theorem truncatePair_fst (w : Weight) (S : Finset ℤ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (truncatePair w S z).fst = truncate w S z.fst := rfl

@[simp] theorem truncatePair_snd (w : Weight) (S : Finset ℤ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (truncatePair w S z).snd = truncate w S z.snd := rfl

/-- Pair truncations converge in the native weighted pair norm. -/
theorem tendsto_truncatePair (w : Weight) (hp : p ≠ ⊤)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    Tendsto (fun S : Finset ℤ => truncatePair w S z) atTop (𝓝 z) := by
  have h := ((WithLp.prodContinuousLinearEquiv p ℝ
    (WeightedRealCoeff w p) (WeightedRealCoeff w p)).symm.continuous.tendsto (z.fst,z.snd)).comp
      ((tendsto_truncate w hp z.fst).prodMk_nhds (tendsto_truncate w hp z.snd))
  have he : (WithLp.prodContinuousLinearEquiv p ℝ
      (WeightedRealCoeff w p) (WeightedRealCoeff w p)).symm (z.fst,z.snd) = z :=
    (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm_apply_apply z
  change Tendsto (fun S : Finset ℤ => truncatePair w S z) atTop
    (𝓝 ((WithLp.prodContinuousLinearEquiv p ℝ _ _).symm (z.fst,z.snd))) at h
  rw [he] at h
  exact h

/-- Forgetting a bounded-below weight commutes with the pair cutoff. -/
theorem forget_truncatePair (w : Weight) (hw : ∀ n, 1 ≤ w n) (S : Finset ℤ)
    (z : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    forgetPairWeightCLM w hw (truncatePair w S z) = RealCoeff.truncatePair S (forgetPairWeightCLM w hw z) := by
  apply Prod.ext
  · exact forget_truncate w hw S z.fst
  · exact forget_truncate w hw S z.snd

end NLS.WeightedRealCoeff

namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- The same finite cutoff preserves equality of every retained quadratic action. -/
theorem pairAction_truncatePair (S : Finset ℤ) (z : RealCoeff p × RealCoeff p) (n : ℤ) :
    pairAction (truncatePair S z) n = if n ∈ S then pairAction z n else 0 := by
  simp only [pairAction,truncatePair,truncate_apply]
  split_ifs <;> simp

end NLS.RealCoeff
