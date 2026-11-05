import NLS.KdV.HillOriginalWeightedMeanZeroSource
import NLS.KdV.HillForwardSobolevBound

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- The action of the ONE fixed real Birkhoff map, by the paper's exact
positive-index convention I_n=(x_n^2+y_n^2)/2. -/
def hillOriginalBirkhoffAction (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) : ℝ :=
  (((hillOriginalBirkhoffMap q).val k).1^2+((hillOriginalBirkhoffMap q).val k).2^2)/2

theorem hillOriginalBirkhoffAction_eq_gapIntegral (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    hillOriginalBirkhoffAction q k =
      hillRealGapIntegral q.val.val q.val.property.1 q.val.property.2 (k+1) 0 := by
  rw [hillOriginalBirkhoffAction,hillOriginalBirkhoffMap_action_identity]
  ring

theorem hillOriginalBirkhoffAction_weighted_source (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0 = 0) (k : ℕ) :
    hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource w p hmean) k =
      hillPeriodOneAction w p.val p.property (k+1) := by
  rw [hillOriginalBirkhoffAction_eq_gapIntegral]
  rfl

/-- Integer weighted action sums of the SAME original real map are the
actual native action masses, with exactly the paper's powers and indices. -/
theorem hillOriginalBirkhoffActionMass_eq_native (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    (∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*m+1)*
      hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean) k) =
      hillNativeActionMass M m p := by
  simp_rw [hillOriginalBirkhoffAction_weighted_source]
  exact (hasSum_hillNativePositiveActions M m hm p).tsum_eq

/-- These action sums really converge; no total-tsum fallback is used. -/
theorem summable_hillOriginalBirkhoffActionMass (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    Summable (fun k : ℕ => (2*Real.pi*(k+1 : ℕ))^(2*m+1)*
      hillOriginalBirkhoffAction (hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean) k) := by
  simp_rw [hillOriginalBirkhoffAction_weighted_source]
  exact (hasSum_hillNativePositiveActions M m hm p).summable

end NLS.KdV
