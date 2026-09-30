import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive
import Mathlib.Tactic.FieldSimp

/-!
# Transporting a normalized primitive between regular square-root sheets

The ratio of two continuous nonzero roots of the same radicand is locally
constant. Multiplying an endpoint-normalized primitive by this ratio
therefore changes its derivative to the prescribed-sheet quotient.
-/

noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis

def rootRatioPrimitive (Q R F : ℂ → ℂ) (A : ℂ) (z : ℂ) : ℂ :=
  (Q z/R z)*(F z-A)

theorem root_ratio_eventually_constant
    (Q R : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hQ : ContinuousOn Q D) (hR : ContinuousOn R D)
    (hsq : ∀ z ∈ D, Q z^2 = R z^2) (hne : ∀ z ∈ D, R z ≠ 0)
    (z : ℂ) (hz : z ∈ D) :
    (fun w => Q w/R w) =ᶠ[𝓝 z] (fun _ => Q z/R z) := by
  have hQne : Q z ≠ 0 := by
    intro h
    have he := hsq z hz
    rw [h,zero_pow (by norm_num : 2 ≠ 0)] at he
    exact (pow_ne_zero 2 (hne z hz)) he.symm
  have hratsq (w : ℂ) (hw : w ∈ D) : (Q w/R w)^2 = 1 := by
    rw [div_pow,hsq w hw,div_self (pow_ne_zero 2 (hne w hw))]
  apply eventuallyEq_of_sq_eq_of_continuousAt _ _ z
    ((hQ.continuousAt (hD.mem_nhds hz)).div (hR.continuousAt (hD.mem_nhds hz)) (hne z hz))
    continuousAt_const rfl (div_ne_zero hQne (hne z hz))
  filter_upwards [hD.mem_nhds hz] with w hw
  exact (hratsq w hw).trans (hratsq z hz).symm

/-- The exact root ratio transports the derivative and the normalized
value, including the case in which the chosen sheet has opposite sign. -/
theorem rootRatioPrimitive_hasDerivAt
    (N Q R F : ℂ → ℂ) (D : Set ℂ) (A : ℂ) (hD : IsOpen D)
    (hQ : ContinuousOn Q D) (hR : ContinuousOn R D)
    (hsq : ∀ z ∈ D, Q z^2 = R z^2) (hne : ∀ z ∈ D, R z ≠ 0)
    (hF : ∀ z ∈ D, HasDerivAt F (N z/Q z) z) :
    ∀ z ∈ D, HasDerivAt (rootRatioPrimitive Q R F A) (N z/R z) z := by
  intro z hz
  have hQne : Q z ≠ 0 := by
    intro h
    have he := hsq z hz
    rw [h,zero_pow (by norm_num : 2 ≠ 0)] at he
    exact (pow_ne_zero 2 (hne z hz)) he.symm
  have hc := root_ratio_eventually_constant Q R D hD hQ hR hsq hne z hz
  have hd := ((hF z hz).sub_const A).const_mul (Q z/R z)
  have heq : rootRatioPrimitive Q R F A =ᶠ[𝓝 z] (fun w => (Q z/R z)*(F w-A)) := by
    filter_upwards [hc] with w hw
    exact congrArg (fun c => c*(F w-A)) hw
  convert hd.congr_of_eventuallyEq heq using 1 <;> try rfl
  field_simp [hQne,hne z hz]

theorem rootRatioPrimitive_analyticOnNhd
    (N Q R F : ℂ → ℂ) (D : Set ℂ) (A : ℂ) (hD : IsOpen D)
    (hQ : ContinuousOn Q D) (hR : ContinuousOn R D)
    (hsq : ∀ z ∈ D, Q z^2 = R z^2) (hne : ∀ z ∈ D, R z ≠ 0)
    (hF : ∀ z ∈ D, HasDerivAt F (N z/Q z) z) :
    AnalyticOnNhd ℂ (rootRatioPrimitive Q R F A) D := by
  have hd : DifferentiableOn ℂ (rootRatioPrimitive Q R F A) D := fun z hz =>
    (rootRatioPrimitive_hasDerivAt N Q R F D A hD hQ hR hsq hne hF z hz).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd hD

end NLS.ComplexAnalysis
