import NLS.SequenceSpaces.FinitePhaseAnalytic
import NLS.SequenceSpaces.PhysicalPositiveMultiplierEquiv
import NLS.SequenceSpaces.PhysicalRealMeanZeroPhaseFlowExponent

/-! # Native real analyticity of physical finite-support phase orbits

The bounded real positive Fourier completion retains the original real
norm and every signed coefficient. It transports the finite-support
complex phase polynomial without changing its time trajectory.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS
variable (w : Weight) {p : ℝ≥0∞} [Fact (1≤p)] (hw : ∀ n : ℤ, w (-n)=w n)

theorem physicalPositiveRealLift_weightIsometry
    (z : physicalRealMeanZeroWeightedExponent w p) :
    WeightedCoeff.physicalPositiveRealLift w p hw ((WeightedCoeff.weightIsometry w p) z.val)=z := by
  apply physicalRealMeanZeroWeightedExponent_ext_positive
  intro j hj
  rw [WeightedCoeff.physicalPositiveRealLift_apply,if_pos hj,if_neg (by omega : ¬0< -j),map_zero,add_zero]
  change ((w j : ℂ)*z.val.val j)/(w j : ℂ)=z.val.val j
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero j)

theorem physicalPositiveRealLift_phase_weightIsometry
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n) (t : ℝ)
    (z : physicalRealMeanZeroWeightedExponent w p) :
    WeightedCoeff.physicalPositiveRealLift w p hw
      (Coeff.phaseFlow ω t ((WeightedCoeff.weightIsometry w p) z.val))=
        physicalRealMeanZeroPhaseFlow w ω hω t z := by
  apply physicalRealMeanZeroWeightedExponent_ext_positive
  intro j hj
  rw [WeightedCoeff.physicalPositiveRealLift_apply,if_pos hj,if_neg (by omega : ¬0< -j),map_zero,add_zero,
    Coeff.phaseFlow_apply,physicalRealMeanZeroPhaseFlow_apply]
  change (Complex.exp _*((w j : ℂ)*z.val.val j))/(w j : ℂ)=Complex.exp _*z.val.val j
  rw [mul_left_comm,mul_div_cancel_left₀ _ (w.complex_ne_zero j)]

include hw in
theorem analyticAt_physicalRealMeanZeroPhaseFlow_of_finite_support
    (ω : ℤ → ℝ) (hω : ∀ n : ℤ, ω (-n)= -ω n)
    (z : physicalRealMeanZeroWeightedExponent w p)
    (hf : (Function.support z.val.val).Finite) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => physicalRealMeanZeroPhaseFlow w ω hω u z) t := by
  classical
  let S := hf.toFinset
  have hz (j : ℤ) (hj : j∉S) : (WeightedCoeff.weightIsometry w p z.val) j=0 := by
    have hj' : z.val.val j=0 := by
      by_contra h
      exact hj (hf.mem_toFinset.mpr h)
    change (w j : ℂ)*z.val.val j=0
    rw [hj',mul_zero]
  have ha := Coeff.analyticAt_phaseFlow_of_finite_support ω S
    ((WeightedCoeff.weightIsometry w p) z.val) hz t
  have hA := ((WeightedCoeff.physicalPositiveRealLift w p hw).analyticAt _).comp ha
  have he : (fun u : ℝ => WeightedCoeff.physicalPositiveRealLift w p hw
      (Coeff.phaseFlow ω u ((WeightedCoeff.weightIsometry w p) z.val)))=
        fun u : ℝ => physicalRealMeanZeroPhaseFlow w ω hω u z :=
    funext (fun u => physicalPositiveRealLift_phase_weightIsometry w hw ω hω u z)
  change AnalyticAt ℝ (fun u : ℝ => WeightedCoeff.physicalPositiveRealLift w p hw
    (Coeff.phaseFlow ω u ((WeightedCoeff.weightIsometry w p) z.val))) t at hA
  rwa [he] at hA

end NLS
