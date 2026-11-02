import NLS.KdV.ClassicalNumeratorHilbert
import NLS.SequenceSpaces.ConjugateDuality
import NLS.ComplexAnalysis.BilinearCircleIntegral

/-! # Literal contour periods of Hilbert coefficient combinations

A genuine l2-valued Bochner circle integral defines the period functional.
Its values on the Fourier basis identify it with the corresponding row
of the constructed actual period operator, for every coefficient vector.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillNumeratorContourVector (N : ℕ) (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    ((2*z)/classicalHillContinuedRoot (z^2,q)) • classicalHillNumeratorHilbert N (z^2,q)

def classicalHillHilbertPeriod (N : ℕ) (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) :
    NLS.Coeff 2 →L[ℂ] ℂ :=
  (2*(Real.pi : ℂ))⁻¹ • (NLS.Coeff.dualPairing (p := 2) (q := 2)).flip
    (classicalHillNumeratorContourVector N k q)

private theorem dualPairing_single (m : ℤ) (b : NLS.Coeff 2) :
    NLS.Coeff.dualPairing (lp.single 2 m (1 : ℂ)) b = b m := by
  simp [NLS.Coeff.dualPairing_apply,lp.single_apply,Pi.single_apply]

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem numerator_contour_integrable (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) :
    CircleIntegrable (fun z : ℂ => ((2*z)/classicalHillContinuedRoot (z^2,q)) •
      classicalHillNumeratorHilbert N (z^2,q)) ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  have hB : AnalyticOnNhd ℂ (fun z : ℂ => classicalHillNumeratorHilbert N (z^2,q))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z _
    exact (D.numeratorHilbert_spec.2 (z^2,q) ⟨mem_univ _,hq⟩).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
  have hR : AnalyticOnNhd ℂ (fun z : ℂ => classicalHillContinuedRoot (z^2,q))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact (analyticOnNhd_classicalHillContinuedRoot (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun w : ℂ => (w^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
  have hi : AnalyticOnNhd ℂ (fun z : ℂ => ((2*z)/classicalHillContinuedRoot (z^2,q)) •
      classicalHillNumeratorHilbert N (z^2,q)) (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :=
    ((analyticOnNhd_const.mul analyticOnNhd_id).div hR
    (fun z hz => classicalHillContinuedRoot_ne_zero (z^2,q) (D.cover k q hq z hz))).smul hB
  exact hi.continuousOn.circleIntegrable (by positivity)

theorem hilbertPeriod_integral (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (c : NLS.Coeff 2) :
    classicalHillHilbertPeriod N k q c = (2*(Real.pi : ℂ))⁻¹ *
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        NLS.Coeff.dualPairing c (classicalHillNumeratorHilbert N (z^2,q))/
          classicalHillContinuedRoot (z^2,q)*(2*z) := by
  change (2*(Real.pi : ℂ))⁻¹ * NLS.Coeff.dualPairing c
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      ((2*z)/classicalHillContinuedRoot (z^2,q)) • classicalHillNumeratorHilbert N (z^2,q)) = _
  rw [map_circleIntegral _ (D.numerator_contour_integrable k q hq)]
  congr 1
  apply circleIntegral.integral_congr (by positivity)
  intro z _
  simp only [map_smul,smul_eq_mul,div_eq_mul_inv]
  ring

theorem hilbertPeriod_single (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (m : ℤ) :
    classicalHillHilbertPeriod N k q (lp.single 2 m 1) = classicalHillPeriodMatrix N q (k : ℤ) m := by
  rw [D.hilbertPeriod_integral k q hq]
  have he (z : ℂ) : NLS.Coeff.dualPairing (lp.single 2 m (1 : ℂ))
      (classicalHillNumeratorHilbert N (z^2,q)) = classicalHillNumeratorCoordinates N (z^2,q) m := by
    rw [dualPairing_single,D.numeratorHilbert_spec.1 (z^2,q) ⟨mem_univ _,hq⟩]
  simp_rw [he]
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  rw [classicalHillPeriodMatrix,dif_pos hk]
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    have hkindex : positiveIntegerIndex (k : ℤ) hk = k := by
      apply Subtype.ext
      simp only [positiveIntegerIndex,Int.toNat_natCast]
      rfl
    rw [hkindex]
    simp only [classicalHillNumeratorCoordinates,dif_pos hm]
    rfl
  · rw [dif_neg hm]
    simp only [classicalHillNumeratorCoordinates,dif_neg hm,zero_div,zero_mul,
      circleIntegral,mul_zero,smul_zero,intervalIntegral.integral_zero]

/-- The actual integral functional equals the row of the constructed
operator on every l2 coefficient vector, by equality on the full basis. -/
theorem hilbertPeriod_eq_row (k : ℕ+) (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V)
    (T : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)
    (hT : ∀ m n : ℤ, (T (lp.single 2 n 1)) m = classicalHillPeriodMatrix N q m n) :
    classicalHillHilbertPeriod N k q = (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (k : ℤ)).comp T := by
  apply NLS.Coeff.continuousLinearMap_eq_of_single (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro m
  exact (D.hilbertPeriod_single k q hq m).trans (hT (k : ℤ) m).symm

end ClassicalAllContourPeriodData
end NLS.KdV
