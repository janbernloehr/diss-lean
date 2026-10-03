import NLS.ZakharovShabat.ClassicalFreeFrequencyDifference
import NLS.ZakharovShabat.ClassicalSobolevRemainderTimeBounds

/-! # The actual solution minus a free solution at a reference frequency

The reference error is the sum of the already controlled remainder and
the free-frequency difference. Inverse-index displacement gives decaying
values and uniformly bounded derivatives for the combined error.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Actual solution error relative to a real reference frequency. -/
def classicalShiftedFreeRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalSolution φ z v t-classicalFreeVector x v t

theorem classicalShiftedFreeRemainder_eq (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : ℝ) :
    classicalShiftedFreeRemainder φ z x v t =
      classicalSolutionRemainder φ z v t+classicalFreeFrequencyDifference z x v t := by
  unfold classicalShiftedFreeRemainder classicalSolutionRemainder classicalFreeFrequencyDifference
  abel

theorem contDiff_classicalShiftedFreeRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) :
    ContDiff ℝ 1 (classicalShiftedFreeRemainder φ z x v) :=
  (contDiff_classicalSolution φ z v).sub (contDiff_classicalFreeVector x v)

theorem deriv_classicalShiftedFreeRemainder (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (t : ℝ) :
    deriv (classicalShiftedFreeRemainder φ z x v) t =
      deriv (classicalSolutionRemainder φ z v) t+deriv (classicalFreeFrequencyDifference z x v) t := by
  have he : classicalShiftedFreeRemainder φ z x v =
      fun s => classicalSolutionRemainder φ z v s+classicalFreeFrequencyDifference z x v s :=
    funext (classicalShiftedFreeRemainder_eq φ z x v)
  rw [he]
  exact (((contDiff_one_iff_deriv.mp (contDiff_classicalSolutionRemainder φ z v)).1 t).hasDerivAt.add
    ((contDiff_one_iff_deriv.mp (contDiff_classicalFreeFrequencyDifference z x v)).1 t).hasDerivAt).deriv

/-- Pointwise estimates for the complete reference error, under inverse-index displacement. -/
theorem classicalShiftedFreeRemainder_time_bounds
    (M B : ℝ) (hB : 0 ≤ B) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    ‖classicalShiftedFreeRemainder (classicalSobolevPotential a) z (Real.pi*(n : ℝ)) v t‖ ≤
        (classicalSobolevErrorConstant M B+2*B)*‖v‖/(n.natAbs : ℝ) ∧
    ‖deriv (classicalShiftedFreeRemainder (classicalSobolevPotential a) z (Real.pi*(n : ℝ)) v) t‖ ≤
        (classicalSobolevDerivativeConstant M B+(2*Real.pi+3)*B)*‖v‖ := by
  have hnpos : 0 < (n.natAbs : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hδ1 : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ 1 :=
    hδ.trans ((div_le_one hnpos).mpr hBn)
  have hδB : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B := hδ.trans (div_le_self hB hn)
  have hδn := (le_div_iff₀ hnpos).mp hδ
  have hnorm : ‖((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ = Real.pi*(n.natAbs : ℝ) := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,Nat.cast_natAbs,Int.cast_abs]
  have hzupper : ‖z‖ ≤ Real.pi*(n.natAbs : ℝ)+1 := by
    have h := norm_le_norm_sub_add z (((Real.pi*(n : ℝ) : ℝ) : ℂ))
    rw [hnorm] at h
    linarith
  have hzlower : (n.natAbs : ℝ) ≤ ‖z‖ := by
    have h := norm_sub_norm_le (((Real.pi*(n : ℝ) : ℝ) : ℂ)) z
    rw [hnorm,norm_sub_rev] at h
    nlinarith [Real.two_le_pi]
  have hz : z ≠ 0 := norm_pos_iff.mp (hnpos.trans_le hzlower)
  have him : |z.im| ≤ B := by
    simpa using (Complex.abs_im_le_norm (z-((Real.pi*(n : ℝ) : ℝ) : ℂ))).trans hδB
  have hC := classicalSobolevErrorConstant_nonneg M B ((norm_nonneg a).trans ha)
  have hR : ‖classicalSolutionRemainder (classicalSobolevPotential a) z v t‖ ≤
      classicalSobolevErrorConstant M B*‖v‖/(n.natAbs : ℝ) := by
    have h := norm_classicalSolutionRemainder_sobolev_strip_le M B a ha z hz him v t
    have he : (4+Real.pi)*M*‖v‖/‖z‖*Real.exp (4*M+B) = classicalSobolevErrorConstant M B*‖v‖/‖z‖ := by
      unfold classicalSobolevErrorConstant
      ring
    rw [he] at h
    exact h.trans (div_le_div_of_nonneg_left (mul_nonneg hC (norm_nonneg _)) hnpos hzlower)
  have hF : ‖classicalFreeFrequencyDifference z (Real.pi*(n : ℝ)) v t‖ ≤ 2*B*‖v‖/(n.natAbs : ℝ) := by
    apply (norm_classicalFreeFrequencyDifference_le z (Real.pi*(n : ℝ)) v hδ1 t).trans
    calc
      _ ≤ 2*(B/(n.natAbs : ℝ))*‖v‖ := by gcongr
      _ = _ := by ring
  have hR' : ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ ≤
      classicalSobolevDerivativeConstant M B*‖v‖ := by
    have h := norm_deriv_classicalSolutionRemainder_sobolev_strip_le M B a ha z hz him v t
    convert h using 1
    unfold classicalSobolevDerivativeConstant
    ring
  have hF' : ‖deriv (classicalFreeFrequencyDifference z (Real.pi*(n : ℝ)) v) t‖ ≤ (2*Real.pi+3)*B*‖v‖ := by
    apply (norm_deriv_classicalFreeFrequencyDifference_le z (Real.pi*(n : ℝ)) v hδ1 t).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ (2*(Real.pi*(n.natAbs : ℝ)+1)+1)*‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ := by gcongr
      _ = 2*Real.pi*(‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖*(n.natAbs : ℝ))+3*‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ := by ring
      _ ≤ 2*Real.pi*B+3*B := by gcongr
      _ = _ := by ring
  constructor
  · rw [classicalShiftedFreeRemainder_eq]
    exact (norm_add_le _ _).trans ((add_le_add hR hF).trans_eq (by ring))
  · rw [deriv_classicalShiftedFreeRemainder]
    exact (norm_add_le _ _).trans ((add_le_add hR' hF').trans_eq (by ring))

end NLS.ZakharovShabat
