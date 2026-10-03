import NLS.ZakharovShabat.ClassicalEndpointGradientDerivativeBound

/-! # Uniform time-derivative bounds for G.5 interpolation -/

noncomputable section
open Set NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalGradientValueConstant (M H : ℝ) : ℝ :=
  6*(Real.exp (4*M+H))^2*classicalSobolevErrorConstant M H

def classicalGradientDerivativeConstant (M H : ℝ) : ℝ :=
  2*classicalGradientValueConstant M H+8*M*(Real.exp (4*M+H))^3

def classicalGradientShiftedValueConstant (M B : ℝ) : ℝ :=
  6*(Real.exp (4*M+B))^2*(classicalSobolevErrorConstant M B+2*B)

def classicalGradientShiftedDerivativeConstant (M B : ℝ) : ℝ :=
  2*(Real.pi+1)*classicalGradientShiftedValueConstant M B+(12*B+8*M)*(Real.exp (4*M+B))^3

theorem classicalGradientValueConstant_nonneg (M H : ℝ) (hM : 0 ≤ M) :
    0 ≤ classicalGradientValueConstant M H := by
  have h := classicalSobolevErrorConstant_nonneg M H hM
  unfold classicalGradientValueConstant
  positivity

theorem classicalGradientDerivativeConstant_nonneg (M H : ℝ) (hM : 0 ≤ M) :
    0 ≤ classicalGradientDerivativeConstant M H := by
  have h := classicalGradientValueConstant_nonneg M H hM
  unfold classicalGradientDerivativeConstant
  positivity

theorem classicalGradientShiftedValueConstant_nonneg (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    0 ≤ classicalGradientShiftedValueConstant M B := by
  have h := classicalSobolevErrorConstant_nonneg M B hM
  unfold classicalGradientShiftedValueConstant
  positivity

theorem classicalGradientShiftedDerivativeConstant_nonneg (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    0 ≤ classicalGradientShiftedDerivativeConstant M B := by
  have h := classicalGradientShiftedValueConstant_nonneg M B hM hB
  unfold classicalGradientShiftedDerivativeConstant
  positivity

/-- The spectral factor cancels against the actual gradient error's inverse-frequency bound. -/
theorem norm_deriv_classicalEndpointGradientRemainder_sobolev_strip_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalEndpointGradientRemainder (classicalSobolevPotential a) z z v L) t‖ ≤
      classicalGradientDerivativeConstant M H := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M := (norm_classicalSobolevPotential_le a).trans (by linarith)
  have hR := norm_classicalEndpointGradientRemainder_sobolev_strip_le M H a ha z hz hH v hv L hL t
  have hm := norm_classicalEndpointGradientMixed_strip_le (4*M) H _ hφ z hH v hv L hL t
  have h := norm_deriv_classicalEndpointGradientRemainder_le (classicalSobolevPotential a) z z v L t
  simp only [sub_self,norm_zero,mul_zero,zero_mul,add_zero] at h
  apply h.trans
  calc
    _ ≤ 2*‖z‖*(classicalGradientValueConstant M H/‖z‖)+4*M*(2*(Real.exp (4*M+H))^3) := by gcongr; exact hR
    _ = _ := by
      unfold classicalGradientDerivativeConstant
      field_simp [norm_ne_zero_iff.mpr hz]
      ring

/-- Inverse-index displacement also leaves a uniformly bounded derivative for the shifted reference. -/
theorem norm_deriv_classicalEndpointGradientRemainder_shifted_le
    (M B : ℝ) (hB : 0 ≤ B) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalEndpointGradientRemainder (classicalSobolevPotential a) z
      ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L) t‖ ≤ classicalGradientShiftedDerivativeConstant M B := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hnpos : 0 < (n.natAbs : ℝ) := by linarith
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M := (norm_classicalSobolevPotential_le a).trans (by linarith)
  have hδB := hδ.trans (div_le_self hB hn)
  have hδ1 := hδ.trans ((div_le_one hnpos).mpr hBn)
  have him : |z.im| ≤ B := by
    simpa using (Complex.abs_im_le_norm (z-((Real.pi*(n : ℝ) : ℝ) : ℂ))).trans hδB
  have hzn : ‖z‖ ≤ (Real.pi+1)*(n.natAbs : ℝ) := by
    have h := norm_le_norm_sub_add z (((Real.pi*(n : ℝ) : ℝ) : ℂ))
    have he : ‖((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ = Real.pi*(n.natAbs : ℝ) := by
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos Real.pi_pos,Nat.cast_natAbs,Int.cast_abs]
    rw [he] at h
    nlinarith
  have hR := norm_classicalEndpointGradientRemainder_shifted_le M B hB a ha n hn hBn z hδ v hv L hL t
  have hm := norm_classicalEndpointGradientMixed_strip_le (4*M) B _ hφ z him v hv L hL t
  have hf := norm_classicalFreeEndpointGradient_strip_le (4*M) B (by positivity)
    (((Real.pi*(n : ℝ) : ℝ) : ℂ)) (by simpa using hB) v hv L hL t
  have hG := classicalGradientShiftedValueConstant_nonneg M B hM hB
  apply (norm_deriv_classicalEndpointGradientRemainder_le _ _ _ _ _ t).trans
  calc
    _ ≤ 2*((Real.pi+1)*(n.natAbs : ℝ))*(classicalGradientShiftedValueConstant M B/(n.natAbs : ℝ))+
        2*B*(6*(Real.exp (4*M+B))^3)+4*M*(2*(Real.exp (4*M+B))^3) := by gcongr; exact hR
    _ = _ := by
      unfold classicalGradientShiftedDerivativeConstant
      field_simp [hnpos.ne']
      ring

/-- A coarse all-frequency derivative bound controls the finite spectral head. -/
theorem norm_deriv_classicalEndpointGradientRemainder_all_frequencies_le
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M) (z w : ℂ)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalEndpointGradientRemainder (classicalSobolevPotential a) z w v L) t‖ ≤
      (24*‖z‖+12*‖z-w‖+8*M)*(Real.exp (4*M+‖z‖+‖w‖))^3 := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M := (norm_classicalSobolevPotential_le a).trans (by linarith)
  have hz : |z.im| ≤ ‖z‖+‖w‖ := (Complex.abs_im_le_norm z).trans (le_add_of_nonneg_right (norm_nonneg w))
  have hw : |w.im| ≤ ‖z‖+‖w‖ := (Complex.abs_im_le_norm w).trans (le_add_of_nonneg_left (norm_nonneg z))
  have hR := norm_classicalEndpointGradientRemainder_all_frequencies_le M a ha z w v hv L hL t
  have hm := norm_classicalEndpointGradientMixed_strip_le (4*M) (‖z‖+‖w‖) _ hφ z hz v hv L hL t
  have hf := norm_classicalFreeEndpointGradient_strip_le (4*M) (‖z‖+‖w‖) (by positivity) w hw v hv L hL t
  rw [← add_assoc] at hm hf
  apply (norm_deriv_classicalEndpointGradientRemainder_le _ _ _ _ _ t).trans
  calc
    _ ≤ 2*‖z‖*(12*(Real.exp (4*M+‖z‖+‖w‖))^3)+
        2*‖z-w‖*(6*(Real.exp (4*M+‖z‖+‖w‖))^3)+4*M*(2*(Real.exp (4*M+‖z‖+‖w‖))^3) := by gcongr
    _ = _ := by ring

end NLS.ZakharovShabat
