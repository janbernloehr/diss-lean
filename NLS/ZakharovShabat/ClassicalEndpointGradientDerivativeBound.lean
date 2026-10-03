import NLS.ZakharovShabat.ClassicalEndpointGradientDerivative
import NLS.ZakharovShabat.ClassicalEndpointGradientBounds

/-! # Bounds for the mixed term and time derivative of the actual gradient error -/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The derivative bound separates the spectral error, reference displacement, and potential term. -/
theorem norm_deriv_classicalEndpointGradientRemainder_le
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    ‖deriv (classicalEndpointGradientRemainder φ z w v L) t‖ ≤
      2*‖z‖*‖classicalEndpointGradientRemainder φ z w v L t‖+
      2*‖z-w‖*‖classicalFreeEndpointGradient w v L t‖+‖φ‖*‖classicalEndpointGradientMixed φ z v L t‖ := by
  rw [(hasDerivAt_classicalEndpointGradientRemainder φ z w v L t).deriv]
  apply norm_prod_le_iff.mpr
  constructor
  · apply (norm_add_le _ _).trans
    apply (add_le_add (norm_add_le _ _) le_rfl).trans
    simp only [norm_mul,norm_I,norm_ofNat,mul_one]
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (norm_fst_le _) (by positivity))
      (mul_le_mul_of_nonneg_left (norm_fst_le _) (by positivity)))
      (mul_le_mul_of_nonneg_right ((norm_snd_le (φ t)).trans (φ.norm_coe_le_norm t)) (norm_nonneg _))
  · apply (norm_sub_le _ _).trans
    apply (add_le_add (norm_sub_le _ _) le_rfl).trans
    simp only [norm_mul,norm_neg,norm_I,norm_ofNat,mul_one]
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (norm_snd_le _) (by positivity))
      (mul_le_mul_of_nonneg_left (norm_snd_le _) (by positivity)))
      (mul_le_mul_of_nonneg_right ((norm_fst_le (φ t)).trans (φ.norm_coe_le_norm t)) (norm_nonneg _))

/-- The mixed term is uniformly cubic in the solution growth bound. -/
theorem norm_classicalEndpointGradientMixed_strip_le
    (M H : ℝ) (φ : Curve (ℂ × ℂ)) (hφ : ‖φ‖ ≤ M) (z : ℂ) (hz : |z.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalEndpointGradientMixed φ z v L t‖ ≤ 2*(Real.exp (M+H))^3 := by
  let E := Real.exp (M+H)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hobs (u : ℂ × ℂ) : ‖L u‖ ≤ ‖u‖ :=
    (L.le_opNorm u).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg u))
  have hinit : ‖classicalEndpointDualInitial φ z L‖ ≤ E := by
    apply norm_prod_le_iff.mpr
    constructor
    · simpa only [classicalEndpointDualInitial,norm_neg] using
        (hobs _).trans (norm_classicalSolution_unit_strip_le M H φ hφ z hz (0,1) (by simp) ⟨1,by constructor <;> norm_num⟩)
    · exact (hobs _).trans (norm_classicalSolution_unit_strip_le M H φ hφ z hz (1,0) (by simp) ⟨1,by constructor <;> norm_num⟩)
  have hdual : ‖classicalSolution φ z (classicalEndpointDualInitial φ z L) t‖ ≤ E^2 := by
    apply (norm_classicalSolution_le_exp_im φ z _ t).trans
    calc
      _ ≤ E*E := by
        apply mul_le_mul hinit _ (Real.exp_nonneg _) hE
        change Real.exp _ ≤ Real.exp (M+H)
        apply Real.exp_le_exp.mpr
        calc
          _ ≤ (|z.im|+‖φ‖)*1 := mul_le_mul_of_nonneg_left t.property.2 (by positivity)
          _ ≤ _ := by linarith
      _ = _ := (pow_two E).symm
  have hu := norm_classicalSolution_unit_strip_le M H φ hφ z hz v hv t
  rw [classicalEndpointGradientMixed_eq_dual_product]
  apply (norm_add_le _ _).trans
  simp only [norm_mul]
  calc
    _ ≤ E^2*E+E^2*E := by
      gcongr
      · exact (norm_fst_le _).trans hdual
      · exact (norm_snd_le _).trans hu
      · exact (norm_snd_le _).trans hdual
      · exact (norm_fst_le _).trans hu
    _ = _ := by ring

/-- The free gradient is controlled by three free solution factors on a spectral strip. -/
theorem norm_classicalFreeEndpointGradient_strip_le
    (M H : ℝ) (hM : 0 ≤ M) (w : ℂ) (hw : |w.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalFreeEndpointGradient w v L t‖ ≤ 6*(Real.exp (M+H))^3 := by
  let E := Real.exp (M+H)
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hfree (u : ℂ × ℂ) (hu : ‖u‖ ≤ 1) (s : Icc (0 : ℝ) 1) : ‖classicalFreeVector w u s‖ ≤ E := by
    have he : classicalFreeVector w u s = classicalSolution 0 w u s := by simp [classicalSolution_free,classicalFreeVector]
    rw [he]
    exact norm_classicalSolution_unit_strip_le M H 0 (by simpa using hM) w hw u hu s
  have hd (i : Fin 5) : ‖classicalFreeEndpointGradientData w v t i‖ ≤ E := by
    fin_cases i
    · exact hfree (1,0) (by simp) t
    · exact hfree (0,1) (by simp) t
    · exact hfree v hv t
    · exact hfree (1,0) (by simp) ⟨1,by constructor <;> norm_num⟩
    · exact hfree (0,1) (by simp) ⟨1,by constructor <;> norm_num⟩
  have h := norm_endpointGradientPolynomial_sub_le L hL (classicalFreeEndpointGradientData w v t)
    (fun _ => 0) E E hE hE hd (fun _ => by simpa using hE) (fun i => by simpa using hd i)
  have hz : endpointGradientPolynomial L (fun _ => 0) = 0 := by simp [endpointGradientPolynomial]
  rw [hz,sub_zero] at h
  exact h.trans_eq (by dsimp [E]; ring)

end NLS.ZakharovShabat
