import NLS.ZakharovShabat.ClassicalEndpointGradientRemainder

/-! # Pointwise inverse-frequency bounds for the actual potential-gradient error

The full terminal factors are retained. These estimates are the value
endpoint for the time-derivative and Fourier estimates in G.5.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Solution/reference bounds transfer to the actual endpoint-gradient error. -/
theorem norm_classicalEndpointGradientRemainder_of_bounds
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (E D : ℝ) (hE : 0 ≤ E) (hD : 0 ≤ D)
    (h : ∀ (u : ℂ × ℂ), ‖u‖ ≤ 1 → ∀ t : Icc (0 : ℝ) 1,
      ‖classicalSolution φ z u t‖ ≤ E ∧ ‖classicalFreeVector w u t‖ ≤ E ∧
      ‖classicalSolution φ z u t-classicalFreeVector w u t‖ ≤ D)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalEndpointGradientRemainder φ z w v L t‖ ≤ 6*E^2*D := by
  have hd (i : Fin 5) :
      ‖classicalEndpointGradientData φ z v t i‖ ≤ E ∧
      ‖classicalFreeEndpointGradientData w v t i‖ ≤ E ∧
      ‖classicalEndpointGradientData φ z v t i-classicalFreeEndpointGradientData w v t i‖ ≤ D := by
    fin_cases i
    · exact h (1,0) (by simp) t
    · exact h (0,1) (by simp) t
    · exact h v hv t
    · exact h (1,0) (by simp) ⟨1,by constructor <;> norm_num⟩
    · exact h (0,1) (by simp) ⟨1,by constructor <;> norm_num⟩
  change ‖endpointGradientPolynomial L (classicalEndpointGradientData φ z v t)-
    endpointGradientPolynomial L (classicalFreeEndpointGradientData w v t)‖ ≤ _
  exact norm_endpointGradientPolynomial_sub_le L hL
    (classicalEndpointGradientData φ z v t) (classicalFreeEndpointGradientData w v t) E D hE hD
    (fun i => (hd i).1) (fun i => (hd i).2.1) (fun i => (hd i).2.2)

/-- Uniform solution growth for a unit initial vector on a potential ball and spectral strip. -/
theorem norm_classicalSolution_unit_strip_le
    (M H : ℝ) (φ : Curve (ℂ × ℂ)) (hφ : ‖φ‖ ≤ M) (z : ℂ) (hz : |z.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution φ z v t‖ ≤ Real.exp (M+H) := by
  apply (norm_classicalSolution_le_exp_im φ z v t).trans
  calc
    _ ≤ 1*Real.exp (M+H) := by
      gcongr
      calc
        _ ≤ (|z.im|+‖φ‖)*1 := mul_le_mul_of_nonneg_left t.property.2 (by positivity)
        _ ≤ _ := by linarith
    _ = _ := one_mul _

/-- G.5's full gradient error has inverse-frequency pointwise decay on every H¹ ball. -/
theorem norm_classicalEndpointGradientRemainder_sobolev_strip_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalEndpointGradientRemainder (classicalSobolevPotential a) z z v L t‖ ≤
      6*(Real.exp (4*M+H))^2*classicalSobolevErrorConstant M H/‖z‖ := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hC := classicalSobolevErrorConstant_nonneg M H hM
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
    (norm_classicalSobolevPotential_le a).trans (by linarith)
  have h := norm_classicalEndpointGradientRemainder_of_bounds (classicalSobolevPotential a) z z v hv L hL
    (Real.exp (4*M+H)) (classicalSobolevErrorConstant M H/‖z‖) (by positivity) (by positivity) ?_ t
  · exact h.trans_eq (by ring)
  intro u hu s
  refine ⟨norm_classicalSolution_unit_strip_le (4*M) H _ hφ z hH u hu s,?_,?_⟩
  · have he : classicalFreeVector z u s = classicalSolution 0 z u s := by
      simp [classicalSolution_free,classicalFreeVector]
    rw [he]
    exact norm_classicalSolution_unit_strip_le (4*M) H 0 (by simpa using (show 0 ≤ 4*M by positivity)) z hH u hu s
  · have hR := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH u s
    change ‖classicalSolutionRemainder (classicalSobolevPotential a) z u s‖ ≤ _
    apply hR.trans
    calc
      _ = classicalSobolevErrorConstant M H*‖u‖/‖z‖ := by unfold classicalSobolevErrorConstant; ring
      _ ≤ _ := by simpa using div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu hC) (norm_nonneg z)

/-- The shifted-free gradient error has the same inverse-index value estimate. -/
theorem norm_classicalEndpointGradientRemainder_shifted_le
    (M B : ℝ) (hB : 0 ≤ B) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalEndpointGradientRemainder (classicalSobolevPotential a) z
      ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L t‖ ≤
      6*(Real.exp (4*M+B))^2*(classicalSobolevErrorConstant M B+2*B)/(n.natAbs : ℝ) := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hC := classicalSobolevErrorConstant_nonneg M B hM
  have him : |z.im| ≤ B := by
    have h := (Complex.abs_im_le_norm (z-((Real.pi*(n : ℝ) : ℝ) : ℂ))).trans
      (hδ.trans (div_le_self hB hn))
    simpa using h
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
    (norm_classicalSobolevPotential_le a).trans (by linarith)
  have h := norm_classicalEndpointGradientRemainder_of_bounds (classicalSobolevPotential a) z
    ((Real.pi*(n : ℝ) : ℝ) : ℂ) v hv L hL (Real.exp (4*M+B))
    ((classicalSobolevErrorConstant M B+2*B)/(n.natAbs : ℝ)) (by positivity) (by positivity) ?_ t
  · exact h.trans_eq (by ring)
  intro u hu s
  refine ⟨norm_classicalSolution_unit_strip_le (4*M) B _ hφ z him u hu s,?_,?_⟩
  · rw [norm_classicalFreeVector_real]
    exact hu.trans (Real.one_le_exp (by positivity))
  · have hR := (classicalShiftedFreeRemainder_time_bounds M B hB a ha n hn hBn z hδ u s).1
    apply hR.trans
    simpa using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ classicalSobolevErrorConstant M B+2*B))
      (by positivity : 0 ≤ (n.natAbs : ℝ))

end NLS.ZakharovShabat
