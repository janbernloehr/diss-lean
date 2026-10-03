import NLS.ZakharovShabat.ClassicalSpectralVariation

/-! # Dirichlet eigenfunction normalization and the actual physical gradient

At a Dirichlet zero, the endpoint-dual solution is proportional to the
normalized eigenfunction. Both characteristic derivatives have the same
proportionality factor. Simplicity makes the bilinear normalization nonzero,
and their quotient is exactly the squared-eigenfunction gradient in G.7.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The normalized Dirichlet solution, an eigenfunction at a characteristic zero. -/
def classicalDirichletEigenfunction (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℝ → ℂ × ℂ :=
  classicalSolution Φ z (1,1)

/-- The bilinear normalization from G.7, without complex conjugation. -/
def classicalDirichletNormalization (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  2*∫ t in (0 : ℝ)..1,
    (classicalDirichletEigenfunction Φ z t).1*(classicalDirichletEigenfunction Φ z t).2

/-- The endpoint-dual proportionality constant. -/
def classicalDirichletDualFactor (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ :=
  classicalSeparatedEndpointCLM .dirichlet (classicalSolution Φ z (1,0) 1)

/-- At a Dirichlet root the dual initial vector is a multiple of (1,1). -/
theorem classicalDirichletDualInitial_of_root (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) :
    classicalSeparatedDualInitial .dirichlet Φ z = classicalDirichletDualFactor Φ z • (1,1) := by
  have he := hz
  rw [classicalSeparatedCharacteristic_eq_endpoint,
    classicalSolution_eq_columns Φ z (1,extensionSign .dirichlet) ⟨1,by constructor <;> norm_num⟩] at he
  simp only [extensionSign,map_add,one_smul] at he
  apply Prod.ext
  · change -classicalSeparatedEndpointCLM .dirichlet (classicalSolution Φ z (0,1) 1) =
      classicalDirichletDualFactor Φ z*1
    dsimp [classicalDirichletDualFactor]
    linear_combination -he
  · simp [classicalSeparatedDualInitial,classicalDirichletDualFactor]

/-- The entire dual solution is proportional to the forward eigenfunction. -/
theorem classicalDirichletDualSolution_of_root (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (classicalSeparatedDualInitial .dirichlet Φ z) t =
      classicalDirichletDualFactor Φ z • classicalDirichletEigenfunction Φ z t := by
  rw [classicalDirichletDualInitial_of_root Φ z hz]
  unfold classicalDirichletEigenfunction
  rw [classicalSolution_eq_columns Φ z (classicalDirichletDualFactor Φ z • (1,1)) t,
    classicalSolution_eq_columns Φ z (1,1) t]
  simp [smul_add]

/-- Unimodularity makes the dual factor nonzero at every Dirichlet root. -/
theorem classicalDirichletDualFactor_ne_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) :
    classicalDirichletDualFactor Φ z ≠ 0 := by
  have hd := classicalDirichletDualSolution_of_root Φ z hz ⟨1,by constructor <;> norm_num⟩
  rw [classicalSeparatedDualSolution_one] at hd
  intro hzero
  rw [hzero,zero_smul] at hd
  have h := congrArg Prod.fst hd
  norm_num [extensionSign] at h

/-- The characteristic's potential gradient at a root is its dual factor
multiplying the two squared eigenfunction components, in reversed order. -/
theorem classicalSeparatedGradient_dirichlet_of_root (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) (t : Icc (0 : ℝ) 1) :
    classicalSeparatedGradient .dirichlet Φ z t = (I*classicalDirichletDualFactor Φ z) •
      ((classicalDirichletEigenfunction Φ z t).2^2,(classicalDirichletEigenfunction Φ z t).1^2) := by
  rw [classicalSeparatedGradient_eq_solution_product,classicalDirichletDualSolution_of_root Φ z hz t]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,extensionSign,
    classicalDirichletEigenfunction] <;> ring

/-- The actual spectral derivative is the same dual factor times the
bilinear normalization, with the opposite i sign. -/
theorem deriv_classicalDirichletCharacteristic_of_root (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0) :
    deriv (classicalSeparatedCharacteristic .dirichlet Φ) z =
      -I*classicalDirichletDualFactor Φ z*classicalDirichletNormalization Φ z := by
  have he : classicalSeparatedCharacteristic .dirichlet Φ =
      fun w => classicalSeparatedEndpointCLM .dirichlet (classicalSolution Φ w (1,1) 1) := by
    funext w
    exact classicalSeparatedCharacteristic_eq_endpoint .dirichlet Φ w
  rw [he,deriv_classicalEndpoint_eq_spectral_integral]
  have hi : (∫ t in (0 : ℝ)..1, -I*
      ((classicalSolution Φ z (classicalEndpointDualInitial Φ z (classicalSeparatedEndpointCLM .dirichlet)) t).2*
        (classicalSolution Φ z (1,1) t).1+
       (classicalSolution Φ z (classicalEndpointDualInitial Φ z (classicalSeparatedEndpointCLM .dirichlet)) t).1*
        (classicalSolution Φ z (1,1) t).2)) =
      ∫ t in (0 : ℝ)..1, (-2*I*classicalDirichletDualFactor Φ z)*
        ((classicalDirichletEigenfunction Φ z t).1*(classicalDirichletEigenfunction Φ z t).2) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    dsimp only
    change -I*((classicalSolution Φ z (classicalSeparatedDualInitial .dirichlet Φ z) t).2*_+
      (classicalSolution Φ z (classicalSeparatedDualInitial .dirichlet Φ z) t).1*_) = _
    rw [classicalDirichletDualSolution_of_root Φ z hz ⟨t,ht'⟩]
    simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,classicalDirichletEigenfunction]
    ring
  rw [hi,intervalIntegral.integral_const_mul]
  unfold classicalDirichletNormalization
  ring

/-- Simplicity supplies nonzero normalization; it need not be assumed separately. -/
theorem classicalDirichletNormalization_ne_zero_of_simple (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0)
    (hsimple : deriv (classicalSeparatedCharacteristic .dirichlet Φ) z ≠ 0) :
    classicalDirichletNormalization Φ z ≠ 0 := by
  rw [deriv_classicalDirichletCharacteristic_of_root Φ z hz] at hsimple
  exact (mul_ne_zero_iff.mp hsimple).2

/-- The squared-eigenfunction expression for the Dirichlet eigenvalue gradient. -/
def classicalDirichletNormalizedGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  ((classicalDirichletEigenfunction Φ z t).2^2/classicalDirichletNormalization Φ z,
   (classicalDirichletEigenfunction Φ z t).1^2/classicalDirichletNormalization Φ z)

/-- The implicit-root quotient of actual characteristic derivatives is
exactly the normalized squared-eigenfunction expression in G.7. -/
theorem classicalDirichletNormalizedGradient_eq_characteristic_quotient
    (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (hz : classicalSeparatedCharacteristic .dirichlet Φ z = 0)
    (hsimple : deriv (classicalSeparatedCharacteristic .dirichlet Φ) z ≠ 0)
    (t : Icc (0 : ℝ) 1) :
    classicalDirichletNormalizedGradient Φ z t =
      -(deriv (classicalSeparatedCharacteristic .dirichlet Φ) z)⁻¹ •
        classicalSeparatedGradient .dirichlet Φ z t := by
  have hQ := classicalDirichletNormalization_ne_zero_of_simple Φ z hz hsimple
  have hα := classicalDirichletDualFactor_ne_zero Φ z hz
  rw [classicalSeparatedGradient_dirichlet_of_root Φ z hz t,
    deriv_classicalDirichletCharacteristic_of_root Φ z hz]
  apply Prod.ext <;> simp only [classicalDirichletNormalizedGradient,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals field_simp [hQ,hα,I_ne_zero]

/-- The free normalization is exactly two at every complex spectral parameter. -/
@[simp] theorem classicalDirichletNormalization_free (z : ℂ) :
    classicalDirichletNormalization 0 z = 2 := by
  have hi : (∫ t in (0 : ℝ)..1,
      (classicalDirichletEigenfunction 0 z t).1*(classicalDirichletEigenfunction 0 z t).2) = 1 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (1 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        dsimp only [classicalDirichletEigenfunction]
        rw [classicalSolution_free z (1,1) ⟨t,ht'⟩]
        simp only [mul_one]
        rw [← exp_add, show -I*z*(t : ℂ)+I*z*(t : ℂ) = 0 by ring, exp_zero]
      _ = 1 := by simp
  exact congrArg (fun w : ℂ => 2*w) hi |>.trans (mul_one 2)

/-- The free normalized gradient has exactly the two opposite waves and factor one half. -/
theorem classicalDirichletNormalizedGradient_free (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalDirichletNormalizedGradient 0 z t =
      (exp (2*I*z*t.val)/2,exp (-2*I*z*t.val)/2) := by
  apply Prod.ext <;> simp only [classicalDirichletNormalizedGradient,classicalDirichletNormalization_free,
    classicalDirichletEigenfunction,classicalSolution_free,mul_one]
  all_goals
    congr 1
    rw [pow_two,← exp_add]
    congr 1
    ring

end NLS.ZakharovShabat
