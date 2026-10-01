import NLS.ZakharovShabat.ClassicalDiscriminantGradient

/-! # Spectral commutation of the actual physical discriminant gradients

The diagonal difference of the transported monodromy completes the two
potential-gradient components to a closed first-order system. A quadratic
pairing of two such systems has derivative equal to the antisymmetric
physical pairing, multiplied by the spectral-parameter difference. Its
matching endpoint values prove commutation, including coincident parameters.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The diagonal difference of `M(s) T M(s)⁻¹`, written through the actual
normalized columns and determinant-one adjugate. -/
def classicalDiscriminantDiagonal (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) : ℂ :=
  let a := classicalSolution Φ z (1,0) s
  let b := classicalSolution Φ z (0,1) s
  let T := classicalMonodromy Φ z
  (T 0 0-T 1 1)*(a.1*b.2+a.2*b.1)-2*T 0 1*a.1*a.2+2*T 1 0*b.1*b.2

theorem continuous_classicalDiscriminantDiagonal (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalDiscriminantDiagonal Φ z) := by
  have ha := continuous_classicalSolution Φ z (1,0)
  have hb := continuous_classicalSolution Φ z (0,1)
  unfold classicalDiscriminantDiagonal
  fun_prop

@[simp] theorem classicalDiscriminantDiagonal_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantDiagonal Φ z 0 = classicalMonodromy Φ z 0 0-classicalMonodromy Φ z 1 1 := by
  simp [classicalDiscriminantDiagonal]

@[simp] theorem classicalDiscriminantDiagonal_one (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantDiagonal Φ z 1 = classicalMonodromy Φ z 0 0-classicalMonodromy Φ z 1 1 := by
  have hdet := det_classicalMonodromy Φ z
  simp only [Matrix.det_fin_two] at hdet
  let T := classicalMonodromy Φ z
  change T 0 0*T 1 1-T 0 1*T 1 0 = 1 at hdet
  change (T 0 0-T 1 1)*(T 0 0*T 1 1+T 1 0*T 0 1)-
    2*T 0 1*T 0 0*T 1 0+2*T 1 0*T 0 1*T 1 1 = T 0 0-T 1 1
  linear_combination (T 0 0-T 1 1)*hdet

theorem hasDerivAt_classicalDiscriminantGradient_fst (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => (classicalDiscriminantGradient Φ z s).1)
      (2*I*z*(classicalDiscriminantGradient Φ z t).1+
        (Φ t).2*classicalDiscriminantDiagonal Φ z t) t := by
  have ha := hasDerivAt_classicalSolution Φ z (1,0) t
  have hb := hasDerivAt_classicalSolution Φ z (0,1) t
  have ha₂ := HasFDerivAt.hasDerivAt ha.snd
  have hb₂ := HasFDerivAt.hasDerivAt hb.snd
  let T := classicalMonodromy Φ z
  have h := ((((ha₂.const_mul (T 0 0-T 1 1)).mul hb₂).sub
    ((ha₂.pow 2).const_mul (T 0 1))).add ((hb₂.pow 2).const_mul (T 1 0))).const_mul I
  convert! h using 1
  simp only [classicalDiscriminantGradient,classicalDiscriminantDiagonal,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,T]
  dsimp
  ring_nf
  simp only [I_sq]
  ring

theorem hasDerivAt_classicalDiscriminantGradient_snd (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => (classicalDiscriminantGradient Φ z s).2)
      (-2*I*z*(classicalDiscriminantGradient Φ z t).2-
        (Φ t).1*classicalDiscriminantDiagonal Φ z t) t := by
  have ha := hasDerivAt_classicalSolution Φ z (1,0) t
  have hb := hasDerivAt_classicalSolution Φ z (0,1) t
  have ha₁ := HasFDerivAt.hasDerivAt ha.fst
  have hb₁ := HasFDerivAt.hasDerivAt hb.fst
  let T := classicalMonodromy Φ z
  have h := ((((ha₁.const_mul (T 0 0-T 1 1)).mul hb₁).sub
    ((ha₁.pow 2).const_mul (T 0 1))).add ((hb₁.pow 2).const_mul (T 1 0))).const_mul I
  convert! h using 1
  simp only [classicalDiscriminantGradient,classicalDiscriminantDiagonal,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,T]
  dsimp
  ring_nf
  simp only [I_sq]
  ring

theorem hasDerivAt_classicalDiscriminantDiagonal (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalDiscriminantDiagonal Φ z)
      (2*((Φ t).1*(classicalDiscriminantGradient Φ z t).1-
        (Φ t).2*(classicalDiscriminantGradient Φ z t).2)) t := by
  have ha := hasDerivAt_classicalSolution Φ z (1,0) t
  have hb := hasDerivAt_classicalSolution Φ z (0,1) t
  have ha₁ := HasFDerivAt.hasDerivAt ha.fst
  have ha₂ := HasFDerivAt.hasDerivAt ha.snd
  have hb₁ := HasFDerivAt.hasDerivAt hb.fst
  have hb₂ := HasFDerivAt.hasDerivAt hb.snd
  let T := classicalMonodromy Φ z
  have h := (((ha₁.mul hb₂).add (ha₂.mul hb₁)).const_mul (T 0 0-T 1 1)).sub
    (((ha₁.const_mul (2*T 0 1)).mul ha₂)) |>.add ((hb₁.const_mul (2*T 1 0)).mul hb₂)
  convert! h using 1
  simp only [classicalDiscriminantGradient,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,T]
  dsimp
  ring

/-- The unconjugated antisymmetric physical gradient pairing. -/
def classicalDiscriminantPairing (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : ℝ) : ℂ :=
  (classicalDiscriminantGradient Φ z s).1*(classicalDiscriminantGradient Φ w s).2-
    (classicalDiscriminantGradient Φ z s).2*(classicalDiscriminantGradient Φ w s).1

theorem continuous_classicalDiscriminantPairing (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    Continuous (classicalDiscriminantPairing Φ z w) := by
  have hz := continuous_classicalDiscriminantGradient Φ z
  have hw := continuous_classicalDiscriminantGradient Φ w
  exact (hz.fst.mul hw.snd).sub (hz.snd.mul hw.fst)

/-- The nonconstant part of the trace pairing of the two transported
monodromies. The fixed trace product has zero derivative. -/
def classicalDiscriminantPairingPrimitive (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : ℝ) : ℂ :=
  (classicalDiscriminantGradient Φ z s).1*(classicalDiscriminantGradient Φ w s).2+
    (classicalDiscriminantGradient Φ z s).2*(classicalDiscriminantGradient Φ w s).1+
      classicalDiscriminantDiagonal Φ z s*classicalDiscriminantDiagonal Φ w s/2

theorem continuous_classicalDiscriminantPairingPrimitive (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    Continuous (classicalDiscriminantPairingPrimitive Φ z w) := by
  have hz := continuous_classicalDiscriminantGradient Φ z
  have hw := continuous_classicalDiscriminantGradient Φ w
  have hdz := continuous_classicalDiscriminantDiagonal Φ z
  have hdw := continuous_classicalDiscriminantDiagonal Φ w
  exact ((hz.fst.mul hw.snd).add (hz.snd.mul hw.fst)).add ((hdz.mul hdw).div_const 2)

theorem classicalDiscriminantPairingPrimitive_endpoints (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    classicalDiscriminantPairingPrimitive Φ z w 1 = classicalDiscriminantPairingPrimitive Φ z w 0 := by
  simp [classicalDiscriminantPairingPrimitive]

/-- Differentiating the trace pairing leaves only the spectral-parameter
difference times the antisymmetric gradient pairing. -/
theorem hasDerivAt_classicalDiscriminantPairingPrimitive (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalDiscriminantPairingPrimitive Φ z w)
      (2*I*(z-w)*classicalDiscriminantPairing Φ z w t) t := by
  have hz₁ := hasDerivAt_classicalDiscriminantGradient_fst Φ z t
  have hz₂ := hasDerivAt_classicalDiscriminantGradient_snd Φ z t
  have hw₁ := hasDerivAt_classicalDiscriminantGradient_fst Φ w t
  have hw₂ := hasDerivAt_classicalDiscriminantGradient_snd Φ w t
  have hdz := hasDerivAt_classicalDiscriminantDiagonal Φ z t
  have hdw := hasDerivAt_classicalDiscriminantDiagonal Φ w t
  have h := ((hz₁.mul hw₂).add (hz₂.mul hw₁)).add ((hdz.mul hdw).div_const 2)
  convert! h using 1
  unfold classicalDiscriminantPairing
  ring

/-- The actual physical discriminant gradients commute at all spectral
parameters and all continuous complex potentials. At distinct parameters
this is boundary cancellation; at coincident parameters it is antisymmetry. -/
theorem integral_classicalDiscriminantPairing_eq_zero (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    (∫ s in (0 : ℝ)..1, classicalDiscriminantPairing Φ z w s) = 0 := by
  by_cases hzw : z = w
  · subst w
    simp [classicalDiscriminantPairing,mul_comm]
  have hc : Continuous (fun s => 2*I*(z-w)*classicalDiscriminantPairing Φ z w s) :=
    continuous_const.mul (continuous_classicalDiscriminantPairing Φ z w)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_classicalDiscriminantPairingPrimitive Φ z w).continuousOn
    (fun s (hs : s ∈ Ioo (0 : ℝ) 1) =>
      hasDerivAt_classicalDiscriminantPairingPrimitive Φ z w ⟨s,⟨hs.1.le,hs.2.le⟩⟩)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul,classicalDiscriminantPairingPrimitive_endpoints,sub_self] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (sub_ne_zero.mpr hzw))

/-- The Hamiltonian direction generated by the actual discriminant at `w`,
with the original physical Poisson sign `-i`. -/
def classicalDiscriminantHamiltonianDirection (Φ : Curve (ℂ × ℂ)) (w : ℂ) : Curve (ℂ × ℂ) :=
  ⟨fun t => (-I*(classicalDiscriminantGradient Φ w t).2,I*(classicalDiscriminantGradient Φ w t).1),by
    have hg : Continuous (fun t : Icc (0 : ℝ) 1 => classicalDiscriminantGradient Φ w t) :=
      (continuous_classicalDiscriminantGradient Φ w).comp continuous_subtype_val
    exact (continuous_const.mul hg.snd).prodMk (continuous_const.mul hg.fst)⟩

/-- The genuine Frechet derivative of the classical discriminant vanishes
in the Hamiltonian direction of every other classical discriminant. -/
theorem fderiv_classicalDiscriminant_hamiltonian_eq_zero (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ)
      (classicalDiscriminantHamiltonianDirection Φ w) = 0 := by
  rw [fderiv_classicalDiscriminant_eq_gradient_integral]
  calc
    _ = -I*(∫ s in (0 : ℝ)..1, classicalDiscriminantPairing Φ z w s) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs',
        classicalDiscriminantHamiltonianDirection,ContinuousMap.coe_mk,classicalDiscriminantPairing]
      ring
    _ = 0 := by rw [integral_classicalDiscriminantPairing_eq_zero,mul_zero]

end NLS.ZakharovShabat
