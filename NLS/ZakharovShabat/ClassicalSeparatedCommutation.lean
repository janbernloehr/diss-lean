import NLS.ZakharovShabat.ClassicalSeparatedGradient

/-! # Physical commutation of each actual separated characteristic family

The endpoint gradient factors into the original forward solution and a
dual homogeneous solution. The latter has a fixed endpoint independent
of spectral parameter. A product of the two cross-parameter Wronskians
vanishes at both endpoints; its derivative is the spectral difference
times the physical antisymmetric gradient pairing. This proves the
actual Dirichlet-Dirichlet and Neumann-Neumann cancellations.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The initial vector of the dual solution in the actual endpoint gradient. -/
def classicalSeparatedDualInitial (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) : ℂ × ℂ :=
  (-classicalSeparatedEndpointCLM b (classicalSolution Φ z (0,1) 1),
    classicalSeparatedEndpointCLM b (classicalSolution Φ z (1,0) 1))

/-- The dual homogeneous solution is the actual adjugate kernel combination. -/
theorem classicalSeparatedDualSolution_eq_columns
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (classicalSeparatedDualInitial b Φ z) t =
      classicalSeparatedEndpointCLM b (classicalSolution Φ z (1,0) 1) • classicalSolution Φ z (0,1) t-
        classicalSeparatedEndpointCLM b (classicalSolution Φ z (0,1) 1) • classicalSolution Φ z (1,0) t := by
  rw [classicalSolution_eq_columns Φ z (classicalSeparatedDualInitial b Φ z) t]
  apply Prod.ext <;> simp only [classicalSeparatedDualInitial,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

/-- The normalized dual endpoint is independent of spectral parameter and
potential. Its literal signs follow from determinant one. -/
theorem classicalSeparatedDualSolution_one
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSolution Φ z (classicalSeparatedDualInitial b Φ z) 1 =
      (-extensionSign b/(2*I),-1/(2*I)) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  rw [classicalSeparatedDualSolution_eq_columns b Φ z t]
  have hdet := det_classicalMonodromy Φ z
  simp only [Matrix.det_fin_two] at hdet
  let T := classicalMonodromy Φ z
  change T 0 0*T 1 1-T 0 1*T 1 0 = 1 at hdet
  apply Prod.ext
  all_goals simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    classicalSeparatedEndpointCLM_apply]
  · change ((extensionSign b*T 1 0-T 0 0)/(2*I))*T 0 1-
      ((extensionSign b*T 1 1-T 0 1)/(2*I))*T 0 0 = -extensionSign b/(2*I)
    linear_combination -(extensionSign b/(2*I))*hdet
  · change ((extensionSign b*T 1 0-T 0 0)/(2*I))*T 1 1-
      ((extensionSign b*T 1 1-T 0 1)/(2*I))*T 1 0 = -1/(2*I)
    linear_combination -(1/(2*I))*hdet

/-- The actual physical gradient factors into the forward and dual solutions. -/
theorem classicalSeparatedGradient_eq_solution_product
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSeparatedGradient b Φ z t =
      (I*(classicalSolution Φ z (classicalSeparatedDualInitial b Φ z) t).2*
          (classicalSolution Φ z (1,extensionSign b) t).2,
        I*(classicalSolution Φ z (classicalSeparatedDualInitial b Φ z) t).1*
          (classicalSolution Φ z (1,extensionSign b) t).1) := by
  rw [classicalSeparatedDualSolution_eq_columns b Φ z t]
  apply Prod.ext <;> simp only [classicalSeparatedGradient,classicalEndpointGradient,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

/-- Wronskian of two actual solutions at possibly different spectral parameters. -/
def classicalCrossWronskian (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v u : ℂ × ℂ) (s : ℝ) : ℂ :=
  (classicalSolution Φ z v s).1*(classicalSolution Φ w u s).2-
    (classicalSolution Φ z v s).2*(classicalSolution Φ w u s).1

theorem continuous_classicalCrossWronskian (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v u : ℂ × ℂ) :
    Continuous (classicalCrossWronskian Φ z w v u) := by
  have hz := continuous_classicalSolution Φ z v
  have hw := continuous_classicalSolution Φ w u
  exact (hz.fst.mul hw.snd).sub (hz.snd.mul hw.fst)

/-- The cross-parameter Wronskian derivative is its symmetric product
multiplied by the original signed spectral difference. -/
theorem hasDerivAt_classicalCrossWronskian (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (v u : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalCrossWronskian Φ z w v u)
      (I*(w-z)*((classicalSolution Φ z v t).1*(classicalSolution Φ w u t).2+
        (classicalSolution Φ z v t).2*(classicalSolution Φ w u t).1)) t := by
  have hz := hasDerivAt_classicalSolution Φ z v t
  have hw := hasDerivAt_classicalSolution Φ w u t
  have hz₁ := HasFDerivAt.hasDerivAt hz.fst
  have hz₂ := HasFDerivAt.hasDerivAt hz.snd
  have hw₁ := HasFDerivAt.hasDerivAt hw.fst
  have hw₂ := HasFDerivAt.hasDerivAt hw.snd
  have h := (hz₁.mul hw₂).sub (hz₂.mul hw₁)
  convert! h using 1
  simp only [classicalODECoefficient_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  ring

/-- The actual same-boundary physical gradient pairing. -/
def classicalSeparatedPairing (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : ℝ) : ℂ :=
  (classicalSeparatedGradient b Φ z s).1*(classicalSeparatedGradient b Φ w s).2-
    (classicalSeparatedGradient b Φ z s).2*(classicalSeparatedGradient b Φ w s).1

theorem continuous_classicalSeparatedPairing (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    Continuous (classicalSeparatedPairing b Φ z w) := by
  have hz := continuous_classicalSeparatedGradient b Φ z
  have hw := continuous_classicalSeparatedGradient b Φ w
  exact (hz.fst.mul hw.snd).sub (hz.snd.mul hw.fst)

/-- The forward Wronskian vanishes initially and the dual Wronskian finally. -/
def classicalSeparatedPairingPrimitive (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : ℝ) : ℂ :=
  classicalCrossWronskian Φ z w (1,extensionSign b) (1,extensionSign b) s*
    classicalCrossWronskian Φ z w (classicalSeparatedDualInitial b Φ z) (classicalSeparatedDualInitial b Φ w) s

theorem continuous_classicalSeparatedPairingPrimitive (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    Continuous (classicalSeparatedPairingPrimitive b Φ z w) :=
  (continuous_classicalCrossWronskian _ _ _ _ _).mul (continuous_classicalCrossWronskian _ _ _ _ _)

@[simp] theorem classicalSeparatedPairingPrimitive_zero (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    classicalSeparatedPairingPrimitive b Φ z w 0 = 0 := by
  simp [classicalSeparatedPairingPrimitive,classicalCrossWronskian]

@[simp] theorem classicalSeparatedPairingPrimitive_one (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    classicalSeparatedPairingPrimitive b Φ z w 1 = 0 := by
  simp [classicalSeparatedPairingPrimitive,classicalCrossWronskian,classicalSeparatedDualSolution_one,mul_comm]

/-- The derivative of the Wronskian product is precisely the physical
gradient pairing times the spectral difference, with no variation hypothesis. -/
theorem hasDerivAt_classicalSeparatedPairingPrimitive (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalSeparatedPairingPrimitive b Φ z w)
      (2*I*(w-z)*classicalSeparatedPairing b Φ z w t) t := by
  have h := (hasDerivAt_classicalCrossWronskian Φ z w (1,extensionSign b) (1,extensionSign b) t).mul
    (hasDerivAt_classicalCrossWronskian Φ z w (classicalSeparatedDualInitial b Φ z) (classicalSeparatedDualInitial b Φ w) t)
  convert! h using 1
  simp only [classicalSeparatedPairing,classicalSeparatedGradient_eq_solution_product b Φ z t,
    classicalSeparatedGradient_eq_solution_product b Φ w t,classicalCrossWronskian]
  ring_nf
  simp only [I_pow_three]
  ring

/-- Each actual separated characteristic family commutes physically for
every continuous complex potential and all spectral parameters. -/
theorem integral_classicalSeparatedPairing_eq_zero (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z w : ℂ) :
    (∫ s in (0 : ℝ)..1, classicalSeparatedPairing b Φ z w s) = 0 := by
  by_cases hzw : w = z
  · subst w
    simp [classicalSeparatedPairing,mul_comm]
  have hc : Continuous (fun s => 2*I*(w-z)*classicalSeparatedPairing b Φ z w s) :=
    continuous_const.mul (continuous_classicalSeparatedPairing b Φ z w)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_classicalSeparatedPairingPrimitive b Φ z w).continuousOn
    (fun s (hs : s ∈ Ioo (0 : ℝ) 1) =>
      hasDerivAt_classicalSeparatedPairingPrimitive b Φ z w ⟨s,⟨hs.1.le,hs.2.le⟩⟩)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul,classicalSeparatedPairingPrimitive_one,
    classicalSeparatedPairingPrimitive_zero,sub_self] at hi
  exact (mul_eq_zero.mp hi).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) (sub_ne_zero.mpr hzw))

end NLS.ZakharovShabat
