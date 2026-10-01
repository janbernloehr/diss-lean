import NLS.ZakharovShabat.ClassicalSeparatedCommutation

/-! # Actual physical brackets of arbitrary linear endpoint functionals

The potential gradients factor through a forward and dual solution.
Their cross-Wronskian product integrates the actual antisymmetric
gradient pairing. Its two endpoint values give a closed bracket law,
including coincident spectral parameters with the difference cleared.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalEndpointDualInitial (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) : ℂ × ℂ :=
  (-ℓ (classicalSolution Φ z (0,1) 1),ℓ (classicalSolution Φ z (1,0) 1))

theorem classicalEndpointDualSolution_eq_columns
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) t =
      ℓ (classicalSolution Φ z (1,0) 1) • classicalSolution Φ z (0,1) t-
        ℓ (classicalSolution Φ z (0,1) 1) • classicalSolution Φ z (1,0) t := by
  rw [classicalSolution_eq_columns Φ z (classicalEndpointDualInitial Φ z ℓ) t]
  apply Prod.ext <;> simp only [classicalEndpointDualInitial,Prod.fst_add,Prod.snd_add,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem classicalEndpointCLM_eq_coordinates (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (v : ℂ × ℂ) :
    ℓ v = v.1*ℓ (1,0)+v.2*ℓ (0,1) := by
  have hv : v = v.1 • ((1 : ℂ),0)+v.2 • ((0 : ℂ),1) := by
    ext <;> simp
  calc
    ℓ v = ℓ (v.1 • ((1 : ℂ),0)+v.2 • ((0 : ℂ),1)) := congrArg ℓ hv
    _ = _ := by rw [map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul]

/-- Unimodularity gives the actual dual endpoint for every continuous
linear endpoint functional, with its original coordinate signs. -/
theorem classicalEndpointDualSolution_one
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) :
    classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) 1 = (-ℓ (0,1),ℓ (1,0)) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  rw [classicalEndpointDualSolution_eq_columns Φ z ℓ t]
  have hdet := det_classicalMonodromy Φ z
  simp only [Matrix.det_fin_two] at hdet
  let T := classicalMonodromy Φ z
  change T 0 0*T 1 1-T 0 1*T 1 0 = 1 at hdet
  apply Prod.ext
  all_goals simp only [Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  all_goals rw [classicalEndpointCLM_eq_coordinates ℓ (classicalSolution Φ z (1,0) 1),
    classicalEndpointCLM_eq_coordinates ℓ (classicalSolution Φ z (0,1) 1)]
  · change (T 0 0*ℓ (1,0)+T 1 0*ℓ (0,1))*T 0 1-
      (T 0 1*ℓ (1,0)+T 1 1*ℓ (0,1))*T 0 0 = -ℓ (0,1)
    linear_combination -ℓ (0,1)*hdet
  · change (T 0 0*ℓ (1,0)+T 1 0*ℓ (0,1))*T 1 1-
      (T 0 1*ℓ (1,0)+T 1 1*ℓ (0,1))*T 1 0 = ℓ (1,0)
    linear_combination ℓ (1,0)*hdet

theorem classicalEndpointGradient_eq_solution_product
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalEndpointGradient Φ z v ℓ t =
      (I*(classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) t).2*(classicalSolution Φ z v t).2,
        I*(classicalSolution Φ z (classicalEndpointDualInitial Φ z ℓ) t).1*(classicalSolution Φ z v t).1) := by
  rw [classicalEndpointDualSolution_eq_columns Φ z ℓ t]
  apply Prod.ext <;> simp only [classicalEndpointGradient,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul]

def classicalEndpointPairing (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ :=
  (classicalEndpointGradient Φ z v ℓ s).1*(classicalEndpointGradient Φ w u k s).2-
    (classicalEndpointGradient Φ z v ℓ s).2*(classicalEndpointGradient Φ w u k s).1

theorem continuous_classicalEndpointPairing (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ) :
    Continuous (classicalEndpointPairing Φ z w v ℓ u k) := by
  have hz := continuous_classicalEndpointGradient Φ z v ℓ
  have hw := continuous_classicalEndpointGradient Φ w u k
  exact (hz.fst.mul hw.snd).sub (hz.snd.mul hw.fst)

def classicalEndpointPairingPrimitive (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ :=
  classicalCrossWronskian Φ z w v u s*
    classicalCrossWronskian Φ z w (classicalEndpointDualInitial Φ z ℓ) (classicalEndpointDualInitial Φ w k) s

theorem hasDerivAt_classicalEndpointPairingPrimitive (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalEndpointPairingPrimitive Φ z w v ℓ u k)
      (2*I*(w-z)*classicalEndpointPairing Φ z w v ℓ u k t) t := by
  have h := (hasDerivAt_classicalCrossWronskian Φ z w v u t).mul
    (hasDerivAt_classicalCrossWronskian Φ z w (classicalEndpointDualInitial Φ z ℓ)
      (classicalEndpointDualInitial Φ w k) t)
  convert! h using 1
  simp only [classicalEndpointPairing,classicalEndpointGradient_eq_solution_product Φ z v ℓ t,
    classicalEndpointGradient_eq_solution_product Φ w u k t,classicalCrossWronskian]
  ring_nf
  simp only [I_pow_three]
  ring

/-- The physical bracket of the two actual endpoint gradient integrals. -/
def classicalEndpointPoissonBracket (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ) : ℂ :=
  -I*(∫ s in (0 : ℝ)..1, classicalEndpointPairing Φ z w v ℓ u k s)

/-- The full physical bracket is determined by the two Wronskian-product
endpoint values, with the spectral difference retained as a factor. -/
theorem classicalEndpointPoissonBracket_mul (Φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (u : ℂ × ℂ) (k : (ℂ × ℂ) →L[ℂ] ℂ) :
    2*(z-w)*classicalEndpointPoissonBracket Φ z w v ℓ u k =
      (ℓ (1,0)*k (0,1)-ℓ (0,1)*k (1,0))*
        classicalCrossWronskian Φ z w v u 1-
      (v.1*u.2-v.2*u.1)*
        (ℓ (classicalSolution Φ z (1,0) 1)*k (classicalSolution Φ w (0,1) 1)-
          ℓ (classicalSolution Φ z (0,1) 1)*k (classicalSolution Φ w (1,0) 1)) := by
  have hc : Continuous (fun s => 2*I*(w-z)*classicalEndpointPairing Φ z w v ℓ u k s) :=
    continuous_const.mul (continuous_classicalEndpointPairing Φ z w v ℓ u k)
  have hprim : Continuous (classicalEndpointPairingPrimitive Φ z w v ℓ u k) :=
    (continuous_classicalCrossWronskian _ _ _ _ _).mul (continuous_classicalCrossWronskian _ _ _ _ _)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hprim.continuousOn
    (fun s (hs : s ∈ Ioo (0 : ℝ) 1) =>
      hasDerivAt_classicalEndpointPairingPrimitive Φ z w v ℓ u k ⟨s,⟨hs.1.le,hs.2.le⟩⟩)
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [classicalEndpointPairingPrimitive,classicalCrossWronskian] at hi
  rw [classicalEndpointDualSolution_one,classicalEndpointDualSolution_one] at hi
  simp only [classicalSolution_zero,classicalEndpointDualInitial] at hi
  unfold classicalEndpointPoissonBracket classicalCrossWronskian
  linear_combination hi

end NLS.ZakharovShabat
