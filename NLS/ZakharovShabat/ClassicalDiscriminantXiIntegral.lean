import NLS.ZakharovShabat.DiscriminantGradientStateAlgebra
import NLS.ZakharovShabat.ClassicalDiscriminantGradient

/-! # Normalized scalar transport with the physical discriminant convention

The operator is diag(i,-i)*d/dx + [[0,phi1],[phi2,0]], as in the paper's
Section 2. The discriminant is the actual normalized monodromy trace;
the gradient represents its unconjugated Fréchet derivative. These choices
fix both the spectral spatial term and the nonlocal sign together.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalDiscriminantXi (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) : ℂ :=
  discriminantXiState (classicalMonodromy Φ z)
    (classicalSolution Φ z (1,0) x) (classicalSolution Φ z (0,1) x)

def classicalDiscriminantRPairing (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) : ℂ :=
  (I*(extend Φ x).1)*(classicalDiscriminantGradient Φ z x).1+
  (-I*(extend Φ x).2)*(classicalDiscriminantGradient Φ z x).2

theorem continuous_classicalDiscriminantRPairing (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalDiscriminantRPairing Φ z) := by
  change Continuous (fun x => classicalDiscriminantRPairing Φ z x)
  have hg := continuous_classicalDiscriminantGradient Φ z
  have hp := continuous_extend Φ
  unfold classicalDiscriminantRPairing
  fun_prop

theorem continuous_classicalDiscriminantXi (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalDiscriminantXi Φ z) := by
  change Continuous (fun t => classicalDiscriminantXi Φ z t)
  have h1 := continuous_classicalSolution Φ z (1,0)
  have h2 := continuous_classicalSolution Φ z (0,1)
  unfold classicalDiscriminantXi discriminantXiState
  fun_prop

theorem hasDerivAt_classicalDiscriminantXi (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (x : Icc (0:ℝ) 1) :
    HasDerivAt (classicalDiscriminantXi Φ z)
      (-2*I*classicalDiscriminantRPairing Φ z x) x := by
  have h := hasDerivAt_discriminantXiState (classicalMonodromy Φ z)
    (classicalSolution Φ z (1,0)) (classicalSolution Φ z (0,1)) (Φ x) z x
    (hasDerivAt_classicalSolution Φ z (1,0) x) (hasDerivAt_classicalSolution Φ z (0,1) x)
  convert! h using 1
  simp only [classicalDiscriminantRPairing,extend_coe,classicalDiscriminantGradient,
    discriminantGradientState]
  ring_nf
  simp only [I_pow_three]
  ring

theorem hasDerivAt_classicalDiscriminantGradient_spatial
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : Icc (0:ℝ) 1) :
    HasDerivAt (classicalDiscriminantGradient Φ z)
      (2*I*z*(classicalDiscriminantGradient Φ z x).1+classicalDiscriminantXi Φ z x*(Φ x).2,
       -2*I*z*(classicalDiscriminantGradient Φ z x).2-classicalDiscriminantXi Φ z x*(Φ x).1) x := by
  exact hasDerivAt_discriminantGradientState (classicalMonodromy Φ z)
    (classicalSolution Φ z (1,0)) (classicalSolution Φ z (0,1)) (Φ x) z x
    (hasDerivAt_classicalSolution Φ z (1,0) x) (hasDerivAt_classicalSolution Φ z (0,1) x)

@[simp] theorem classicalDiscriminantXi_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantXi Φ z 0 = (classicalMonodromy Φ z) 0 0-(classicalMonodromy Φ z) 1 1 := by
  simp [classicalDiscriminantXi,discriminantXiState]

theorem classicalDiscriminantXi_eq_R_integral (Φ : Curve (ℂ × ℂ)) (z : ℂ)
    (x : Icc (0:ℝ) 1) :
    classicalDiscriminantXi Φ z x = (classicalMonodromy Φ z) 0 0-(classicalMonodromy Φ z) 1 1-
      2*I*∫ t in (0:ℝ)..x.val, classicalDiscriminantRPairing Φ z t := by
  have hcont := continuous_classicalDiscriminantXi Φ z
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le x.property.1
    hcont.continuousOn (fun t (ht : t ∈ Ioo (0:ℝ) x.val) =>
      hasDerivAt_classicalDiscriminantXi Φ z ⟨t,ht.1.le,ht.2.le.trans x.property.2⟩)
    ((continuous_const.mul (continuous_classicalDiscriminantRPairing Φ z)).intervalIntegrable 0 x.val)
  simp only [Pi.mul_apply] at hi
  rw [classicalDiscriminantXi_zero,intervalIntegral.integral_const_mul] at hi
  linear_combination -hi

/-- The paper's printed alternative, with the positive nonlocal sign. -/
def classicalPrintedDiscriminantXi (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) : ℂ :=
  (classicalMonodromy Φ z) 0 0-(classicalMonodromy Φ z) 1 1+
    2*I*∫ t in (0:ℝ)..x, classicalDiscriminantRPairing Φ z t

theorem hasDerivAt_classicalPrintedDiscriminantXi (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) :
    HasDerivAt (classicalPrintedDiscriminantXi Φ z)
      (2*I*classicalDiscriminantRPairing Φ z x) x := by
  have hc := continuous_classicalDiscriminantRPairing Φ z
  have h := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_mul (2*I)
  exact h.const_add _

end NLS.ZakharovShabat
