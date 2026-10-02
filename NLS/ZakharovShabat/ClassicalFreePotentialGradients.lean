import NLS.ZakharovShabat.ClassicalFreeDiscriminant
import NLS.ZakharovShabat.ClassicalAntiDiscriminantGradient
import NLS.Fourier.IntervalBilinearParseval

/-! # Free physical gradients at the signed spectral lattice

The actual variation-of-constants gradients at zero potential are
explicit Fourier waves. The two components have opposite frequencies;
the anti-discriminant also has the opposite second-component sign.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

private theorem free_lattice_exponentials (n : ℤ) :
    exp (I*((Real.pi : ℂ)*n)) = cos ((Real.pi : ℂ)*n) ∧
      exp (-I*((Real.pi : ℂ)*n)) = cos ((Real.pi : ℂ)*n) := by
  have hs : sin ((Real.pi : ℂ)*n) = 0 := by rw [mul_comm]; exact sin_int_mul_pi n
  constructor
  · rw [mul_comm,exp_mul_I,hs,zero_mul,add_zero]
  · rw [show -I*((Real.pi : ℂ)*n) = (-((Real.pi : ℂ)*n))*I by ring,
      exp_mul_I,cos_neg,sin_neg,hs,neg_zero,zero_mul,add_zero]

private theorem free_lattice_wave_squares (n : ℤ) (s : ℝ) :
    exp (I*((Real.pi : ℂ)*n)*s)^2 = wave (2*n) s ∧
      exp (-I*((Real.pi : ℂ)*n)*s)^2 = wave (-(2*n)) s := by
  constructor <;> rw [pow_two,← exp_add] <;> unfold wave <;> congr 1 <;> push_cast <;> ring

/-- The original separated characteristic gradient at zero, with its
Dirichlet/Neumann sign and exact sine normalization. -/
theorem classicalSeparatedGradient_free_lattice
    (b : BoundaryCondition) (n : ℤ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    classicalSeparatedGradient b 0 ((Real.pi : ℂ)*n) s =
      (-(BoundaryCondition.extensionSign b * cos ((Real.pi : ℂ)*n))/2 * wave (2*n) s,
       -(BoundaryCondition.extensionSign b * cos ((Real.pi : ℂ)*n))/2 * wave (-(2*n)) s) := by
  have hf (v : ℂ × ℂ) := classicalSolution_free ((Real.pi : ℂ)*n) v ⟨s,hs⟩
  have h1 (v : ℂ × ℂ) : classicalSolution 0 ((Real.pi : ℂ)*n) v 1 =
      (cos ((Real.pi : ℂ)*n)*v.1,cos ((Real.pi : ℂ)*n)*v.2) := by
    simpa only [Complex.ofReal_one,mul_one,(free_lattice_exponentials n).1,(free_lattice_exponentials n).2]
      using classicalSolution_free ((Real.pi : ℂ)*n) v ⟨1,by constructor <;> norm_num⟩
  have hw := free_lattice_wave_squares n s
  unfold classicalSeparatedGradient classicalEndpointGradient
  simp only [hf,h1]
  simp only [classicalSeparatedEndpointCLM_apply,mul_one,mul_zero,sub_zero,zero_sub]
  rw [← hw.1,← hw.2]
  apply Prod.ext <;> dsimp <;> field_simp

/-- The physical gradient of the off-diagonal monodromy sum at zero. -/
theorem classicalAntiDiscriminantGradient_free_lattice
    (n : ℤ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    classicalAntiDiscriminantGradient 0 ((Real.pi : ℂ)*n) s =
      (I*cos ((Real.pi : ℂ)*n)*wave (2*n) s,
       -I*cos ((Real.pi : ℂ)*n)*wave (-(2*n)) s) := by
  have hf (v : ℂ × ℂ) := classicalSolution_free ((Real.pi : ℂ)*n) v ⟨s,hs⟩
  have h1 (v : ℂ × ℂ) : classicalSolution 0 ((Real.pi : ℂ)*n) v 1 =
      (cos ((Real.pi : ℂ)*n)*v.1,cos ((Real.pi : ℂ)*n)*v.2) := by
    simpa only [Complex.ofReal_one,mul_one,(free_lattice_exponentials n).1,(free_lattice_exponentials n).2]
      using classicalSolution_free ((Real.pi : ℂ)*n) v ⟨1,by constructor <;> norm_num⟩
  have hw := free_lattice_wave_squares n s
  unfold classicalAntiDiscriminantGradient classicalEndpointGradient
  simp only [hf,h1]
  simp only [ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',mul_one,mul_zero,sub_zero,zero_sub]
  rw [← hw.1,← hw.2]
  apply Prod.ext <;> dsimp <;> ring

/-- The free discriminant has zero first potential variation at every
spectral parameter, not only at the free lattice. -/
theorem classicalDiscriminantGradient_free
    (z : ℂ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    classicalDiscriminantGradient 0 z s = 0 := by
  have hf (v : ℂ × ℂ) := classicalSolution_free z v ⟨s,hs⟩
  have hM := classicalFundamentalMatrix_free z ⟨1,by constructor <;> norm_num⟩
  change classicalMonodromy 0 z = _ at hM
  simp [classicalDiscriminantGradient,hf,hM]

end NLS.ZakharovShabat
