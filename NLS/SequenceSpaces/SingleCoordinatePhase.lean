import NLS.SequenceSpaces.ModulusFiberInvariance
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Differentiable one-coordinate phase rotations and full modulus fibers -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS

def lpCoordinatePhase {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k : α) (t : ℝ) : lp (fun _ : α => ℂ) p :=
  lpReplaceCoordinate z k (Complex.exp ((t : ℂ)*I)*z k)

theorem lpCoordinatePhase_apply {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k j : α) (t : ℝ) :
    lpCoordinatePhase z k t j = if j = k then Complex.exp ((t : ℂ)*I)*z k else z j := by
  classical
  simp only [lpCoordinatePhase,lpReplaceCoordinate,lp.coeFn_add,Pi.add_apply,lp.single_apply]
  by_cases hj : j = k <;> simp [hj]

theorem lpCoordinatePhase_zero {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k : α) : lpCoordinatePhase z k 0 = z := by
  ext j
  simp only [lpCoordinatePhase_apply,ofReal_zero,zero_mul,Complex.exp_zero,one_mul]
  split_ifs with h <;> simp [h]

theorem norm_lpCoordinatePhase_apply {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k j : α) (t : ℝ) :
    ‖lpCoordinatePhase z k t j‖ = ‖z j‖ := by
  rw [lpCoordinatePhase_apply]
  split_ifs with h
  · subst j
    simp only [norm_mul,Complex.norm_exp,mul_re,ofReal_re,I_re,I_im,ofReal_im,
      mul_zero,zero_mul,sub_self,Real.exp_zero,one_mul]
  · rfl

theorem differentiable_lpCoordinatePhase {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (z : lp (fun _ : α => ℂ) p) (k : α) : Differentiable ℝ (lpCoordinatePhase z k) := by
  classical
  have he : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ)*I)) :=
    Complex.differentiable_exp.comp (Complex.differentiable_ofReal.mul_const I)
  have hs : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ)*I)*z k-z k) :=
    (he.mul_const (z k)).sub_const (z k)
  exact (differentiable_const z).add
    (((lp.singleContinuousLinearMap ℂ (fun _ : α => ℂ) p k).restrictScalars ℝ).differentiable.comp hs)

/-- Equal-modulus complex scalars are connected by a genuine smooth phase
rotation, including the zero coordinate. -/
theorem exists_exp_phase_mul_eq_of_norm_eq (a b : ℂ) (h : ‖a‖ = ‖b‖) :
    ∃ t : ℝ, Complex.exp ((t : ℂ)*I)*a = b := by
  refine ⟨b.arg-a.arg,?_⟩
  calc
    _ = Complex.exp (((b.arg-a.arg : ℝ) : ℂ)*I)*
        ((‖a‖ : ℂ)*Complex.exp ((a.arg : ℂ)*I)) :=
      congrArg (fun c => Complex.exp (((b.arg-a.arg : ℝ) : ℂ)*I)*c)
        (Complex.norm_mul_exp_arg_mul_I a).symm
    _ = (‖a‖ : ℂ)*Complex.exp ((b.arg : ℂ)*I) := by
      rw [mul_left_comm,←Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = b := by rw [h,Complex.norm_mul_exp_arg_mul_I]

/-- Invariance under the actual differentiable one-coordinate rotations
determines every full infinite-dimensional equal-modulus fiber. -/
theorem eq_of_coordinate_moduli_of_phase_invariance
    {α : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {F : Type*} [TopologicalSpace F] [T2Space F]
    (f : lp (fun _ : α => ℂ) p → F) (hf : Continuous f)
    (hinv : ∀ z k t, f (lpCoordinatePhase z k t) = f z)
    (z w : lp (fun _ : α => ℂ) p) (he : ∀ k, ‖z k‖ = ‖w k‖) : f w = f z := by
  apply eq_of_coordinate_moduli_of_replace_invariance hp f hf _ z w he
  intro v k c hc
  obtain ⟨t,ht⟩ := exists_exp_phase_mul_eq_of_norm_eq (v k) c hc.symm
  simpa only [lpCoordinatePhase,ht] using hinv v k t

end NLS
