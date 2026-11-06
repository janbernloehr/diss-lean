import NLS.KdV.SingularHillFreeMultiplicity
import NLS.KdV.SingularHillRealSpectrum
import NLS.SequenceSpaces.WeightedSingle

/-! # The free ground root space is exactly the constants

All statements retain the original H1 domain and H^-1 base space.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

theorem singularHillOperator_zero : singularHillOperator (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) =
    singularHillLaplacian := by
  have hz := (hminusOneMultiplicationFamily (L := 2)).map_zero
  change hminusOneMultiplication (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) = 0 at hz
  rw [singularHillOperator,hz,add_zero]

theorem singularHillFreeGround_coefficient_zero
    (f : singularHillEigenspace (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0) (k : ℤ) (hk : k ≠ 0) :
    f.val.val (mode (-k)) = 0 := by
  have he := (mem_singularHillEigenspace_iff _ _ _).mp f.property
  have hc := congrArg (fun u : FourierLebesgueSpace (2 : ℝ) (-1) 2 => u.val (mode (-k))) he
  rw [singularHillOperator_zero,singularHillLaplacian_coefficient,zero_smul] at hc
  have hc' : (freeHillValue k : ℂ)*f.val.val (mode (-k)) = 0 := hc
  apply (mul_eq_zero.mp hc').resolve_left
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero) (pow_ne_zero 2 (by exact_mod_cast hk))

def singularHillFreeGroundEvaluation : singularHillEigenspace
    (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0 →ₗ[ℂ] ℂ where
  toFun f := f.val.val (mode 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem singularHillFreeGroundEvaluation_injective : Function.Injective singularHillFreeGroundEvaluation := by
  intro f g he
  apply Subtype.ext
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  by_cases hk : k = 0
  · subst k
    exact he
  · rw [singularHillFreeGround_coefficient_zero f k hk,singularHillFreeGround_coefficient_zero g k hk]

theorem singularHillFreeGroundEvaluation_surjective : Function.Surjective singularHillFreeGroundEvaluation := by
  intro c
  let f := (sobolevCoefficients (L := 2) 1 2).symm (WeightedCoeff.single (p := 2) (Weight.sobolev 1) 0 c)
  have hfc (k : ℤ) : f.val (mode (-k)) = if k = 0 then c else 0 := by
    change ((sobolevCoefficients (L := 2) 1 2) ((sobolevCoefficients (L := 2) 1 2).symm _)).val k = _
    rw [LinearIsometryEquiv.apply_symm_apply,WeightedCoeff.single_val]
    simp [Pi.single_apply]
  have hf : f ∈ singularHillEigenspace (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0 := by
    apply (mem_singularHillEigenspace_iff _ _ _).mpr
    rw [singularHillOperator_zero,zero_smul]
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    rw [singularHillLaplacian_coefficient,hfc]
    change (freeHillValue k : ℂ)*(if k = 0 then c else 0) = 0
    split_ifs with hk
    · subst k
      simp [freeHillValue]
    · exact mul_zero _
  refine ⟨⟨f,hf⟩,?_⟩
  change f.val (mode 0) = c
  simpa only [neg_zero,ite_true] using hfc 0

def singularHillFreeGroundEquiv : singularHillEigenspace
    (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective singularHillFreeGroundEvaluation
    ⟨singularHillFreeGroundEvaluation_injective,singularHillFreeGroundEvaluation_surjective⟩

theorem singularHillAlgebraicMultiplicity_zero_ground :
    singularHillAlgebraicMultiplicity (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0 = 1 := by
  have hr : (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2).val =
      (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2).val.conjugate := by
    ext g
    change (0 : ℂ) = star (0 : ℂ)
    simp
  unfold singularHillAlgebraicMultiplicity
  rw [singularHillRootSpaceTop_eq_one_of_real _ hr]
  calc
    _ = Module.finrank ℂ (singularHillEigenspace (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) 0) :=
      (singularHillEigenspaceRootEquiv _ _).finrank_eq.symm
    _ = Module.finrank ℂ ℂ := singularHillFreeGroundEquiv.finrank_eq
    _ = 1 := by simp

end NLS.KdV
