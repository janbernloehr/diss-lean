import NLS.Articles.MKdVBelowL2.ClassicalRenormalizedFourthFlow
import NLS.Fourier.PeriodOneCoefficientLinear

/-! # Smooth physical renormalized fourth fields and their original Fourier coefficients -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.MKdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2

/-- The independently calibrated fourth field is smooth and period one
on every smooth period-one physical pair. -/
theorem classicalNLSFourthVectorField_regular (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) :
    (ContDiff ℝ ∞ (classicalNLSFourthVectorField f g).1 ∧
      ContDiff ℝ ∞ (classicalNLSFourthVectorField f g).2) ∧
    (Function.Periodic (classicalNLSFourthVectorField f g).1 1 ∧
      Function.Periodic (classicalNLSFourthVectorField f g).2 1) := by
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hf2 := (contDiff_infty_iff_deriv.mp hf1).2
  have hf3 := (contDiff_infty_iff_deriv.mp hf2).2
  have hg1 := (contDiff_infty_iff_deriv.mp hg).2
  have hg2 := (contDiff_infty_iff_deriv.mp hg1).2
  have hg3 := (contDiff_infty_iff_deriv.mp hg2).2
  have hpf1 := periodic_deriv_of_periodic f 1 hpf
  have hpf2 := periodic_deriv_of_periodic (deriv f) 1 hpf1
  have hpf3 := periodic_deriv_of_periodic (deriv (deriv f)) 1 hpf2
  have hpg1 := periodic_deriv_of_periodic g 1 hpg
  have hpg2 := periodic_deriv_of_periodic (deriv g) 1 hpg1
  have hpg3 := periodic_deriv_of_periodic (deriv (deriv g)) 1 hpg2
  rw [classicalNLSFourthVectorField_formula]
  refine ⟨⟨hf3.neg.add (((contDiff_const.mul hf).mul hg).mul hf1),
    hg3.neg.add (((contDiff_const.mul hf).mul hg).mul hg1)⟩,⟨?_,?_⟩⟩
  · intro x
    change -deriv (deriv (deriv f)) (x+1)+6*f (x+1)*g (x+1)*deriv f (x+1) = _
    rw [hpf3 x,hpf x,hpg x,hpf1 x]
  · intro x
    change -deriv (deriv (deriv g)) (x+1)+6*f (x+1)*g (x+1)*deriv g (x+1) = _
    rw [hpg3 x,hpf x,hpg x,hpg1 x]

/-- Subtracting the physical mass translation preserves smoothness and
the exact original spatial period in both components. -/
theorem classicalRenormalizedFourthField_regular (M : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) :
    (ContDiff ℝ ∞ (classicalRenormalizedFourthField M f g).1 ∧
      ContDiff ℝ ∞ (classicalRenormalizedFourthField M f g).2) ∧
    (Function.Periodic (classicalRenormalizedFourthField M f g).1 1 ∧
      Function.Periodic (classicalRenormalizedFourthField M f g).2 1) := by
  obtain ⟨hs,hp⟩ := classicalNLSFourthVectorField_regular f g hf hg hpf hpg
  have hf1 := (contDiff_infty_iff_deriv.mp hf).2
  have hg1 := (contDiff_infty_iff_deriv.mp hg).2
  have hpf1 := periodic_deriv_of_periodic f 1 hpf
  have hpg1 := periodic_deriv_of_periodic g 1 hpg
  refine ⟨⟨hs.1.sub (contDiff_const.mul hf1),hs.2.sub (contDiff_const.mul hg1)⟩,⟨?_,?_⟩⟩
  · intro x
    change (classicalNLSFourthVectorField f g).1 (x+1)-6*M*deriv f (x+1) = _
    rw [hp.1 x,hpf1 x]
    rfl
  · intro x
    change (classicalNLSFourthVectorField f g).2 (x+1)-6*M*deriv g (x+1) = _
    rw [hp.2 x,hpg1 x]
    rfl

/-- The physical renormalization has precisely the period-one derivative
multiplier in its original Fourier integrals. -/
theorem classicalRenormalizedFourthField_coefficients (M : ℂ) (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : Function.Periodic f 1) (hpg : Function.Periodic g 1) (n : ℤ) :
    periodOneCoefficient (classicalRenormalizedFourthField M f g).1 n =
      periodOneCoefficient (classicalNLSFourthVectorField f g).1 n-
        (6*M)*(2*I*(Real.pi:ℂ)*n*periodOneCoefficient f n) ∧
    periodOneCoefficient (classicalRenormalizedFourthField M f g).2 n =
      periodOneCoefficient (classicalNLSFourthVectorField f g).2 n-
        (6*M)*(2*I*(Real.pi:ℂ)*n*periodOneCoefficient g n) := by
  have hs := (classicalNLSFourthVectorField_regular f g hf hg hpf hpg).1
  constructor
  · change periodOneCoefficient ((classicalNLSFourthVectorField f g).1-(fun x => 6*M*deriv f x)) n = _
    rw [periodOneCoefficient_sub (classicalNLSFourthVectorField f g).1 (fun x => 6*M*deriv f x) hs.1.continuous
      (continuous_const.mul (contDiff_infty_iff_deriv.mp hf).2.continuous) n,
      periodOneCoefficient_const_mul,periodOneCoefficient_deriv_of_smooth_periodic f hf hpf n]
  · change periodOneCoefficient ((classicalNLSFourthVectorField f g).2-(fun x => 6*M*deriv g x)) n = _
    rw [periodOneCoefficient_sub (classicalNLSFourthVectorField f g).2 (fun x => 6*M*deriv g x) hs.2.continuous
      (continuous_const.mul (contDiff_infty_iff_deriv.mp hg).2.continuous) n,
      periodOneCoefficient_const_mul,periodOneCoefficient_deriv_of_smooth_periodic g hg hpg n]

end NLS.Articles.MKdVBelowL2
