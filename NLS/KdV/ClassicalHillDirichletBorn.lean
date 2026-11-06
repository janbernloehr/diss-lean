import NLS.KdV.ClassicalHillPositionFreeError

/-! # The actual Dirichlet characteristic through its first Born term

The sine-column Volterra remainder has three frequency powers. After
multiplication by twice the energy, the leading integral is the cosine
Fourier term minus the potential mean times the free cosine.
-/
noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillDirichletBorn (q : Curve ℂ) (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s*(sin (z*s)/z)

theorem classicalHillDirichlet_born_remainder_bound (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖(classicalHillFlow q (z^2) (0,1) 1).1-sin z/z-classicalHillDirichletBorn q z‖ ≤
      2*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖^3 := by
  let S : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) (0,1) s).1
  let eS : ℝ → ℂ := fun s => S s-sin (z*s)/z
  let b : ℝ → ℂ := fun s => sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s
  have hS : Continuous S := (continuous_classicalHillFlow q (z^2) (0,1)).fst
  have hs : Continuous (fun s : ℝ => sin (z*s)/z) := by fun_prop
  have hq : Continuous (NLS.LinearVolterra.extend q) := continuous_extend q
  have hb : Continuous b := by dsimp only [b]; fun_prop
  have hduh := classicalHillFlow_sine_duhamel q z hz (0,1) ⟨1,by norm_num⟩
  simp only [ofReal_one,mul_one,mul_zero,zero_add] at hduh
  have he : (classicalHillFlow q (z^2) (0,1) 1).1-sin z/z-classicalHillDirichletBorn q z =
      ∫ s in (0 : ℝ)..1,b s*eS s := by
    rw [hduh,add_sub_cancel_left,classicalHillDirichletBorn,
      ← intervalIntegral.integral_sub (f := fun s => b s*S s) (g := fun s => b s*(sin (z*s)/z))
        ((hb.mul hS).intervalIntegrable 0 1) ((hb.mul hs).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [b,eS,S]
    ring
  have heS_bound (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
      ‖eS s‖ ≤ 2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2 := by
    have h := classicalHillFlow_position_free_error_small q z hz H hH hsmall (0,1) ⟨s,hs'⟩
    simpa only [eS,S,norm_one,norm_zero,zero_add,mul_one,mul_zero,div_mul_div_comm,
      one_mul,← pow_two] using h
  have h := norm_sine_duhamel_integral_le (NLS.LinearVolterra.extend q) eS z H
    (2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ heS_bound
  rw [he]
  exact h.trans_eq (by
    change (Real.exp H/‖z‖*(2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2))*classicalHillPotentialMass q = _
    ring)

theorem classicalHillDirichlet_cosine_residual_bound (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
      ∫ s in (0 : ℝ)..1, (cos (z*((2*s-1 : ℝ) : ℂ))-cos z)*NLS.LinearVolterra.extend q s‖ ≤
      4*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖ := by
  have hborn : 2*z^2*classicalHillDirichletBorn q z =
      ∫ s in (0 : ℝ)..1,(cos (z*((2*s-1 : ℝ) : ℂ))-cos z)*NLS.LinearVolterra.extend q s := by
    rw [classicalHillDirichletBorn,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    have h₁ : z*((2*s-1 : ℝ) : ℂ) = z*s-z*((1-s : ℝ) : ℂ) := by push_cast; ring
    have h₂ : z = z*s+z*((1-s : ℝ) : ℂ) := by push_cast; ring
    have htrig : cos (z*((2*s-1 : ℝ) : ℂ))-cos z =
        2*sin (z*((1-s : ℝ) : ℂ))*sin (z*s) := by
      conv_lhs => rw [h₁]; arg 2; rw [h₂]
      rw [cos_sub,cos_add]
      ring
    rw [htrig]
    field_simp
  have h := classicalHillDirichlet_born_remainder_bound q z hz H hH hsmall
  have he : 2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
      ∫ s in (0 : ℝ)..1,(cos (z*((2*s-1 : ℝ) : ℂ))-cos z)*NLS.LinearVolterra.extend q s =
        (2*z^2)*((classicalHillFlow q (z^2) (0,1) 1).1-sin z/z-classicalHillDirichletBorn q z) := by
    rw [← hborn]
    field_simp
  rw [he,norm_mul,norm_mul,norm_ofNat,norm_pow]
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*‖z‖^2)).trans_eq
  field_simp
  ring

end NLS.KdV
