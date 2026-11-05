import NLS.KdV.ClassicalHillPositionFreeError

/-! # The first Born term of the actual Hill terminal sheet root

The difference of the two diagonal monodromy entries has a sine Fourier
leading term. Its remainder is quadratic in the potential mass and has
two powers of frequency decay, for complex sources and frequencies.
-/
noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillSheetRootBorn (q : Curve ℂ) (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, sin (z*((2*s-1 : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s

theorem classicalHillSheetRoot_born_remainder_bound (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖2*(classicalHillFlow q (z^2) (0,1) 1).2-classicalHillDiscriminant q (z^2)-
      classicalHillSheetRootBorn q z‖ ≤
      4*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖^2 := by
  let Q := NLS.LinearVolterra.extend q
  let C : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) (1,0) s).1
  let S : ℝ → ℂ := fun s => (classicalHillFlow q (z^2) (0,1) s).1
  let eC : ℝ → ℂ := fun s => C s-cos (z*s)
  let eS : ℝ → ℂ := fun s => S s-sin (z*s)/z
  let a : ℝ → ℂ := fun s => cos (z*((1-s : ℝ) : ℂ))*Q s
  let b : ℝ → ℂ := fun s => sin (z*((1-s : ℝ) : ℂ))/z*Q s
  have hC : Continuous C := (continuous_classicalHillFlow q (z^2) (1,0)).fst
  have hS : Continuous S := (continuous_classicalHillFlow q (z^2) (0,1)).fst
  have hc : Continuous (fun s : ℝ => cos (z*s)) := by fun_prop
  have hs : Continuous (fun s : ℝ => sin (z*s)/z) := by fun_prop
  have hQ : Continuous Q := continuous_extend q
  have ha : Continuous a := by dsimp only [a]; fun_prop
  have hb : Continuous b := by dsimp only [b]; fun_prop
  have hborn : classicalHillSheetRootBorn q z =
      (∫ s in (0 : ℝ)..1, a s*(sin (z*s)/z))-
        ∫ s in (0 : ℝ)..1, b s*cos (z*s) := by
    rw [← intervalIntegral.integral_sub (f := fun s => a s*(sin (z*s)/z)) (g := fun s => b s*cos (z*s)) ((ha.mul hs).intervalIntegrable 0 1)
      ((hb.mul hc).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [classicalHillSheetRootBorn,a,b,Q]
    have he : z*((2*s-1 : ℝ) : ℂ) = z*s-z*((1-s : ℝ) : ℂ) := by push_cast; ring
    rw [he,sin_sub]
    ring
  have hdiag : 2*(classicalHillFlow q (z^2) (0,1) 1).2-classicalHillDiscriminant q (z^2) =
      (∫ s in (0 : ℝ)..1, a s*S s)-∫ s in (0 : ℝ)..1,b s*C s := by
    have h₁ := classicalHillFlow_sine_duhamel q z hz (1,0) ⟨1,by norm_num⟩
    have h₂ := classicalHillFlow_cosine_duhamel q z (0,1) ⟨1,by norm_num⟩
    simp only [ofReal_one,mul_one,mul_zero,add_zero,zero_add] at h₁ h₂
    rw [← classicalHillFlow_trace]
    change 2*(classicalHillFlow q (z^2) (0,1) 1).2-
      ((classicalHillFlow q (z^2) (1,0) 1).1+(classicalHillFlow q (z^2) (0,1) 1).2) = _
    change (classicalHillFlow q (z^2) (1,0) 1).1 = cos z+∫ s in (0 : ℝ)..1,b s*C s at h₁
    change (classicalHillFlow q (z^2) (0,1) 1).2 = cos z+∫ s in (0 : ℝ)..1,a s*S s at h₂
    rw [h₁,h₂]
    ring
  have herr : 2*(classicalHillFlow q (z^2) (0,1) 1).2-classicalHillDiscriminant q (z^2)-
      classicalHillSheetRootBorn q z =
      (∫ s in (0 : ℝ)..1,a s*eS s)-∫ s in (0 : ℝ)..1,b s*eC s := by
    rw [hdiag,hborn]
    simp only [eS,eC,mul_sub]
    rw [intervalIntegral.integral_sub (f := fun s => a s*S s) (g := fun s => a s*(sin (z*s)/z)) ((ha.mul hS).intervalIntegrable 0 1)
      ((ha.mul hs).intervalIntegrable 0 1),
      intervalIntegral.integral_sub (f := fun s => b s*C s) (g := fun s => b s*cos (z*s)) ((hb.mul hC).intervalIntegrable 0 1)
      ((hb.mul hc).intervalIntegrable 0 1)]
    ring
  have heC_bound (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
      ‖eC s‖ ≤ 2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖ := by
    have h := classicalHillFlow_position_free_error_small q z hz H hH hsmall (1,0) ⟨s,hs'⟩
    simpa only [eC,C,norm_one,norm_zero,zero_div,add_zero,mul_one,mul_zero] using h
  have heS_bound (s : ℝ) (hs' : s ∈ Icc (0 : ℝ) 1) :
      ‖eS s‖ ≤ 2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2 := by
    have h := classicalHillFlow_position_free_error_small q z hz H hH hsmall (0,1) ⟨s,hs'⟩
    simpa only [eS,S,norm_one,norm_zero,zero_add,mul_one,mul_zero,div_mul_div_comm,
      one_mul,← pow_two] using h
  have h₁ := norm_cosine_duhamel_integral_le Q eS z H
    (2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ heS_bound
  have h₂ := norm_sine_duhamel_integral_le Q eC z H
    (2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ heC_bound
  rw [herr]
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by
    change Real.exp H*(2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2)*classicalHillPotentialMass q+
      (Real.exp H/‖z‖*(2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖))*classicalHillPotentialMass q = _
    ring))

end NLS.KdV
