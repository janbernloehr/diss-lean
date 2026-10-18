import NLS.ZakharovShabat.ClassicalSobolevDiscriminantError
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ZakharovShabat.ClassicalSobolevBoundaryRootDisplacement
import NLS.ComplexAnalysis.BanachTaylorBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Inverse-index displacement of physical H1 critical roots

Cauchy estimates control the actual discriminant derivative error on physical H1 balls; the sine quotient gives inverse-index displacement on both signed tails.
-/

noncomputable section
open Set Complex Metric NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Cauchy estimates preserve the inverse-frequency bound for the actual
spectral derivative on physical H1 balls, without an extra derivative. -/
theorem norm_classicalDiscriminant_deriv_add_sin_sobolev_le
    (M H : ℝ) (hM : 0 ≤ M) (a : Domain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (him : |z.im| ≤ H) :
    ‖deriv (classicalDiscriminant (classicalSobolevPotential a)) z+2*sin z‖ ≤
      16*classicalSobolevErrorConstant M (H+1)/‖z‖ := by
  let f := fun w => classicalDiscriminant (classicalSobolevPotential a) w-freeDiscriminant w
  have han (w : ℂ) : AnalyticAt ℂ
      (classicalDiscriminant (classicalSobolevPotential a)) w :=
    (analyticOnNhd_classicalDiscriminant_joint (w,classicalSobolevPotential a) (mem_univ _)).comp
      (f := fun v : ℂ => (v,classicalSobolevPotential a)) (analyticAt_id.prod analyticAt_const)
  have hfree (w : ℂ) : HasDerivAt freeDiscriminant (-2*sin w) w := by
    convert! (Complex.hasDerivAt_cos w).const_mul (2:ℂ) using 1
    simp
  have hf : DifferentiableOn ℂ f (ball z (1/2+1/2)) := by
    intro w _
    exact ((han w).differentiableAt.sub (hfree w).differentiableAt).differentiableWithinAt
  have hE : 0 ≤ classicalSobolevErrorConstant M (H+1) :=
    classicalSobolevErrorConstant_nonneg _ _ hM
  have hb : ∀ w ∈ ball z (1/2+1/2), ‖f w‖ ≤
      4*classicalSobolevErrorConstant M (H+1)/‖z‖ := by
    intro w hw
    have hd : ‖w-z‖ < 1 := by
      simpa only [mem_ball,dist_eq_norm,show (1:ℝ)/2+1/2=1 by norm_num] using hw
    have ht := norm_le_norm_add_norm_sub w z
    have hw1 : 1 ≤ ‖w‖ := by linarith
    have hwz : ‖z‖ ≤ 2*‖w‖ := by linarith
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by linarith)
    have hi := abs_im_le_norm (w-z)
    have hs := abs_add_le (w.im-z.im) z.im
    simp only [sub_im] at hi
    rw [sub_add_cancel] at hs
    have hwH : |w.im| ≤ H+1 := by linarith
    apply (norm_classicalDiscriminant_sub_free_sobolev_strip_le M (H+1) a ha w hw0 hwH).trans
    calc
      2*classicalSobolevErrorConstant M (H+1)/‖w‖ =
          4*classicalSobolevErrorConstant M (H+1)/(2*‖w‖) := by ring
      _ ≤ 4*classicalSobolevErrorConstant M (H+1)/‖z‖ :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hwz
  have hd := NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound f z z (1/2) (1/2)
    (4*classicalSobolevErrorConstant M (H+1)/‖z‖) (by norm_num) hf hb (by simp)
  have he : deriv f z = deriv (classicalDiscriminant (classicalSobolevPotential a)) z+2*sin z := by
    convert! ((han z).differentiableAt.hasDerivAt.sub (hfree z)).deriv using 1
    simp
  rw [← he,norm_deriv_eq_norm_fderiv]
  convert hd using 1
  ring

/-- Every critical root in a distant quarter-pi disc has inverse-index
displacement, uniformly on the physical H1 ball and both signed tails. -/
theorem exists_classicalCriticalRoot_sobolev_inverse_index_bound
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : Domain 2, ‖a‖ ≤ M → ∀ n : ℤ, N ≤ n.natAbs →
      ∀ z : ℂ, ‖z-(Real.pi:ℂ)*n‖ ≤ Real.pi/4 →
        deriv (classicalDiscriminant (classicalSobolevPotential a)) z = 0 →
        ‖z-(Real.pi:ℂ)*n‖ ≤ B/(n.natAbs:ℝ) := by
  obtain ⟨C,hC,hdisp⟩ := exists_freeDisc_sine_displacement_bound
    (r := Real.pi/4) (by nlinarith [Real.pi_pos])
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff (Real.pi/4) (by positivity)
  let E := classicalSobolevErrorConstant M (Real.pi/4+1)
  have hE : 0 ≤ E := classicalSobolevErrorConstant_nonneg _ _ hM
  refine ⟨max N 2,hN.trans_le (le_max_left _ _),16*C*E/Real.pi,by positivity,?_⟩
  intro a ha n hn z hz hzero
  obtain ⟨him,_,hzn⟩ := hcut n ((le_max_left _ _).trans hn) z hz
  have hn2 : (2:ℝ) ≤ n.natAbs := by exact_mod_cast (le_max_right N 2).trans hn
  have hz2 : 2 ≤ ‖z‖ := by nlinarith [Real.two_le_pi]
  have hs := norm_classicalDiscriminant_deriv_add_sin_sobolev_le M (Real.pi/4) hM a ha z hz2 him
  rw [hzero,zero_add,norm_mul,norm_ofNat] at hs
  calc
    ‖z-(Real.pi:ℂ)*n‖ ≤ C*‖sin z‖ := hdisp n z hz
    _ ≤ C*(8*E/‖z‖) := mul_le_mul_of_nonneg_left (by
      have hh : 2*‖sin z‖ ≤ 2*(8*E/‖z‖) := by
        convert hs using 1
        ring
      exact (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ) < 2)).mp hh) hC
    _ ≤ C*(8*E/(Real.pi*(n.natAbs:ℝ)/2)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hzn) hC
    _ = (16*C*E/Real.pi)/(n.natAbs:ℝ) := by ring

end NLS.ZakharovShabat
