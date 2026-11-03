import NLS.ComplexAnalysis.EntireEvenSquareDescent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.DSlope

/-! # The entire hyperbolic cosine in the squared coordinate

Evenness removes the square-root branch. On real arguments the resulting
entire function is a hyperbolic cosine on the nonnegative axis and an
ordinary cosine on the nonpositive axis.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

def coshSquareCoordinate (w : ℂ) : ℂ := cosh (Complex.sqrt w)

theorem coshSquareCoordinate_sq (z : ℂ) : coshSquareCoordinate (z^2) = cosh z := by
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sqrt (z^2)) z (complex_sqrt_sq (z^2)) with he | he
  · simp only [coshSquareCoordinate,he]
  · simp only [coshSquareCoordinate,he,cosh_neg]

theorem analyticOnNhd_coshSquareCoordinate : AnalyticOnNhd ℂ coshSquareCoordinate univ := by
  have hc : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => cosh (Complex.sqrt p.1)) univ :=
    analyticOnNhd_entire_even_square_descent (fun p : ℂ × ℂ => cosh p.1)
      (fun _ _ => Complex.analyticAt_cosh.comp analyticAt_fst)
      (fun _ z => cosh_neg z) Complex.sqrt complex_sqrt_sq
  intro w _
  exact (hc (w,0) (mem_univ _)).comp (f := fun w : ℂ => (w,(0 : ℂ)))
    (analyticAt_id.prod analyticAt_const)

theorem coshSquareCoordinate_ofReal (r : ℝ) (hr : 0 ≤ r) :
    coshSquareCoordinate (r : ℂ) = (Real.cosh (Real.sqrt r) : ℂ) := by
  have he : (Real.sqrt r : ℂ)^2 = (r : ℂ) := by rw [← ofReal_pow,Real.sq_sqrt hr]
  rw [← he,coshSquareCoordinate_sq,← ofReal_cosh]

theorem coshSquareCoordinate_neg_ofReal (r : ℝ) (hr : 0 ≤ r) :
    coshSquareCoordinate (-(r : ℂ)) = (Real.cos (Real.sqrt r) : ℂ) := by
  have he : (I*(Real.sqrt r : ℂ))^2 = -(r : ℂ) := by
    rw [mul_pow,I_sq,← ofReal_pow,Real.sq_sqrt hr,neg_one_mul]
  rw [← he,coshSquareCoordinate_sq,mul_comm I,cosh_mul_I,← ofReal_cos]

theorem coshSquareCoordinate_re_le_one_of_nonpos (r : ℝ) (hr : r ≤ 0) :
    (coshSquareCoordinate (r : ℂ)).re ≤ 1 := by
  have he : (r : ℂ) = -((-r : ℝ) : ℂ) := by simp only [ofReal_neg,neg_neg]
  rw [he,coshSquareCoordinate_neg_ofReal (-r) (by linarith),ofReal_re]
  exact Real.cos_le_one _

theorem cosh_add_I_nat_pi (z : ℂ) (n : ℕ) :
    cosh (z+I*(n : ℂ)*Real.pi) = (-1 : ℂ)^n*cosh z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : z+I*((n+1 : ℕ) : ℂ)*Real.pi =
        (z+I*(n : ℂ)*Real.pi)+(Real.pi : ℂ)*I := by push_cast; ring
    rw [he,cosh_add_pi_mul_I,ih,pow_succ]
    ring

theorem deriv_coshSquareCoordinate_zero : deriv coshSquareCoordinate 0 = 1/2 := by
  have hder (z : ℂ) (hz : z ≠ 0) :
      deriv coshSquareCoordinate (z^2) = dslope sinh 0 z/2 := by
    have hd := ((analyticOnNhd_coshSquareCoordinate (z^2) (mem_univ _)).differentiableAt.hasDerivAt).comp z
      ((hasDerivAt_id z).pow 2)
    have he : (fun w : ℂ => coshSquareCoordinate (w^2)) = cosh := funext coshSquareCoordinate_sq
    change HasDerivAt (fun w : ℂ => coshSquareCoordinate (w^2)) _ z at hd
    rw [he] at hd
    have hv := hd.unique (Complex.hasDerivAt_cosh z)
    simp only [Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,mul_one,id_eq] at hv
    rw [dslope_of_ne sinh hz,slope_def_field,sinh_zero,sub_zero,sub_zero]
    field_simp [hz]
    linear_combination hv
  have hc : ContinuousAt (fun z : ℂ => deriv coshSquareCoordinate (z^2)) 0 :=
    (analyticOnNhd_coshSquareCoordinate.deriv.continuous.comp (continuous_id.pow 2)).continuousAt
  have hl : Tendsto (fun z : ℂ => deriv coshSquareCoordinate (z^2)) (𝓝[≠] 0)
      (𝓝 (deriv coshSquareCoordinate 0)) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun z : ℂ => dslope sinh 0 z/2) (𝓝[≠] 0) (𝓝 ((1 : ℂ)/2)) := by
    have hd : deriv sinh 0 = 1 := by simpa only [cosh_zero] using (Complex.hasDerivAt_sinh 0).deriv
    simpa only [dslope_same,hd] using
      ((continuousAt_dslope_same.mpr (Complex.hasDerivAt_sinh 0).differentiableAt).div_const 2).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (hder z hz).symm

end NLS.ComplexAnalysis
