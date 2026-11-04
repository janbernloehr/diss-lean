import NLS.ComplexAnalysis.SecondOrderDuhamel
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Periodic third-order Lagrange identity for squared-eigenfunction
systems. Only continuous jets, interior derivatives and literal endpoint
equalities are required. The potential derivative need not be continuous. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem integral_self_mul_derivative_eq_zero
    (f f1 : ℝ → ℂ) (hf : Continuous f) (hf1 : Continuous f1)
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t) (hperiod : f 1=f 0) :
    (∫ x in (0:ℝ)..1, f x*f1 x)=0 := by
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun x => (f x)^2) (2*(f t*f1 t)) t := by
    convert (hd t ht).pow 2 using 1 <;> first | rfl | ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    (hf.pow 2).continuousOn hderiv ((continuous_const.mul (hf.mul hf1)).intervalIntegrable 0 1)
  simp only [Pi.pow_apply] at hi
  rw [intervalIntegral.integral_const_mul,hperiod,sub_self] at hi
  linear_combination (1/2:ℂ)*hi

theorem thirdOrder_periodic_lagrange_integral
    (Q Qdot f f1 f2 g g1 g2 : ℝ → ℂ) (μ ν : ℂ)
    (hQ : Continuous Q) (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hg : Continuous g) (hg1 : Continuous g1) (hg2 : Continuous g2)
    (hdQ : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt Q (Qdot t) t)
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t)
    (hdf1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (hdf2 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f2 (2*Qdot t*f t+4*(Q t-μ)*f1 t) t)
    (hdg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (g1 t) t)
    (hdg1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g1 (g2 t) t)
    (hdg2 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g2 (2*Qdot t*g t+4*(Q t-ν)*g1 t) t)
    (hQp : Q 1=Q 0) (hfp : f 1=f 0) (hf1p : f1 1=f1 0) (hf2p : f2 1=f2 0)
    (hgp : g 1=g 0) (hg1p : g1 1=g1 0) (hg2p : g2 1=g2 0) :
    (μ-ν)*(∫ x in (0:ℝ)..1, f x*g1 x)=0 := by
  let P : ℝ → ℂ := fun x => f2 x*g x-f1 x*g1 x+f x*g2 x-4*(Q x*(f x*g x))
  have hP : Continuous P :=
    (((hf2.mul hg).sub (hf1.mul hg1)).add (hf.mul hg2)).sub (continuous_const.mul (hQ.mul (hf.mul hg)))
  have hdP (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt P ((-4*μ)*(f1 t*g t)+(-4*ν)*(f t*g1 t)) t := by
    have hd := ((((hdf2 t ht).mul (hdg t ht)).sub ((hdf1 t ht).mul (hdg1 t ht))).add
      ((hdf t ht).mul (hdg2 t ht))).sub (((hdQ t ht).mul ((hdf t ht).mul (hdg t ht))).const_mul 4)
    convert hd using 1 <;> first | rfl | (dsimp only [Pi.mul_apply]; ring)
  have hPp : P 1=P 0 := by simp only [P,hQp,hfp,hf1p,hf2p,hgp,hg1p,hg2p]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hP.continuousOn hdP (((continuous_const.mul (hf1.mul hg)).add
      (continuous_const.mul (hf.mul hg1))).intervalIntegrable 0 1)
  have hA : IntervalIntegrable (fun x : ℝ => f1 x*g x) volume 0 1 := (hf1.mul hg).intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun x : ℝ => f x*g1 x) volume 0 1 := (hf.mul hg1).intervalIntegrable 0 1
  have hAc : IntervalIntegrable (fun x : ℝ => (-4*μ)*(f1 x*g x)) volume 0 1 :=
    (continuous_const.mul (hf1.mul hg)).intervalIntegrable 0 1
  have hBc : IntervalIntegrable (fun x : ℝ => (-4*ν)*(f x*g1 x)) volume 0 1 :=
    (continuous_const.mul (hf.mul hg1)).intervalIntegrable 0 1
  rw [hPp,sub_self,intervalIntegral.integral_add hAc hBc,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hi
  have hdFG (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun x => f x*g x) (f1 t*g t+f t*g1 t) t := (hdf t ht).mul (hdg t ht)
  have hFG := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    (hf.mul hg).continuousOn hdFG (((hf1.mul hg).add (hf.mul hg1)).intervalIntegrable 0 1)
  simp only [Pi.mul_apply] at hFG
  rw [hfp,hgp,sub_self,intervalIntegral.integral_add hA hB] at hFG
  linear_combination (1/4:ℂ)*hi+μ*hFG

end NLS.ComplexAnalysis
