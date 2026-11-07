import NLS.ComplexAnalysis.ThirdOrderPeriodicLagrange

/-! A boundary Green identity for quadratic solution kernels.
The kinetic formulation uses only the continuous potential, not its
derivative. No periodic or zero boundary conditions are hidden. -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

theorem quadraticKernel_boundary_lagrange_integral
    (Q f f1 K g g1 L : ℝ → ℂ) (μ ν : ℂ)
    (_hQ : Continuous Q) (hf : Continuous f) (hf1 : Continuous f1) (hK : Continuous K)
    (hg : Continuous g) (hg1 : Continuous g1) (hL : Continuous L)
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t)
    (hdf1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f1 (2*(Q t-μ)*f t+2*K t) t)
    (hdK : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt K ((Q t-μ)*f1 t) t)
    (hdg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (g1 t) t)
    (hdg1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g1 (2*(Q t-ν)*g t+2*L t) t)
    (hdL : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt L ((Q t-ν)*g1 t) t) :
    4*(μ-ν)*(∫ x in (0:ℝ)..1, f x*g1 x)=
      (2*K 1*g 1-f1 1*g1 1+2*f 1*L 1-2*(μ+ν)*f 1*g 1)-
        (2*K 0*g 0-f1 0*g1 0+2*f 0*L 0-2*(μ+ν)*f 0*g 0)+
          4*μ*(f 1*g 1-f 0*g 0) := by
  let P : ℝ → ℂ := fun x => 2*K x*g x-f1 x*g1 x+2*f x*L x-2*(μ+ν)*f x*g x
  have hP : Continuous P := by
    dsimp only [P]
    fun_prop
  have hdP (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt P ((-4*μ)*(f1 t*g t)+(-4*ν)*(f t*g1 t)) t := by
    have hd := ((((hdK t ht).const_mul 2).mul (hdg t ht)).sub ((hdf1 t ht).mul (hdg1 t ht))).add
      (((hdf t ht).const_mul 2).mul (hdL t ht)) |>.sub
        ((((hdf t ht).const_mul (2*(μ+ν))).mul (hdg t ht)))
    convert hd using 1 <;> first | rfl | ring
  have hAc : IntervalIntegrable (fun x : ℝ => (-4*μ)*(f1 x*g x)) volume 0 1 :=
    (continuous_const.mul (hf1.mul hg)).intervalIntegrable 0 1
  have hBc : IntervalIntegrable (fun x : ℝ => (-4*ν)*(f x*g1 x)) volume 0 1 :=
    (continuous_const.mul (hf.mul hg1)).intervalIntegrable 0 1
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hP.continuousOn hdP (hAc.add hBc)
  rw [intervalIntegral.integral_add hAc hBc,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hi
  have hdFG (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (fun x => f x*g x) (f1 t*g t+f t*g1 t) t := (hdf t ht).mul (hdg t ht)
  have hA : IntervalIntegrable (fun x : ℝ => f1 x*g x) volume 0 1 := (hf1.mul hg).intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun x : ℝ => f x*g1 x) volume 0 1 := (hf.mul hg1).intervalIntegrable 0 1
  have hFG := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    (hf.mul hg).continuousOn hdFG (hA.add hB)
  rw [intervalIntegral.integral_add hA hB] at hFG
  dsimp only [Pi.mul_apply] at hFG
  dsimp only [P] at hi
  linear_combination hi+4*μ*hFG

theorem quadraticKernel_dirichlet_lagrange_integral
    (Q f f1 K g g1 L : ℝ → ℂ) (μ ν : ℂ)
    (hQ : Continuous Q) (hf : Continuous f) (hf1 : Continuous f1) (hK : Continuous K)
    (hg : Continuous g) (hg1 : Continuous g1) (hL : Continuous L)
    (hdf : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f (f1 t) t)
    (hdf1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt f1 (2*(Q t-μ)*f t+2*K t) t)
    (hdK : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt K ((Q t-μ)*f1 t) t)
    (hdg : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (g1 t) t)
    (hdg1 : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g1 (2*(Q t-ν)*g t+2*L t) t)
    (hdL : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt L ((Q t-ν)*g1 t) t)
    (hf0 : f 0=0) (hfend : f 1=0) (hg0 : g 0=0) (hgend : g 1=0)
    (hfirst : f1 1*g1 1=f1 0*g1 0) :
    (μ-ν)*(∫ x in (0:ℝ)..1, f x*g1 x)=0 := by
  have hi := quadraticKernel_boundary_lagrange_integral Q f f1 K g g1 L μ ν
    hQ hf hf1 hK hg hg1 hL hdf hdf1 hdK hdg hdg1 hdL
  rw [hf0,hfend,hg0,hgend] at hi
  simp only [mul_zero,zero_mul,sub_zero,add_zero,zero_sub,hfirst,sub_self] at hi
  linear_combination (1/4:ℂ)*hi

end NLS.ComplexAnalysis
