import NLS.SequenceSpaces.HilbertScalarConcavity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Deriv
import NLS.SequenceSpaces.NonnegativeActions

/-! # Strict Jensen inequalities from the analytic Hessian

Restrict an analytic function to real affine segments and identify its
second derivative with the complex Hessian. Negative chord Hessians imply
strict concavity. The uniform Hilbert bound then applies on the whole real
ball; the source Hamiltonian restricts this result to nonnegative actions.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Coeff

/-- A real restriction of a complex affine line has the literal Hessian as second derivative. -/
theorem real_line_second_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (H : X → ℂ) (U : Set X) (hU : IsOpen U) (hH : AnalyticOnNhd ℂ H U)
    (x v : X) (t : ℝ) (ht : x + (t : ℂ) • v ∈ U) :
    (deriv^[2] (fun r : ℝ => (H (x + (r : ℂ) • v)).re)) t =
      (fderiv ℂ (fderiv ℂ H) (x + (t : ℂ) • v) v v).re := by
  have hline (z : ℂ) : HasDerivAt (fun w : ℂ => x + w • v) v z :=
    by simpa only [id_eq, one_smul] using
      ((hasDerivAt_id z).smul_const v).const_add x
  have hfirst (z : ℂ) (hz : x + z • v ∈ U) :
      HasDerivAt (fun w : ℂ => H (x + w • v))
        (fderiv ℂ H (x + z • v) v) z :=
    (hH _ hz).differentiableAt.hasFDerivAt.comp_hasDerivAt z (hline z)
  have hsecond : HasDerivAt (fun z : ℂ => fderiv ℂ H (x + z • v) v)
      (fderiv ℂ (fderiv ℂ H) (x + (t : ℂ) • v) v v) (t : ℂ) := by
    have hfd : HasDerivAt (fun z : ℂ => fderiv ℂ H (x + z • v))
        (fderiv ℂ (fderiv ℂ H) (x + (t : ℂ) • v) v) (t : ℂ) :=
      (hH.fderiv _ ht).differentiableAt.hasFDerivAt.comp_hasDerivAt
        (t : ℂ) (hline t)
    simpa only [ContinuousLinearMap.map_zero, add_zero] using
      hfd.clm_apply (hasDerivAt_const (t : ℂ) v)
  have he : ∀ᶠ r : ℝ in 𝓝 t,
      deriv (fun u : ℝ => (H (x + (u : ℂ) • v)).re) r =
        (fderiv ℂ H (x + (r : ℂ) • v) v).re := by
    have hc : Continuous (fun r : ℝ => x + (r : ℂ) • v) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hU.mem_nhds ht)] with r hr
    exact (hfirst r hr).real_of_complex.deriv
  exact (Filter.EventuallyEq.deriv_eq he).trans hsecond.real_of_complex.deriv

/-- A negative Hessian along every chord gives literal strict concavity. -/
theorem strictConcaveOn_re_of_hessian_neg
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
    (H : X → ℂ) (U S : Set X) (hU : IsOpen U) (hH : AnalyticOnNhd ℂ H U)
    (hS : Convex ℝ S) (hSU : S ⊆ U)
    (hess : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ z ∈ S,
      (fderiv ℂ (fderiv ℂ H) z (y-x) (y-x)).re < 0) :
    StrictConcaveOn ℝ S (fun x => (H x).re) := by
  refine ⟨hS,?_⟩
  intro x hx y hy hxy a b ha hb hab
  let f : ℝ → ℝ := fun t => (H (x + (t : ℂ) • (y-x))).re
  have hline (t : ℝ) : x + (t : ℂ) • (y-x) = (1-t) • x + t • y := by
    have hs : (t : ℂ) • (y-x) = t • (y-x) := algebraMap_smul ℂ t (y-x)
    rw [hs]
    simp only [smul_sub,sub_smul,one_smul]
    abel
  have hmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : x + (t:ℂ) • (y-x) ∈ S := by
    rw [hline]
    exact hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hc : ContinuousOn f (Icc (0:ℝ) 1) := by
    intro t ht
    have hcLine : ContinuousAt (fun r : ℝ => x + (r:ℂ) • (y-x)) t := by fun_prop
    have hcH : ContinuousAt (fun r : ℝ => H (x + (r:ℂ) • (y-x))) t :=
      ContinuousAt.comp (hH _ (hSU (hmem t ht))).continuousAt hcLine
    exact (Complex.continuous_re.continuousAt.comp hcH).continuousWithinAt
  have hstrict : StrictConcaveOn ℝ (Icc (0:ℝ) 1) f :=
    strictConcaveOn_of_deriv2_neg' (convex_Icc _ _) hc (by
      intro t ht
      rw [real_line_second_derivative H U hU hH x (y-x) t (hSU (hmem t ht))]
      exact hess x hx y hy hxy _ (hmem t ht))
  have hzero : f 0 = (H x).re := by
    simp only [f,Complex.ofReal_zero,zero_smul,add_zero]
  have hone : f 1 = (H y).re := by
    simp only [f,Complex.ofReal_one,one_smul,add_sub_cancel]
  have hcomb : f (a • (0:ℝ) + b • 1) = (H (a • x + b • y)).re := by
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add]
    change (H (x + (b:ℂ) • (y-x))).re = _
    rw [hline,show 1-b=a by linarith]
  have hi := hstrict.2 (show (0:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num) ha hb hab
  rwa [hzero,hone,hcomb] at hi

/-- The uniform real-direction Hessian bound gives strict concavity on the
entire real Hilbert ball, including signed action directions. -/
theorem strictConcaveOn_real_hilbert_ball
    (H : Coeff 2 → ℂ) (U : Set (Coeff 2)) (hU : IsOpen U)
    (hH : AnalyticOnNhd ℂ H U) (r : ℝ) (hball : Metric.ball (0:Coeff 2) r ⊆ U)
    (hess : ∀ b ∈ Metric.ball (0:Coeff 2) r, ∀ J : RealCoeff 2,
      (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J)
        (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2) :
    StrictConcaveOn ℝ (Metric.ball (0:Coeff 2) r ∩ realLocus 2) (fun b => (H b).re) := by
  have hconv : Convex ℝ (realLocus 2) := by
    intro a ha b hb u v _ _ _ n
    change (u • a n + v • b n).im = 0
    simp [ha n,hb n]
  apply strictConcaveOn_re_of_hessian_neg H U _ hU hH
    ((convex_ball (0:Coeff 2) r).inter hconv) (fun _ hb => hball hb.1)
  intro x hx y hy hxy z hz
  let J := reCLM 2 (y-x)
  have hJ : RealCoeff.complexCLM 2 J = y-x :=
    RealCoeff.complexCLM_reCLM 2 (y-x) (by
      intro n
      change (y n-x n).im = 0
      simp only [Complex.sub_im,hx.2 n,hy.2 n,sub_self])
  have hne : J ≠ 0 := by
    intro he
    have hz := hJ.symm
    rw [he,map_zero] at hz
    exact hxy (sub_eq_zero.mp hz).symm
  have hb := hess z hz.1 J
  rw [hJ] at hb
  exact hb.trans_lt (neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hne)))

end NLS.Coeff
