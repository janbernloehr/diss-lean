import NLS.ZakharovShabat.SourceStandardRootEllipseGeometry
import NLS.ComplexAnalysis.PiecewiseC1Loop

/-!
# Actual smooth ellipse contours and their weighted integrals

The contours below are genuine one-piece C¹ loops. The standard-root
Jacobian cancels pointwise, reducing their weighted periods to ordinary
integrals over the unit interval.
-/

noncomputable section
open Set Metric Complex Filter NLS.ComplexAnalysis
open scoped Topology unitInterval
namespace NLS.ZakharovShabat

private theorem ellipse_circle_ne_zero (r t : ℝ) (hr : 0 < r) :
    circleMap 0 r ((2*Real.pi)*t) ≠ 0 := by
  apply norm_ne_zero_iff.mp
  simpa only [norm_circleMap_zero,abs_of_pos hr] using hr.ne'

theorem contDiff_standardRootEllipseMap (τ δ : ℂ) (r : ℝ) (hr : 0 < r)
    {n : WithTop ℕ∞} : ContDiff ℝ n (standardRootEllipseMap τ δ r) := by
  have he : ContDiff ℝ n (fun t : ℝ => circleMap 0 r ((2*Real.pi)*t)) :=
    (contDiff_circleMap 0 r).comp (by fun_prop)
  exact contDiff_const.add (contDiff_const.mul (he.add (he.inv (fun t => ellipse_circle_ne_zero r t hr))))

theorem standardRootEllipseMap_one (τ δ : ℂ) (r : ℝ) :
    standardRootEllipseMap τ δ r 1 = standardRootEllipseMap τ δ r 0 := by
  simp only [standardRootEllipseMap,mul_one,mul_zero]
  rw [show circleMap 0 r (2*Real.pi) = circleMap 0 r 0 by
    simpa using (periodic_circleMap 0 r) 0]

/-- The closed ellipse path, traversed once counterclockwise. -/
def standardRootEllipsePath (τ δ : ℂ) (r : ℝ) (hr : 0 < r) :
    Path (standardRootEllipseMap τ δ r 0) (standardRootEllipseMap τ δ r 0) :=
  Path.ofLine ((contDiff_standardRootEllipseMap τ δ r hr (n := 2)).continuous.continuousOn)
    rfl (standardRootEllipseMap_one τ δ r)

theorem standardRootEllipsePath_extend (τ δ : ℂ) (r : ℝ) (hr : 0 < r)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    (standardRootEllipsePath τ δ r hr).extend t = standardRootEllipseMap τ δ r t := by
  rw [Path.extend_apply _ ht]
  rfl

theorem standardRootEllipsePath_contDiffOn (τ δ : ℂ) (r : ℝ) (hr : 0 < r) :
    ContDiffOn ℝ 2 (standardRootEllipsePath τ δ r hr).extend (Icc 0 1) :=
  (contDiff_standardRootEllipseMap τ δ r hr).contDiffOn.congr
    (fun t ht => standardRootEllipsePath_extend τ δ r hr t ht)

/-- The ellipse as an actual piecewise C¹ contour. -/
def standardRootEllipseLoop (τ δ : ℂ) (r : ℝ) (hr : 0 < r) : PiecewiseC1Loop :=
  PiecewiseC1Loop.ofPath (standardRootEllipsePath τ δ r hr)
    ((standardRootEllipsePath_contDiffOn τ δ r hr).of_le (by norm_num))

theorem standardRootEllipseLoop_inside (τ δ : ℂ) (r : ℝ) (hr : 0 < r)
    {U : Set ℂ} (hU : ∀ t ∈ Icc (0:ℝ) 1, standardRootEllipseMap τ δ r t ∈ U) :
    (standardRootEllipseLoop τ δ r hr).Inside U := by
  intro i t
  exact hU t t.property

/-- The normalized-root Jacobian is the constant -2πi on the ellipse. -/
theorem standardRootEllipseMap_deriv_div_root (τ δ : ℂ) (r t : ℝ)
    (hδ : δ ≠ 0) (hr : 1 < r) :
    deriv (standardRootEllipseMap τ δ r) t /
      normalizedStandardRoot τ ((2*δ)^2) (standardRootEllipseMap τ δ r t) =
        -(2*(Real.pi:ℂ))*Complex.I := by
  let u : ℂ := circleMap 0 r ((2*Real.pi)*t)
  have hu : 1 < ‖u‖ := by
    simpa only [u,norm_circleMap_zero,abs_of_pos (by linarith : 0 < r)] using hr
  have hu0 : u ≠ 0 := ellipse_circle_ne_zero r t (by linarith)
  have he : HasDerivAt (fun x : ℝ => circleMap 0 r ((2*Real.pi)*x))
      ((2*(Real.pi:ℂ))*(u*Complex.I)) t := by
    simpa only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      using (hasDerivAt_circleMap 0 r ((2*Real.pi)*t)).scomp t (hasDerivAt_const_mul (2*Real.pi))
  have hd : deriv (standardRootEllipseMap τ δ r) t =
      (δ/2*(1-(u^2)⁻¹))*((2*(Real.pi:ℂ))*(u*Complex.I)) := by
    change deriv (fun x : ℝ => standardRootJoukowski τ δ (circleMap 0 r ((2*Real.pi)*x))) t = _
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using
      ((standardRootJoukowski_hasDerivAt τ δ u hu0).scomp t he).deriv
  calc
    _ = ((δ/2*(1-(u^2)⁻¹))/normalizedStandardRoot τ ((2*δ)^2)
        (standardRootEllipseMap τ δ r t))*((2*(Real.pi:ℂ))*(u*Complex.I)) := by rw [hd]; ring
    _ = (-u⁻¹)*((2*(Real.pi:ℂ))*(u*Complex.I)) := by
      rw [show standardRootEllipseMap τ δ r t = τ+δ/2*(u+u⁻¹) from rfl,
        normalizedStandardRoot_joukowski_derivative_div τ δ u hδ hu]
    _ = _ := by field_simp [hu0]

/-- The actual contour integral equals -2πi times the ellipse average. -/
theorem standardRootEllipseLoop_weighted_integral (τ δ : ℂ) (r : ℝ) (hr : 1 < r)
    (hδ : δ ≠ 0) (f : ℂ → ℂ) :
    (standardRootEllipseLoop τ δ r (by linarith)).integral
        (fun z => f z/normalizedStandardRoot τ ((2*δ)^2) z) =
      (-(2*(Real.pi:ℂ))*Complex.I)*(∫ t in (0:ℝ)..1, f (standardRootEllipseMap τ δ r t)) := by
  rw [standardRootEllipseLoop,PiecewiseC1Loop.integral_ofPath,curveIntegral_eq_intervalIntegral_deriv,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro t ht
  have he : (standardRootEllipsePath τ δ r (by linarith)).extend =ᶠ[𝓝 t]
      standardRootEllipseMap τ δ r :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht)
      (fun x hx => standardRootEllipsePath_extend τ δ r _ x (Ioo_subset_Icc_self hx))
  simp only [holomorphicOneForm_apply]
  rw [he.deriv_eq,standardRootEllipsePath_extend τ δ r _ t (Ioo_subset_Icc_self ht)]
  calc
    _ = (deriv (standardRootEllipseMap τ δ r) t /
        normalizedStandardRoot τ ((2*δ)^2) (standardRootEllipseMap τ δ r t))*
          f (standardRootEllipseMap τ δ r t) := by ring
    _ = _ := by rw [standardRootEllipseMap_deriv_div_root τ δ r t hδ hr]

end NLS.ZakharovShabat
