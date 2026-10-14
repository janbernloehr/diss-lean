import NLS.ZakharovShabat.SourceStandardRootJoukowski
import NLS.ZakharovShabat.SourceStandardRootGapSideIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Ellipses around a complex spectral gap

The Joukowski image of a circle outside the unit disk avoids the gap.
As its radius decreases to one, the ellipse approaches the gap uniformly.
-/

noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace NLS.ZakharovShabat

/-- Joukowski points outside the unit disk do not lie on the gap. -/
theorem standardRootJoukowski_not_mem_gap (τ δ u : ℂ) (hδ : δ ≠ 0) (hu : 1 < ‖u‖) :
    standardRootJoukowski τ δ u ∉ standardRootGapSegment τ δ := by
  rintro ⟨t,ht,he⟩
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hmul : δ*((u+u⁻¹)/2-(t:ℂ)) = 0 := by
    dsimp [standardRootJoukowski] at he
    linear_combination -he
  have hj : (u+u⁻¹)/2 = (t:ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hδ)
  have he2 : u^2-2*(t:ℂ)*u+1 = 0 := by
    have h := congrArg (fun z : ℂ => z*(2*u)) hj
    field_simp [hu0] at h
    linear_combination h
  have hre : u.re^2-u.im^2-2*t*u.re+1 = 0 := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re he2
  have him : 2*u.re*u.im-2*t*u.im = 0 := by
    have h := congrArg Complex.im he2
    simp [pow_two, Complex.mul_im] at h
    nlinarith
  have hn : 1 < u.re^2+u.im^2 := by
    have h : 1 < ‖u‖^2 := by nlinarith [norm_nonneg u]
    have he : ‖u‖^2 = u.re^2+u.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    rwa [he] at h
  have hfac : (u.re-t)*u.im = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with hx | hy
  · have hx := sub_eq_zero.mp hx
    rw [hx] at hre hn
    nlinarith
  · have ht2 : t^2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ t+1 by linarith [ht.1])]
    rw [hy] at hre hn
    have hs : (u.re-t)^2 = 0 := by nlinarith [sq_nonneg (u.re-t)]
    have hx := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    rw [hx] at hn
    nlinarith

/-- Ellipse parameterized on the unit interval, with one positive traversal. -/
def standardRootEllipseMap (τ δ : ℂ) (r t : ℝ) : ℂ :=
  standardRootJoukowski τ δ (circleMap 0 r ((2*Real.pi)*t))

theorem standardRootEllipseMap_not_mem_gap (τ δ : ℂ) (r t : ℝ)
    (hδ : δ ≠ 0) (hr : 1 < r) :
    standardRootEllipseMap τ δ r t ∉ standardRootGapSegment τ δ := by
  apply standardRootJoukowski_not_mem_gap τ δ _ hδ
  simpa only [norm_circleMap_zero, abs_of_pos (by linarith : 0 < r)] using hr

/-- The unit circle maps onto points of the closed gap. -/
theorem standardRootJoukowski_mem_gap_of_norm_one (τ δ u : ℂ) (hu : ‖u‖ = 1) :
    standardRootJoukowski τ δ u ∈ standardRootGapSegment τ δ := by
  have hsq : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hi : u⁻¹ = starRingEnd ℂ u := by simp [Complex.inv_def, hsq]
  have hre : |u.re| ≤ 1 := by simpa only [hu] using Complex.abs_re_le_norm u
  refine ⟨u.re,abs_le.mp hre,?_⟩
  rw [standardRootJoukowski, hi]
  have he : u+starRingEnd ℂ u = 2*(u.re:ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  rw [he]
  ring

/-- Every analytic gap neighborhood contains the image of a closed annulus
of positive width outside the unit circle. No enclosing disk is assumed. -/
theorem exists_standardRootJoukowski_annulus_subset (τ δ : ℂ) (U : Set ℂ)
    (hU : IsOpen U) (hgap : standardRootGapSegment τ δ ⊆ U) :
    ∃ R : ℝ, 1 < R ∧ ∀ u : ℂ, 1 ≤ ‖u‖ → ‖u‖ ≤ R → standardRootJoukowski τ δ u ∈ U := by
  let Ω : Set ℂ := {u | u ≠ 0 ∧ standardRootJoukowski τ δ u ∈ U}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro u hu
    exact inter_mem (isOpen_compl_singleton.mem_nhds hu.1)
      ((standardRootJoukowski_analyticAt τ δ u hu.1).continuousAt.preimage_mem_nhds
        (hU.mem_nhds hu.2))
  have hc : sphere (0:ℂ) 1 ⊆ Ω := by
    intro u hu
    have hn := mem_sphere_zero_iff_norm.mp hu
    refine ⟨?_,hgap (standardRootJoukowski_mem_gap_of_norm_one τ δ u hn)⟩
    intro he
    norm_num [he] at hn
  obtain ⟨ε,hε,hsub⟩ := (isCompact_sphere (0:ℂ) 1).exists_thickening_subset_open hΩ hc
  refine ⟨1+ε/2,by linarith,?_⟩
  intro u hu hR
  have hu0 : 0 < ‖u‖ := lt_of_lt_of_le zero_lt_one hu
  have hv : ‖u‖⁻¹ • u ∈ sphere (0:ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hu0), inv_mul_cancel₀ hu0.ne']
  have hd : dist u (‖u‖⁻¹ • u) = ‖u‖-1 := by
    rw [dist_eq_norm, show u-‖u‖⁻¹ • u = (1-‖u‖⁻¹) • u by module,
      norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ hu))]
    field_simp
  have hthick : u ∈ thickening ε (sphere (0:ℂ) 1) :=
    mem_thickening_iff.mpr ⟨‖u‖⁻¹ • u,hv,by rw [hd]; linarith⟩
  exact (hsub hthick).2

/-- At radius one the ellipse degenerates to the cosine parametrization of the gap. -/
theorem standardRootEllipseMap_radius_one (τ δ : ℂ) (t : ℝ) :
    standardRootEllipseMap τ δ 1 t = τ+δ*(Real.cos ((2*Real.pi)*t):ℂ) := by
  let u := circleMap 0 1 ((2*Real.pi)*t)
  have hu : ‖u‖ = 1 := by simp [u]
  have hsq : Complex.normSq u = 1 := by rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  have hi : u⁻¹ = starRingEnd ℂ u := by simp [Complex.inv_def, hsq]
  change τ+δ/2*(u+u⁻¹) = _
  rw [hi]
  have he : u+starRingEnd ℂ u = 2*(u.re:ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  rw [he]
  have hre : u.re = Real.cos ((2*Real.pi)*t) := by simp [u,circleMap,Complex.exp_re]
  rw [hre]
  ring

/-- Joint continuity in ellipse radius and parameter away from radius zero. -/
theorem standardRootEllipseMap_continuousAt (τ δ : ℂ) (r t : ℝ) (hr : 0 < r) :
    ContinuousAt (fun x : ℝ × ℝ => standardRootEllipseMap τ δ x.1 x.2) (r,t) := by
  have he : ContinuousAt (fun x : ℝ × ℝ => circleMap 0 x.1 ((2*Real.pi)*x.2)) (r,t) := by
    simp only [circleMap]
    fun_prop
  have hn : circleMap 0 r ((2*Real.pi)*t) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa only [norm_circleMap_zero,abs_of_pos hr] using hr.ne'
  exact continuousAt_const.add (continuousAt_const.mul (he.add (he.inv₀ hn)))

end NLS.ZakharovShabat
