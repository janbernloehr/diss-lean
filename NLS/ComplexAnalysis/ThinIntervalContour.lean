import NLS.ComplexAnalysis.VerticalEllipseLoop
import Mathlib.Topology.MetricSpace.Thickening

/-! Any open neighborhood of a closed real interval contains an actual
smooth comparison contour avoiding that interval and winding once about
EVERY point of it. Degenerate intervals are included. The contour may
be arbitrarily thin; no false shrinking-disc assertion is used. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem ellipseLoop_bounds (c R s : ℝ) (hR : 0 ≤ R) (hs : 0 ≤ s) :
    (ellipseLoop c R s).Inside {z : ℂ | c-R ≤ z.re ∧ z.re ≤ c+R ∧ |z.im| ≤ s*R} := by
  intro i u
  let w := circlePath (c:ℂ) R u
  have hnorm : ‖w-(c:ℂ)‖ = R := by
    exact mem_sphere_iff_norm.mp (circleMap_mem_sphere (c:ℂ) hR ((2*Real.pi)*(u:ℝ)))
  have hx := Complex.abs_re_le_norm (w-(c:ℂ))
  have hy := Complex.abs_im_le_norm (w-(c:ℂ))
  rw [hnorm] at hx hy
  simp only [sub_re,Complex.ofReal_re] at hx
  simp only [sub_im,Complex.ofReal_im,sub_zero] at hy
  change c-R ≤ w.re ∧ w.re ≤ c+R ∧ |s*w.im| ≤ s*R
  refine ⟨by linarith [(abs_le.mp hx).1],by linarith [(abs_le.mp hx).2],?_⟩
  rw [abs_mul,abs_of_nonneg hs]
  exact mul_le_mul_of_nonneg_left hy hs

theorem ellipseLoop_avoids_real_point (c R s a : ℝ) (hR : 0 < R) (hs : 0 < s)
    (ha : (a:ℂ) ∈ ball (c:ℂ) R) : (ellipseLoop c R s).Inside {z : ℂ | z ≠ (a:ℂ)} := by
  intro i u
  let w := circlePath (c:ℂ) R u
  have hw : w ≠ (a:ℂ) := by
    intro he
    have hmem : w ∈ sphere (c:ℂ) R := circleMap_mem_sphere (c:ℂ) hR.le ((2*Real.pi)*(u:ℝ))
    rw [he] at hmem
    exact (mem_ball.mp ha).ne (mem_sphere.mp hmem)
  have h := affine_verticalScale_ne_real s 1 hs (by norm_num) w a hw
  change verticalScale s w ≠ (a:ℂ)
  simpa only [sub_self,zero_smul,one_smul,zero_add] using h

theorem exists_close_real_interval_point (l r δ : ℝ) (hlr : l ≤ r) (hδ : 0 ≤ δ) (z : ℂ)
    (hl : l-δ ≤ z.re) (hr : z.re ≤ r+δ) (hi : |z.im| ≤ δ) :
    ∃ a ∈ Icc l r, dist z (a:ℂ) ≤ 2*δ := by
  have hb (a : ℝ) : dist z (a:ℂ) ≤ |z.re-a|+|z.im| := by
    simpa only [dist_eq_norm,sub_re,sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] using
      Complex.norm_le_abs_re_add_abs_im (z-(a:ℂ))
  by_cases hleft : z.re ≤ l
  · refine ⟨l,⟨le_rfl,hlr⟩,?_⟩
    have hh := hb l
    rw [abs_of_nonpos (sub_nonpos.mpr hleft)] at hh
    linarith
  · by_cases hright : r ≤ z.re
    · refine ⟨r,⟨hlr,le_rfl⟩,?_⟩
      have hh := hb r
      rw [abs_of_nonneg (sub_nonneg.mpr hright)] at hh
      linarith
    · refine ⟨z.re,⟨(not_le.mp hleft).le,(not_le.mp hright).le⟩,?_⟩
      have hh := hb z.re
      rw [sub_self,abs_zero,zero_add] at hh
      linarith

theorem exists_thin_interval_contour (l r : ℝ) (hlr : l ≤ r) (U : Set ℂ) (hU : IsOpen U)
    (hinterval : ∀ a ∈ Icc l r, (a:ℂ) ∈ U) :
    ∃ Γ : PiecewiseC1Loop, Γ.Inside (U \ Complex.ofReal '' Icc l r) ∧
      ∀ a ∈ Icc l r, Γ.windingIntegral (a:ℂ) = 1 := by
  let K : Set ℂ := Complex.ofReal '' Icc l r
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hKU : K ⊆ U := by rintro z ⟨a,ha,rfl⟩; exact hinterval a ha
  obtain ⟨ε,hε,hthick⟩ := hK.exists_thickening_subset_open hU hKU
  let δ : ℝ := ε/4
  let c : ℝ := (l+r)/2
  let R : ℝ := (r-l)/2+δ
  let s : ℝ := δ/R
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hR : 0 < R := by dsimp only [R]; linarith
  have hs : 0 < s := div_pos hδ hR
  have hleft : c-R = l-δ := by dsimp only [c,R]; ring
  have hright : c+R = r+δ := by dsimp only [c,R]; ring
  have hheight : s*R = δ := by dsimp only [s]; exact div_mul_cancel₀ δ hR.ne'
  have hball (a : ℝ) (ha : a ∈ Icc l r) : (a:ℂ) ∈ ball (c:ℂ) R := by
    have ht : |a-c| < R := abs_lt.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩
    simpa only [mem_ball,dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using ht
  refine ⟨ellipseLoop c R s,?_,?_⟩
  · intro i u
    have hb := ellipseLoop_bounds c R s hR.le hs.le i u
    rw [hleft,hright,hheight] at hb
    obtain ⟨a,ha,hd⟩ := exists_close_real_interval_point l r δ hlr hδ.le _ hb.1 hb.2.1 hb.2.2
    refine ⟨hthick (mem_thickening_iff.mpr ⟨(a:ℂ),⟨a,ha,rfl⟩,?_⟩),?_⟩
    · dsimp only [δ] at hd
      linarith
    · rintro ⟨b,hb,he⟩
      exact ellipseLoop_avoids_real_point c R s b hR hs (hball b hb) i u he.symm
  · intro a ha
    exact ellipseLoop_winding_one c R s a hR hs (hball a ha)

end NLS.ComplexAnalysis
