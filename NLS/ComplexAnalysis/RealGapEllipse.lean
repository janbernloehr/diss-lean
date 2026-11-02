import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.RealCutConjugation

/-!
# Ellipses shrinking onto a real gap

The clockwise ellipse with horizontal semiaxis `d + ε` and vertical
semiaxis `ε` encloses `[c-d,c+d]` for every `d > 0`, `ε > 0`.
Its trace and tangent have explicit limits as `ε` decreases to zero.
These formulas retain the orientation needed when a contour is collapsed
onto the two sides of a spectral gap.
-/

noncomputable section
open Set Metric Complex Filter
open scoped unitInterval Topology

namespace NLS.ComplexAnalysis

/-- Clockwise ellipse, with a line segment as its zero-height limit. -/
def realGapEllipse (c d ε θ : ℝ) : ℂ :=
  (c : ℂ) + (((d + ε) * Real.cos θ : ℝ) : ℂ) -
    ((ε * Real.sin θ : ℝ) : ℂ) * Complex.I

@[simp] theorem realGapEllipse_re (c d ε θ : ℝ) :
    (realGapEllipse c d ε θ).re = c + (d + ε) * Real.cos θ := by
  simp only [realGapEllipse, add_re, sub_re, mul_re, ofReal_re,
    ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero]

@[simp] theorem realGapEllipse_im (c d ε θ : ℝ) :
    (realGapEllipse c d ε θ).im = -ε * Real.sin θ := by
  simp only [realGapEllipse, add_im, sub_im, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_one, mul_zero, add_zero, zero_sub]
  ring

@[simp] theorem realGapEllipse_zero (c d ε : ℝ) :
    realGapEllipse c d ε 0 = ((c + d + ε : ℝ) : ℂ) := by
  simp [realGapEllipse]
  ring

@[simp] theorem realGapEllipse_two_pi (c d ε : ℝ) :
    realGapEllipse c d ε (2 * Real.pi) = ((c + d + ε : ℝ) : ℂ) := by
  simp [realGapEllipse]
  ring

theorem hasDerivAt_realGapEllipse (c d ε θ : ℝ) :
    HasDerivAt (realGapEllipse c d ε)
      (((-(d + ε) * Real.sin θ : ℝ) : ℂ) -
        ((ε * Real.cos θ : ℝ) : ℂ) * Complex.I) θ := by
  simpa only [realGapEllipse, zero_add, neg_mul, mul_neg, ofReal_neg] using!
    ((hasDerivAt_const θ (c : ℂ)).add
    (((Real.hasDerivAt_cos θ).const_mul (d + ε)).ofReal_comp)).sub
    ((((Real.hasDerivAt_sin θ).const_mul ε).ofReal_comp).mul_const Complex.I)

/-- Uniform containment in the circle through the two horizontal vertices. -/
theorem realGapEllipse_mem_closedBall (c d ε θ : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε) :
    realGapEllipse c d ε θ ∈ closedBall (c : ℂ) (d + ε) := by
  rw [mem_closedBall, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ d + ε)).mp
  rw [Complex.sq_norm]
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im,
    realGapEllipse_re, realGapEllipse_im, add_sub_cancel_left, sub_zero]
  have htrig := Real.sin_sq_add_cos_sq θ
  have hsin : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hfactor : 0 ≤ d ^ 2 + 2 * d * ε := by positivity
  nlinarith [mul_nonneg hfactor hsin]

/-- A real segment has its real projection between its ordered endpoints. -/
theorem re_mem_Icc_of_mem_real_segment (a b : ℝ) (hab : a ≤ b) (z : ℂ)
    (hz : z ∈ segment ℝ (a : ℂ) b) : z.re ∈ Icc a b := by
  obtain ⟨t, ht, rfl⟩ := by rw [segment_eq_image_lineMap] at hz; exact hz
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul,
    add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hab),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hab)]

/-- All ellipses of positive height avoid the entire enclosed segment. -/
theorem realGapEllipse_not_mem_segment (c d ε θ : ℝ)
    (hd : 0 < d) (hε : 0 < ε) :
    realGapEllipse c d ε θ ∉ segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ) := by
  intro hz
  have him := im_eq_zero_of_mem_real_segment (c - d) (c + d) _ hz
  rw [realGapEllipse_im] at him
  have hs : Real.sin θ = 0 := (mul_eq_zero.mp him).resolve_left (neg_ne_zero.mpr hε.ne')
  have hr := re_mem_Icc_of_mem_real_segment (c - d) (c + d)
    (by linarith) _ hz
  rw [realGapEllipse_re] at hr
  have hc : Real.cos θ ^ 2 = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
  have hbounds : -d ≤ (d + ε) * Real.cos θ ∧ (d + ε) * Real.cos θ ≤ d := by
    constructor <;> linarith [hr.1, hr.2]
  have hsq : ((d + ε) * Real.cos θ) ^ 2 ≤ d ^ 2 :=
    sq_le_sq' hbounds.1 hbounds.2
  rw [mul_pow, hc, mul_one] at hsq
  nlinarith [sq_nonneg ε]

/-- The positive-height ellipses tend to the real segment parameterization. -/
theorem tendsto_realGapEllipse (c d θ : ℝ) :
    Tendsto (fun ε => realGapEllipse c d ε θ) (𝓝 0)
      (𝓝 (((c + d * Real.cos θ : ℝ) : ℂ))) := by
  have hc : Continuous (fun ε => realGapEllipse c d ε θ) := by
    unfold realGapEllipse
    fun_prop
  simpa [realGapEllipse] using hc.continuousAt.tendsto (x := 0)

/-- Smooth closed path based at the right horizontal vertex. -/
def realGapEllipsePath (c d ε : ℝ) :
    Path (((c + d + ε : ℝ) : ℂ)) (((c + d + ε : ℝ) : ℂ)) :=
  Path.ofLine (f := fun t : ℝ => realGapEllipse c d ε ((2 * Real.pi) * t))
    (by unfold realGapEllipse; fun_prop)
    (by simp)
    (by simp)

theorem realGapEllipsePath_contDiffOn (c d ε : ℝ) :
    ContDiffOn ℝ 2 (realGapEllipsePath c d ε).extend (Icc 0 1) := by
  have hcos : ContDiff ℝ 2 (fun t : ℝ =>
      (((d + ε) * Real.cos ((2 * Real.pi) * t) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp
        (show ContDiff ℝ 2 (fun t : ℝ => (d + ε) * Real.cos ((2 * Real.pi) * t))
          from by fun_prop)
  have hsin : ContDiff ℝ 2 (fun t : ℝ =>
      ((ε * Real.sin ((2 * Real.pi) * t) : ℝ) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp
        (show ContDiff ℝ 2 (fun t : ℝ => ε * Real.sin ((2 * Real.pi) * t))
          from by fun_prop)
  have h : ContDiff ℝ 2
      (fun t : ℝ => realGapEllipse c d ε ((2 * Real.pi) * t)) :=
    (contDiff_const.add hcos).sub (hsin.mul contDiff_const)
  apply h.contDiffOn.congr
  intro t ht
  rw [(realGapEllipsePath c d ε).extend_apply ht]
  rfl

end NLS.ComplexAnalysis
