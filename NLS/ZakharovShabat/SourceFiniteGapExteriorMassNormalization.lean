import NLS.ZakharovShabat.SourceFiniteGapExteriorPrimitive
import NLS.ZakharovShabat.SourceMassNormalizedPrimitive

/-! # Mass normalization of the finite-gap exterior primitive

The exterior primitive and the normalized upper primitive have the same
derivative along a terminal imaginary ray. One additive correction gives
the exterior primitive the exact source mass coefficient. This is still
a ray limit, not yet a Laurent expansion or an action trace formula.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- The primitive on the full exterior can be normalized to recover half
the original Hilbert source norm squared on the upper imaginary ray. -/
theorem exists_sourceFiniteGap_exterior_primitive_norm_normalized
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ R : ℝ, 0 < R ∧ ∃ F : ℂ → ℂ,
      (∀ z : ℂ, R < ‖z‖ → HasDerivAt F
        (sourceFloquetLogDerivative (by simp) (by norm_num) φ.val z) z) ∧
      Tendsto (fun y : ℝ => (2*y : ℂ)*(F ((y : ℂ)*I) - y)) atTop
        (𝓝 ((‖φ.val‖^2/2 : ℝ) : ℂ)) := by
  obtain ⟨R, hR, F, hF⟩ := exists_sourceFiniteGap_exterior_primitive
    (by simp) (by norm_num) φ hfinite
  obtain ⟨G, hG, hmass⟩ := exists_sourceUpperPrimitive_norm_normalized_finiteGap φ hfinite
  let q := fun z => deriv (canonicalDiscriminant (by simp) (periodOnePotential φ.val)) z /
    sourceCanonicalRoot (by simp) (by norm_num) φ.val z
  have hpos (y : ℝ) (hy : y ∈ Ioi R) : 0 < y := hR.trans hy
  have hf (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => F ((y : ℂ)*I)) (q ((y : ℂ)*I)*I) y := by
    have hn : R < ‖(y : ℂ)*I‖ := by
      simpa only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos y hy), mem_Ioi] using hy
    have hz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) φ.val φ.property
      ((y : ℂ)*I) (by simpa using ne_of_gt (hpos y hy))
    have hd := hF ((y : ℂ)*I) hn
    rw [sourceFloquetLogDerivative_eq_criticalRootRatio (by simp) (by norm_num)
      φ.val φ.property _ hz] at hd
    simpa only [one_mul, Function.comp_def] using!
      (hd.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  have hg (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => G ((y : ℂ)*I)) (q ((y : ℂ)*I)*I) y := by
    simpa only [one_mul, Function.comp_def] using!
      ((hG ((y : ℂ)*I) (by simpa using hpos y hy)).comp (y : ℂ)
        ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq (convex_Ioi R).isPreconnected
    (fun y hy => (hf y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hf y hy).deriv.trans (hg y hy).deriv.symm)
  refine ⟨R, hR, fun z => F z - c, fun z hz => (hF z hz).sub_const c, ?_⟩
  apply hmass.congr'
  filter_upwards [eventually_gt_atTop R] with y hy
  have he : F ((y : ℂ)*I) = G ((y : ℂ)*I) + c := hc hy
  rw [he, add_sub_cancel_right]

end NLS.ZakharovShabat
