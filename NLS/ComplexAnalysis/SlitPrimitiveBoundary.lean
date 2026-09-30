import NLS.ComplexAnalysis.IntegrableDerivativeBoundary
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A common primitive boundary value at a slit endpoint

The change of coordinate `z = -w²` turns inverse-square-root
derivative growth into a bounded derivative on a convex right
half-disc. Comparing with the negative real ray gives one limit
for all approaches in the positive-ray complement, including
approaches from both sides of the slit.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory Metric
namespace NLS.ComplexAnalysis

/-- The plane with the nonnegative real ray removed. -/
def positiveSlitPlane : Set ℂ := {z | z.re < 0 ∨ z.im ≠ 0}

theorem positiveSlitPlane_ne_zero {z : ℂ} (hz : z ∈ positiveSlitPlane) : z ≠ 0 := by
  intro h
  subst z
  simp [positiveSlitPlane] at hz

theorem neg_mem_slitPlane {z : ℂ} (hz : z ∈ positiveSlitPlane) : -z ∈ slitPlane := by
  simpa [positiveSlitPlane, slitPlane] using hz

theorem neg_sq_mem_positiveSlitPlane {w : ℂ} (hw : 0 < w.re) :
    -w^2 ∈ positiveSlitPlane := by
  by_cases hi : w.im = 0
  · left
    simp only [neg_re, pow_two, mul_re, hi, mul_zero, sub_zero]
    nlinarith
  · right
    simp only [neg_im, pow_two, mul_im, neg_ne_zero]
    rw [show w.re*w.im+w.im*w.re = 2*w.re*w.im by ring]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hw)) hi

/-- A local inverse-square-root bound supplies a full slit-plane
boundary limit. Derivative and continuity assumptions are local. -/
theorem exists_primitive_positiveSlit_boundary_limit
    (f F : ℂ → ℂ) (δ M ε : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hf : ContinuousOn f (ball 0 ε ∩ positiveSlitPlane))
    (hF : ∀ z ∈ ball 0 ε ∩ positiveSlitPlane, HasDerivAt F (f z) z)
    (hbound : ∀ z ∈ ball 0 ε ∩ positiveSlitPlane,
      ‖f z * (Real.sqrt (δ*‖z‖) : ℂ)‖ ≤ M) :
    ∃ A : ℂ, Tendsto F (𝓝[positiveSlitPlane] 0) (𝓝 A) := by
  have hneg (t : ℝ) (ht : t ∈ Ioo (0:ℝ) ε) :
      -(t:ℂ) ∈ ball 0 ε ∩ positiveSlitPlane := by
    refine ⟨?_,Or.inl (by simpa using ht.1)⟩
    simpa [mem_ball, dist_eq_norm, abs_of_pos ht.1] using ht.2
  have hcont : ContinuousOn (fun t : ℝ => f (-(t:ℂ))) (Ioo 0 ε) :=
    hf.comp (by fun_prop) hneg
  have hint : IntegrableOn (fun t : ℝ => f (-(t:ℂ))) (Ioo 0 ε) := by
    apply integrableOn_Ioo_of_norm_mul_sqrt_mul_le hδ hε
      (hcont.aestronglyMeasurable measurableSet_Ioo)
    intro t ht
    simpa [abs_of_pos ht.1] using hbound _ (hneg t ht)
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) ε) :
      HasDerivAt (fun u : ℝ => F (-(u:ℂ))) (-f (-(t:ℂ))) t := by
    have hn : HasDerivAt (fun u : ℝ => -(u:ℂ)) (-1) t :=
      ((hasDerivAt_id (t:ℂ)).neg).comp_ofReal
    simpa only [Function.comp_def, smul_eq_mul, mul_neg, mul_one, neg_one_mul] using
      (hF _ (hneg t ht)).scomp t hn
  obtain ⟨A,hA,_⟩ := exists_tendsto_zero_of_integrable_derivative
    (fun t : ℝ => F (-(t:ℂ))) (fun t : ℝ => -f (-(t:ℂ))) ε hε hint.neg hderiv
  let U : Set ℂ := {w | 0 < w.re} ∩ ball 0 (Real.sqrt ε)
  let G : ℂ → ℂ := fun w => F (-w^2)
  let g : ℂ → ℂ := fun w => f (-w^2) * (-2*w)
  let C : ℝ := 2*M/Real.sqrt δ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hUconv : Convex ℝ U := (convex_halfSpace_re_gt 0).inter (convex_ball _ _)
  have hUw (w : ℂ) (hw : w ∈ U) : -w^2 ∈ ball 0 ε ∩ positiveSlitPlane := by
    refine ⟨?_,neg_sq_mem_positiveSlitPlane hw.1⟩
    have hwR : ‖w‖ < Real.sqrt ε := by
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hw.2
    have hs : (Real.sqrt ε)^2 = ε := Real.sq_sqrt hε.le
    simp only [mem_ball, dist_eq_norm, sub_zero, norm_neg, norm_pow]
    nlinarith [norm_nonneg w, Real.sqrt_nonneg ε]
  have hG (w : ℂ) (hw : w ∈ U) : HasDerivAt G (g w) w := by
    have hn : HasDerivAt (fun v : ℂ => -v^2) (-2*w) w := by
      convert ((hasDerivAt_id w).pow 2).neg using 1 <;>
        first | rfl | (simp only [id_eq, Nat.cast_ofNat, mul_one]; ring)
    exact (hF _ (hUw w hw)).comp w hn
  have hg (w : ℂ) (hw : w ∈ U) : ‖g w‖ ≤ C := by
    have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hb := hbound _ (hUw w hw)
    have hs : Real.sqrt (δ*‖-w^2‖) = Real.sqrt δ * ‖w‖ := by
      rw [norm_neg, norm_pow, Real.sqrt_mul hδ.le, Real.sqrt_sq_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),hs] at hb
    have hnorm : ‖g w‖ = 2 * (‖f (-w^2)‖ * ‖w‖) := by
      simp [g,norm_neg]; ring
    rw [hnorm]
    dsimp only [C]
    apply (le_div_iff₀ hsd).2
    nlinarith
  have hcomparison (z : ℂ) (hz : z ∈ ball 0 ε ∩ positiveSlitPlane) :
      ‖F z - F (-(‖z‖:ℂ))‖ ≤ 2*C*Real.sqrt ‖z‖ := by
    let w := Complex.sqrt (-z)
    have hw2 : w^2 = -z := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
    have hwre : 0 < w.re := by
      have hn : ‖-z‖ + (-z).re > 0 := by
        rcases neg_mem_slitPlane hz.2 with hr | hi
        · linarith [norm_nonneg (-z)]
        · have hlt := Complex.abs_re_lt_norm.mpr hi
          linarith [neg_le_abs (-z).re]
      change 0 < (Complex.sqrt (-z)).re
      rw [Complex.sqrt, Complex.cpow_inv_two_re]
      exact Real.sqrt_pos.2 (by linarith)
    have hwsq : ‖w‖^2 = ‖z‖ := by
      simpa only [norm_pow,norm_neg] using congrArg norm hw2
    have hwnorm : ‖w‖ = Real.sqrt ‖z‖ := by
      rw [← hwsq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
    have hwR : ‖w‖ < Real.sqrt ε := by
      rw [hwnorm]
      exact Real.sqrt_lt_sqrt (norm_nonneg _) (by
        simpa only [mem_ball,dist_eq_norm,sub_zero] using hz.1)
    have hwU : w ∈ U := ⟨hwre,by simpa [mem_ball,dist_eq_norm] using hwR⟩
    have hrpos : 0 < ‖w‖ := (Complex.re_le_norm w).trans_lt' hwre
    have hrU : (‖w‖:ℂ) ∈ U := ⟨by simpa using hrpos,by
      simpa [mem_ball,dist_eq_norm,abs_of_nonneg (norm_nonneg w)] using hwR⟩
    have hb := hUconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun q hq => (hG q hq).hasDerivWithinAt) hg hrU hwU
    have hlen : ‖w-(‖w‖:ℂ)‖ ≤ 2*‖w‖ := by
      simpa [abs_of_nonneg (norm_nonneg w),two_mul] using norm_sub_le w (‖w‖:ℂ)
    have hleft : G w = F z := by dsimp [G]; rw [hw2,neg_neg]
    have hright : G (‖w‖:ℂ) = F (-(‖z‖:ℂ)) := by
      dsimp [G]
      congr 1
      rw [← Complex.ofReal_pow,hwsq]
    rw [hleft,hright] at hb
    exact hb.trans (by
      calc
        C*‖w-(‖w‖:ℂ)‖ ≤ C*(2*‖w‖) := mul_le_mul_of_nonneg_left hlen hC
        _ = 2*C*Real.sqrt ‖z‖ := by rw [hwnorm]; ring)
  have hnormlim : Tendsto (fun z : ℂ => ‖z‖) (𝓝[positiveSlitPlane] 0) (𝓝 (0:ℝ)) := by
    simpa using (continuous_norm.continuousAt (x := (0:ℂ))).tendsto.mono_left nhdsWithin_le_nhds
  have hnormpos : ∀ᶠ z in 𝓝[positiveSlitPlane] 0, 0 < ‖z‖ := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pos_iff.mpr (positiveSlitPlane_ne_zero hz)
  have hray : Tendsto (fun z : ℂ => F (-(‖z‖:ℂ)))
      (𝓝[positiveSlitPlane] 0) (𝓝 A) :=
    hA.comp (tendsto_nhdsWithin_iff.mpr ⟨hnormlim,hnormpos⟩)
  have hdiff : Tendsto (fun z : ℂ => F z - F (-(‖z‖:ℂ)))
      (𝓝[positiveSlitPlane] 0) (𝓝 (0:ℂ)) := by
    have hsqrt : Tendsto (fun z : ℂ => Real.sqrt ‖z‖)
        (𝓝[positiveSlitPlane] 0) (𝓝 (0:ℝ)) := by
      convert (Real.continuous_sqrt.tendsto (0:ℝ)).comp hnormlim using 1 <;>
        first | rfl | simp only [Real.sqrt_zero]
    have hmajor : Tendsto (fun z : ℂ => 2*C*Real.sqrt ‖z‖)
        (𝓝[positiveSlitPlane] 0) (𝓝 (0:ℝ)) := by
      simpa using tendsto_const_nhds.mul hsqrt
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
    filter_upwards [self_mem_nhdsWithin, hnormlim.eventually (Iio_mem_nhds hε)] with z hz hn
    exact hcomparison z ⟨by simpa [mem_ball,dist_eq_norm] using hn,hz⟩
  refine ⟨A,?_⟩
  simpa only [sub_add_cancel,zero_add] using hdiff.add hray

end NLS.ComplexAnalysis
