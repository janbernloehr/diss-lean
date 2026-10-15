import NLS.ComplexAnalysis.PrimitiveRadialContinuation
import Mathlib.Tactic.Module

/-!
# Smooth admissible paths avoiding a complex segment

A quadratic Bézier arc stays in any open convex set and lies strictly on one
side of the line through a given segment. Its distances to both segment
endpoints have a common positive lower bound proportional to t(1-t).
The construction includes coincident endpoints and closed paths.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The quadratic Bézier polynomial with endpoints a and b and control point c. -/
def quadraticBezier (a c b : ℂ) (t : ℝ) : ℂ :=
  (1-t)^2 • a + (2*t*(1-t)) • c + t^2 • b

/-- The quadratic Bézier polynomial restricted to the unit interval. -/
def quadraticBezierPath (a c b : ℂ) : Path a b :=
  Path.ofLine (f := quadraticBezier a c b)
    (by unfold quadraticBezier; fun_prop)
    (by simp [quadraticBezier]) (by simp [quadraticBezier])

/-- On the parameter interval the extended path is the Bézier polynomial. -/
theorem quadraticBezierPath_extend (a c b : ℂ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (quadraticBezierPath a c b).extend t = quadraticBezier a c b t := by
  rw [Path.extend_apply _ ht]
  rfl

/-- The constructed path is continuously differentiable, including at both endpoints. -/
theorem quadraticBezierPath_contDiffOn (a c b : ℂ) :
    ContDiffOn ℝ 1 (quadraticBezierPath a c b).extend (Icc 0 1) := by
  have h : ContDiff ℝ 1 (quadraticBezier a c b) := by unfold quadraticBezier; fun_prop
  exact h.contDiffOn.congr (fun t ht => quadraticBezierPath_extend a c b t ht)

/-- The Bézier curve is an iterated convex interpolation. -/
theorem quadraticBezier_eq_lineMap (a c b : ℂ) (t : ℝ) :
    quadraticBezier a c b t =
      AffineMap.lineMap (AffineMap.lineMap a c t) (AffineMap.lineMap c b t) t := by
  simp only [quadraticBezier,AffineMap.lineMap_apply_module,smul_add,smul_smul]
  module

/-- Every convex set containing the control points contains the entire arc. -/
theorem quadraticBezierPath_mem_convex (a c b : ℂ) (S : Set ℂ) (hS : Convex ℝ S)
    (ha : a ∈ S) (hc : c ∈ S) (hb : b ∈ S)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (quadraticBezierPath a c b).extend t ∈ S := by
  rw [quadraticBezierPath_extend _ _ _ _ ht,quadraticBezier_eq_lineMap]
  apply hS.segment_subset
    (hS.segment_subset ha hc (lineMap_mem_segment ℝ a c ht))
    (hS.segment_subset hc hb (lineMap_mem_segment ℝ c b ht))
  exact lineMap_mem_segment ℝ _ _ ht

/-- A convex disk containing the three control points contains the entire curve. -/
theorem quadraticBezierPath_mem_ball (a c b o : ℂ) (R : ℝ)
    (ha : a ∈ ball o R) (hc : c ∈ ball o R) (hb : b ∈ ball o R)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (quadraticBezierPath a c b).extend t ∈ ball o R :=
  quadraticBezierPath_mem_convex a c b _ (convex_ball o R) ha hc hb t ht

/-- The initial displacement has a useful polynomial factorization. -/
theorem quadraticBezier_sub (a c b : ℂ) (t : ℝ) :
    quadraticBezier a c b t-a = (2*t*(1-t)) • (c-a) + t^2 • (b-a) := by
  simp only [quadraticBezier,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_sub,
    Complex.ofReal_one,Complex.ofReal_pow,Complex.ofReal_ofNat]
  ring

/-- The transverse coordinate is a nonnegative combination of the control-point coordinates. -/
theorem quadraticBezier_im_div (a c b v : ℂ) (t : ℝ) :
    ((quadraticBezier a c b t-a)/v).im =
      2*t*(1-t)*((c-a)/v).im+t^2*((b-a)/v).im := by
  rw [quadraticBezier_sub]
  simp only [Complex.real_smul,add_div,mul_div_assoc,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

private theorem segment_im_div_eq_zero (a r v z : ℂ)
    (hr : ((r-a)/v).im = 0) (hz : z ∈ segment ℝ a r) : ((z-a)/v).im = 0 := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t,_,rfl⟩ := hz
  have he : AffineMap.lineMap a r t-a = t • (r-a) := by
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul]
    push_cast
    ring
  rw [he]
  simp [Complex.real_smul,mul_div_assoc,hr]

private theorem transverse_distance_lower (a v z w : ℂ) (hv : v ≠ 0)
    (hz : ((z-a)/v).im = 0) (u : ℝ) (hu : u ≤ ((w-a)/v).im) :
    u*‖v‖ ≤ ‖z-w‖ := by
  have he : ((w-z)/v).im = ((w-a)/v).im := by
    rw [show w-z = (w-a)-(z-a) by ring,sub_div,Complex.sub_im,hz,sub_zero]
  have hh : u ≤ ‖w-z‖/‖v‖ := by
    calc
      u ≤ ((w-z)/v).im := by rwa [he]
      _ ≤ ‖(w-z)/v‖ := im_le_norm _
      _ = _ := norm_div _ _
  simpa only [norm_sub_rev] using (le_div_iff₀ (norm_pos_iff.mpr hv)).mp hh

private theorem exists_upper_bezier_path (a r b v : ℂ) (S : Set ℂ) (hS : IsOpen S) (hconv : Convex ℝ S)
    (ha : a ∈ S) (hb : b ∈ S) (hv : v ≠ 0)
    (hr : ((r-a)/v).im = 0) (hbup : 0 ≤ ((b-a)/v).im) :
    ∃ γ : Path a b, ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ S) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
        γ.extend t ∉ segment ℝ a r ∧
        k*t*(1-t) ≤ ‖a-γ.extend t‖ ∧ k*t*(1-t) ≤ ‖r-γ.extend t‖ := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  let ε := δ/(2*‖v‖)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hε : 0 < ε := by dsimp [ε]; positivity
  let c := a+(ε:ℂ)*Complex.I*v
  have hc : c ∈ S := by
    apply hball
    rw [mem_ball,dist_eq_norm]
    have he : ‖c-a‖ = δ/2 := by
      simp only [c,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_of_nonneg hε.le,norm_I,mul_one]
      dsimp [ε]
      field_simp
    rw [he]
    linarith
  have hcim : ((c-a)/v).im = ε := by simp [c,hv]
  let γ := quadraticBezierPath a c b
  let k := 2*ε*‖v‖
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨γ,quadraticBezierPath_contDiffOn _ _ _,quadraticBezierPath_mem_convex _ _ _ _ hconv ha hc hb,k,hk,?_⟩
  intro t ht
  have hi : 2*ε*t*(1-t) ≤ ((γ.extend t-a)/v).im := by
    rw [quadraticBezierPath_extend _ _ _ _ (Ioo_subset_Icc_self ht),quadraticBezier_im_div,hcim]
    nlinarith [mul_nonneg (sq_nonneg t) hbup]
  have hdist (z : ℂ) (hz : ((z-a)/v).im = 0) : k*t*(1-t) ≤ ‖z-γ.extend t‖ := by
    have h := transverse_distance_lower a v z (γ.extend t) hv hz _ hi
    convert h using 1
    dsimp [k]
    ring
  refine ⟨?_,hdist a (by simp),hdist r hr⟩
  intro hseg
  have h := hdist (γ.extend t) (segment_im_div_eq_zero a r v _ hr hseg)
  have hpos : 0 < k*t*(1-t) := mul_pos (mul_pos hk ht.1) (sub_pos.mpr ht.2)
  simp only [sub_self,norm_zero] at h
  linarith

/-- An open convex set admits a segment-avoiding smooth path with endpoint separation. -/
theorem exists_bezier_admissible_path_in_open_convex (a r b : ℂ)
    (S : Set ℂ) (hS : IsOpen S) (hconv : Convex ℝ S)
    (ha : a ∈ S) (hb : b ∈ S) :
    ∃ γ : Path a b, ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ S) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
        γ.extend t ∉ segment ℝ a r ∧
        k*t*(1-t) ≤ ‖a-γ.extend t‖ ∧ k*t*(1-t) ≤ ‖r-γ.extend t‖ := by
  let v := if r = a then (1:ℂ) else r-a
  have hv : v ≠ 0 := by
    dsimp [v]
    split_ifs with h
    · exact one_ne_zero
    · exact sub_ne_zero.mpr h
  have hr : ((r-a)/v).im = 0 := by
    dsimp [v]
    split_ifs with h
    · simp [h]
    · simp [sub_ne_zero.mpr h]
  by_cases hbup : 0 ≤ ((b-a)/v).im
  · exact exists_upper_bezier_path a r b v S hS hconv ha hb hv hr hbup
  · apply exists_upper_bezier_path a r b (-v) S hS hconv ha hb (neg_ne_zero.mpr hv)
    · simp only [div_neg,Complex.neg_im,hr,neg_zero]
    · simp only [div_neg,Complex.neg_im]
      linarith


/-- A disk admits a smooth segment-avoiding path with quantitative endpoint separation. -/
theorem exists_bezier_admissible_path (a r b o : ℂ) (R : ℝ)
    (ha : a ∈ ball o R) (hb : b ∈ ball o R) :
    ∃ γ : Path a b, ContDiffOn ℝ 1 γ.extend (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ ball o R) ∧
      ∃ k : ℝ, 0 < k ∧ ∀ t ∈ Ioo (0:ℝ) 1,
        γ.extend t ∉ segment ℝ a r ∧
        k*t*(1-t) ≤ ‖a-γ.extend t‖ ∧ k*t*(1-t) ≤ ‖r-γ.extend t‖ :=
  exists_bezier_admissible_path_in_open_convex a r b (ball o R) isOpen_ball (convex_ball o R) ha hb

end NLS.ComplexAnalysis
