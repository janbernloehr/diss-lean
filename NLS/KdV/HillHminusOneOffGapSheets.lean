import NLS.KdV.HillHminusOneOffGapPrimitive
import NLS.KdV.HillHminusOnePrimitiveSquareSheets
import NLS.KdV.HillHminusOneRealGapRoot

/-! # The off-gap primitive agrees with both actual physical sheets

A vertical midpoint value fixes the sign, including at a collapsed gap.
Connectedness of each half-disc propagates that value to the ACTUAL
source-continued primitive, without choosing a new square-root sign.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusOffGapPrimitive_midpoint_sign
    (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (l u s y : ℝ) (hs : s = 1 ∨ s = -1) (hy : 0 < y)
    (hnorm : ‖hillHminusJointNormalizedGapRoot n r K
      ((((l+u)/2 : ℝ) : ℂ)+(s*y : ℝ)*I,q)-1‖ < 1) :
    0 < s*(hillHminusOffGapPrimitive n r K q (l : ℂ) (u : ℂ)
      ((((l+u)/2 : ℝ) : ℂ)+(s*y : ℝ)*I)).re := by
  let m : ℝ := (l+u)/2
  let d : ℝ := (u-l)/2
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : ((l : ℂ)+(u : ℂ))/2 = (m : ℂ) := by dsimp [m]; push_cast; rfl
  have hd : ((u : ℂ)-(l : ℂ))^2 = (2*(d : ℂ))^2 := by dsimp [d]; push_cast; ring
  obtain ⟨a,ha,hup,hdown⟩ := exists_standardRoot_vertical_midpoint_value (m : ℂ) d y hy
  have hroot : normalizedStandardRoot (m : ℂ) ((2*(d : ℂ))^2)
      ((m : ℂ)+(s*y : ℝ)*I) = -(s : ℂ)*(a : ℂ)*I := by
    rcases hs with rfl | rfl
    · simpa using hup
    · simpa [sub_eq_add_neg] using hdown
  have hcoef : I/(2*((Real.pi : ℂ)*(n : ℕ)))*(-(s : ℂ)*(a : ℂ)*I) =
      (((s*a/(2*c) : ℝ) : ℂ)) := by
    dsimp [c]
    push_cast
    field_simp
    rw [I_sq]
    ring
  have hsp : 0 < (hillHminusJointNormalizedGapRoot n r K
      ((m : ℂ)+(s*y : ℝ)*I,q)).re := re_pos_of_norm_sub_one_lt_one _ hnorm
  have hs2 : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  dsimp only [hillHminusOffGapPrimitive]
  rw [hm,hd,hroot,hcoef]
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  calc
    _ = s^2*(a/(2*c)*(hillHminusJointNormalizedGapRoot n r K
        ((m : ℂ)+(s*y : ℝ)*I,q)).re) := by ring
    _ > 0 := by rw [hs2,one_mul]; exact mul_pos (div_pos ha (by positivity)) hsp

theorem hillHminusOffGapPrimitive_eq_shifted_half_disc
    (n : ℕ+) (r : ℝ) (hr : 0 < r) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (l u : ℝ) (hlu : l ≤ u)
    (hpair : HillHminusHighGapPair q n r (l : ℂ) (u : ℂ))
    (hS : AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)))
    (hnorm : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ < 1)
    (hf : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
      K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
        (4*((Real.pi : ℂ)*(n : ℕ))^2))
    (hmatch : ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r), z.im ≠ 0 →
      K (z,q) = (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^2)
    (s : ℝ) (hs : s = 1 ∨ s = -1) (z : ℂ)
    (hz : z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) (hside : 0 < s*z.im) :
    hillHminusOffGapPrimitive n r K q (l : ℂ) (u : ℂ) z =
      hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi := by
  let U : Set ℂ := ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
  let D : Set ℂ := U ∩ {w : ℂ | 0 < s*w.im}
  let F : ℂ → ℂ := fun w => hillHminusContinuedPrimitive (w,q)+I*(n : ℂ)*Real.pi
  let G := hillHminusOffGapPrimitive n r K q (l : ℂ) (u : ℂ)
  have hne (w : ℂ) (hw : w ∈ D) : w.im ≠ 0 := by
    intro he
    have hh : 0 < s*w.im := hw.2
    rw [he,mul_zero] at hh
    exact lt_irrefl _ hh
  have hsign (w : ℂ) (hw : w ∈ D) : 0 < s*(F w).re := by
    rcases hs with rfl | rfl
    · have him : 0 < w.im := by simpa [D] using hw.2
      simpa [F] using hillHminusContinuedPrimitive_boundary_re_pos q hq w him
    · have him : w.im < 0 := by simpa [D] using hw.2
      simpa [F] using hillHminusContinuedPrimitive_boundary_re_neg q hq w him
  have hD : Convex ℝ D := by
    rcases hs with rfl | rfl
    · simpa [D,U] using (convex_ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)).inter
        (convex_halfSpace_im_gt 0)
    · simpa [D,U] using (convex_ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)).inter
        (convex_halfSpace_im_lt 0)
  have hF : ContinuousOn F D :=
    ((analyticOnNhd_hillHminusContinuedPrimitive_off_real q hq).continuousOn.mono
      (fun w hw => hne w hw)).add continuousOn_const
  have hG : ContinuousOn G D :=
    (analyticOnNhd_hillHminusOffGapPrimitive n r K q (l : ℂ) (u : ℂ) U hS).continuousOn.mono
      (fun w hw => ⟨hw.1,not_mem_real_segment_of_im_ne_zero l u w (hne w hw)⟩)
  have hsq (w : ℂ) (hw : w ∈ D) : G w^2 = F w^2 :=
    (hillHminusOffGapPrimitive_sq n r hr K q (l : ℂ) (u : ℂ) hpair w
      (not_mem_real_segment_of_im_ne_zero l u w (hne w hw)) (hf w hw.1)).trans
      (hmatch w hw.1 (hne w hw))
  let m : ℝ := (l+u)/2
  have hm : (m : ℂ) ∈ U := hpair.real_gap_mem_ball m (by dsimp [m]; constructor <;> linarith)
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_ball.mem_nhds hm)
  let y : ℝ := e/2
  have hy : 0 < y := half_pos he
  let a : ℂ := (m : ℂ)+(s*y : ℝ)*I
  have haU : a ∈ U := by
    apply hball
    have habs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
    simpa [a,dist_eq_norm,abs_mul,habs,abs_of_pos he,y] using half_lt_self he
  have haD : a ∈ D := by
    refine ⟨haU,?_⟩
    have hs2 : s^2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    change 0 < s*((m : ℂ)+(s*y : ℝ)*I).im
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,add_zero]
    nlinarith [hs2]
  have hGa : 0 < s*(G a).re := hillHminusOffGapPrimitive_midpoint_sign n r K q l u s y hs hy
    (hnorm a haU)
  have hbase : G a = F a := by
    rcases eq_or_eq_neg_of_sq_eq_sq (G a) (F a) (hsq a haD) with heq | heq
    · exact heq
    · have hh := hsign a haD
      rw [heq,neg_re] at hGa
      nlinarith
  have hFnz {w : ℂ} (hw : w ∈ D) : F w ≠ 0 := by
    intro heq
    have hh := hsign w hw
    rw [heq,zero_re,mul_zero] at hh
    exact lt_irrefl _ hh
  exact hD.isPreconnected.eq_of_sq_eq hG hF hsq hFnz haD hbase ⟨hz,hside⟩

end NLS.KdV
