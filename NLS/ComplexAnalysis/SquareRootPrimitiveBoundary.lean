import NLS.ComplexAnalysis.IntegrableDerivativeBoundary
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundary continuity of primitives with square-root derivative growth

A primitive in the upper or lower half-plane extends continuously to
a real boundary point when its derivative grows no faster than the
inverse square root of the distance to that point. The comparison
uses three short segments lifted to a height comparable to the
distance from the boundary point.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

private theorem primitive_segment_bound
    (f F : ℂ → ℂ) (a b : ℂ) (C : ℝ)
    (hF : ∀ z ∈ segment ℝ a b, HasDerivAt F (f z) z)
    (hbound : ∀ z ∈ segment ℝ a b, ‖f z‖ ≤ C) :
    ‖F b - F a‖ ≤ C * ‖b-a‖ :=
  (convex_segment a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hF z hz).hasDerivWithinAt) hbound
    (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)

private theorem lineMap_re (a b : ℂ) (t : ℝ) :
    (AffineMap.lineMap a b t).re = (1-t)*a.re+t*b.re := by
  simp only [AffineMap.lineMap_apply_module, Complex.add_re,
    Complex.smul_re, smul_eq_mul]

private theorem lineMap_im (a b : ℂ) (t : ℝ) :
    (AffineMap.lineMap a b t).im = (1-t)*a.im+t*b.im := by
  simp only [AffineMap.lineMap_apply_module, Complex.add_im,
    Complex.smul_im, smul_eq_mul]

private theorem norm_ge_of_same_re_im_ge
    (c z w : ℂ) (hc : c.im = 0)
    (hre : z.re = w.re) (hzi : 0 ≤ z.im) (hi : z.im ≤ w.im) :
    ‖z-c‖ ≤ ‖w-c‖ := by
  have hs : ‖z-c‖ ^ 2 ≤ ‖w-c‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, hc, sub_zero, hre]
    nlinarith
  nlinarith [norm_nonneg (z-c), norm_nonneg (w-c)]

/-- Three short segments connect an upper-half-plane point to the
vertical ray at its distance from a real boundary point. Every point
on them remains in an annulus of comparable radius. -/
private theorem upper_lift_segments
    (c z : ℂ) (hc : c.im = 0) (hz : 0 < z.im) :
    let ρ := ‖z-c‖
    let w := z + (ρ:ℂ)*I
    let v := c + ((z.im+ρ:ℝ):ℂ)*I
    let a := c + (ρ:ℂ)*I
    0 < ρ ∧
      (∀ q ∈ (segment ℝ z w ∪ segment ℝ w v ∪ segment ℝ v a),
        0 < q.im ∧ ρ ≤ ‖q-c‖ ∧ ‖q-c‖ ≤ 2*ρ) ∧
      ‖w-z‖ ≤ ρ ∧ ‖v-w‖ ≤ ρ ∧ ‖a-v‖ ≤ ρ := by
  dsimp only
  let ρ := ‖z-c‖
  let w := z + (ρ:ℂ)*I
  let v := c + ((z.im+ρ:ℝ):ℂ)*I
  let a := c + (ρ:ℂ)*I
  have hρ : 0 < ρ := by
    have hne : z ≠ c := by
      intro h
      rw [h] at hz
      rw [hc] at hz
      exact (lt_irrefl 0 hz).elim
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hyρ : z.im ≤ ρ := by
    have h := Complex.im_le_norm (z-c)
    simpa only [Complex.sub_im, hc, sub_zero, ρ] using h
  have hwre : w.re = z.re := by simp [w]
  have hwim : w.im = z.im+ρ := by simp [w]
  have hvim : v.im = z.im+ρ := by simp [v,hc]
  have haim : a.im = ρ := by simp [a,hc]
  have hzball : z ∈ Metric.closedBall c (2*ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖z-c‖ ≤ 2*ρ
    dsimp [ρ]
    linarith
  have hwball : w ∈ Metric.closedBall c (2*ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    calc
      ‖w-c‖ = ‖(z-c)+(ρ:ℂ)*I‖ := by congr 1; dsimp [w]; ring
      _ ≤ ‖z-c‖ + ‖(ρ:ℂ)*I‖ := norm_add_le _ _
      _ = 2*ρ := by simp [ρ]; ring
  have hvball : v ∈ Metric.closedBall c (2*ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hvnorm : ‖v-c‖ = z.im+ρ := by
      dsimp [v]
      rw [add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real]
      exact abs_of_pos (by linarith)
    rw [hvnorm]
    linarith
  have haball : a ∈ Metric.closedBall c (2*ρ) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hanorm : ‖a-c‖ = ρ := by
      dsimp [a]
      rw [add_sub_cancel_left, norm_mul, norm_I, mul_one, Complex.norm_real]
      exact abs_of_pos hρ
    rw [hanorm]
    linarith
  have hball (e d : ℂ) (he : e ∈ Metric.closedBall c (2*ρ))
      (hd : d ∈ Metric.closedBall c (2*ρ))
      (q : ℂ) (hq : q ∈ segment ℝ e d) : ‖q-c‖ ≤ 2*ρ := by
    have hqball := (convex_closedBall c (2*ρ)).segment_subset he hd hq
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hqball
  have hfirst (q : ℂ) (hq : q ∈ segment ℝ z w) :
      0 < q.im ∧ ρ ≤ ‖q-c‖ ∧ ‖q-c‖ ≤ 2*ρ := by
    obtain ⟨t,ht,rfl⟩ := by
      rw [segment_eq_image_lineMap] at hq
      exact hq
    have htre : (AffineMap.lineMap z w t).re = z.re := by
      rw [lineMap_re, hwre]
      ring
    have htim : z.im ≤ (AffineMap.lineMap z w t).im := by
      rw [lineMap_im, hwim]
      nlinarith [mul_nonneg ht.1 hρ.le]
    refine ⟨lt_of_lt_of_le hz htim,?_,hball z w hzball hwball _
      (lineMap_mem_segment ℝ z w ht)⟩
    exact norm_ge_of_same_re_im_ge c z _ hc htre.symm hz.le htim
  have hsecond (q : ℂ) (hq : q ∈ segment ℝ w v) :
      0 < q.im ∧ ρ ≤ ‖q-c‖ ∧ ‖q-c‖ ≤ 2*ρ := by
    obtain ⟨t,ht,rfl⟩ := by
      rw [segment_eq_image_lineMap] at hq
      exact hq
    have hqim : (AffineMap.lineMap w v t).im = z.im+ρ := by
      rw [lineMap_im,hwim,hvim]
      ring
    have hlow : ρ ≤ ‖AffineMap.lineMap w v t-c‖ := by
      have h := Complex.im_le_norm (AffineMap.lineMap w v t-c)
      rw [Complex.sub_im,hc,sub_zero,hqim] at h
      linarith
    exact ⟨by rw [hqim]; linarith,hlow,
      hball w v hwball hvball _ (lineMap_mem_segment ℝ w v ht)⟩
  have hthird (q : ℂ) (hq : q ∈ segment ℝ v a) :
      0 < q.im ∧ ρ ≤ ‖q-c‖ ∧ ‖q-c‖ ≤ 2*ρ := by
    obtain ⟨t,ht,rfl⟩ := by
      rw [segment_eq_image_lineMap] at hq
      exact hq
    have hqim : ρ ≤ (AffineMap.lineMap v a t).im := by
      rw [lineMap_im,hvim,haim]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hz.le]
    have hlow : ρ ≤ ‖AffineMap.lineMap v a t-c‖ := by
      have h := Complex.im_le_norm (AffineMap.lineMap v a t-c)
      rw [Complex.sub_im,hc,sub_zero] at h
      linarith
    exact ⟨lt_of_lt_of_le hρ hqim,hlow,
      hball v a hvball haball _ (lineMap_mem_segment ℝ v a ht)⟩
  refine ⟨hρ,?_,?_,?_,?_⟩
  · intro q hq
    rcases hq with (hq|hq)|hq
    · exact hfirst q hq
    · exact hsecond q hq
    · exact hthird q hq
  · simp
  ·
    have heq : c + ((z.im+ρ:ℝ):ℂ)*I - (z+(ρ:ℂ)*I) =
        ((c.re-z.re:ℝ):ℂ) := by
      apply Complex.ext
      · simp
      · simp [hc]
    rw [heq, Complex.norm_real]
    have h := Complex.abs_re_le_norm (z-c)
    simpa [Complex.sub_re,abs_sub_comm,ρ] using h
  ·
    have heq : c+(ρ:ℂ)*I - (c+((z.im+ρ:ℝ):ℂ)*I) =
        ((-z.im:ℝ):ℂ)*I := by
      push_cast
      ring
    rw [heq,norm_mul,norm_I,mul_one,Complex.norm_real]
    simpa [Real.norm_eq_abs,abs_of_pos hz] using hyρ

/-- A primitive whose derivative has inverse-square-root growth at a
real boundary point has a full upper-half-plane boundary limit once
it has a limit along the vertical ray. -/
theorem tendsto_primitive_upper_of_sqrt_bound
    (f F : ℂ → ℂ) (c A : ℂ) (δ M ε : ℝ)
    (hc : c.im = 0) (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (f z) z)
    (hbound : ∀ z : ℂ, 0 < z.im →
      0 < ‖z-c‖ → ‖z-c‖ ≤ ε →
      ‖f z * ((Real.sqrt (δ*‖z-c‖) : ℝ) : ℂ)‖ ≤ M)
    (hray : Tendsto (fun y : ℝ => F (c+(y:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 A)) :
    Tendsto F (𝓝[{z : ℂ | 0 < z.im}] c) (𝓝 A) := by
  let U : Set ℂ := {z | 0 < z.im}
  let ρ : ℂ → ℝ := fun z => ‖z-c‖
  have hρlim : Tendsto ρ (𝓝[U] c) (𝓝 (0:ℝ)) := by
    have hcont : ContinuousAt ρ c := by fun_prop
    simpa only [ρ,sub_self,norm_zero] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hρpos : ∀ᶠ z in 𝓝[U] c, 0 < ρ z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hne : z ≠ c := by
      intro h
      subst z
      change 0 < c.im at hz
      rw [hc] at hz
      exact (lt_irrefl 0 hz).elim
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hρray : Tendsto ρ (𝓝[U] c) (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hρlim,hρpos⟩
  have hanchor : Tendsto (fun z : ℂ => F (c+((ρ z:ℝ):ℂ)*I))
      (𝓝[U] c) (𝓝 A) := by
    simpa only [Function.comp_def] using hray.comp hρray
  have hnear : ∀ᶠ z in 𝓝[U] c, 2*ρ z ≤ ε := by
    have hsmall : ∀ᶠ v in 𝓝 (0:ℝ), v < ε/2 := Iio_mem_nhds (by linarith)
    filter_upwards [hρlim.eventually hsmall] with z hz
    linarith
  have hdist (z : ℂ) (hz : 0 < z.im) (hzρ : 0 < ρ z)
      (hεz : 2*ρ z ≤ ε) :
      ‖F z - F (c+((ρ z:ℝ):ℂ)*I)‖ ≤
        3 * (M / Real.sqrt δ) * Real.sqrt (ρ z) := by
    let r := ρ z
    let w := z + (r:ℂ)*I
    let v := c + ((z.im+r:ℝ):ℂ)*I
    let a := c + (r:ℂ)*I
    obtain ⟨hr,hgood,hlen₁,hlen₂,hlen₃⟩ := upper_lift_segments c z hc hz
    let B := M / Real.sqrt (δ*r)
    have hδr : 0 < Real.sqrt (δ*r) := Real.sqrt_pos.2 (mul_pos hδ hr)
    have hpoint (q : ℂ)
        (hq : q ∈ segment ℝ z w ∪ segment ℝ w v ∪ segment ℝ v a) :
        ‖f q‖ ≤ B := by
      obtain ⟨hqu,hqr, hqR⟩ := hgood q hq
      have hqpos : 0 < ‖q-c‖ := lt_of_lt_of_le hr hqr
      have hqbound := hbound q hqu hqpos (hqR.trans hεz)
      have hweight : Real.sqrt (δ*r) ≤ Real.sqrt (δ*‖q-c‖) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hqr hδ.le)
      have hw : ‖f q‖ * Real.sqrt (δ*‖q-c‖) ≤ M := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)] using hqbound
      have hsmall : ‖f q‖ * Real.sqrt (δ*r) ≤ M :=
        (mul_le_mul_of_nonneg_left hweight (norm_nonneg _)).trans hw
      exact (le_div_iff₀ hδr).2 hsmall
    have hseg₁ : ‖F w-F z‖ ≤ B*‖w-z‖ :=
      primitive_segment_bound f F z w B
        (fun q hq => hF q (hgood q (Or.inl (Or.inl hq))).1)
        (fun q hq => hpoint q (Or.inl (Or.inl hq)))
    have hseg₂ : ‖F v-F w‖ ≤ B*‖v-w‖ :=
      primitive_segment_bound f F w v B
        (fun q hq => hF q (hgood q (Or.inl (Or.inr hq))).1)
        (fun q hq => hpoint q (Or.inl (Or.inr hq)))
    have hseg₃ : ‖F a-F v‖ ≤ B*‖a-v‖ :=
      primitive_segment_bound f F v a B
        (fun q hq => hF q (hgood q (Or.inr hq)).1)
        (fun q hq => hpoint q (Or.inr hq))
    have hB : 0 ≤ B := div_nonneg hM (Real.sqrt_nonneg _)
    have htotal : ‖F z-F a‖ ≤ 3*B*r := by
      calc
        ‖F z-F a‖ = ‖(F w-F z)+(F v-F w)+(F a-F v)‖ := by
          rw [← norm_neg (F z-F a)]
          congr 1
          ring
        _ ≤ (‖F w-F z‖+‖F v-F w‖)+‖F a-F v‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ B*‖w-z‖ + B*‖v-w‖ + B*‖a-v‖ := by
          gcongr
        _ ≤ 3*B*r := by
          have h₁ := mul_le_mul_of_nonneg_left hlen₁ hB
          have h₂ := mul_le_mul_of_nonneg_left hlen₂ hB
          have h₃ := mul_le_mul_of_nonneg_left hlen₃ hB
          linarith
    have hsqrtr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
    have hsqrtd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hBident : B*r = (M / Real.sqrt δ)*Real.sqrt r := by
      dsimp [B]
      rw [Real.sqrt_mul hδ.le]
      calc
        (M / (Real.sqrt δ * Real.sqrt r))*r =
            (M / (Real.sqrt δ * Real.sqrt r))*(Real.sqrt r*Real.sqrt r) := by
              rw [Real.mul_self_sqrt hr.le]
        _ = (M/Real.sqrt δ)*Real.sqrt r := by
              field_simp
    simpa only [a,r,ρ] using htotal.trans_eq (by rw [mul_assoc,hBident]; ring)
  have hdiff : Tendsto
      (fun z : ℂ => F z - F (c+((ρ z:ℝ):ℂ)*I))
      (𝓝[U] c) (𝓝 (0:ℂ)) := by
    have hsqrt : Tendsto (fun z : ℂ => Real.sqrt (ρ z))
        (𝓝[U] c) (𝓝 (0:ℝ)) := by
      simpa only [Function.comp_def,Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0:ℝ)).comp hρlim
    have hmajor : Tendsto (fun z : ℂ =>
        3*(M/Real.sqrt δ)*Real.sqrt (ρ z))
        (𝓝[U] c) (𝓝 (0:ℝ)) := by
      simpa using tendsto_const_nhds.mul hsqrt
    have hnorm : Tendsto (fun z : ℂ =>
        ‖F z - F (c+((ρ z:ℝ):ℂ)*I)‖)
        (𝓝[U] c) (𝓝 (0:ℝ)) := by
      apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hmajor
      filter_upwards [self_mem_nhdsWithin,hρpos,hnear] with z hz hp hn
      exact hdist z hz hp hn
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hnorm)
  have hsum := hdiff.add hanchor
  simpa only [sub_add_cancel,zero_add] using hsum

/-- The lower-half-plane counterpart follows by reflecting the
spectral coordinate through the origin. -/
theorem tendsto_primitive_lower_of_sqrt_bound
    (f F : ℂ → ℂ) (c A : ℂ) (δ M ε : ℝ)
    (hc : c.im = 0) (hδ : 0 < δ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hF : ∀ z : ℂ, z.im < 0 → HasDerivAt F (f z) z)
    (hbound : ∀ z : ℂ, z.im < 0 →
      0 < ‖z-c‖ → ‖z-c‖ ≤ ε →
      ‖f z * ((Real.sqrt (δ*‖z-c‖) : ℝ) : ℂ)‖ ≤ M)
    (hray : Tendsto (fun y : ℝ => F (c+((-y:ℝ):ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 A)) :
    Tendsto F (𝓝[{z : ℂ | z.im < 0}] c) (𝓝 A) := by
  let g : ℂ → ℂ := fun z => -f (-z)
  let G : ℂ → ℂ := fun z => F (-z)
  have hcneg : (-c).im = 0 := by simp [hc]
  have hG (z : ℂ) (hz : 0 < z.im) : HasDerivAt G (g z) z := by
    have hzneg : (-z).im < 0 := by simpa using hz
    have hneg : HasDerivAt (fun w : ℂ => -w) (-1) z := by
      change HasDerivAt (-id : ℂ → ℂ) (-1) z
      exact (hasDerivAt_id z).neg
    simpa only [G,g,Function.comp_def,smul_eq_mul,mul_neg, mul_one] using
      (hF (-z) hzneg).comp z hneg
  have hgBound (z : ℂ) (hz : 0 < z.im)
      (hpos : 0 < ‖z-(-c)‖) (hnear : ‖z-(-c)‖ ≤ ε) :
      ‖g z * ((Real.sqrt (δ*‖z-(-c)‖) : ℝ) : ℂ)‖ ≤ M := by
    have hzneg : (-z).im < 0 := by simpa using hz
    have hdist : ‖(-z)-c‖ = ‖z-(-c)‖ := by
      rw [← norm_neg (z-(-c))]
      congr 1
      ring
    have hb := hbound (-z) hzneg (by rw [hdist]; exact hpos)
      (by rw [hdist]; exact hnear)
    simpa only [g,hdist,neg_mul,norm_neg] using hb
  have hGr : Tendsto (fun y : ℝ => G (-c+(y:ℂ)*I))
      (𝓝[>] (0:ℝ)) (𝓝 A) := by
    convert hray using 1
    funext y
    dsimp [G]
    congr 1
    push_cast
    ring
  have hGU := tendsto_primitive_upper_of_sqrt_bound
    g G (-c) A δ M ε hcneg hδ hM hε hG hgBound hGr
  have hneg : Tendsto (fun z : ℂ => -z)
      (𝓝[{z : ℂ | z.im < 0}] c)
      (𝓝[{z : ℂ | 0 < z.im}] (-c)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun z : ℂ => -z) c := by fun_prop
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  simpa only [G,Function.comp_def,neg_neg] using hGU.comp hneg

end NLS.ComplexAnalysis
