import NLS.ComplexAnalysis.CosineRootCoefficient
import NLS.ComplexAnalysis.PrimitiveRadialContinuation

/-!
# Normalized cosine charts and equal endpoint values of a gap primitive

In a cosine coordinate the selected square root cancels, leaving a
constant sheet coefficient times an analytic numerator. An analytic
primitive of that numerator exists across the real angle interval. The
normalized pullback formula is exposed for continuation onto local sheets.
The upper and lower angle charts have opposite coefficients. Their
endpoint differences must therefore be both equal and opposite.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

private theorem tendsto_signed_angle_ray
    (U : Set ℂ) (hU : IsOpen U) (e : ℂ) (he : e ∈ U) (hei : e.im = 0)
    (σ : ℝ) (hσ : σ^2 = 1) :
    Tendsto (fun y : ℝ => e+((σ*y:ℝ):ℂ)*I) (𝓝[>] (0:ℝ))
      (𝓝[U ∩ {θ : ℂ | 0 < σ*θ.im}] e) := by
  have hlim : Tendsto (fun y : ℝ => e+((σ*y:ℝ):ℂ)*I)
      (𝓝[>] (0:ℝ)) (𝓝 e) := by
    have hc : ContinuousAt (fun y : ℝ => e+((σ*y:ℝ):ℂ)*I) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim,?_⟩
  filter_upwards [hlim.eventually (hU.mem_nhds he),self_mem_nhdsWithin] with y hy hp
  refine ⟨hy,?_⟩
  change 0 < σ*(e+((σ*y:ℝ):ℂ)*I).im
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,hei]
  rw [add_zero,← mul_assoc,← pow_two,hσ,one_mul]
  exact hp

/-- A normalized spectral primitive pulls back to one analytic angle
primitive, multiplied by the corresponding constant sheet coefficient.
Only the boundary value at the left endpoint is needed. -/
theorem exists_cosine_gap_primitive_chart
    (g Q F : ℂ → ℂ) (Ω : Set ℂ) (τ δ A : ℂ)
    (hΩ : IsOpen Ω) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A)) :
    ∃ U : Set ℂ, ∃ H : ℂ → ℂ,
      IsOpen U ∧ Convex ℝ U ∧ segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ U ∧
      U ⊆ (cosineGapPoint τ δ) ⁻¹' Ω ∧
      (∀ θ ∈ U, HasDerivAt H (g (cosineGapPoint τ δ θ)) θ) ∧
      ∀ θ ∈ U, θ.im ≠ 0 → F (cosineGapPoint τ δ θ)-A =
        cosineRootCoefficient Q τ δ θ*(H θ-H (Real.pi:ℂ)) := by
  let T := cosineGapPoint τ δ
  let D := Ω \ segment ℝ (τ-δ) (τ+δ)
  have hTcont : Continuous T := by
    change Continuous (fun θ : ℂ => τ+δ*Complex.cos θ)
    fun_prop
  have hangle : segment ℝ (0:ℂ) (Real.pi:ℂ) ⊆ T ⁻¹' Ω := by
    intro θ hθ
    obtain ⟨t,ht,rfl⟩ := by rw [segment_eq_image_lineMap] at hθ; exact hθ
    have heq : AffineMap.lineMap (0:ℂ) (Real.pi:ℂ) t = (t*Real.pi:ℝ) := by
      simp [AffineMap.lineMap_apply_module,Complex.real_smul]
    rw [heq]
    exact hgap (cosineGapPoint_real_mem_segment τ δ (t*Real.pi))
  obtain ⟨U,hU,hconv,hsegU,hUT⟩ := exists_convex_open_neighborhood_of_segment
    (0:ℂ) (Real.pi:ℂ) (T ⁻¹' Ω) (hΩ.preimage hTcont) hangle
  have h0U : (0:ℂ) ∈ U := hsegU (left_mem_segment ℝ _ _)
  have hπU : (Real.pi:ℂ) ∈ U := hsegU (right_mem_segment ℝ _ _)
  have hh : AnalyticOnNhd ℂ (fun θ => g (T θ)) U := by
    intro θ hθ
    exact (hg (T θ) (hUT hθ)).comp (x := θ)
      (analyticAt_const.add (analyticAt_const.mul Complex.analyticAt_cos))
  obtain ⟨H,hH⟩ := exists_primitive_on_convex (fun θ => g (T θ)) U hconv hU hh.differentiableOn
  have hside (σ : ℝ) (hσ : σ^2 = 1) (a : ℂ)
      (ha : a ∈ U ∩ {θ : ℂ | 0 < σ*θ.im}) :
      F (T a)-A = cosineRootCoefficient Q τ δ a*(H a-H (Real.pi:ℂ)) := by
    let S := U ∩ {θ : ℂ | 0 < σ*θ.im}
    let C := cosineRootCoefficient Q τ δ a
    have hSconv : Convex ℝ S := hconv.inter (convex_halfSpace_gt
      (show IsLinearMap ℝ (fun θ : ℂ => σ*θ.im) from ⟨by
        intro x z; simp [Complex.add_im,mul_add],by
        intro t θ; simp [smul_eq_mul]; ring⟩) 0)
    have hθne (θ : ℂ) (hθ : θ ∈ S) : θ.im ≠ 0 := by
      intro h
      have hpos := hθ.2
      change 0 < σ*θ.im at hpos
      rw [h,mul_zero] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hTD (θ : ℂ) (hθ : θ ∈ S) : T θ ∈ D :=
      ⟨hUT hθ.1,cosineGapPoint_not_mem_segment τ δ θ hδ (hθne θ hθ)⟩
    have hcoef : ∀ θ ∈ S, cosineRootCoefficient Q τ δ θ = C :=
      cosineRootCoefficient_eq_on_connected Q τ δ S hδ hSconv.isPreconnected hθne
        (hQ.comp hTcont.continuousOn hTD) (fun θ hθ => hsq _ (hTD θ hθ)) a ha
    let J : ℂ → ℂ := fun θ => F (T θ)-C*H θ
    have hJ (θ : ℂ) (hθ : θ ∈ S) : HasDerivAt J 0 θ := by
      have hcomp : HasDerivAt (fun v => F (T v)) (C*g (T θ)) θ := by
        convert (hF _ (hTD θ hθ)).comp θ (hasDerivAt_cosineGapPoint τ δ θ) using 1 <;>
          try rfl
        rw [← hcoef θ hθ]
        dsimp only [cosineRootCoefficient,T]
        ring
      convert hcomp.sub ((hH θ hθ.1).const_mul C) using 1 <;> first | rfl | ring
    have hconstant (θ : ℂ) (hθ : θ ∈ S) : J θ = J a := by
      have hb := hSconv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun q hq => (hJ q hq).hasDerivWithinAt)
        (fun q _ => (by simp : ‖(0:ℂ)‖ ≤ (0:ℝ))) ha hθ
      have hn : ‖J θ-J a‖ = 0 := le_antisymm (by simpa using hb) (norm_nonneg _)
      exact sub_eq_zero.mp (norm_eq_zero.mp hn)
    have hlimit (e E : ℂ) (he : e ∈ U) (hei : e.im = 0)
        (hE : Tendsto F (𝓝[D] (T e)) (𝓝 E)) : E-C*H e = J a := by
      let : NeBot (𝓝[S] e) := (tendsto_signed_angle_ray U hU e he hei σ hσ).neBot
      have hmap : Tendsto T (𝓝[S] e) (𝓝[D] (T e)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨hTcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
        filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact hTD θ hθ
      have hHlim : Tendsto H (𝓝[S] e) (𝓝 (H e)) :=
        (hH e he).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hJlim : Tendsto J (𝓝[S] e) (𝓝 (E-C*H e)) :=
        (hE.comp hmap).sub (tendsto_const_nhds.mul hHlim)
      have hJconst : Tendsto J (𝓝[S] e) (𝓝 (J a)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [self_mem_nhdsWithin] with θ hθ
        exact (hconstant θ hθ).symm
      exact tendsto_nhds_unique hJlim hJconst
    have hleft := hlimit (Real.pi:ℂ) A hπU (by simp) (by
      simpa [D,T,cosineGapPoint,sub_eq_add_neg] using hA)
    dsimp only [J,C] at hleft
    linear_combination -hleft
  refine ⟨U,H,hU,hconv,hsegU,hUT,hH,?_⟩
  intro θ hθ hi
  rcases lt_or_gt_of_ne hi with hn | hp
  · exact hside (-1) (by norm_num) θ ⟨hθ,by simpa using neg_pos.mpr hn⟩
  · exact hside 1 (by norm_num) θ ⟨hθ,by simpa using hp⟩

/-- A single-valued primitive of an analytic numerator divided by a
continuous square root of the endpoint polynomial has equal relative
values at the two endpoints of a noncollapsed complex gap. -/
theorem primitive_cosine_gap_boundary_values_eq
    (g Q F : ℂ → ℂ) (Ω : Set ℂ) (τ δ A B : ℂ)
    (hΩ : IsOpen Ω) (hδ : δ ≠ 0)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ Ω)
    (hg : AnalyticOnNhd ℂ g Ω)
    (hQ : ContinuousOn Q (Ω \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hF : ∀ z ∈ Ω \ segment ℝ (τ-δ) (τ+δ), HasDerivAt F (g z/Q z) z)
    (hA : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ-δ)) (𝓝 A))
    (hB : Tendsto F (𝓝[Ω \ segment ℝ (τ-δ) (τ+δ)] (τ+δ)) (𝓝 B)) : A = B := by
  obtain ⟨U,H,hU,hconv,hsegU,hUT,hH,hchart⟩ := exists_cosine_gap_primitive_chart
    g Q F Ω τ δ A hΩ hδ hgap hg hQ hsq hF hA
  let T := cosineGapPoint τ δ
  let D := Ω \ segment ℝ (τ-δ) (τ+δ)
  have hTcont : Continuous T := by
    change Continuous (fun θ : ℂ => τ+δ*Complex.cos θ)
    fun_prop
  have h0U : (0:ℂ) ∈ U := hsegU (left_mem_segment ℝ _ _)
  obtain ⟨η,hη,hball⟩ := Metric.isOpen_iff.mp hU 0 h0U
  let y := η/2
  have hy : 0 < y := by dsimp [y]; linarith
  let p : ℂ := (y:ℂ)*I
  have hp : p ∈ U := hball (by
    simp only [mem_ball,dist_eq_norm,sub_zero,p,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,norm_I,mul_one,abs_of_pos hy]
    dsimp [y]; linarith)
  have hnp : -p ∈ U := hball (by
    simp only [mem_ball,dist_eq_norm,sub_zero,norm_neg,p,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,norm_I,mul_one,abs_of_pos hy]
    dsimp [y]; linarith)
  have hside (σ : ℝ) (hσ : σ^2 = 1) (a : ℂ)
      (ha : a ∈ U ∩ {θ : ℂ | 0 < σ*θ.im}) :
      B-A = cosineRootCoefficient Q τ δ a*(H 0-H (Real.pi:ℂ)) := by
    let S := U ∩ {θ : ℂ | 0 < σ*θ.im}
    have hSconv : Convex ℝ S := hconv.inter (convex_halfSpace_gt
      (show IsLinearMap ℝ (fun θ : ℂ => σ*θ.im) from ⟨by
        intro x z; simp [Complex.add_im,mul_add],by
        intro t θ; simp [smul_eq_mul]; ring⟩) 0)
    have hθne (θ : ℂ) (hθ : θ ∈ S) : θ.im ≠ 0 := by
      intro h
      have hpos := hθ.2
      change 0 < σ*θ.im at hpos
      rw [h,mul_zero] at hpos
      exact (lt_irrefl 0 hpos).elim
    have hTD (θ : ℂ) (hθ : θ ∈ S) : T θ ∈ D :=
      ⟨hUT hθ.1,cosineGapPoint_not_mem_segment τ δ θ hδ (hθne θ hθ)⟩
    have hcoef := cosineRootCoefficient_eq_on_connected Q τ δ S hδ hSconv.isPreconnected hθne
      (hQ.comp hTcont.continuousOn hTD) (fun θ hθ => hsq _ (hTD θ hθ)) a ha
    let : NeBot (𝓝[S] (0:ℂ)) :=
      (tendsto_signed_angle_ray U hU 0 h0U (by simp) σ hσ).neBot
    have hmap : Tendsto T (𝓝[S] (0:ℂ)) (𝓝[D] (τ+δ)) := by
      have ht : T 0 = τ+δ := by simp [T,cosineGapPoint]
      rw [← ht]
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hTcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact hTD θ hθ
    have hleft : Tendsto (fun θ => F (T θ)-A) (𝓝[S] (0:ℂ)) (𝓝 (B-A)) :=
      (hB.comp hmap).sub tendsto_const_nhds
    have hright : Tendsto (fun θ => cosineRootCoefficient Q τ δ a*(H θ-H (Real.pi:ℂ)))
        (𝓝[S] (0:ℂ)) (𝓝 (cosineRootCoefficient Q τ δ a*(H 0-H (Real.pi:ℂ)))) :=
      tendsto_const_nhds.mul
        (((hH 0 h0U).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds)
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [hchart θ hθ.1 (hθne θ hθ),hcoef θ hθ]
  have hup := hside 1 (by norm_num) p ⟨hp,by simpa [p] using hy⟩
  have hdown := hside (-1) (by norm_num) (-p) ⟨hnp,by simpa [p] using hy⟩
  rw [cosineRootCoefficient_neg] at hdown
  have hzero : B-A = 0 := by linear_combination (hup+hdown)/2
  exact (sub_eq_zero.mp hzero).symm

end NLS.ComplexAnalysis
