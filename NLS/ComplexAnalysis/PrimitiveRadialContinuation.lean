import NLS.ComplexAnalysis.AnnularHolomorphicPrimitive
import NLS.ComplexAnalysis.RadialSegmentGeometry

/-!
# Continuing a primitive inward along radial connectors

A primitive on an outer open region extends to an open holomorphic
domain when each point has an outward radial anchor there. A convex
neighborhood of each compact connector supplies a local primitive.
Joining anchors within the outer region proves that the value does
not depend on the anchor. The same local primitive comparison proves
holomorphy of the extension, without differentiating the chosen anchor.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem contDiffOn_segment_extend (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend (Icc 0 1) := by
  have hline : ContDiff ℝ 1 (fun t : ℝ => AffineMap.lineMap a b t) := by
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  exact hline.contDiffOn.congr (Path.eqOn_extend_segment a b)

theorem curveIntegral_segment_eq_sub_of_primitive
    (f F : ℂ → ℂ) (U : Set ℂ) (hf : ContinuousOn f U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z) (a b : ℂ)
    (hseg : segment ℝ a b ⊆ U) :
    (∫ᶜ z in Path.segment a b, holomorphicOneForm f z) = F b-F a := by
  have hrange : ∀ t : I, Path.segment a b t ∈ U :=
    fun t => hseg (lineMap_mem_segment ℝ a b t.property)
  have hω : ContinuousOn (holomorphicOneForm f) U := hf.smul continuousOn_const
  have hint := hω.curveIntegrable_of_contDiffOn (contDiffOn_segment_extend a b) hrange
  exact curveIntegral_eq_sub_of_primitive f F U hF _ (contDiffOn_segment_extend a b)
    (fun t ht => by simpa only [Path.extend_apply _ ht] using hrange ⟨t,ht⟩) hint

theorem exists_convex_open_neighborhood_of_segment
    (a b : ℂ) (Ω : Set ℂ) (hΩ : IsOpen Ω) (hseg : segment ℝ a b ⊆ Ω) :
    ∃ U : Set ℂ, IsOpen U ∧ Convex ℝ U ∧ segment ℝ a b ⊆ U ∧ U ⊆ Ω := by
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨ε,hε,hsub⟩ := hcompact.exists_thickening_subset_open hΩ hseg
  exact ⟨thickening ε (segment ℝ a b),isOpen_thickening,
    (convex_segment a b).thickening ε,self_subset_thickening hε _,hsub⟩

def radialPrimitiveValue (f G : ℂ → ℂ) (c z : ℂ) (t : ℝ) : ℂ :=
  G (radialPoint c z t) - ∫ᶜ w in Path.segment z (radialPoint c z t), holomorphicOneForm f w

/-- Independence of two outward anchors follows from local convex
primitives and the existing primitive on their joining segment. -/
theorem radialPrimitiveValue_eq_of_anchors
    (f G : ℂ → ℂ) (c z : ℂ) (Ω A : Set ℂ) (hΩ : IsOpen Ω)
    (hf : AnalyticOnNhd ℂ f Ω) (hAΩ : A ⊆ Ω)
    (hG : ∀ w ∈ A, HasDerivAt G (f w) w)
    (hsegments : ∀ v : ℝ, 1 ≤ v → radialPoint c z v ∈ A →
      segment ℝ z (radialPoint c z v) ⊆ Ω)
    (hjoins : ∀ v u : ℝ, 1 ≤ v → 1 ≤ u → radialPoint c z v ∈ A → radialPoint c z u ∈ A →
      segment ℝ (radialPoint c z v) (radialPoint c z u) ⊆ A)
    (t u : ℝ) (ht : 1 < t) (hu : 1 < u)
    (hat : radialPoint c z t ∈ A) (hau : radialPoint c z u ∈ A) :
    radialPrimitiveValue f G c z t = radialPrimitiveValue f G c z u := by
  have hordered (a b : ℝ) (ha : 1 < a) (hb : 1 < b) (hab : a ≤ b)
      (hpa : radialPoint c z a ∈ A) (hpb : radialPoint c z b ∈ A) :
      radialPrimitiveValue f G c z a = radialPrimitiveValue f G c z b := by
    obtain ⟨U,hU,hconv,hseg,hUΩ⟩ := exists_convex_open_neighborhood_of_segment
      z (radialPoint c z b) Ω hΩ (hsegments b hb.le hpb)
    obtain ⟨H,hH⟩ := exists_primitive_on_convex f U hconv hU (hf.mono hUΩ).differentiableOn
    have hzU := hseg (left_mem_segment ℝ _ _)
    have haU := hseg (radialPoint_mem_segment c z a b ha.le hab hb)
    have hbU := hseg (right_mem_segment ℝ _ _)
    have hshort := hconv.segment_subset hzU haU
    have hjoinU := hconv.segment_subset haU hbU
    have hjoinA := hjoins a b ha.le hb.le hpa hpb
    have hIa := curveIntegral_segment_eq_sub_of_primitive f H U (hf.continuousOn.mono hUΩ)
      hH z (radialPoint c z a) hshort
    have hIb := curveIntegral_segment_eq_sub_of_primitive f H U (hf.continuousOn.mono hUΩ)
      hH z (radialPoint c z b) hseg
    have hIG := curveIntegral_segment_eq_sub_of_primitive f G A (hf.continuousOn.mono hAΩ)
      hG (radialPoint c z a) (radialPoint c z b) hjoinA
    have hIH := curveIntegral_segment_eq_sub_of_primitive f H U (hf.continuousOn.mono hUΩ)
      hH (radialPoint c z a) (radialPoint c z b) hjoinU
    have heq := hIG.symm.trans hIH
    unfold radialPrimitiveValue
    rw [hIa,hIb]
    linear_combination -heq
  rcases le_total t u with htu | hut
  · exact hordered t u ht hu htu hat hau
  · exact (hordered u t hu ht hut hau hat).symm

private theorem primitive_difference_eq_on_ball
    (f G H : ℂ → ℂ) (a : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hG : ∀ w ∈ ball a ε, HasDerivAt G (f w) w)
    (hH : ∀ w ∈ ball a ε, HasDerivAt H (f w) w)
    (w : ℂ) (hw : w ∈ ball a ε) : G w-H w = G a-H a := by
  have hd : ∀ q ∈ ball a ε, HasDerivAt (fun x => G x-H x) 0 q := by
    intro q hq
    convert (hG q hq).sub (hH q hq) using 1 <;> first | rfl | simp only [sub_self]
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q hq => (hd q hq).hasDerivWithinAt)
    (fun _ _ => le_of_eq (norm_zero : ‖(0:ℂ)‖ = 0)) (convex_ball a ε) (mem_ball_self hε) hw
  have hzero : (G w-H w)-(G a-H a) = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _))
  exact sub_eq_zero.mp hzero

/-- A holomorphic primitive on an outer radial region extends to the
whole domain, retaining its values on the original region. -/
theorem exists_primitive_of_outward_radial_anchors
    (f G : ℂ → ℂ) (c : ℂ) (Ω A : Set ℂ) (hΩ : IsOpen Ω) (hA : IsOpen A)
    (hf : AnalyticOnNhd ℂ f Ω) (hAΩ : A ⊆ Ω)
    (hG : ∀ w ∈ A, HasDerivAt G (f w) w)
    (hanchors : ∀ z ∈ Ω, ∃ t : ℝ, 1 < t ∧ radialPoint c z t ∈ A)
    (hsegments : ∀ z ∈ Ω, ∀ v : ℝ, 1 ≤ v → radialPoint c z v ∈ A →
      segment ℝ z (radialPoint c z v) ⊆ Ω)
    (hjoins : ∀ z ∈ Ω, ∀ v u : ℝ, 1 ≤ v → 1 ≤ u → radialPoint c z v ∈ A → radialPoint c z u ∈ A →
      segment ℝ (radialPoint c z v) (radialPoint c z u) ⊆ A) :
    ∃ F : ℂ → ℂ, EqOn F G A ∧ ∀ z ∈ Ω, HasDerivAt F (f z) z := by
  classical
  let T : ℂ → ℝ := fun z => if hz : z ∈ Ω then Classical.choose (hanchors z hz) else 1
  have hT (z : ℂ) (hz : z ∈ Ω) : 1 < T z ∧ radialPoint c z (T z) ∈ A := by
    simpa only [T,dif_pos hz] using Classical.choose_spec (hanchors z hz)
  let F : ℂ → ℂ := fun z => radialPrimitiveValue f G c z (T z)
  refine ⟨F,?_,?_⟩
  · intro z hzA
    have hzΩ := hAΩ hzA
    have ht := hT z hzΩ
    have hsegA : segment ℝ z (radialPoint c z (T z)) ⊆ A := by
      simpa only [radialPoint_one] using hjoins z hzΩ 1 (T z) le_rfl ht.1.le
        (by simpa only [radialPoint_one] using hzA) ht.2
    change radialPrimitiveValue f G c z (T z) = G z
    unfold radialPrimitiveValue
    rw [curveIntegral_segment_eq_sub_of_primitive f G A (hf.continuousOn.mono hAΩ) hG
      z (radialPoint c z (T z)) hsegA]
    ring
  · intro z hzΩ
    let t := T z
    let a := radialPoint c z t
    have ht : 1 < t := (hT z hzΩ).1
    have haA : a ∈ A := (hT z hzΩ).2
    obtain ⟨U,hU,hconv,hseg,hUΩ⟩ := exists_convex_open_neighborhood_of_segment z a Ω hΩ
      (hsegments z hzΩ t ht.le haA)
    obtain ⟨H,hH⟩ := exists_primitive_on_convex f U hconv hU (hf.mono hUΩ).differentiableOn
    have hzU := hseg (left_mem_segment ℝ _ _)
    have haU := hseg (right_mem_segment ℝ _ _)
    obtain ⟨ε,hε,hB⟩ := Metric.isOpen_iff.mp (hA.inter hU) a ⟨haA,haU⟩
    let V : Set ℂ := U ∩ (fun w => radialPoint c w t) ⁻¹' ball a ε
    have hpoint : Continuous (fun w : ℂ => radialPoint c w t) := by unfold radialPoint; fun_prop
    have hV : IsOpen V := hU.inter (isOpen_ball.preimage hpoint)
    have hzV : z ∈ V := ⟨hzU,mem_ball_self hε⟩
    have hEq : F =ᶠ[𝓝 z] (fun w => H w+(G a-H a)) := by
      filter_upwards [hV.mem_nhds hzV] with w hw
      have hwΩ := hUΩ hw.1
      have hpa := hB hw.2
      have hvalue := radialPrimitiveValue_eq_of_anchors f G c w Ω A hΩ hf hAΩ hG
        (hsegments w hwΩ) (hjoins w hwΩ) (T w) t (hT w hwΩ).1 ht (hT w hwΩ).2 hpa.1
      have hInt := curveIntegral_segment_eq_sub_of_primitive f H U (hf.continuousOn.mono hUΩ)
        hH w (radialPoint c w t) (hconv.segment_subset hw.1 hpa.2)
      have hdiff := primitive_difference_eq_on_ball f G H a ε hε
        (fun q hq => hG q (hB hq).1) (fun q hq => hH q (hB hq).2)
        (radialPoint c w t) hw.2
      change radialPrimitiveValue f G c w (T w) = H w+(G a-H a)
      rw [hvalue,radialPrimitiveValue,hInt]
      linear_combination hdiff
    exact ((hH z hzU).add_const (G a-H a)).congr_of_eventuallyEq hEq

end NLS.ComplexAnalysis
