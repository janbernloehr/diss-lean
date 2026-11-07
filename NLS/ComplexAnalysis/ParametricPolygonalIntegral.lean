import NLS.ComplexAnalysis.ParametricConvexPrimitivePathIntegral
import NLS.ComplexAnalysis.CompactSliceLocalProperties

/-! Literal finite polygonal path integrals of a jointly analytic
one-form are analytic on the OPEN source domain where the ENTIRE
chosen path is admissible. This domain depends only on the joint
energy/source domain, before any indexed choice of the one-form. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

omit [NormedSpace ℂ A] in
theorem exists_convex_segment_parameter_chart (D : Set (ℂ × A)) (hD : IsOpen D)
    (a b : ℂ) (q : A) (hsegment : ∀ z ∈ segment ℝ a b, (z,q) ∈ D) :
    ∃ U : Set ℂ, ∃ V : Set A, IsOpen U ∧ Convex ℝ U ∧ a ∈ U ∧ b ∈ U ∧
      IsOpen V ∧ q ∈ V ∧ U ×ˢ V ⊆ D := by
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨S,V,hS,hV,hseg,hq,hsub⟩ := generalized_tube_lemma hcompact isCompact_singleton hD
    (by rintro ⟨z,y⟩ ⟨hz,hy⟩; have : y = q := hy; subst y; exact hsegment z hz)
  obtain ⟨U,hU,hconv,hpath,hUS⟩ := exists_convex_open_neighborhood_of_segment a b S hS hseg
  exact ⟨U,V,hU,hconv,hpath (left_mem_segment ℝ a b),hpath (right_mem_segment ℝ a b),
    hV,hq (mem_singleton q),fun t ht => hsub ⟨hUS ht.1,ht.2⟩⟩

theorem analyticAt_parametric_fixed_segment_integral (F : ℂ × A → ℂ)
    (D : Set (ℂ × A)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (a b : ℂ) (q : A) (hsegment : ∀ z ∈ segment ℝ a b, (z,q) ∈ D) :
    AnalyticAt ℂ (fun y => ∫ᶜ z in Path.segment a b, holomorphicOneForm (fun E => F (E,y)) z) q := by
  obtain ⟨U,V,hU,hconv,ha,hb,hV,hq,hsub⟩ := exists_convex_segment_parameter_chart D hD a b q hsegment
  have hP := analyticOnNhd_parametricConvexPrimitive F U V a hU hconv hV ha (hF.mono hsub)
  have hqP := (hP (b,q) ⟨hb,hq⟩).comp (f := fun y : A => (b,y)) (analyticAt_const.prod analyticAt_id)
  simpa only [Function.comp_def,parametricConvexPrimitive_eq_curveIntegral] using hqP

def parametricPolygonalDomain (k : ℕ) (v : ℕ → ℂ) (D : Set (ℂ × A)) : Set A :=
  {q | ∀ i : Fin k, ∀ z ∈ segment ℝ (v i.val) (v (i.val+1)), (z,q) ∈ D}

def parametricPolygonalIntegral (F : ℂ × A → ℂ) (k : ℕ) (v : ℕ → ℂ) (q : A) : ℂ :=
  ∑ i : Fin k, ∫ᶜ z in Path.segment (v i.val) (v (i.val+1)), holomorphicOneForm (fun E => F (E,q)) z

omit [NormedSpace ℂ A] in
theorem isOpen_parametricPolygonalDomain (k : ℕ) (v : ℕ → ℂ)
    (D : Set (ℂ × A)) (hD : IsOpen D) : IsOpen (parametricPolygonalDomain k v D) := by
  let K : Set ℂ := ⋃ i : Fin k, segment ℝ (v i.val) (v (i.val+1))
  have hK : IsCompact K := isCompact_iUnion (fun i => by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous)
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hlocal : ∀ z ∈ K, ∃ U : Set (ℂ × A), IsOpen U ∧ (z,q) ∈ U ∧ ∀ t ∈ U, t ∈ D := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact ⟨D,hD,hq i z hi,fun _ ht => ht⟩
  obtain ⟨V,hV,hqV,hsub⟩ := exists_uniform_local_property_near_compact_slice K hK q (fun t => t ∈ D) hlocal
  apply mem_of_superset (hV.mem_nhds hqV)
  intro y hy i z hz
  exact hsub y hy z (mem_iUnion.mpr ⟨i,hz⟩)

theorem analyticOnNhd_parametricPolygonalIntegral (F : ℂ × A → ℂ) (k : ℕ) (v : ℕ → ℂ)
    (D : Set (ℂ × A)) (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) :
    AnalyticOnNhd ℂ (parametricPolygonalIntegral F k v) (parametricPolygonalDomain k v D) := by
  intro q hq
  have hsum := Finset.analyticAt_sum (f := fun i : Fin k => fun y : A =>
    ∫ᶜ z in Path.segment (v i.val) (v (i.val+1)), holomorphicOneForm (fun E => F (E,y)) z)
    Finset.univ (fun i _ => analyticAt_parametric_fixed_segment_integral F D hD hF _ _ q (hq i))
  convert hsum using 1
  funext y
  simp only [parametricPolygonalIntegral,Finset.sum_apply]

end NLS.ComplexAnalysis
