import NLS.ComplexAnalysis.PrimitiveRadialContinuation

/-! # Actual polygonal integrals and their improper endpoint limits

Finite chains of integrable segment integrals connect any two points of
an open connected domain. If a primitive exists, their sum is independent
of the chain. Taking a relative limit at a boundary point defines a genuine
improper endpoint integral, without defining it by primitive values.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped unitInterval Classical
namespace NLS.ComplexAnalysis

/-- A finite chain of actual, integrable segment integrals inside the domain. -/
inductive HasPolygonalIntegral (f : ℂ → ℂ) (D : Set ℂ) (a : ℂ) : ℂ → ℂ → Prop
  | refl (ha : a ∈ D) : HasPolygonalIntegral f D a a 0
  | step {b c v : ℂ} (h : HasPolygonalIntegral f D a b v)
      (hseg : segment ℝ b c ⊆ D)
      (hint : CurveIntegrable (holomorphicOneForm f) (Path.segment b c)) :
      HasPolygonalIntegral f D a c (v+∫ᶜ z in Path.segment b c, holomorphicOneForm f z)

namespace HasPolygonalIntegral
variable {f : ℂ → ℂ} {D : Set ℂ} {a b v : ℂ}

theorem terminal_mem (h : HasPolygonalIntegral f D a b v) : b ∈ D := by
  cases h with
  | refl ha => exact ha
  | step _ hseg _ => exact hseg (right_mem_segment ℝ _ _)

theorem eq_sub (h : HasPolygonalIntegral f D a b v) (F : ℂ → ℂ)
    (hf : ContinuousOn f D) (hF : ∀ z ∈ D, HasDerivAt F (f z) z) : v = F b-F a := by
  induction h with
  | refl _ => simp
  | step _ hseg _ ih =>
    rw [ih,curveIntegral_segment_eq_sub_of_primitive f F D hf hF _ _ hseg]
    ring

theorem append_segment (h : HasPolygonalIntegral f D a b v) (hf : ContinuousOn f D)
    (c : ℂ) (hseg : segment ℝ b c ⊆ D) :
    ∃ w, HasPolygonalIntegral f D a c w := by
  have hω : ContinuousOn (holomorphicOneForm f) D := hf.smul continuousOn_const
  exact ⟨_,h.step hseg (hω.curveIntegrable_of_contDiffOn (contDiffOn_segment_extend b c)
    (fun t => hseg (lineMap_mem_segment ℝ b c t.property)))⟩

end HasPolygonalIntegral

/-- Open connected domains admit finite integrable polygonal connectors. -/
theorem exists_hasPolygonalIntegral (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hc : IsPreconnected D) (hf : ContinuousOn f D) (a b : ℂ) (ha : a ∈ D) (hb : b ∈ D) :
    ∃ v, HasPolygonalIntegral f D a b v := by
  let S := {z | ∃ v, HasPolygonalIntegral f D a z v}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    obtain ⟨v,hv⟩ := hz
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hv.terminal_mem)
    apply mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hr))
    intro w hw
    exact hv.append_segment hf w ((convex_ball z r).segment_subset (mem_ball_self hr) hw |>.trans hball)
  apply hc.subset_of_closure_inter_subset hS ⟨a,ha,0,HasPolygonalIntegral.refl ha⟩ ?_ hb
  rintro z ⟨hzS,hzD⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hzD)
  obtain ⟨w,⟨v,hv⟩,hw⟩ := Metric.mem_closure_iff.mp hzS r hr
  have hwB : w ∈ ball z r := by simpa only [mem_ball,dist_comm] using hw
  exact hv.append_segment hf z ((convex_ball z r).segment_subset hwB (mem_ball_self hr) |>.trans hball)

/-- Choose a finite sum of literal segment integrals; default to zero if no chain exists. -/
def polygonalIntegral (f : ℂ → ℂ) (D : Set ℂ) (a b : ℂ) : ℂ :=
  if h : ∃ v, HasPolygonalIntegral f D a b v then Classical.choose h else 0

theorem polygonalIntegral_spec (f : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hc : IsPreconnected D) (hf : ContinuousOn f D) (a b : ℂ) (ha : a ∈ D) (hb : b ∈ D) :
    HasPolygonalIntegral f D a b (polygonalIntegral f D a b) := by
  have h := exists_hasPolygonalIntegral f D hD hc hf a b ha hb
  rw [polygonalIntegral,dif_pos h]
  exact Classical.choose_spec h

theorem polygonalIntegral_eq_sub (f F : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hc : IsPreconnected D) (hf : ContinuousOn f D)
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (a b : ℂ) (ha : a ∈ D) (hb : b ∈ D) :
    polygonalIntegral f D a b = F b-F a :=
  (polygonalIntegral_spec f D hD hc hf a b ha hb).eq_sub F hf hF

/-- Improper endpoint integration as a limit of actual polygonal integrals. -/
def endpointPolygonalIntegral (f : ℂ → ℂ) (D : Set ℂ) (a b : ℂ) : ℂ :=
  limUnder (𝓝[D] a) (fun z => polygonalIntegral f D z b)

theorem tendsto_polygonalIntegral_endpoint (f F : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hc : IsPreconnected D) (hf : ContinuousOn f D)
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (a b A : ℂ) (hb : b ∈ D)
    (hlim : Tendsto F (𝓝[D] a) (𝓝 A)) :
    Tendsto (fun z => polygonalIntegral f D z b) (𝓝[D] a) (𝓝 (F b-A)) := by
  apply (tendsto_const_nhds.sub hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (polygonalIntegral_eq_sub f F D hD hc hf hF z b hz hb).symm

theorem endpointPolygonalIntegral_eq_sub (f F : ℂ → ℂ) (D : Set ℂ) (hD : IsOpen D)
    (hc : IsPreconnected D) (hf : ContinuousOn f D)
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (a b A : ℂ) (ha : a ∈ closure D) (hb : b ∈ D)
    (hlim : Tendsto F (𝓝[D] a) (𝓝 A)) : endpointPolygonalIntegral f D a b = F b-A := by
  let : NeBot (𝓝[D] a) := mem_closure_iff_nhdsWithin_neBot.mp ha
  exact (tendsto_polygonalIntegral_endpoint f F D hD hc hf hF a b A hb hlim).limUnder_eq

end NLS.ComplexAnalysis
