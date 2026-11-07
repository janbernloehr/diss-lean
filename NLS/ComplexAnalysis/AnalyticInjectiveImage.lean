import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! A single analytic inverse on the entire open image of an injective
analytic map with invertible derivative. Local inverse branches agree by uniqueness. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Local analytic inverse branches glue on the ENTIRE image of the open domain. -/
theorem exists_analytic_inverse_on_injective_open_image (f : E → E) (U : Set E)
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) (hi : Set.InjOn f U)
    (hd : ∀ x ∈ U, Function.Bijective (fderiv ℂ f x)) :
    ∃ g : E → E, IsOpen (f '' U) ∧ AnalyticOnNhd ℂ g (f '' U) ∧
      (∀ x ∈ U, g (f x) = x) ∧ ∀ y ∈ f '' U, g y ∈ U ∧ f (g y) = y := by
  classical
  have hlocal (x : E) (hx : x ∈ U) : ∃ P : OpenPartialHomeomorph E E,
      (P : E → E) = f ∧ x ∈ P.source ∧ P.source ⊆ U ∧
      AnalyticOnNhd ℂ f P.source ∧ AnalyticOnNhd ℂ P.symm P.target :=
    exists_analytic_openPartialHomeomorph hU hf hx (ContinuousLinearMap.isUnit_iff_bijective.mpr (hd x hx))
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨P, hP, hxP, hsub, _, _⟩ := hlocal x hx
    have htarget : f x ∈ P.target := by rw [← hP]; exact P.map_source hxP
    apply Filter.mem_of_superset (P.open_target.mem_nhds htarget)
    intro z hz
    exact ⟨P.symm z, hsub (P.map_target hz), by rw [← hP]; exact P.right_inv hz⟩
  let g (y : E) : E := if h : y ∈ f '' U then Classical.choose h else 0
  have hright (y : E) (hy : y ∈ f '' U) : g y ∈ U ∧ f (g y) = y := by
    dsimp only [g]
    rw [dif_pos hy]
    exact Classical.choose_spec hy
  have hleft (x : E) (hx : x ∈ U) : g (f x) = x :=
    hi (hright _ ⟨x,hx,rfl⟩).1 hx (hright _ ⟨x,hx,rfl⟩).2
  refine ⟨g, hopen, ?_, hleft, hright⟩
  intro y hy
  obtain ⟨hgU, hfg⟩ := hright y hy
  obtain ⟨P, hP, hxP, hsub, _, hPinv⟩ := hlocal (g y) hgU
  have hyP : y ∈ P.target := by rw [← hfg, ← hP]; exact P.map_source hxP
  apply (hPinv y hyP).congr
  filter_upwards [P.open_target.mem_nhds hyP] with z hz
  have hzU : P.symm z ∈ U := hsub (P.map_target hz)
  have hzimage : z ∈ f '' U := ⟨P.symm z, hzU, by rw [← hP]; exact P.right_inv hz⟩
  have hPz : f (P.symm z) = z := by rw [← hP]; exact P.right_inv hz
  exact hi hzU (hright z hzimage).1 (hPz.trans (hright z hzimage).2.symm)

end NLS.ComplexAnalysis
