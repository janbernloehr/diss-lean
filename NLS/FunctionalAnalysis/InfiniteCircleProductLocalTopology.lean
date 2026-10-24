import NLS.FunctionalAnalysis.CircleNoncontractible
import Mathlib.Topology.Homotopy.LocallyContractible

/-! # Local noncontractibility of an infinite product of circles

Every neighborhood constrains only finitely many coordinates. An unused
coordinate supplies a circle retract, so the neighborhood's inclusion in
the whole product is not nullhomotopic. In particular no neighborhood is
contractible, and even classical local contractibility fails.
-/
noncomputable section
open Set Filter Topology ContinuousMap
namespace NLS.FunctionalAnalysis
variable {ι : Type*} [Infinite ι]

/-- An unrestricted coordinate gives a circle retract inside any product neighborhood. -/
theorem exists_circle_retract_of_mem_nhds
    (x : ι → Circle) {V : Set (ι → Circle)} (hV : V ∈ 𝓝 x) :
    ∃ s : C(Circle,V), ∃ r : C((ι → Circle),Circle),
      r.comp ((⟨Subtype.val,continuous_subtype_val⟩ : C(V,ι → Circle)).comp s) =
        ContinuousMap.id Circle := by
  classical
  rw [nhds_pi] at hV
  obtain ⟨I,t,ht,hsub⟩ := Filter.mem_pi'.mp hV
  obtain ⟨i,hi⟩ := I.exists_notMem
  have hmem (z : Circle) : Function.update x i z ∈ V := by
    apply hsub
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simpa only [Function.update_of_ne hji] using mem_of_mem_nhds (ht j)
  have hs : Continuous (fun z : Circle => Function.update x i z) :=
    (continuous_const : Continuous (fun _ : Circle => x)).update i continuous_id
  let s : C(Circle,V) := ⟨fun z => ⟨Function.update x i z,hmem z⟩,hs.subtype_mk hmem⟩
  let r : C((ι → Circle),Circle) := ⟨fun y => y i,continuous_apply i⟩
  refine ⟨s,r,?_⟩
  ext z
  simp [s,r]

/-- No neighborhood inclusion into an infinite circle product is nullhomotopic. -/
theorem not_nullhomotopic_circleProduct_neighborhood_inclusion
    (x : ι → Circle) {V : Set (ι → Circle)} (hV : V ∈ 𝓝 x) :
    ¬ (⟨Subtype.val,continuous_subtype_val⟩ : C(V,ι → Circle)).Nullhomotopic := by
  intro h
  obtain ⟨s,r,he⟩ := exists_circle_retract_of_mem_nhds x hV
  have hn := (h.comp_left s).comp_right r
  rw [he] at hn
  exact not_contractibleSpace_circle ((contractible_iff_id_nullhomotopic Circle).mpr hn)

/-- Every neighborhood of every point in an infinite circle product is noncontractible. -/
theorem not_contractible_circleProduct_neighborhood
    (x : ι → Circle) {V : Set (ι → Circle)} (hV : V ∈ 𝓝 x) :
    ¬ ContractibleSpace V := by
  intro h
  let := h
  have hn := (id_nullhomotopic V).comp_right
    (⟨Subtype.val,continuous_subtype_val⟩ : C(V,ι → Circle))
  exact not_nullhomotopic_circleProduct_neighborhood_inclusion x hV hn

/-- This neighborhood obstruction transfers along any homeomorphism to an infinite circle product. -/
theorem not_contractible_neighborhood_of_homeomorph_circleProduct
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ (ι → Circle))
    (x : X) {V : Set X} (hV : V ∈ 𝓝 x) : ¬ ContractibleSpace V := by
  intro h
  let := h
  have hi : ContractibleSpace (e '' V) :=
    (e.isEmbedding.homeomorphImage V).symm.contractibleSpace
  exact not_contractible_circleProduct_neighborhood (e x)
    (e.isOpenMap.image_mem_nhds hV) hi

/-- An infinite product of circles fails even classical local contractibility. -/
theorem not_locallyContractibleSpace_circleProduct :
    ¬ LocallyContractibleSpace (ι → Circle) := by
  intro h
  let x : ι → Circle := fun _ => 1
  obtain ⟨V,hVU,hV,hn⟩ := h x univ (by simp)
  have hi := hn.comp_right
    (⟨Subtype.val,continuous_subtype_val⟩ : C((univ : Set (ι → Circle)),ι → Circle))
  exact not_nullhomotopic_circleProduct_neighborhood_inclusion x hV hi

end NLS.FunctionalAnalysis
