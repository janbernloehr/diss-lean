import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Contraction through a common fiber section

Overlapping product domains contract through a shared continuous section, then along the real base space.
-/

noncomputable section
open Set ContinuousMap
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous section and straight contractions in its fibers make
the whole domain contractible over a real normed vector space. -/
theorem contractible_of_fiber_segments
    (U : Set (E × F)) (s : E → F) (hs : Continuous s)
    (hgraph : ∀ x, (x,s x) ∈ U)
    (hsegment : ∀ t ∈ U, segment ℝ t (t.1,s t.1) ⊆ U) :
    ContractibleSpace U := by
  let P : C(U,U) := {
    toFun := fun t => ⟨(t.val.1,s t.val.1),hgraph t.val.1⟩
    continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
      (hs.comp (continuous_fst.comp continuous_subtype_val))).subtype_mk _
  }
  let z : U := ⟨(0,s 0),hgraph 0⟩
  let H : (ContinuousMap.id U).Homotopy P := {
    toFun := fun q => ⟨(1-(q.1:ℝ)) • q.2.val+(q.1:ℝ) • (q.2.val.1,s q.2.val.1),by
      apply hsegment q.2.val q.2.property
      exact ⟨1-(q.1:ℝ),(q.1:ℝ),sub_nonneg.mpr q.1.property.2,q.1.property.1,
        sub_add_cancel _ _,rfl⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (((continuous_fst.comp continuous_subtype_val).prodMk
            (hs.comp (continuous_fst.comp continuous_subtype_val))).comp continuous_snd))
    map_zero_left := by intro t; apply Subtype.ext; simp
    map_one_left := by intro t; apply Subtype.ext; simp [P]
  }
  let G : P.Homotopy (ContinuousMap.const U z) := {
    toFun := fun q => ⟨((1-(q.1:ℝ)) • q.2.val.1,s ((1-(q.1:ℝ)) • q.2.val.1)),hgraph _⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      have hx : Continuous (fun q : unitInterval × U => (1-(q.1:ℝ)) • q.2.val.1) :=
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
      exact hx.prodMk (hs.comp hx)
    map_zero_left := by intro t; apply Subtype.ext; simp [P]
    map_one_left := by intro t; apply Subtype.ext; simp [z]
  }
  exact (contractible_iff_id_nullhomotopic U).mpr ⟨z,⟨H.trans G⟩⟩

/-- Overlapping product charts need only share a section in each fiber;
their union need not itself be convex. -/
theorem contractible_iUnion_products_of_section
    {ι : Type*} (V : ι → Set E) (D : ι → Set F)
    (s : E → F) (hs : Continuous s)
    (hcover : ∀ x, ∃ i, x ∈ V i)
    (hD : ∀ i, Convex ℝ (D i))
    (hsection : ∀ i x, x ∈ V i → s x ∈ D i) :
    ContractibleSpace (⋃ i, V i ×ˢ D i) := by
  apply contractible_of_fiber_segments _ s hs
  · intro x
    obtain ⟨i,hi⟩ := hcover x
    exact mem_iUnion.mpr ⟨i,hi,hsection i x hi⟩
  · intro t ht
    obtain ⟨i,hi⟩ := mem_iUnion.mp ht
    rintro u ⟨a,b,ha,hb,hab,rfl⟩
    apply mem_iUnion.mpr
    refine ⟨i,?_,(hD i) hi.2 (hsection i t.1 hi.1) ha hb hab⟩
    change a • t.1+b • t.1 ∈ V i
    rw [← add_smul,hab,one_smul]
    exact hi.1

end NLS.FunctionalAnalysis
