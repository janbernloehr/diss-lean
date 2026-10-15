import Mathlib.Analysis.Normed.Module.Connected
/-! # Connected preimages under dense linear maps

Open connected sets lift to connected sets along a dense real linear map.
Preimages of balls are convex, and density lifts the overlaps in a chain
of balls. Continuity of the linear map is not needed.
-/
noncomputable section
open Set Metric Relation
namespace NLS.ComplexAnalysis

/-- Dense linear maps preserve connectedness of open sets under preimage. -/
theorem isConnected_preimage_dense_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E →ₗ[ℝ] F) (hd : DenseRange f) {U : Set F}
    (hU : IsOpen U) (hc : IsConnected U) : IsConnected (f ⁻¹' U) := by
  let B := {cr : F × ℝ // 0 < cr.2 ∧ ball cr.1 cr.2 ⊆ U}
  let s : B → Set F := fun b => ball b.val.1 b.val.2
  have hs (b : B) : IsOpen (s b) := isOpen_ball
  have hne (b : B) : (s b).Nonempty := ⟨b.val.1,mem_ball_self b.property.1⟩
  have hunion : (⋃ b : B, s b) = U := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨b,hb⟩ := mem_iUnion.mp hx
      exact b.property.2 hb
    · intro x hx
      obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
      exact mem_iUnion.mpr ⟨⟨(x,r),hr,hball⟩,mem_ball_self hr⟩
  have hB : Nonempty B := by
    obtain ⟨x,hx⟩ := hc.nonempty
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨⟨(x,r),hr,hball⟩⟩
  let : Nonempty B := hB
  have hd' : Dense (range f) := hd
  have hpre (b : B) : IsConnected (f ⁻¹' s b) := by
    apply ((convex_ball b.val.1 b.val.2).linear_preimage f).isConnected
    obtain ⟨x,⟨y,rfl⟩,hy⟩ := hd'.exists_mem_open (hs b) (hne b)
    exact ⟨y,hy⟩
  have hconn : IsPreconnected (⋃ b : B, s b) := hunion.symm ▸ hc.isPreconnected
  have hchains (i j : B) : ReflTransGen
      (fun a b : B => ((f ⁻¹' s a) ∩ (f ⁻¹' s b)).Nonempty) i j := by
    apply Relation.TransGen.to_reflTransGen
    apply Relation.TransGen.mono (r := fun a b : B => (s a ∩ s b).Nonempty) ?_ i j
      (hconn.transGen_of_iUnion hs i j (hne i) (hne j))
    intro a b hab
    obtain ⟨x,⟨y,rfl⟩,hy⟩ := hd'.exists_mem_open ((hs a).inter (hs b)) hab
    exact ⟨y,hy⟩
  have h := IsConnected.iUnion_of_reflTransGen hpre hchains
  rwa [← preimage_iUnion,hunion] at h
end NLS.ComplexAnalysis
