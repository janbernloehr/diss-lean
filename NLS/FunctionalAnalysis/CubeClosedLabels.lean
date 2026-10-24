import NLS.FunctionalAnalysis.CubeFixedPoint

/-! # Intersections of closed face-compatible label sets in a cube

A complete Sperner simplex on finer grids supplies points in all label
sets whose mutual distances tend to zero. Compactness and closedness
produce a common point.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.CubicalSperner
variable {n : ℕ}

/-- A closed covering by the n+1 compatible cubical labels has a common point. -/
theorem exists_mem_all_cube_closed_labels (D : Fin (n+1) → Set (@unit_cube n))
    (hclosed : ∀ c, IsClosed (D c)) (hcover : ∀ x, ∃ c, x ∈ D c)
    (hface : ∀ c x, x ∈ D c → ∀ k : Fin n,
      (x.val k = 0 → c.val ≠ k.val) ∧ (x.val k = 1 → c.val ≤ k.val)) :
    ∃ x, ∀ c, x ∈ D c := by
  classical
  choose label hlabel using hcover
  have happ (p0 : ℕ) : ∃ x0 : @unit_cube n, ∀ c : Fin (n+1),
      ∃ xc ∈ D c, dist x0 xc ≤ 1 / (p0+1 : ℝ) := by
    let p := p0+1
    have hp : 0 < p := by omega
    let SC : SpernerCube := {
      n := n
      p := p
      RL := fun v => (label (discrete_map p v)).val
      rl_proper := by
        intro v
        refine ⟨(label (discrete_map p v)).is_le,fun k => ⟨?_,?_⟩⟩
        · intro h0
          apply (hface _ _ (hlabel _) k).1
          change (v k).val / (p : ℝ) = 0
          simp [h0]
        · intro h1
          apply (hface _ _ (hlabel _) k).2
          change (v k).val / (p : ℝ) = 1
          rw [h1]
          exact div_self (by exact_mod_cast hp.ne') }
    obtain ⟨I,hI⟩ := weaker_cubical_sperner SC
    refine ⟨discrete_map p (I 0),?_⟩
    intro c
    have hc : c.val ∈ Set.range (fun i => SC.RL (I i)) :=
      hI.2.symm.subset c.is_le
    obtain ⟨i,hi⟩ := hc
    have he : label (discrete_map p (I i)) = c := Fin.ext hi
    refine ⟨discrete_map p (I i),he ▸ hlabel _,?_⟩
    have hd := dist_discrete_map p hp (I 0) (I i) (fun k =>
      ⟨le_add_one_of_simplex SC I hI.1 0 i k,
        le_add_one_of_simplex SC I hI.1 i 0 k⟩)
    simpa only [p,Nat.cast_add,Nat.cast_one] using hd
  choose x0 hx0 using happ
  have hcompact : IsCompact (@unit_cube n) := isCompact_Icc
  obtain ⟨a,ha,φ,hmono,hlim⟩ := hcompact.isSeqCompact (fun i => (x0 i).property)
  let x : @unit_cube n := ⟨a,ha⟩
  have hx : Tendsto (x0 ∘ φ) atTop (𝓝 x) := tendsto_subtype_rng.mpr hlim
  refine ⟨x,?_⟩
  intro c
  choose y hy hdist using fun j => hx0 (φ j) c
  have hy_lim : Tendsto y atTop (𝓝 x) := by
    apply tendsto_of_tendsto_of_dist hx
    have hzero := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hmono.tendsto_atTop
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => hdist j) hzero
  exact (hclosed c).mem_of_tendsto hy_lim (Eventually.of_forall hy)

end NLS.CubicalSperner
