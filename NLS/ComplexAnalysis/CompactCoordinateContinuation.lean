import NLS.ComplexAnalysis.CompactCoordinateJointExtension

/-! # One joint analytic continuation of a compact scalar-coordinate lift

The Banach inverse fixes all values of the reference compact lift at once.
Evaluation and local scalar inversion then give a single jointly analytic
function on the interior and one common complex parameter neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem exists_joint_compact_coordinate_continuation
    (K Ω : Set ℂ) [CompactSpace K] (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ univ)
    (u : C(K,ℂ)) (hu : ∀ k, deriv φ (u k) ≠ 0)
    (D : ℂ × P → ℂ) (hD : AnalyticOnNhd ℂ D univ)
    (a : P) (hbase : ∀ k : K, D (k,a) = φ (u k)) :
    ∃ V : Set P, IsOpen V ∧ a ∈ V ∧ ∃ G : ℂ × P → ℂ,
      AnalyticOnNhd ℂ G (Ω ×ˢ V) ∧
      (∀ z : K, G (z,a) = u z) ∧
      ∀ t ∈ Ω ×ˢ V, φ (G t) = D t ∧ deriv φ (G t) ≠ 0 := by
  let B : P → C(K,ℂ) := fun b =>
    ⟨fun z => D (z,b), hD.continuous.comp (continuous_subtype_val.prodMk continuous_const)⟩
  have hB : Continuous B := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hD.continuous.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
  have hBa : AnalyticAt ℂ B a := by
    apply analyticOnNhd_continuousMap_of_eval B isOpen_univ hB.continuousOn _ a (mem_univ _)
    intro k b _
    exact (hD (k,b) (mem_univ _)).comp (f := fun b : P => ((k : ℂ),b))
      (analyticAt_const.prod analyticAt_id)
  obtain ⟨V,hV,ha,H,hH,hHa,hdata⟩ :=
    exists_analytic_compact_coordinate_family φ hφ u hu B a hBa hbase
  refine ⟨V,hV,ha,compactFamilyExtension K H,?_,?_,?_⟩
  · exact analyticOnNhd_compactFamilyExtension K Ω hΩ hΩK V hV H hH φ hφ D
      (hD.mono (subset_univ _)) (fun b hb k => (hdata b hb k).1)
      (fun b hb k => (hdata b hb k).2)
  · intro z
    simp only [compactFamilyExtension,dif_pos z.property,hHa]
  · intro t ht
    have hk := hΩK ht.1
    dsimp only [compactFamilyExtension]
    rw [dif_pos hk]
    exact hdata t.2 ht.2 ⟨t.1,hk⟩

end NLS.ComplexAnalysis
