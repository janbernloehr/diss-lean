import NLS.ComplexAnalysis.CompactCoordinateExtension

/-! # Joint analyticity of a compactly selected scalar-coordinate lift

Uniform-norm parameter analyticity and continuity of evaluation supply
joint continuity. A regular scalar coordinate then recovers joint
analyticity on the interior of the compact set.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped Classical
namespace NLS.ComplexAnalysis
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]

def compactFamilyExtension (K : Set ℂ) (H : P → C(K,ℂ)) (t : ℂ × P) : ℂ :=
  if h : t.1 ∈ K then H t.2 ⟨t.1,h⟩ else 0

theorem analyticOnNhd_compactFamilyExtension
    (K Ω : Set ℂ) [CompactSpace K] (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (V : Set P) (hV : IsOpen V) (H : P → C(K,ℂ))
    (hH : AnalyticOnNhd ℂ H V)
    (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ univ)
    (D : ℂ × P → ℂ) (hD : AnalyticOnNhd ℂ D (Ω ×ˢ V))
    (heq : ∀ b ∈ V, ∀ k : K, φ (H b k) = D (k,b))
    (hne : ∀ b ∈ V, ∀ k : K, deriv φ (H b k) ≠ 0) :
    AnalyticOnNhd ℂ (compactFamilyExtension K H) (Ω ×ˢ V) := by
  have hc : ContinuousOn (compactFamilyExtension K H) (Ω ×ˢ V) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hp : Continuous (fun t : Ω ×ˢ V => (⟨t.val.2,t.property.2⟩ : V)) := by
      fun_prop
    have hz : Continuous (fun t : Ω ×ˢ V => (⟨t.val.1,hΩK t.property.1⟩ : K)) := by
      fun_prop
    have hHv : Continuous (V.domRestrict H) :=
      continuousOn_iff_continuous_domRestrict.mp hH.continuousOn
    have h := continuous_eval.comp ((hHv.comp hp).prodMk hz)
    convert h using 1
    funext t
    simp only [Set.domRestrict_apply, compactFamilyExtension, dif_pos (hΩK t.property.1)]
    rfl
  intro t ht
  have hk : t.1 ∈ K := hΩK ht.1
  have hv : compactFamilyExtension K H t = H t.2 ⟨t.1,hk⟩ := dif_pos hk
  apply analyticAt_of_continuousAt_scalar_coordinate φ (compactFamilyExtension K H) t
    (hφ _ (mem_univ _))
  · rw [hv]
    exact hne t.2 ht.2 ⟨t.1,hk⟩
  · exact hc.continuousAt ((hΩ.prod hV).mem_nhds ht)
  · apply (hD t ht).congr
    filter_upwards [(hΩ.prod hV).mem_nhds ht] with s hs
    change D s = φ (compactFamilyExtension K H s)
    rw [compactFamilyExtension, dif_pos (hΩK hs.1)]
    exact (heq s.2 hs.2 ⟨s.1,hΩK hs.1⟩).symm

end NLS.ComplexAnalysis
