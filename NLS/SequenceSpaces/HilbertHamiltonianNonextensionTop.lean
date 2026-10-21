import NLS.SequenceSpaces.HilbertHamiltonianNonextension

/-! # The infinity endpoint for Hamiltonian nonextension

The original local quadratic bound obstructs continuity on the nonnegative action cone, including exponent infinity.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
local instance hamiltonianEndpointThreeFact : Fact ((1:ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The endpoint obstruction follows by restriction along the contractive
inclusion from exponent three into infinity. -/
theorem not_continuousWithinAt_top_extension_of_quadratic_bound
    (H : Coeff 2 → ℂ) (hzero : H 0 = 0) (r : ℝ) (hr : 0 < r)
    (hbound : ∀ b ∈ nonnegativeLocus 2, ‖b‖ < r → (H b).re ≤ -‖b‖^2/2)
    (G : Coeff ⊤ → ℂ) (U : Set (Coeff ⊤)) (hU : U ∈ 𝓝 (0:Coeff ⊤))
    (hagree : ∀ a : Coeff 1, a ∈ nonnegativeLocus 1 →
      exponentInclusion (show (1:ℝ≥0∞) ≤ ⊤ from le_top) a ∈ U →
      ‖exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a‖ < r →
      G (exponentInclusion (show (1:ℝ≥0∞) ≤ ⊤ from le_top) a) =
        H (exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a)) :
    ¬ ContinuousWithinAt G (nonnegativeLocus ⊤) 0 := by
  let L := exponentInclusion (show (3:ℝ≥0∞) ≤ ⊤ from le_top)
  have hL : MapsTo L (nonnegativeLocus 3) (nonnegativeLocus ⊤) := by
    intro a ha n
    exact ha n
  have hpre : L ⁻¹' U ∈ 𝓝 (0:Coeff 3) := by
    exact L.continuous.continuousAt.preimage_mem_nhds (by simpa using hU)
  have hn := not_continuousWithinAt_extension_of_quadratic_bound
    (q := 3) (by simp) (by norm_num) H hzero r hr hbound
    (G ∘ L) (L ⁻¹' U) hpre (fun a ha hUa hnorm => by
      simpa only [Function.comp_apply,L,exponentInclusion_trans] using
        hagree a ha (by simpa only [mem_preimage,L,exponentInclusion_trans] using hUa) hnorm)
  intro hG
  apply hn
  exact hG.comp_of_eq L.continuous.continuousAt.continuousWithinAt hL (map_zero L)

/-- Every exponent above two, including infinity, obstructs a continuous
extension under the same local quadratic bound. -/
theorem not_continuousWithinAt_extension_of_quadratic_bound_all
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (h2q : 2 < q)
    (H : Coeff 2 → ℂ) (hzero : H 0 = 0) (r : ℝ) (hr : 0 < r)
    (hbound : ∀ b ∈ nonnegativeLocus 2, ‖b‖ < r → (H b).re ≤ -‖b‖^2/2)
    (G : Coeff q → ℂ) (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0:Coeff q))
    (hagree : ∀ a : Coeff 1, a ∈ nonnegativeLocus 1 →
      exponentInclusion (le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a ∈ U →
      ‖exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a‖ < r →
      G (exponentInclusion (le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) h2q.le) a) =
        H (exponentInclusion (by norm_num : (1:ℝ≥0∞) ≤ 2) a)) :
    ¬ ContinuousWithinAt G (nonnegativeLocus q) 0 := by
  by_cases hq : q = ⊤
  · subst q
    exact not_continuousWithinAt_top_extension_of_quadratic_bound H hzero r hr hbound G U hU hagree
  · exact not_continuousWithinAt_extension_of_quadratic_bound hq h2q H hzero r hr hbound G U hU hagree

end NLS.Coeff
