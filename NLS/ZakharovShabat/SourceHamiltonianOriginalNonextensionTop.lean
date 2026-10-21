import NLS.ZakharovShabat.SourceHamiltonianOriginalNonextension
import NLS.SequenceSpaces.HilbertHamiltonianNonextensionTop

/-! # Nonextension at every action exponent above two

The original local quadratic bound obstructs continuity on the nonnegative action cone, including exponent infinity.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceOriginalHamiltonianData
local instance hamiltonianEndpointFourFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance hamiltonianEndpointFourHolder : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The same Hamiltonian has no continuous (and hence no C¹) extension
near zero in any action exponent above two, including infinity, even relative to the cone. -/
theorem no_continuous_extension_all (Q : SourceOriginalHamiltonianData D T F H)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (h2q : 2 < q)
    (G : Coeff q → ℂ) (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0 : Coeff q))
    (hagree : ∀ a : Coeff 1, a ∈ Coeff.nonnegativeLocus 1 →
      Coeff.exponentInclusion (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) h2q.le) a ∈ U →
      G (Coeff.exponentInclusion (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) h2q.le) a) =
        H (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a)) :
    ¬ ContinuousWithinAt G (Coeff.nonnegativeLocus q) 0 ∧
      ¬ ContDiffWithinAt ℝ 1 G (Coeff.nonnegativeLocus q) 0 := by
  obtain ⟨r,hr,hbound⟩ := Q.quadratic_bound
  have hnc := Coeff.not_continuousWithinAt_extension_of_quadratic_bound_all h2q H Q.map_zero
    r hr hbound G U hU (fun a ha hU _ => hagree a ha hU)
  exact ⟨hnc,fun hC => hnc hC.continuousWithinAt⟩

end NLS.ZakharovShabat.SourceOriginalHamiltonianData
