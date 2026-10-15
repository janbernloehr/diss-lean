import NLS.ZakharovShabat.SourceHamiltonianOriginal
import NLS.SequenceSpaces.HilbertHamiltonianNonextension

/-!
# Remark 18.4 for the same original Hamiltonian

The concavity estimate obstructs even continuous extensions on the
nonnegative action cone at every finite exponent above two.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceOriginalHamiltonianData
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

theorem map_zero (Q : SourceOriginalHamiltonianData D T F H) : H 0 = 0 :=
  (Q.sign 0 Q.frequency.zero_mem (Coeff.zero_mem_nonnegativeLocus 2)).2.2.mpr rfl

theorem gradient_zero (Q : SourceOriginalHamiltonianData D T F H) : Coeff.scalarGradient H 0 = 0 :=
  (Q.gradient_eq Q.frequency.zero_mem).symm.trans Q.frequency.map_zero

/-- A uniform quadratic bound for this Hamiltonian follows from its Hessian estimate. -/
theorem quadratic_bound (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ r : ℝ, 0 < r ∧ ∀ b ∈ Coeff.nonnegativeLocus 2, ‖b‖ < r → (H b).re ≤ -‖b‖^2/2 := by
  obtain ⟨r,hr,hball,he⟩ := Q.concavity
  refine ⟨r,hr,?_⟩
  intro b hpos hnorm
  let J := Coeff.reCLM 2 b
  have hJ : RealCoeff.complexCLM 2 J = b :=
    RealCoeff.complexCLM_reCLM 2 b (fun n => (hpos n).1)
  have hn : ‖J‖ = ‖b‖ := by rw [← Coeff.norm_real_hilbert_inclusion J,hJ]
  simpa only [hJ,hn] using Coeff.real_value_le_negative_half_norm_sq H T Q.analytic
    Q.map_zero Q.gradient_zero r hball he J (by simpa only [hn] using hnorm)

/-- The same Hamiltonian has no continuous (and hence no C¹) extension
near zero in any finite action exponent above two, even relative to the cone. -/
theorem no_continuous_extension (Q : SourceOriginalHamiltonianData D T F H)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q ≠ ⊤) (h2q : 2 < q)
    (G : Coeff q → ℂ) (U : Set (Coeff q)) (hU : U ∈ 𝓝 (0 : Coeff q))
    (hagree : ∀ a : Coeff 1, a ∈ Coeff.nonnegativeLocus 1 →
      Coeff.exponentInclusion (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) h2q.le) a ∈ U →
      G (Coeff.exponentInclusion (le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 2) h2q.le) a) =
        H (Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) a)) :
    ¬ ContinuousWithinAt G (Coeff.nonnegativeLocus q) 0 ∧
      ¬ ContDiffWithinAt ℝ 1 G (Coeff.nonnegativeLocus q) 0 := by
  obtain ⟨r,hr,hbound⟩ := Q.quadratic_bound
  have hnc := Coeff.not_continuousWithinAt_extension_of_quadratic_bound hq h2q H Q.map_zero
    r hr hbound G U hU (fun a ha hU _ => hagree a ha hU)
  exact ⟨hnc,fun hC => hnc hC.continuousWithinAt⟩

end NLS.ZakharovShabat.SourceOriginalHamiltonianData
