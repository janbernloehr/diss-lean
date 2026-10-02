import NLS.ZakharovShabat.SourceBirkhoffCoordinates
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Sequence-valued rectangular Birkhoff coordinates

The total definitions retain the actual scalar coordinates whenever
their spectral majorants prove membership. Local uniform bounds then
assemble the coordinate power series into Banach-valued analytic maps.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBirkhoffXSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => sourceBirkhoffX hp hp1 n s ψ)

def sourceBirkhoffYSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => sourceBirkhoffY hp hp1 n s ψ)

/-- The complex Birkhoff map, with the two sequence components of (3.2). -/
def sourceBirkhoffMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : Coeff p × Coeff p :=
  (sourceBirkhoffXSequence hp hp1 s ψ,sourceBirkhoffYSequence hp hp1 s ψ)

/-- A uniform spectral bound simultaneously proves actual sequence
membership, exact coordinate evaluation, a norm bound, and analyticity. -/
theorem sourceBirkhoffSequence_analytic_of_uniform_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (C G : ℝ) (hC : 0 ≤ C)
    (hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceBirkhoffX hp hp1 n s) U ∧
      AnalyticOnNhd ℂ (sourceBirkhoffY hp hp1 n s) U)
    (hbound : ∀ ψ ∈ U, ∀ n : ℤ,
      ‖sourceBirkhoffX hp hp1 n s ψ‖ ≤ C*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ n‖) ∧
      ‖sourceBirkhoffY hp hp1 n s ψ‖ ≤ C*(‖sourcePeriodicGapDisplacement hp hp1 ψ n‖+
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ n‖))
    (hG : ∀ ψ ∈ U, ‖sourcePeriodicGapDisplacement hp hp1 ψ‖+
      ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤ G) :
    AnalyticOnNhd ℂ (sourceBirkhoffMap hp hp1 s) U ∧
      ∀ ψ ∈ U, ‖sourceBirkhoffMap hp hp1 s ψ‖ ≤ C*G ∧ ∀ n : ℤ,
        (sourceBirkhoffMap hp hp1 s ψ).1 n = sourceBirkhoffX hp hp1 n s ψ ∧
        (sourceBirkhoffMap hp hp1 s ψ).2 n = sourceBirkhoffY hp hp1 n s ψ := by
  have hx ψ (hψ : ψ ∈ U) := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (fun n => sourceBirkhoffX hp hp1 n s ψ) (sourcePeriodicGapDisplacement hp hp1 ψ)
    (sourceDirichletMidpointDisplacement hp hp1 ψ) C hC (fun n => (hbound ψ hψ n).1)
  have hy ψ (hψ : ψ ∈ U) := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (fun n => sourceBirkhoffY hp hp1 n s ψ) (sourcePeriodicGapDisplacement hp hp1 ψ)
    (sourceDirichletMidpointDisplacement hp hp1 ψ) C hC (fun n => (hbound ψ hψ n).2)
  have heval ψ (hψ : ψ ∈ U) n :
      sourceBirkhoffXSequence hp hp1 s ψ n = sourceBirkhoffX hp hp1 n s ψ ∧
      sourceBirkhoffYSequence hp hp1 s ψ n = sourceBirkhoffY hp hp1 n s ψ :=
    ⟨Coeff.ofFunctionOrZero_apply_of_mem p _ (hx ψ hψ).1 n,
      Coeff.ofFunctionOrZero_apply_of_mem p _ (hy ψ hψ).1 n⟩
  have hnorm ψ (hψ : ψ ∈ U) :
      ‖sourceBirkhoffXSequence hp hp1 s ψ‖ ≤ C*G ∧ ‖sourceBirkhoffYSequence hp hp1 s ψ‖ ≤ C*G :=
    ⟨(hx ψ hψ).2.trans (mul_le_mul_of_nonneg_left (hG ψ hψ) hC),
      (hy ψ hψ).2.trans (mul_le_mul_of_nonneg_left (hG ψ hψ) hC)⟩
  have hxA : AnalyticOnNhd ℂ (sourceBirkhoffXSequence hp hp1 s) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ (C*G) (fun ψ hψ => (hnorm ψ hψ).1)
    intro n ψ hψ
    apply ((hcoord n).1 ψ hψ).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (heval χ hχ n).1.symm
  have hyA : AnalyticOnNhd ℂ (sourceBirkhoffYSequence hp hp1 s) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ (C*G) (fun ψ hψ => (hnorm ψ hψ).2)
    intro n ψ hψ
    apply ((hcoord n).2 ψ hψ).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (heval χ hχ n).2.symm
  refine ⟨fun ψ hψ => (hxA ψ hψ).prod (hyA ψ hψ),?_⟩
  intro ψ hψ
  exact ⟨by simpa only [sourceBirkhoffMap,Prod.norm_def,max_le_iff] using hnorm ψ hψ,
    fun n => heval ψ hψ n⟩

end NLS.ZakharovShabat
