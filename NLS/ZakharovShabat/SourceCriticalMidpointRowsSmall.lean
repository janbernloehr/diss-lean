import NLS.SequenceSpaces.ReciprocalRowContinuity
import NLS.ZakharovShabat.SourceNormalizedActionSequenceMajorants
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity

/-! # Uniformly small distant reciprocal rows of the actual critical offsets -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem continuousAt_sourceCriticalMidpointOffset_of_realType
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ContinuousAt (fun ψ : CoeffPair 2 => canonicalCriticalMidpointOffset
      (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ)) φ := by
  have he : (fun ψ : CoeffPair 2 => canonicalCriticalMidpointOffset
      (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ)) =
      (fun ψ : CoeffPair 2 => sourceCriticalDisplacement (by simp) (by norm_num) ψ-
        sourcePeriodicMidpointDisplacement (by simp) (by norm_num) ψ) := by
    funext ψ
    ext n
    simp only [canonicalCriticalMidpointOffset_apply,lp.coeFn_sub,Pi.sub_apply,
      sourceCriticalDisplacement,canonicalCriticalDisplacement_apply,sourcePeriodicMidpointDisplacement_apply]
    ring
  rw [he]
  exact (continuousAt_sourceCriticalDisplacement_of_realType (by simp) (by norm_num) φ hφ).sub
    (continuousAt_sourcePeriodicMidpointDisplacement_of_realType (by simp) (by norm_num) φ hφ)

/-- One neighborhood and one index cutoff make every finite critical-offset row small. -/
theorem exists_uniform_sourceCriticalMidpoint_reciprocal_rows
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ ∈ U ∧ ∃ K : ℕ,
      ∀ ψ ∈ U, ∀ n : ℤ, K ≤ n.natAbs → ∀ s : Finset ℤ,
        (∀ m ∈ s, m ≠ n) →
        (∑ m ∈ s, ‖canonicalCriticalPoints (by simp) (by norm_num)
            (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
          canonicalPeriodicMidpoint (by simp) (by norm_num)
            (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖/|((m-n:ℤ):ℝ)|) ≤ ε := by
  obtain ⟨V,_,hφV,_,_,hb⟩ := exists_local_sourceCriticalMidpointOffset_one_bound
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num) le_rfl φ hφ
  let a := fun ψ : CoeffPair 2 => canonicalCriticalMidpointOffset
    (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := sourceCriticalMidpointOffsetAtExponent (by simp : (2:ℝ≥0∞) ≠ ⊤)
    (by norm_num) (q := 1) (source_half_le_one (by simp) le_rfl) φ
  have he (m : ℤ) : a φ m = b m := by
    simpa only [a,canonicalCriticalMidpointOffset_apply] using (hb φ hφV).2 m
  obtain ⟨U,hU,hφU,K,hK⟩ := exists_uniform_reciprocal_rows_of_continuousAt a φ
    (continuousAt_sourceCriticalMidpointOffset_of_realType φ hφ) b he ε hε
  refine ⟨U,hU,hφU,K,?_⟩
  intro ψ hψ n hn s hs
  simpa only [a,canonicalCriticalMidpointOffset_apply] using hK ψ hψ n hn s hs

end NLS.ZakharovShabat
