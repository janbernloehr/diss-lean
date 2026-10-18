import NLS.ZakharovShabat.SourceGapWeightedEtaH1Sequence
import NLS.ZakharovShabat.SourceBirkhoffH1NormalizationPhase

/-! # The signed Birkhoff coordinate minus eta in h2

Applying the exact normalization-phase multiplier to the actual eta h1
sequence proves an h2 remainder uniformly on physical H1 balls. Both
signs use the same original Birkhoff family.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual signed Birkhoff coordinate minus its eta coordinate gains one sequence derivative. -/
theorem birkhoff_minus_eta_uniform_physical_H1_ball (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ z : WeightedCoeff (Weight.sobolev 2) 2,
          (∀ n, z.val n = sourceBirkhoffWeightedCoordinate (by simp) (by norm_num)
            n s (sign:ℂ) (sobolevSourceInclusion a.val)-sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
              n s (sign:ℂ) (sobolevSourceInclusion a.val)) ∧ ‖z‖ ≤ M := by
  obtain ⟨K,hK,h⟩ := D.normalization_phase_multipliers_uniform_physical_H1_ball R
  obtain ⟨A,hA,hgap⟩ := exists_sourceH1WeightedGapSequence_bound_on_physical_ball R
  refine ⟨2*K*A,by positivity,?_⟩
  intro a ha sign hsign
  have hs : (sign:ℂ) = 1 ∨ (sign:ℂ) = -1 := by
    rcases hsign with rfl | rfl <;> simp
  have habs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hmult := h a ha 2 inferInstance 1 sign
  rw [show (1:ℝ)+1 = 2 by norm_num] at hmult
  obtain ⟨T,hT,hnT⟩ := hmult
  let c := D.signedEtaH1 a (sign:ℂ) hs
  refine ⟨T c,?_,?_⟩
  · intro n
    rw [hT]
    simp only [c,signedEtaH1_apply,sourceBirkhoffWeightedCoordinate]
    ring
  · have hc : ‖c‖ ≤ A := (D.norm_signedEtaH1_le a (sign:ℂ) hs).trans (hgap a ha)
    have ht : ‖T‖ ≤ 2*K := by simpa only [habs,show (1:ℝ)+1=2 by norm_num] using hnT
    exact (T.le_opNorm c).trans (mul_le_mul ht hc (norm_nonneg _) (by positivity))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
