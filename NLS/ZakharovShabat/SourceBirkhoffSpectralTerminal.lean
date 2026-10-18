import NLS.ZakharovShabat.SourceBirkhoffH1EtaDifference
import NLS.ZakharovShabat.SourceEtaRemainderPhaseSmoothing

/-! # The Birkhoff coordinate and its literal spectral terminal

The terminal coordinate consists only of the actual Dirichlet root,
periodic midpoint and sine numerator. Removing the exact eta remainder
phase proves that all normalization and angular factors together
contribute an h2 error uniformly on physical H1 balls.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal spectral terminal part of the gap-weighted eta formula, before its remainder phase. -/
def sourceGapWeightedEtaTerminalCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (sign : ℂ) (ψ : CoeffPair p) : ℂ :=
  -2*(canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-
    canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n+
      sign*I*sourceDirichletEtaSineNumerator hp hp1 n ψ)

/-- The terminal coordinate is recovered by the exact inverse remainder phase at every complex source. -/
theorem sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (sign : ℂ) (ψ : CoeffPair p) :
    sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ =
      sourceGapWeightedEtaCoordinate hp hp1 n s sign ψ*exp (-sign*I*sourceAngularEtaRemainder hp hp1 n s ψ) := by
  let z := sourceGapWeightedEtaTerminalCoordinate hp hp1 n sign ψ
  change z = (z*exp (sign*I*sourceAngularEtaRemainder hp hp1 n s ψ))*
    exp (-sign*I*sourceAngularEtaRemainder hp hp1 n s ψ)
  rw [mul_assoc,← exp_add]
  have he : sign*I*sourceAngularEtaRemainder hp hp1 n s ψ+
      -sign*I*sourceAngularEtaRemainder hp hp1 n s ψ = 0 := by ring
  rw [he,exp_zero,mul_one]

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- All nonlinear normalization and angle factors contribute an h2 error on physical H1 balls. -/
theorem birkhoff_minus_spectral_terminal_uniform_physical_H1_ball (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ z : WeightedCoeff (Weight.sobolev 2) 2,
          (∀ n, z.val n = sourceBirkhoffWeightedCoordinate (by simp) (by norm_num)
            n s (sign:ℂ) (sobolevSourceInclusion a.val)-sourceGapWeightedEtaTerminalCoordinate
              (by simp) (by norm_num) n (sign:ℂ) (sobolevSourceInclusion a.val)) ∧ ‖z‖ ≤ M := by
  obtain ⟨M,hM,hB⟩ := D.birkhoff_minus_eta_uniform_physical_H1_ball R
  obtain ⟨K,hK,hT⟩ := D.etaRemainder_phase_multipliers_uniform_physical_H1_ball R
  obtain ⟨A,hA,hgap⟩ := exists_sourceH1WeightedGapSequence_bound_on_physical_ball R
  refine ⟨M+K*A,by positivity,?_⟩
  intro a ha sign hsign
  have hs : (sign:ℂ) = 1 ∨ (sign:ℂ) = -1 := by rcases hsign with rfl | rfl <;> simp
  have habs : |-sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  obtain ⟨z,hz,hnz⟩ := hB a ha sign hsign
  have hmult := hT a ha 2 inferInstance 1 (-sign)
  rw [show (1:ℝ)+1 = 2 by norm_num] at hmult
  obtain ⟨T,hT,hnT⟩ := hmult
  let c := D.signedEtaH1 a (sign:ℂ) hs
  have hc : ‖c‖ ≤ A := (D.norm_signedEtaH1_le a (sign:ℂ) hs).trans (hgap a ha)
  have ht : ‖T‖ ≤ K := by simpa only [habs,one_mul] using hnT
  refine ⟨z-T c,?_,?_⟩
  · intro n
    rw [WeightedCoeff.sub_val,hz,hT]
    simp only [c,signedEtaH1_apply,Complex.ofReal_neg]
    rw [sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase (by simp) (by norm_num) n s]
    ring
  · exact (norm_sub_le z (T c)).trans (add_le_add hnz
      ((T.le_opNorm c).trans (mul_le_mul ht hc (norm_nonneg _) hK)))

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
