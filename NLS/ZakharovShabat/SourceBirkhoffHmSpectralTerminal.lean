import NLS.ZakharovShabat.SourceGapWeightedEtaHmSequence
import NLS.ZakharovShabat.SourceBirkhoffSpectralTerminal
import NLS.ZakharovShabat.HigherSobolevH1Realization

/-! # Higher-order angular smoothing for the actual spectral terminal

For every integer m >= 1, the actual signed Birkhoff coordinate minus
its literal spectral terminal belongs to h^(m+1), uniformly on physical
Hm balls. Both signs use the same retained original Birkhoff family.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal

namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- All normalization and angle factors gain one derivative at every positive integer order. -/
theorem birkhoff_minus_spectral_terminal_uniform_physical_Hm_ball (m : ℕ) (hm : 1 ≤ m) (R : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : realTypeHigherSobolevSourceLocus m,
      ‖sourcePiSobolevCoordinates m m le_rfl a.val‖ ≤ R →
      ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
        ∃ z : WeightedCoeff (Weight.sobolev (m+1)) 2,
          (∀ n, z.val n = sourceBirkhoffWeightedCoordinate (by simp) (by norm_num)
            n s (sign:ℂ) (higherSobolevSourceInclusion m a.val)-sourceGapWeightedEtaTerminalCoordinate
              (by simp) (by norm_num) n (sign:ℂ) (higherSobolevSourceInclusion m a.val)) ∧ ‖z‖ ≤ M := by
  obtain ⟨K,hK,hT⟩ := D.normalization_phase_multipliers_uniform_physical_H1_ball R
  obtain ⟨L,hL,hS⟩ := D.etaRemainder_phase_multipliers_uniform_physical_H1_ball R
  obtain ⟨A,hA,hgap⟩ := exists_sourceHmWeightedGapSequence_bound_on_physical_ball m hm R
  refine ⟨(2*K+L)*A,by positivity,?_⟩
  intro a ha sign hsign
  let b := realHigherSobolevToH1 m hm a
  have hb : ‖sourcePhysicalH1Coordinates b.val‖ ≤ R := by
    change ‖sourcePhysicalH1Coordinates (higherSobolevToH1 m hm a.val)‖ ≤ R
    rw [sourcePhysicalH1Coordinates_higherSobolevToH1]
    exact (norm_sourcePiSobolevCoordinates_mono m 1 m hm le_rfl hm a.val).trans ha
  have hbsource : sobolevSourceInclusion b.val = higherSobolevSourceInclusion m a.val :=
    sobolevSourceInclusion_higherSobolevToH1 m hm a.val
  have hs : (sign:ℂ) = 1 ∨ (sign:ℂ) = -1 := by rcases hsign with rfl | rfl <;> simp
  have habs : |sign| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  obtain ⟨T,hT,hnT⟩ := hT b hb 2 inferInstance m sign
  obtain ⟨S,hS,hnS⟩ := hS b hb 2 inferInstance m (-sign)
  let c := D.signedEtaHm m a (sign:ℂ) hs
  have hc : ‖c‖ ≤ A := (D.norm_signedEtaHm_le m a (sign:ℂ) hs).trans (hgap a ha)
  have ht : ‖T‖ ≤ 2*K := by simpa only [habs,show (1:ℝ)+1=2 by norm_num] using hnT
  have hu : ‖S‖ ≤ L := by simpa only [abs_neg,habs,one_mul] using hnS
  refine ⟨T c-S c,?_,?_⟩
  · intro n
    rw [WeightedCoeff.sub_val,hT,hS,hbsource]
    simp only [c,signedEtaHm_apply,Complex.ofReal_neg]
    rw [sourceGapWeightedEtaTerminalCoordinate_eq_inverse_phase (by simp) (by norm_num) n s]
    simp only [sourceBirkhoffWeightedCoordinate]
    ring
  · have htbound := (T.le_opNorm c).trans (mul_le_mul ht hc (norm_nonneg _) (by positivity))
    have hubound := (S.le_opNorm c).trans (mul_le_mul hu hc (norm_nonneg _) hL)
    exact (norm_sub_le (T c) (S c)).trans ((add_le_add htbound hubound).trans_eq (by ring))

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
