import NLS.ZakharovShabat.SourceDirichletTerminalFourierSmoothing
import NLS.ZakharovShabat.SourceSignedTerminalSequence
import NLS.SequenceSpaces.WeightedSignedPositiveSplice

/-! The actual signed Hill terminal sequence has an analytic Fourier
defect gaining one order at every positive integer source order.
Both selected positive labels and the original zero mode are retained. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceSignedTerminalFourier_zero (ψ : CoeffPair 2) : sourceSignedTerminalFourier ψ 0 = 0 := by
  change Coeff.signedPositiveSplice
    (sourceGapWeightedEtaTerminalFourier 1 ψ, sourceGapWeightedEtaTerminalFourier (-1) ψ) 0 = 0
  exact Coeff.signedPositiveSplice_zero _ _

def sourceSignedTerminalFourierRemainder (m : ℕ) (b : SobolevSource m) :
    WeightedCoeff (Weight.sobolev ((m : ℝ) + 1)) 2 :=
  WeightedCoeff.signedPositiveSplice _ 2
    (sourceTerminalFourierRemainder m 1 b, sourceTerminalFourierRemainder m (-1) b)

theorem exists_local_sourceSignedTerminalFourierRemainder_analytic
    (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    ∃ U : Set (SobolevSource m), IsOpen U ∧ a.val ∈ U ∧
      AnalyticOnNhd ℂ (sourceSignedTerminalFourierRemainder m) U ∧
        ∀ b ∈ U, ∀ k : ℤ, (sourceSignedTerminalFourierRemainder m b).val k =
          sourceSignedTerminalSequence (higherSobolevSourceInclusion m b) k -
            sourceSignedTerminalFourier (higherSobolevSourceInclusion m b) k := by
  obtain ⟨V,hV,haV,hR⟩ := exists_local_sourceTerminalFourierRemainder_analytic m hm a
  obtain ⟨W,hW,hreal,_,hT⟩ := exists_sourceSignedTerminalSequence_compact_derivative_domain
  let L := higherSobolevSourceInclusion m
  let U := V ∩ L ⁻¹' W
  have hU : IsOpen U := hV.inter (hW.preimage L.continuous)
  refine ⟨U,hU,⟨haV,hreal a.property⟩,?_,?_⟩
  · intro b hb
    have hp : AnalyticAt ℂ (fun c : SobolevSource m =>
        (sourceTerminalFourierRemainder m 1 c, sourceTerminalFourierRemainder m (-1) c)) b :=
      ((hR 1).1 b hb.1).prod ((hR (-1)).1 b hb.1)
    exact ((WeightedCoeff.signedPositiveSplice (Weight.sobolev ((m : ℝ) + 1)) 2).analyticAt _).comp hp
  · intro b hb k
    rcases lt_trichotomy 0 k with hk | hk | hk
    · rw [(hT (L b) hb.2).1 k hk, sourceSignedTerminalFourier_positive _ k hk]
      rw [sourceSignedTerminalFourierRemainder,
        WeightedCoeff.signedPositiveSplice_positive _ _ _ _ k hk, (hR 1).2 b hb.1 k,
        sourceGapWeightedEtaTerminalFourier_apply]
      ring
    · subst k
      rw [sourceSignedTerminalSequence_zero, sourceSignedTerminalFourier_zero,
        sourceSignedTerminalFourierRemainder, WeightedCoeff.signedPositiveSplice_zero, sub_self]
    · rw [(hT (L b) hb.2).2.1 k hk, sourceSignedTerminalFourier_negative _ k hk]
      rw [sourceSignedTerminalFourierRemainder,
        WeightedCoeff.signedPositiveSplice_negative _ _ (by
          intro j
          simp only [Weight.sobolev_apply, Int.cast_neg, abs_neg]) _ _ k hk,
        (hR (-1)).2 b hb.1 (-k), sourceGapWeightedEtaTerminalFourier_apply, neg_neg]
      ring

end NLS.ZakharovShabat
