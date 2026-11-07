import NLS.KdV.HillRotatedDiracSource
import NLS.ZakharovShabat.SourceHillWeightedTerminalModel
import NLS.ZakharovShabat.SourceSignedTerminalOneSmoothing
import NLS.SequenceSpaces.SobolevToSignedHalfLift

/-! The literal phase-diagonal Dirac Fourier map sends an H2 scalar
remainder to native signed H3/2. Its central coefficient vanishes, so
an original constant Miura energy shift contributes nothing. -/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.KdV

private def diagonalTerminalSymbol (k : ℤ) : ℂ :=
  if 0 < k then 2 * I else if k < 0 then -2 * I else 0

private theorem diagonalTerminalSymbol_bound (k : ℤ) :
    Weight.sobolev (1+1) k * ‖diagonalTerminalSymbol k‖ ≤ 2 * Weight.sobolev (1+1) k := by
  unfold diagonalTerminalSymbol
  split_ifs <;> norm_num [norm_mul, norm_neg, Complex.norm_I] <;>
    nlinarith [(Weight.sobolev (1+1)).positive k]

def hillMiuraH2TerminalFourier : WeightedCoeff (Weight.sobolev (1+1)) 2 →L[ℂ]
    WeightedCoeff (Weight.signedSobolev (3/2)) 2 :=
  sourceHillTerminalScale •
    ((WeightedCoeff.sobolevToSignedHalfLift (1+1) (3/2) (by norm_num) (by norm_num) 2).comp
      (WeightedCoeff.weightedMultiplierCLM _ _ diagonalTerminalSymbol 2 (by norm_num)
        diagonalTerminalSymbol_bound))

theorem hillMiuraH2TerminalFourier_apply (a : WeightedCoeff (Weight.sobolev (1+1)) 2) (k : ℤ) :
    (hillMiuraH2TerminalFourier a).val k =
      sourceHillTerminalScale * (Weight.signedSobolev (-1/2) k : ℂ)⁻¹ *
        (if 0 < k then 2 * I else if k < 0 then -2 * I else 0) * a.val k := by
  change sourceHillTerminalScale * ((Weight.signedSobolev (-1/2) k : ℂ)⁻¹ *
    (diagonalTerminalSymbol k * a.val k)) = _
  unfold diagonalTerminalSymbol
  ring

private theorem signedFourier_phase_diagonal (v : Coeff 2) (k : ℤ) :
    sourceSignedTerminalFourier (sourcePhase (hillMiuraDiagonal v)) k =
      diagonalTerminalSymbol k * v k := by
  rcases lt_trichotomy 0 k with hk | hk | hk
  · rw [sourceSignedTerminalFourier_positive _ k hk, sourcePhase_snd, hillMiuraDiagonal_snd]
    simp only [diagonalTerminalSymbol, if_pos hk, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  · subst k
    rw [sourceSignedTerminalFourier_zero]
    simp only [diagonalTerminalSymbol, lt_self_iff_false, ite_false, zero_mul]
  · rw [sourceSignedTerminalFourier_negative _ k hk, sourcePhase_fst, hillMiuraDiagonal_fst]
    simp only [diagonalTerminalSymbol, if_neg (not_lt_of_ge hk.le), if_pos hk,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring

theorem hillMiuraH2TerminalFourier_eq_actual
    (a : WeightedCoeff (Weight.sobolev (1+1)) 2) (v : Coeff 2)
    (hv : ∀ j : ℤ, j ≠ 0 → v j = a.val j) (k : ℤ) :
    (hillMiuraH2TerminalFourier a).val k =
      (sourceHillTerminalFourier (sourcePhase (hillMiuraDiagonal v))).val k := by
  let w := (Weight.signedSobolev (-1/2) k : ℂ)
  have hw : w ≠ 0 := (Weight.signedSobolev (-1/2)).complex_ne_zero k
  have hf := sourceHillTerminalFourier_weighted_apply (sourcePhase (hillMiuraDiagonal v)) k
  change w * (sourceHillTerminalFourier (sourcePhase (hillMiuraDiagonal v))).val k = _ at hf
  rw [signedFourier_phase_diagonal] at hf
  have he : diagonalTerminalSymbol k * a.val k = diagonalTerminalSymbol k * v k := by
    by_cases hk : k = 0
    · simp only [hk, diagonalTerminalSymbol, lt_self_iff_false, ite_false, zero_mul]
    · rw [hv k hk]
  apply mul_left_cancel₀ hw
  rw [hf, hillMiuraH2TerminalFourier_apply]
  change w * (sourceHillTerminalScale * w⁻¹ * diagonalTerminalSymbol k * a.val k) = _
  calc
    _ = sourceHillTerminalScale * (diagonalTerminalSymbol k * a.val k) := by field_simp
    _ = _ := by rw [he]

theorem hillMiuraH2TerminalFourier_eq_difference
    (a : WeightedCoeff (Weight.sobolev (1+1)) 2) (u v : Coeff 2)
    (h : ∀ j : ℤ, j ≠ 0 → u j - v j = a.val j) (k : ℤ) :
    (hillMiuraH2TerminalFourier a).val k =
      (sourceHillTerminalFourier (sourcePhase (hillMiuraDiagonal u))).val k -
        (sourceHillTerminalFourier (sourcePhase (hillMiuraDiagonal v))).val k := by
  have he := hillMiuraH2TerminalFourier_eq_actual a (u-v) (by
    intro j hj
    simpa only [lp.coeFn_sub, Pi.sub_apply] using h j hj) k
  simpa only [map_sub, WeightedCoeff.sub_val] using he

end NLS.KdV
