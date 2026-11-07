import NLS.ZakharovShabat.SourceNormalizedMidpointSymbol
import NLS.SequenceSpaces.SobolevEvenReciprocal

/-! The actual normalized midpoint minus one is analytic in H1 already
on the original complex L2 source domain. The original pi*n divisor,
even signed labels and zero central defect are unchanged. -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

theorem sourcePositiveNormalizedMidpoint_sub_one_eq_displacement
    (n : ℕ+) (ψ : CoeffPair 2) :
    sourcePositiveNormalizedMidpoint (by simp) (by norm_num) n ψ - 1 =
      sourcePeriodicMidpointDisplacement (by simp) (by norm_num) ψ ((n : ℕ) : ℤ) /
        ((Real.pi : ℂ) * (n : ℕ)) := by
  simp only [sourcePositiveNormalizedMidpoint, sourcePeriodicMidpointDisplacement_apply,
    Int.cast_natCast]
  have hn : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

def sourceNormalizedMidpointSobolevRemainder (ψ : CoeffPair 2) :
    WeightedCoeff (Weight.sobolev 1) 2 :=
  Coeff.sobolevEvenReciprocal 2 (sourcePeriodicMidpointDisplacement (by simp) (by norm_num) ψ)

namespace SourceLemma12_12Data
variable {W₀ W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem normalized_midpoint_one_smoothing
    (H : SourceLemma12_12Data (by simp) (by norm_num) W₀ W s) :
    AnalyticOnNhd ℂ sourceNormalizedMidpointSobolevRemainder W ∧
      ∀ ψ ∈ W, ∀ k : ℤ, (sourceNormalizedMidpointSobolevRemainder ψ).val k =
        sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ k - 1 := by
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact ((Coeff.sobolevEvenReciprocal 2).analyticAt _).comp
      (H.periodic_midpoint_displacement_analytic ψ hψ)
  · intro ψ hψ k
    rw [sourceNormalizedMidpointSobolevRemainder, Coeff.sobolevEvenReciprocal_apply,
      H.normalized_midpoint_symbol_data.1 ψ hψ k]
    by_cases hk : k = 0
    · simp [hk, Coeff.evenUnitExtension]
    · simp only [if_neg hk, Coeff.evenUnitExtension, dif_neg hk]
      exact (sourcePositiveNormalizedMidpoint_sub_one_eq_displacement
        ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩ ψ).symm

end SourceLemma12_12Data

theorem exists_sourceNormalizedMidpoint_one_smoothing_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      AnalyticOnNhd ℂ sourceNormalizedMidpointSobolevRemainder W ∧
      ∀ ψ ∈ W, ∀ k : ℤ, (sourceNormalizedMidpointSobolevRemainder ψ).val k =
        sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ k - 1 := by
  obtain ⟨W₀,_,_,_,W,hW,_,hreal,s,H⟩ := sourceLemma12_12 (p := 2) (by simp) (by norm_num)
  exact ⟨W,hW,hreal,H.normalized_midpoint_one_smoothing.1,H.normalized_midpoint_one_smoothing.2⟩

end NLS.ZakharovShabat
