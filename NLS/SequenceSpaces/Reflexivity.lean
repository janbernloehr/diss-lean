import NLS.SequenceSpaces.FullDuality
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Normed.Module.DoubleDual

/-! # Reflexivity of weighted coefficient spaces

The canonical evaluation map into the continuous double dual is surjective
for every exponent strictly between one and infinity. This uses both full
dual representations and preserves arbitrary positive weights.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

theorem bidual_surjective (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (Coeff p)) := by
  intro F
  let K : Coeff q →L[ℂ] ℂ := F.comp (Coeff.dualPairing (p := q) (q := p))
  let x : Coeff p := fullCotangent hq K
  refine ⟨x,?_⟩
  apply ContinuousLinearMap.ext
  intro L
  let a : Coeff q := fullCotangent hp L
  have hL : Coeff.dualPairing a = L := dualPairing_fullCotangent hp L
  have hK : Coeff.dualPairing x = K := dualPairing_fullCotangent hq K
  change L x = F L
  calc
    L x = Coeff.dualPairing a x := congrArg (fun G : Coeff p →L[ℂ] ℂ => G x) hL.symm
    _ = Coeff.dualPairing x a := by
      simp only [Coeff.dualPairing_apply]
      exact tsum_congr (fun n => mul_comm _ _)
    _ = K a := congrArg (fun G : Coeff q →L[ℂ] ℂ => G a) hK
    _ = F L := by change F (Coeff.dualPairing a) = F L; rw [hL]


end NLS.Coeff

namespace NLS.Coeff
theorem exists_finite_conjugate (p : ℝ≥0∞) (hp : 1 < p) :
    ∃ q : ℝ≥0∞, 1 ≤ q ∧ q ≠ ⊤ ∧ p.HolderConjugate q := by
  let q := (1 - p⁻¹)⁻¹
  have hi : p⁻¹ < 1 := by simpa using (ENNReal.inv_lt_inv).mpr hp
  have hpos : 0 < 1 - p⁻¹ := tsub_pos_iff_lt.mpr hi
  have he : p.HolderConjugate q := by
    apply ENNReal.holderConjugate_iff.mpr
    change p⁻¹ + ((1 - p⁻¹)⁻¹)⁻¹ = 1
    rw [inv_inv,add_tsub_cancel_of_le hi.le]
  let := he
  refine ⟨q,ENNReal.HolderConjugate.one_le q p,?_,he⟩
  exact ENNReal.inv_ne_top.mpr hpos.ne'

end NLS.Coeff

namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

theorem bidual_surjective_of_conjugate (w : Weight) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (WeightedCoeff w p)) := by
  intro F
  let e := (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv
  let F' := F.comp (e.toContinuousLinearMap.precomp ℂ)
  obtain ⟨x,hx⟩ := Coeff.bidual_surjective (q := q) hp hq F'
  refine ⟨e.symm x,?_⟩
  apply ContinuousLinearMap.ext
  intro L
  have h := congrArg (fun G : (Coeff p →L[ℂ] ℂ) →L[ℂ] ℂ =>
    G (L.comp e.symm.toContinuousLinearMap)) hx
  change L (e.symm x) = F L
  change L (e.symm x) = F ((L.comp e.symm.toContinuousLinearMap).comp e.toContinuousLinearMap) at h
  convert h using 1
  congr 1
  ext z
  simp [e]


end NLS.WeightedCoeff

namespace NLS.WeightedCoeff

/-- The scalar Fourier-Lebesgue space is reflexive in the full printed range. -/
theorem bidual_surjective (w : Weight) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpfin : p ≠ ⊤) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℂ (WeightedCoeff w p)) := by
  obtain ⟨q,hq,hqfin,hpq⟩ := Coeff.exists_finite_conjugate p hp
  let : Fact (1 ≤ q) := ⟨hq⟩
  let := hpq
  exact bidual_surjective_of_conjugate (q := q) w hpfin hqfin

end NLS.WeightedCoeff
