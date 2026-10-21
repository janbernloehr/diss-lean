import NLS.SequenceSpaces.HolderEmbedding

/-! # The critical negative-half Sobolev inclusion

This implements the finite-exponent inclusion from the introduction, printed p. 10.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The finite Hölder multiplier exponent for ell^p into H^(-1/2). -/
def criticalHolderExponent (p : ℝ) : ℝ := 1/(1/2-1/p)

theorem criticalHolderExponent_gt_two {p : ℝ} (hp : 2 < p) :
    2 < criticalHolderExponent p := by
  have hppos : 0 < p := by linarith
  have hd : 0 < 1/2-1/p := sub_pos.mpr
    (one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<2) hp)
  rw [criticalHolderExponent,lt_div_iff₀ hd]
  have h := one_div_pos.mpr hppos
  nlinarith

theorem criticalHolderTriple {p : ℝ} (hp : 2 < p) :
    (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal (criticalHolderExponent p)) 2 := by
  have hppos : 0 < p := by linarith
  have hrpos : 0 < criticalHolderExponent p := lt_trans (by norm_num) (criticalHolderExponent_gt_two hp)
  rw [ENNReal.holderTriple_iff]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_inv_of_pos hppos,← ENNReal.ofReal_inv_of_pos hrpos,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (inv_nonneg.mpr hppos.le) (inv_nonneg.mpr hrpos.le)]
  congr 1
  simp [criticalHolderExponent,one_div]

namespace Coeff
/-- Every finite exponent above two embeds continuously into the critical
negative-half Sobolev coefficient space, without changing any coefficient. -/
def criticalSobolevInclusion (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 2 < p) :
    Coeff (ENNReal.ofReal p) →L[ℂ] WeightedCoeff (Weight.sobolev (-1/2)) 2 := by
  let r := ENNReal.ofReal (criticalHolderExponent p)
  letI : Fact (1 ≤ r) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show 1 ≤ criticalHolderExponent p by
      linarith [criticalHolderExponent_gt_two hp])⟩
  letI : (ENNReal.ofReal p).HolderTriple r 2 := criticalHolderTriple hp
  have ht : 1 < (0-(-1/2:ℝ))*r.toReal := by
    rw [show r.toReal = criticalHolderExponent p from
      ENNReal.toReal_ofReal (by linarith [criticalHolderExponent_gt_two hp])]
    linarith [criticalHolderExponent_gt_two hp]
  exact (WeightedCoeff.sobolevHolderInclusion (p := ENNReal.ofReal p) (r := r) (q := 2)
    0 (-1/2) ENNReal.ofReal_ne_top ht).comp
    (WeightedCoeff.weightIsometry (Weight.sobolev 0) (ENNReal.ofReal p)).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem criticalSobolevInclusion_apply (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 2 < p) (a : Coeff (ENNReal.ofReal p)) (n : ℤ) :
    (criticalSobolevInclusion p hp a).val n = a n := by
  let : Fact (1 ≤ ENNReal.ofReal (criticalHolderExponent p)) := ⟨by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show 1 ≤ criticalHolderExponent p by
      linarith [criticalHolderExponent_gt_two hp])⟩
  let : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal (criticalHolderExponent p)) 2 :=
    criticalHolderTriple hp
  unfold criticalSobolevInclusion
  rw [ContinuousLinearMap.comp_apply,WeightedCoeff.sobolevHolderInclusion_apply]
  change a n / ((Weight.sobolev 0 n : ℝ) : ℂ) = a n
  simp

end Coeff
end NLS
