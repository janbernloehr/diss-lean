import NLS.SequenceSpaces.SignedPairActionProducts
import NLS.SequenceSpaces.MeanZeroSobolevInclusion

/-! Exact quadratic actions of signed normalized Sobolev coordinates. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

theorem quadraticActions_deletedToSignedPair_apply
    (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0) (k : ℤ) :
    quadraticActionsExponent (q := 1) (deletedToSignedPair e b) k=
      b.val (positiveIndexInjection e k)*b.val (-positiveIndexInjection e k) := by
  have h := signedPairToDeleted_product e (deletedToSignedPair e b) k
  rw [signedPairToDeleted_apply_inverse] at h
  exact h.symm

theorem quadraticActions_deletedToSignedPair_sobolevInclusion
    (e : ℤ ≃ ℕ+) {r s : ℝ} (h : r≤s) (b : DeletedCoeff 2 0) (k : ℤ) :
    quadraticActionsExponent (q := 1) (deletedToSignedPair e (WeightedCoeff.meanZeroSobolevInclusion h b)) k=
      ((Weight.sobolev r (positiveIndexInjection e k):ℂ)/(Weight.sobolev s (positiveIndexInjection e k):ℂ))^2*
        quadraticActionsExponent (q := 1) (deletedToSignedPair e b) k := by
  have hn : positiveIndexInjection e k≠0 := by
    have hp : 0<positiveIndexInjection e k := by
      dsimp only [positiveIndexInjection]
      exact_mod_cast (e k).pos
    omega
  rw [quadraticActions_deletedToSignedPair_apply,quadraticActions_deletedToSignedPair_apply]
  have he (j : ℤ) (hj : j≠0) : (WeightedCoeff.meanZeroSobolevInclusion h b).val j=
      (Weight.sobolev r j:ℂ)*(b.val j/(Weight.sobolev s j:ℂ)) := by
    change (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev r)
      (WeightedCoeff.sobolevInclusion h (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev s) b))).val j=_
    rw [WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj,
      WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.meanZeroWeightedLift_apply]
  rw [he _ hn,he _ (neg_ne_zero.mpr hn)]
  simp only [Weight.sobolev_apply,Int.cast_neg,abs_neg]
  ring

end NLS
