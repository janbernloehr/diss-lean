import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement
import NLS.ZakharovShabat.SourceCriticalSobolevDisplacement
import NLS.ZakharovShabat.ClassicalSobolevDiscriminantError
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds

/-! # The squared trace compared with its free value

The canonical squared discriminant has a uniform inverse-frequency error on original Sobolev balls and horizontal strips.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The squared canonical discriminant differs from its free value by
O(1/|z|), uniformly on original Hs balls and horizontal strips. No smooth
representative is assumed. -/
theorem exists_uniform_higherSobolev_discriminant_sq_free_strip_bound
    (s : ℕ) (hs : 1 ≤ s) (R H : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H →
      ‖(canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) z)^2-
        (freeDiscriminant z)^2‖ ≤ C/‖z‖ := by
  let A := 2*classicalSobolevErrorConstant (2*R) H
  let B := 2*Real.exp (H+8*R)
  have hA : 0 ≤ A := mul_nonneg (by norm_num) (classicalSobolevErrorConstant_nonneg _ _ (by positivity))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨A*(2*B+A),by positivity,?_⟩
  intro ab hab z hz hzH
  let a := higherSobolevOperatorDomain s hs ab
  have ha : ‖a‖ ≤ 2*R := (norm_higherSobolevOperatorDomain_le s hs ab).trans
    (mul_le_mul_of_nonneg_left hab (by norm_num))
  have he : canonicalDiscriminant (by norm_num) (periodOnePotential (higherSobolevSourceInclusion s ab)) =
      classicalDiscriminant (classicalSobolevPotential a) :=
    funext (canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _
      (physicalBase_source_sobolev_compatibility _ a (higherSobolevOperatorDomain_compatibility s hs ab)))
  rw [he]
  let d := classicalDiscriminant (classicalSobolevPotential a) z
  let f := freeDiscriminant z
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hz)
  have herr : ‖d-f‖ ≤ A/‖z‖ :=
    norm_classicalDiscriminant_sub_free_sobolev_strip_le (2*R) H a ha z hz0 hzH
  have hsmall : ‖d-f‖ ≤ A := herr.trans (div_le_self hA hz)
  have hd : ‖d‖ ≤ B := norm_classicalDiscriminant_le_of_bounds _ z (8*R) H
    ((norm_classicalSobolevPotential_le a).trans (by linarith)) hzH
  have hf : ‖f‖ ≤ B+A := by
    have h := norm_le_norm_add_norm_sub d f
    linarith
  have hsum : ‖d+f‖ ≤ 2*B+A := (norm_add_le _ _).trans (by linarith)
  change ‖d^2-f^2‖ ≤ _
  rw [show d^2-f^2 = (d-f)*(d+f) by ring,norm_mul]
  exact (mul_le_mul herr hsum (norm_nonneg _) (div_nonneg hA (norm_nonneg _))).trans_eq (by ring)

end NLS.ZakharovShabat
