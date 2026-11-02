import NLS.KdV.HillWeightedCoefficients
import NLS.SequenceSpaces.Pairing
import NLS.SequenceSpaces.Reflection

/-!
# The complex bilinear symmetry behind the equal Hill diagonals

The pairing is the physical bilinear product integral, not a Hermitian
pairing: the second Fourier index is reversed and there is no conjugation.
Absolute convergence comes from the existing coefficient duality proofs.
Literal convolution and the even free symbol give the Green identity for
the reconstructed solutions, hence symmetry of the effective two-mode
operator with respect to the off-diagonal pairing.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

private theorem summable_bilinear_coefficients (a : Coeff 2) (b : Coeff 1) :
    Summable (fun k : ℤ => a k*b (-k)) := by
  simpa only [lp.star_apply, Coeff.reflection_apply, starRingEnd_apply, star_star] using
    (Coeff.summable_norm_pairing a (star (Coeff.reflection b))).of_norm

set_option maxHeartbeats 800000 in
private theorem convolution_bilinear_symmetric (q : Coeff 2) (f g : Coeff 1) :
    (∑' k : ℤ, Coeff.convolution q f k*g (-k)) =
      ∑' k : ℤ, Coeff.convolution q g k*f (-k) := by
  have hs : Summable (fun nk : ℤ × ℤ => q (nk.1-nk.2)*f nk.2*g (-nk.1)) := by
    simpa only [lp.star_apply, Coeff.reflection_apply, starRingEnd_apply, star_star] using
      Coeff.summable_convolution_pairing q f (star (Coeff.reflection g))
  simp only [Coeff.convolution_apply, ← tsum_mul_right]
  calc
    _ = ∑' k : ℤ, ∑' j : ℤ, q (j-k)*f k*g (-j) := hs.tsum_comm.symm
    _ = ∑' k : ℤ, ∑' j : ℤ, q (-k-j)*g j*f k := by
      apply tsum_congr
      intro k
      rw [← (Equiv.neg ℤ).tsum_eq (fun j : ℤ => q (-k-j)*g j*f k)]
      apply tsum_congr
      intro j
      simp only [Equiv.neg_apply]
      rw [show -k - -j = j-k by ring]
      ring
    _ = _ := by
      simpa only [Equiv.neg_apply, neg_neg] using
        (Equiv.neg ℤ).tsum_eq (fun k : ℤ => ∑' j : ℤ, q (k-j)*g j*f (-k))

/-- The physical complex bilinear Fourier pairing. -/
def hillBilinear (w : SpectralWeight) (a : WeightedCoeff w.toWeight 2)
    (b : WeightedCoeff w.toWeight 1) : ℂ := ∑' k : ℤ, a.val k*b.val (-k)

theorem summable_hillBilinear (w : SpectralWeight) (a : WeightedCoeff w.toWeight 2)
    (b : WeightedCoeff w.toWeight 1) : Summable (fun k : ℤ => a.val k*b.val (-k)) := by
  simpa only [SpectralWeight.toCoeff_apply] using
    summable_bilinear_coefficients (w.toCoeff a) (w.toCoeff b)

theorem hillBilinear_add_left (w : SpectralWeight) (a c : WeightedCoeff w.toWeight 2)
    (b : WeightedCoeff w.toWeight 1) :
    hillBilinear w (a+c) b = hillBilinear w a b+hillBilinear w c b := by
  unfold hillBilinear
  simp only [WeightedCoeff.add_val, add_mul]
  exact (summable_hillBilinear w a b).tsum_add (summable_hillBilinear w c b)

theorem hillBilinear_single (w : SpectralWeight) (k : ℤ) (c : ℂ)
    (b : WeightedCoeff w.toWeight 1) :
    hillBilinear w (WeightedCoeff.single w.toWeight k c) b = c*b.val (-k) := by
  simp [hillBilinear, WeightedCoeff.single_val, Pi.single_apply]

theorem hillBilinear_convolution_symmetric (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (f g : WeightedCoeff w.toWeight 1) :
    hillBilinear w (w.convolution q f) g = hillBilinear w (w.convolution q g) f := by
  have h := convolution_bilinear_symmetric (w.toCoeff q) (w.toCoeff f) (w.toCoeff g)
  rw [← w.toCoeff_convolution, ← w.toCoeff_convolution] at h
  simpa only [hillBilinear, SpectralWeight.toCoeff_apply] using h

variable (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
  (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
  (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- The residual of a reconstructed vector lives on the actual two resonant modes. -/
def hillResonantResidual (u : ℂ × ℂ) : WeightedCoeff w.toWeight 2 :=
  WeightedCoeff.single w.toWeight (n : ℤ) (hillReducedOperator w q n hn z hz hcut u).1 +
    WeightedCoeff.single w.toWeight (-(n : ℤ)) (hillReducedOperator w q n hn z hz hcut u).2

theorem hillResonantResidual_apply (u : ℂ × ℂ) (k : ℤ) :
    (hillResonantResidual w q n hn z hz hcut u).val k =
      (if k = (n : ℤ) then (hillReducedOperator w q n hn z hz hcut u).1 else 0) +
      (if k = -(n : ℤ) then (hillReducedOperator w q n hn z hz hcut u).2 else 0) := by
  simp [hillResonantResidual, WeightedCoeff.single_val, Pi.single_apply]

/-- Reconstruction satisfies the full equation with precisely its finite residual. -/
theorem hillReconstruct_residual_equation (u : ℂ × ℂ) (k : ℤ) :
    (z-(freeHillValue k : ℂ))*(hillReconstruct w q n hn z hz hcut u).val k =
      (hillEffectivePotential w q n hn z hz hcut u).val k +
        (hillResonantResidual w q n hn z hz hcut u).val k := by
  by_cases hkp : k = (n : ℤ)
  · subst k
    have hr := congrArg Prod.fst (hillModeCoordinates_reconstruct w q n hn z hz hcut u)
    change (hillReconstruct w q n hn z hz hcut u).val n = u.1 at hr
    rw [hr, hillResonantResidual_apply, if_pos rfl,
      if_neg (show (n : ℤ) ≠ -(n : ℤ) by omega), add_zero]
    change (z-(freeHillValue n : ℂ))*u.1 =
      (hillEffectivePotential w q n hn z hz hcut u).val n +
        ((z-(freeHillValue n : ℂ))*u.1-(hillEffectivePotential w q n hn z hz hcut u).val n)
    ring
  by_cases hkm : k = -(n : ℤ)
  · subst k
    have hr := congrArg Prod.snd (hillModeCoordinates_reconstruct w q n hn z hz hcut u)
    change (hillReconstruct w q n hn z hz hcut u).val (-(n : ℤ)) = u.2 at hr
    rw [hr, freeHillValue_neg, hillResonantResidual_apply,
      if_neg (show -(n : ℤ) ≠ (n : ℤ) by omega), if_pos rfl, zero_add]
    change (z-(freeHillValue n : ℂ))*u.2 =
      (hillEffectivePotential w q n hn z hz hcut u).val (-(n : ℤ)) +
        ((z-(freeHillValue n : ℂ))*u.2-(hillEffectivePotential w q n hn z hz hcut u).val (-(n : ℤ)))
    ring
  have hk : k.natAbs ≠ n := fun h => (Int.natAbs_eq_iff.mp h).elim hkp hkm
  rw [hillResonantResidual_apply, if_neg hkp, if_neg hkm, zero_add, add_zero]
  change (z-(freeHillValue k : ℂ)) * ((hillModes w.toWeight n u).val k +
    (hillComplementToL1 w.toWeight n hn z hz (hillEffectivePotential w q n hn z hz hcut u)).val k) = _
  rw [hillModes_apply, if_neg hkp, if_neg hkm, zero_add, zero_add,
    hillComplementToL1_apply, if_neg hk, ← mul_assoc,
    mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

theorem hillBilinear_residual (u v : ℂ × ℂ) :
    hillBilinear w (hillResonantResidual w q n hn z hz hcut u)
      (hillReconstruct w q n hn z hz hcut v) =
      (hillReducedOperator w q n hn z hz hcut u).1*v.2 +
        (hillReducedOperator w q n hn z hz hcut u).2*v.1 := by
  rw [hillResonantResidual, hillBilinear_add_left, hillBilinear_single, hillBilinear_single]
  have hp := congrArg Prod.fst (hillModeCoordinates_reconstruct w q n hn z hz hcut v)
  have hm := congrArg Prod.snd (hillModeCoordinates_reconstruct w q n hn z hz hcut v)
  change (hillReconstruct w q n hn z hz hcut v).val n = v.1 at hp
  change (hillReconstruct w q n hn z hz hcut v).val (-(n : ℤ)) = v.2 at hm
  simp only [neg_neg]
  rw [hp, hm]

theorem hillReduced_bilinearSymmetry (u v : ℂ × ℂ) :
    (hillReducedOperator w q n hn z hz hcut u).1*v.2 +
      (hillReducedOperator w q n hn z hz hcut u).2*v.1 =
    (hillReducedOperator w q n hn z hz hcut v).1*u.2 +
      (hillReducedOperator w q n hn z hz hcut v).2*u.1 := by
  have hg : hillBilinear w
      (hillEffectivePotential w q n hn z hz hcut u + hillResonantResidual w q n hn z hz hcut u)
      (hillReconstruct w q n hn z hz hcut v) = hillBilinear w
      (hillEffectivePotential w q n hn z hz hcut v + hillResonantResidual w q n hn z hz hcut v)
      (hillReconstruct w q n hn z hz hcut u) := by
    unfold hillBilinear
    rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
      (hillEffectivePotential w q n hn z hz hcut v + hillResonantResidual w q n hn z hz hcut v).val k *
        (hillReconstruct w q n hn z hz hcut u).val (-k))]
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply, neg_neg, WeightedCoeff.add_val]
    rw [← hillReconstruct_residual_equation w q n hn z hz hcut u k,
      ← hillReconstruct_residual_equation w q n hn z hz hcut v (-k), freeHillValue_neg]
    ring
  have hp := hillBilinear_convolution_symmetric w q
    (hillReconstruct w q n hn z hz hcut u) (hillReconstruct w q n hn z hz hcut v)
  rw [convolution_hillReconstruct, convolution_hillReconstruct] at hp
  rw [hillBilinear_add_left, hillBilinear_add_left, hp] at hg
  have he := add_left_cancel hg
  rwa [hillBilinear_residual, hillBilinear_residual] at he

/-- Both diagonal corrections coincide for complex potentials as well as real ones. -/
theorem hillDiagonal_eq_opposite :
    hillDiagonal w q n hn z hz hcut = hillOppositeDiagonal w q n hn z hz hcut := by
  have he := hillReduced_bilinearSymmetry w q n hn z hz hcut (1,0) (0,1)
  simp only [mul_one, mul_zero, add_zero, zero_add] at he
  unfold hillDiagonal hillOppositeDiagonal
  rw [hillCorrectedMode_pos, hillCorrectedMode_neg]
  change (z-(freeHillValue n : ℂ))*1 -
      (hillEffectivePotential w q n hn z hz hcut (1,0)).val n =
    (z-(freeHillValue n : ℂ))*1 -
      (hillEffectivePotential w q n hn z hz hcut (0,1)).val (-(n : ℤ)) at he
  linear_combination -he

end NLS.KdV
