import NLS.KdV.PseudomeasureAnalytic
import NLS.KdV.SingularHillBilinear
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant

/-! # Equal diagonals for the singular endpoint Hill reduction

The full original H1 reconstruction satisfies the physical spectral pencil
with exactly its two resonant residuals. Applying the singular Green identity
shows that the actual effective matrix has equal diagonal corrections, for
complex as well as real endpoint potentials.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The shared resonant coordinates agree with the actual normalized physical modes. -/
theorem endpointHillH1Modes_eq (n : ℕ) (u : ℂ × ℂ) :
    endpointHillH1Modes n u =
      u.1 • ofSmooth 1 2 (mode (n:ℤ)) + u.2 • ofSmooth 1 2 (mode (-(n:ℤ))) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change _ = u.1 * (ofSmooth 1 2 (mode (n:ℤ))).val (mode (-k)) +
    u.2 * (ofSmooth 1 2 (mode (-(n:ℤ)))).val (mode (-k))
  simp only [endpointHillH1Modes_coefficient, ofSmooth_h1_mode_coefficient,
    mul_ite, mul_one, mul_zero]

/-- An original unit mode evaluates the opposite Fourier coordinate in the bilinear pairing. -/
theorem singularHillPairing_mode (k : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillDomainInclusion (ofSmooth 1 2 (mode k))) f =
      f.val (mode k) := by
  rw [singularHillDomainInclusion_bilinear]
  simp only [singularHillPairing, sobolevDualIsometry_ofSmooth, singularHillDomainInclusion_val]

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The finite resonant residual in the actual original H-minus-one target. -/
def endpointHillResonantResidual (u : ℂ × ℂ) : FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillDomainInclusion (endpointHillH1Modes n
    (endpointHillReducedOperator r hr hr1 n hn z hz q hs u))

/-- Every reconstructed amplitude solves the full physical equation with its actual finite residual. -/
theorem endpointHillReconstruct_residual_equation (u : ℂ × ℂ) :
    z • singularHillDomainInclusion (endpointHillReconstruct r hr hr1 n hn z hz q hs u) -
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q)
        (endpointHillReconstruct r hr hr1 n hn z hz q hs u) =
      endpointHillResonantResidual r hr hr1 n hn z hz q hs u := by
  have hp := endpointH1Multiplication_physical r hr hr1 q
    (endpointHillReconstruct r hr hr1 n hn z hz q hs u)
  rw [endpointH1Multiplication_reconstruct r hr hr1 n hn z hz q hs u] at hp
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change z * (singularHillDomainInclusion _).val (mode (-k)) -
    ((singularHillLaplacian _).val (mode (-k)) +
      (hminusOneMultiplication _ _).val (mode (-k))) = _
  rw [singularHillDomainInclusion_coefficient, singularHillLaplacian_coefficient, ← hp,
    endpointHillHminusOne_coefficient]
  change _ = (singularHillDomainInclusion (endpointHillH1Modes n
    (endpointHillReducedOperator r hr hr1 n hn z hz q hs u))).val (mode (-k))
  rw [singularHillDomainInclusion_coefficient, endpointHillH1Modes_coefficient,
    endpointHillReconstruct_coefficient]
  by_cases hkp : k = (n:ℤ)
  · subst k
    simp [reducedHillSymbol, show (n:ℤ) ≠ -(n:ℤ) by omega]
    change z*u.1 - ((freeHillValue n:ℂ)*u.1 +
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val n) =
      (z-(freeHillValue n:ℂ))*u.1 -
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val n
    ring
  by_cases hkm : k = -(n:ℤ)
  · subst k
    simp [reducedHillSymbol, show -(n:ℤ) ≠ (n:ℤ) by omega]
    change z*u.2 - ((freeHillValue n:ℂ)*u.2 +
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val (-(n:ℤ))) =
      (z-(freeHillValue n:ℂ))*u.2 -
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs u).val (-(n:ℤ))
    ring
  have hk : k.natAbs ≠ n := fun he => ((hill_resonance_iff n k).mp he).elim hkp hkm
  simp only [if_neg hkp, if_neg hkm, zero_add, reducedHillSymbol, if_neg hk]
  have hd := freeHill_denominator_ne_zero hn hz hk
  field_simp [hd]
  ring

/-- Pairing the finite residual with reconstruction gives the off-diagonal two-mode pairing. -/
theorem endpointHillPairing_residual (u v : ℂ × ℂ) :
    singularHillPairing (endpointHillResonantResidual r hr hr1 n hn z hz q hs u)
      (endpointHillReconstruct r hr hr1 n hn z hz q hs v) =
      (endpointHillReducedOperator r hr hr1 n hn z hz q hs u).1*v.2 +
        (endpointHillReducedOperator r hr hr1 n hn z hz q hs u).2*v.1 := by
  unfold endpointHillResonantResidual
  rw [endpointHillH1Modes_eq, map_add, map_smul, map_smul,
    singularHillPairing_add_left, singularHillPairing_smul_left, singularHillPairing_smul_left,
    singularHillPairing_mode, singularHillPairing_mode]
  have hp := congrArg Prod.fst (endpointHillH1Coordinates_reconstruct r hr hr1 n hn z hz q hs v)
  have hm := congrArg Prod.snd (endpointHillH1Coordinates_reconstruct r hr hr1 n hn z hz q hs v)
  change (endpointHillReconstruct r hr hr1 n hn z hz q hs v).val (mode (-(n:ℤ))) = v.1 at hp
  change (endpointHillReconstruct r hr hr1 n hn z hz q hs v).val (mode (-(-(n:ℤ)))) = v.2 at hm
  simp only [neg_neg] at hm
  rw [hp, hm]

/-- The effective endpoint matrix inherits the physical bilinear Green symmetry. -/
theorem endpointHillReduced_bilinearSymmetry (u v : ℂ × ℂ) :
    (endpointHillReducedOperator r hr hr1 n hn z hz q hs u).1*v.2 +
      (endpointHillReducedOperator r hr hr1 n hn z hz q hs u).2*v.1 =
    (endpointHillReducedOperator r hr hr1 n hn z hz q hs v).1*u.2 +
      (endpointHillReducedOperator r hr hr1 n hn z hz q hs v).2*u.1 := by
  have he := singularHillPencil_bilinear (endpointHillHminusOne SpectralWeight.one r hr1 q) z
    (endpointHillReconstruct r hr hr1 n hn z hz q hs u)
    (endpointHillReconstruct r hr hr1 n hn z hz q hs v)
  rw [endpointHillReconstruct_residual_equation, endpointHillReconstruct_residual_equation,
    endpointHillPairing_residual, endpointHillPairing_residual] at he
  exact he

/-- Equality of the actual diagonal corrections, with no reality assumption on q. -/
theorem endpointHillEffectivePotential_diagonals_eq :
    (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val n =
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val (-(n:ℤ)) := by
  have he := endpointHillReduced_bilinearSymmetry r hr hr1 n hn z hz q hs (1,0) (0,1)
  simp only [mul_one, mul_zero, add_zero, zero_add] at he
  change (z-(freeHillValue n:ℂ))*1 -
    (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)).val n =
      (z-(freeHillValue n:ℂ))*1 -
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)).val (-(n:ℤ)) at he
  linear_combination -he

end NLS.KdV
