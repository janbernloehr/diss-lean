import NLS.Poisson.HminusGardnerBracket
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.Poisson

/-- Leibniz for the genuine scalar H-minus-one Gardner bracket. -/
theorem hminusGardnerBracket_mul_left (F H G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (hF : DifferentiableAt ℂ F q) (hH : DifferentiableAt ℂ H q) :
    hminusGardnerBracket (fun a => F a * H a) G q =
      F q * hminusGardnerBracket H G q + H q * hminusGardnerBracket F G q := by
  unfold hminusGardnerBracket hminusScalarGradient
  rw [fderiv_fun_mul hF hH]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]

theorem hminusGardnerBracket_mul_right (F G H : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (hG : DifferentiableAt ℂ G q) (hH : DifferentiableAt ℂ H q) :
    hminusGardnerBracket F (fun a => G a * H a) q =
      G q * hminusGardnerBracket F H q + H q * hminusGardnerBracket F G q := by
  rw [hminusGardnerBracket_antisymm,hminusGardnerBracket_mul_left G H F q hG hH,
    hminusGardnerBracket_antisymm H F,hminusGardnerBracket_antisymm G F]
  ring

/-- A pointwise differential identity transfers to the actual bracket. -/
theorem hminusGardnerBracket_of_fderiv_smul_left
    (F A G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (q : WeightedCoeff (Weight.sobolev (-1)) 2) (c : ℂ)
    (he : fderiv ℂ F q = c • fderiv ℂ A q) :
    hminusGardnerBracket F G q = c * hminusGardnerBracket A G q := by
  unfold hminusGardnerBracket hminusScalarGradient
  rw [he]
  simp only [map_smul,smul_apply,smul_eq_mul]

theorem hminusGardnerBracket_of_fderiv_smul_right
    (F G A : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (q : WeightedCoeff (Weight.sobolev (-1)) 2) (c : ℂ)
    (he : fderiv ℂ G q = c • fderiv ℂ A q) :
    hminusGardnerBracket F G q = c * hminusGardnerBracket F A q := by
  rw [hminusGardnerBracket_antisymm,hminusGardnerBracket_of_fderiv_smul_left G A F q c he,
    hminusGardnerBracket_antisymm A F]
  ring

/-- Products commute when every factor in one product commutes with
both factors in the other, with the actual Fréchet derivatives used. -/
theorem hminusGardnerBracket_products_zero
    (A F B G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hA : DifferentiableAt ℂ A q) (hF : DifferentiableAt ℂ F q)
    (hB : DifferentiableAt ℂ B q) (hG : DifferentiableAt ℂ G q)
    (hAB : hminusGardnerBracket A B q = 0) (hAG : hminusGardnerBracket A G q = 0)
    (hFB : hminusGardnerBracket F B q = 0) (hFG : hminusGardnerBracket F G q = 0) :
    hminusGardnerBracket (fun a => A a * F a) (fun a => B a * G a) q = 0 := by
  rw [hminusGardnerBracket_mul_left A F _ q hA hF,
    hminusGardnerBracket_mul_right F B G q hB hG,
    hminusGardnerBracket_mul_right A B G q hB hG,hAB,hAG,hFB,hFG]
  ring

end NLS.Poisson
