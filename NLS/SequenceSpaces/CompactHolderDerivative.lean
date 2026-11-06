import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.CompactRowMajorant
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Compact symbol terms in derivatives of actual sequence packets

Multiplication of an ell-infinity variation by a FIXED finite-exponent
sequence is compact. Hence differentiating a native analytic symbol
packet leaves a compact remainder after its actual leading multiplier.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- A fixed finite-exponent sequence gives a compact map from bounded
symbols to the original sequence space, with no tail support assumption. -/
theorem isCompactOperator_holderProduct_fixed_right (hp : p≠⊤) (a : Coeff p) :
    IsCompactOperator ((holderProduct (p := ⊤) (r := p) (q := p)).flip a) := by
  apply isCompactOperator_of_rowMajorant hp _ a
  intro n b
  change ‖b n*a n‖≤‖a n‖*‖b‖
  rw [norm_mul,mul_comm ‖a n‖]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (by simp) b n) (norm_nonneg _)

/-- Exact derivative of the actual symbol packet, retaining both terms. -/
theorem fderiv_holderProduct_packet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : E → Coeff ⊤) (F : E → Coeff p) (q : E)
    (hσ : DifferentiableAt ℂ σ q) (hF : DifferentiableAt ℂ F q) :
    fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q=
      (holderProduct (q := p) (σ q)).comp (fderiv ℂ F q)+
        ((holderProduct (p := ⊤) (r := p) (q := p)).flip (F q)).comp (fderiv ℂ σ q) := by
  have H := (holderProduct (p := ⊤) (r := p) (q := p)).hasFDerivAt_of_bilinear
    hσ.hasFDerivAt hF.hasFDerivAt
  rw [H.fderiv]
  ext v n
  change σ q n*(fderiv ℂ F q v) n+(fderiv ℂ σ q v) n*F q n=
    σ q n*(fderiv ℂ F q v) n+(fderiv ℂ σ q v) n*F q n
  ring

/-- The actual symbol derivative contributes a compact remainder.
Neither the symbol nor the sequence is replaced by its amplitude. -/
theorem isCompactOperator_fderiv_holderProduct_packet_sub (hp : p≠⊤)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : E → Coeff ⊤) (F : E → Coeff p) (q : E)
    (hσ : DifferentiableAt ℂ σ q) (hF : DifferentiableAt ℂ F q) :
    IsCompactOperator (fderiv ℂ (fun x => holderProduct (q := p) (σ x) (F x)) q-
      (holderProduct (q := p) (σ q)).comp (fderiv ℂ F q)) := by
  rw [fderiv_holderProduct_packet σ F q hσ hF,add_sub_cancel_left]
  exact (isCompactOperator_holderProduct_fixed_right hp (F q)).comp_clm (fderiv ℂ σ q)

end NLS.Coeff
