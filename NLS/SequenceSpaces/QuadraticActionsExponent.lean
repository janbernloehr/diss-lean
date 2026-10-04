import NLS.SequenceSpaces.QuadraticActions
import NLS.SequenceSpaces.QuasiHolderProduct

/-! # Quadratic actions at every Banach half exponent

The Hilbert action map extends to lp pairs with values in l(p/2)
whenever p >= 2. The Holder triple keeps the exponent relation explicit.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The quadratic coordinate actions in their half-exponent space. -/
def quadraticActionsExponent (z : Coeff p × Coeff p) : Coeff q :=
  (1/2 : ℂ) • (Coeff.doublingProduct z.1 z.1 + Coeff.doublingProduct z.2 z.2)

@[simp] theorem quadraticActionsExponent_apply (z : Coeff p × Coeff p) (n : ℤ) :
    quadraticActionsExponent (q := q) z n = (z.1 n^2+z.2 n^2)/2 := by
  change (1/2 : ℂ)*(z.1 n*z.1 n+z.2 n*z.2 n) = _
  ring

/-- The polynomial action map is entire in the sequence norm. -/
theorem analyticOnNhd_quadraticActionsExponent :
    AnalyticOnNhd ℂ (quadraticActionsExponent (p := p) (q := q)) univ := by
  intro z _
  have hx := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).analyticAt z
  have hy := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).analyticAt z
  exact (((Coeff.doublingProduct (p := q) (q := p)).analyticAt_bilinear _).comp₂ hx hx).add
    (((Coeff.doublingProduct (p := q) (q := p)).analyticAt_bilinear _).comp₂ hy hy)
      |>.const_smul (c := (1/2 : ℂ))

/-- The action norm is bounded by the squared product-space norm. -/
theorem norm_quadraticActionsExponent_le (z : Coeff p × Coeff p) :
    ‖quadraticActionsExponent (q := q) z‖ ≤ ‖z‖^2 := by
  unfold quadraticActionsExponent
  rw [norm_smul]
  have hx := Coeff.norm_doublingProduct_le (p := q) z.1 z.1
  have hy := Coeff.norm_doublingProduct_le (p := q) z.2 z.2
  have hs := norm_add_le (Coeff.doublingProduct (p := q) z.1 z.1)
    (Coeff.doublingProduct (p := q) z.2 z.2)
  have hzx := norm_fst_le z
  have hzy := norm_snd_le z
  norm_num
  nlinarith [norm_nonneg z.1,norm_nonneg z.2,norm_nonneg z]

/-- At the Hilbert exponent this is the original action map. -/
theorem quadraticActionsExponent_two (z : Coeff 2 × Coeff 2) :
    quadraticActionsExponent (q := 1) z = quadraticActions z := rfl

end NLS
