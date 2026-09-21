import NLS.SequenceSpaces.PairNorm
import NLS.SequenceSpaces.ExponentEmbedding

/-! # Exponent inclusion in the source coefficient-pair topology
The continuous inclusion keeps both raw coefficient sequences while changing
the component-sum norm to the target exponent's source pair norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.CoeffPair
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The coefficient-preserving continuous inclusion between source pair spaces. -/
def exponentInclusion (h : p ≤ q) : CoeffPair p →L[ℂ] CoeffPair q :=
  (toMax q).symm.toContinuousLinearMap.comp
    (((Coeff.exponentInclusion h).prodMap (Coeff.exponentInclusion h)).comp
      (toMax p).toContinuousLinearMap)

@[simp] theorem exponentInclusion_fst (h : p ≤ q) (φ : CoeffPair p) :
    (exponentInclusion h φ).fst = Coeff.exponentInclusion h φ.fst := rfl

@[simp] theorem exponentInclusion_snd (h : p ≤ q) (φ : CoeffPair p) :
    (exponentInclusion h φ).snd = Coeff.exponentInclusion h φ.snd := rfl

/-- The source inclusion is injective because it keeps every coefficient. -/
theorem exponentInclusion_injective (h : p ≤ q) : Function.Injective (exponentInclusion h) := by
  intro φ ψ he
  apply (toMax p).injective
  exact Prod.ext
    (Coeff.exponentInclusion_injective h (congrArg WithLp.fst he))
    (Coeff.exponentInclusion_injective h (congrArg WithLp.snd he))

/-- Successive source inclusions compose without changing coefficients. -/
@[simp] theorem exponentInclusion_trans [Fact (1 ≤ r)] (hpq : p ≤ q) (hqr : q ≤ r)
    (φ : CoeffPair p) :
    exponentInclusion hqr (exponentInclusion hpq φ) = exponentInclusion (hpq.trans hqr) φ := by
  apply (toMax r).injective
  apply Prod.ext <;> exact Coeff.exponentInclusion_trans hpq hqr _

end NLS.CoeffPair
