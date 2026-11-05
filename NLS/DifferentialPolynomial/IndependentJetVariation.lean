import NLS.DifferentialPolynomial.MultiJet
import NLS.DifferentialPolynomial.AlgebraicPolynomialVariation
import NLS.DifferentialPolynomial.EulerLagrange

/-! # Independent variations of the two physical jet families -/
noncomputable section
open MvPolynomial
namespace NLS.DifferentialPolynomial

abbrev VariationPolynomial := MultiJetPolynomial (Bool × Bool)

/-- The first Boolean marks background or variation; the second marks field. -/
def backgroundEmbedding : Polynomial →ₐ[ℂ] VariationPolynomial := renameFields (fun i => (false,i))

@[simp] theorem backgroundEmbedding_X (v : Jet) :
    backgroundEmbedding (X v) = X ((false,v.1),v.2) := by simp [backgroundEmbedding, renameFields]

theorem backgroundEmbedding_spatialDerivative (p : Polynomial) :
    backgroundEmbedding (spatialDerivative p) =
      multiSpatialDerivative (Bool × Bool) (backgroundEmbedding p) :=
  renameFields_spatialDerivative (fun i : Bool => (false,i)) p

def independentJetVariation : Derivation ℂ VariationPolynomial VariationPolynomial :=
  evolutionaryDerivative (fun i => if i.1 then 0 else X ((true,i.2),0))

@[simp] theorem independentJetVariation_background_X (v : Jet) :
    independentJetVariation (X ((false,v.1),v.2)) = X ((true,v.1),v.2) := by
  simp [independentJetVariation]

theorem independentJetVariation_commute (p : VariationPolynomial) :
    independentJetVariation (multiSpatialDerivative (Bool × Bool) p) =
      multiSpatialDerivative (Bool × Bool) (independentJetVariation p) :=
  evolutionaryDerivative_commute _ p

def variationFields (a b h k : ℝ → ℂ) (i : Bool × Bool) : ℝ → ℂ :=
  if i.1 then (if i.2 then k else h) else (if i.2 then b else a)

theorem evaluateMulti_backgroundEmbedding (a b h k : ℝ → ℂ) (p : Polynomial) :
    evaluateMulti (variationFields a b h k) (backgroundEmbedding p) = evaluate a b p := by
  funext x
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ (MvPolynomial.rename _ p) = _
  rw [MvPolynomial.eval₂_rename]
  rfl

/-- The algebraic evolutionary derivative is exactly the pointwise first
variation on arbitrary actual fields and arbitrary independent directions. -/
theorem evaluate_independentJetVariation (a b h k : ℝ → ℂ) (p : Polynomial) :
    evaluateMulti (variationFields a b h k) (independentJetVariation (backgroundEmbedding p)) =
      firstVariationDensity a b h k p := by
  classical
  have he := derivation_aeval_mvPolynomial independentJetVariation
    (fun v : Jet => backgroundEmbedding (X v)) p
  have hF := MvPolynomial.aeval_unique backgroundEmbedding
  change backgroundEmbedding = MvPolynomial.aeval (fun v : Jet => backgroundEmbedding (X v)) at hF
  rw [← hF] at he
  simp only [backgroundEmbedding_X, independentJetVariation_background_X] at he
  funext x
  rw [he]
  simp only [evaluateMulti, map_sum]
  unfold firstVariationDensity
  apply Finset.sum_congr rfl
  intro v _
  change evaluateMulti (variationFields a b h k)
      (X ((true,v.1),v.2)*backgroundEmbedding (MvPolynomial.pderiv v p)) x = _
  rw [evaluateMulti_mul, evaluateMulti_X, evaluateMulti_backgroundEmbedding]
  rfl

end NLS.DifferentialPolynomial
