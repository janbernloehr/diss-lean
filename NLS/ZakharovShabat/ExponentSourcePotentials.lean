import NLS.SequenceSpaces.PairExponentEmbedding
import NLS.ZakharovShabat.ExponentIntervalExtension
import NLS.ZakharovShabat.ExponentBoundaryCoordinates
import NLS.ZakharovShabat.ExponentPeriodicCoordinates
import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryRoots
import NLS.ZakharovShabat.PeriodOneEmbedding

/-!
# Source potential realizations across finite exponents
The original period-one coefficient pair has distinct periodic, ordinary
boundary, and auxiliary boundary realizations. Each commutes with exponent
inclusion. Consequently the source canonical boundary coordinates and the
original periodic endpoint pairs retain the same signed indices.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Changing exponent commutes with the source frequency-doubling convention. -/
theorem Coeff.periodDouble_exponent (h : p ≤ q) (a : Coeff p) :
    Coeff.exponentInclusion h (Coeff.periodDouble a) =
      Coeff.periodDouble (Coeff.exponentInclusion h a) := by
  ext n
  rfl

namespace ZakharovShabat

/-- The source inclusion agrees with the ambient pair inclusion under the norm equivalence. -/
theorem toMax_exponentInclusion (h : p ≤ q) (φ : CoeffPair p) :
    CoeffPair.toMax q (CoeffPair.exponentInclusion h φ) =
      pairExponentInclusion h (CoeffPair.toMax p φ) := rfl

/-- The original periodic source realization commutes with exponent inclusion. -/
theorem periodOnePotential_exponent (h : p ≤ q) (φ : CoeffPair p) :
    pairExponentInclusion h (periodOnePotential φ) =
      periodOnePotential (CoeffPair.exponentInclusion h φ) := by
  apply Prod.ext <;> exact Coeff.periodDouble_exponent h _

/-- The ordinary reflected source potential commutes with finite exponent inclusion. -/
theorem periodOneBoundaryPotential_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : CoeffPair p) :
    pairExponentInclusion h (periodOneBoundaryPotential hp hp1 φ).val =
      (periodOneBoundaryPotential hq hq1 (CoeffPair.exponentInclusion h φ)).val :=
  BoundaryCondition.intervalExtensionCLM_exponent .dirichlet hp hq hp1 hq1 h _

/-- The distinct auxiliary source potential also commutes with finite exponent inclusion. -/
theorem auxiliaryPeriodOnePotential_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : CoeffPair p) :
    pairExponentInclusion h (auxiliaryPeriodOnePotential hp hp1 φ).val =
      (auxiliaryPeriodOnePotential hq hq1 (CoeffPair.exponentInclusion h φ)).val :=
  BoundaryCondition.intervalExtensionCLM_exponent .neumann hp hq hp1 hq1 h _

/-- Ordinary source boundary coordinates agree at every signed index across finite exponents. -/
theorem canonicalPeriodOneBoundaryRoots_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (b : BoundaryCondition) (φ : CoeffPair p) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ =
      canonicalPeriodOneBoundaryRoots hq hq1 b (CoeffPair.exponentInclusion h φ) := by
  have hψ : pairExponentInclusion h (periodOneBoundaryPotential hp hp1 φ).val ∈ dirichletSubspace :=
    (pairExponentInclusion_mem_boundary_iff h _ .dirichlet).mpr
      (periodOneBoundaryPotential hp hp1 φ).property
  have he := b.canonicalRoots_exponent hp hq hp1 hq1 h
    (periodOneBoundaryPotential hp hp1 φ).val
    (periodOneBoundaryPotential hp hp1 φ).property hψ
  have hs : (⟨pairExponentInclusion h (periodOneBoundaryPotential hp hp1 φ).val, hψ⟩ :
      dirichletSubspace (p := q)) = periodOneBoundaryPotential hq hq1 (CoeffPair.exponentInclusion h φ) :=
    Subtype.ext (periodOneBoundaryPotential_exponent hp hq hp1 hq1 h φ)
  exact he.trans (congrArg (fun ψ : dirichletSubspace (p := q) =>
    b.canonicalRoots hq hq1 ψ.val ψ.property) hs)

/-- The ordinary source characteristic keeps its full normalization across exponents. -/
theorem periodOneBoundaryCharacteristic_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (b : BoundaryCondition) (φ : CoeffPair p) :
    periodOneBoundaryCharacteristic hp hp1 b φ =
      periodOneBoundaryCharacteristic hq hq1 b (CoeffPair.exponentInclusion h φ) := by
  rw [periodOneBoundaryCharacteristic_eq_canonicalProduct,
    periodOneBoundaryCharacteristic_eq_canonicalProduct,
    canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 h b φ]

/-- Both original periodic source endpoints agree across finite exponents. -/
theorem canonicalPeriodicEndpoints_periodOne_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) =
      canonicalPeriodicLeft hq hq1 (periodOnePotential (CoeffPair.exponentInclusion h φ))
        (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) =
      canonicalPeriodicRight hq hq1 (periodOnePotential (CoeffPair.exponentInclusion h φ))
        (periodOnePotential_mem _) := by
  have hψ := (pairExponentInclusion_mem_parity_iff h (periodOnePotential φ) 0).mpr
    (periodOnePotential_mem φ)
  have he := canonicalPeriodicEndpoints_exponent hp hq hp1 hq1 h (periodOnePotential φ)
    (periodOnePotential_mem φ) hψ
  have hs : (⟨pairExponentInclusion h (periodOnePotential φ), hψ⟩ :
      pairParitySubspace (p := q) 0) =
      ⟨periodOnePotential (CoeffPair.exponentInclusion h φ), periodOnePotential_mem _⟩ :=
    Subtype.ext (periodOnePotential_exponent h φ)
  exact ⟨he.1.trans (congrArg (fun ψ : pairParitySubspace (p := q) 0 =>
    canonicalPeriodicLeft hq hq1 ψ.val ψ.property) hs),
    he.2.trans (congrArg (fun ψ : pairParitySubspace (p := q) 0 =>
      canonicalPeriodicRight hq hq1 ψ.val ψ.property) hs)⟩

end ZakharovShabat
end NLS
