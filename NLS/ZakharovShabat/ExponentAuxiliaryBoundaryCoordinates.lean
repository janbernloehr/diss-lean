import NLS.ZakharovShabat.AuxiliaryBoundaryCharacteristic
import NLS.ZakharovShabat.ExponentSourcePotentials
import NLS.ZakharovShabat.ExponentBoundaryCoordinates

/-! # Starred source boundary data across finite exponents
The phase map preserves raw Fourier coefficients. Combining that fact with
the Neumann source-extension and ordinary boundary comparisons identifies the
actual auxiliary signed coordinates and normalized products across exponents.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Coefficient inclusion commutes with the exact auxiliary phase rotation. -/
theorem pairExponentInclusion_auxiliaryPotential (h : p ≤ q) (φ : PairSpace p) :
    pairExponentInclusion h (auxiliaryPotential φ) =
      auxiliaryPotential (pairExponentInclusion h φ) := by
  apply Prod.ext <;> ext n <;>
    simp only [pairExponentInclusion_apply, auxiliaryPotential_apply,
      Coeff.exponentInclusion_apply, lp.coeFn_smul, Pi.smul_apply]

/-- The conjugated ordinary source potential is exponent independent. -/
theorem auxiliaryPeriodOneDirichletPotential_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (φ : CoeffPair p) :
    pairExponentInclusion h (auxiliaryPeriodOneDirichletPotential hp hp1 φ).val =
      (auxiliaryPeriodOneDirichletPotential hq hq1 (CoeffPair.exponentInclusion h φ)).val := by
  change pairExponentInclusion h (auxiliaryPotential (auxiliaryPeriodOnePotential hp hp1 φ).val) =
    auxiliaryPotential (auxiliaryPeriodOnePotential hq hq1 (CoeffPair.exponentInclusion h φ)).val
  rw [pairExponentInclusion_auxiliaryPotential,
    auxiliaryPeriodOnePotential_exponent hp hq hp1 hq1 h φ]

/-- Every canonical starred coordinate agrees across finite exponents. -/
theorem canonicalAuxiliaryPeriodOneRoots_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (b : BoundaryCondition) (φ : CoeffPair p) :
    canonicalAuxiliaryPeriodOneRoots hp hp1 b φ =
      canonicalAuxiliaryPeriodOneRoots hq hq1 b (CoeffPair.exponentInclusion h φ) := by
  let ψ := auxiliaryPeriodOneDirichletPotential hp hp1 φ
  have hψ : pairExponentInclusion h ψ.val ∈ dirichletSubspace :=
    (pairExponentInclusion_mem_boundary_iff h _ .dirichlet).mpr ψ.property
  have he := b.canonicalRoots_exponent hp hq hp1 hq1 h ψ.val ψ.property hψ
  have hs : (⟨pairExponentInclusion h ψ.val, hψ⟩ : dirichletSubspace (p := q)) =
      auxiliaryPeriodOneDirichletPotential hq hq1 (CoeffPair.exponentInclusion h φ) :=
    Subtype.ext (auxiliaryPeriodOneDirichletPotential_exponent hp hq hp1 hq1 h φ)
  exact he.trans (congrArg (fun θ : dirichletSubspace (p := q) =>
    b.canonicalRoots hq hq1 θ.val θ.property) hs)

/-- The normalized entire starred characteristic is exponent independent. -/
theorem auxiliaryPeriodOneCharacteristic_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q) (b : BoundaryCondition) (φ : CoeffPair p) :
    auxiliaryPeriodOneCharacteristic hp hp1 b φ =
      auxiliaryPeriodOneCharacteristic hq hq1 b (CoeffPair.exponentInclusion h φ) := by
  rw [auxiliaryPeriodOneCharacteristic_eq_canonicalProduct,
    auxiliaryPeriodOneCharacteristic_eq_canonicalProduct,
    canonicalAuxiliaryPeriodOneRoots_exponent hp hq hp1 hq1 h b φ]

end NLS.ZakharovShabat
