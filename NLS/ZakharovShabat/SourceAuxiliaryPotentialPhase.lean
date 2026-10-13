import NLS.SequenceSpaces.FiniteSourceCoefficients
import NLS.ZakharovShabat.SourceAuxiliaryReality
import NLS.ZakharovShabat.SourcePhaseCompatibility

/-!
# Exact original potential phase and auxiliary spectral transport

The potential rotation (iφ₋,−iφ₊) is an isometry of the original finite-exponent
coefficient norm. Its inverse gives the exact spectral correspondence between
completed auxiliary Neumann reflection and ordinary Dirichlet reflection.
This retains the norm appearing in the printed height of Proposition 5.2.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The auxiliary potential phase is an isometry in the original finite-exponent norm. -/
def sourceAuxiliaryPotentialPhase (hp : p ≠ ⊤) : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p where
  toFun u := WithLp.toLp p (Complex.I • u.ofLp.1, -Complex.I • u.ofLp.2)
  invFun u := WithLp.toLp p (-Complex.I • u.ofLp.1, Complex.I • u.ofLp.2)
  left_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  right_inv u := by apply WithLp.ofLp_injective; simp [smul_smul]; rfl
  map_add' u v := by apply WithLp.ofLp_injective; simp [smul_add]
  map_smul' c u := by
    apply WithLp.ofLp_injective
    exact Prod.ext (smul_comm Complex.I c u.ofLp.1) (smul_comm (-Complex.I) c u.ofLp.2)
  norm_map' u := by
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos
      (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
    simp [WithLp.prod_norm_eq_add hp0, norm_smul]

/-- This is exactly the existing original source phase, with its norm now retained. -/
theorem sourceAuxiliaryPotentialPhase_eq_sourcePhase (hp : p ≠ ⊤) (φ : CoeffPair p) :
    sourceAuxiliaryPotentialPhase hp φ = sourcePhase φ := rfl

/-- The inverse phase retains finite Fourier inputs, with explicit component phases. -/
theorem sourceAuxiliaryPotentialPhase_symm_ofFinsupp (hp : p ≠ ⊤) (a b : ℤ →₀ ℂ) :
    (sourceAuxiliaryPotentialPhase hp).symm (CoeffPair.ofFinsupp (a,b)) =
      CoeffPair.ofFinsupp (-Complex.I • a, Complex.I • b) := by
  apply (CoeffPair.toMax p).injective
  change (-Complex.I • Coeff.ofFinsupp a, Complex.I • Coeff.ofFinsupp b) =
    (Coeff.ofFinsupp (-Complex.I • a), Coeff.ofFinsupp (Complex.I • b))
  simp only [map_smul]

/-- Actual source auxiliary spectra equal ordinary spectra at the phase-rotated original input. -/
theorem sourceAuxiliarySpectrum_eq_sourcePhaseBoundary (b : BoundaryCondition) (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    sourceAuxiliarySpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp φ)
      (sourceAuxiliaryReflectedPotential_mem hp1 hp φ) =
      b.spectrum hp (periodOneBoundaryPotential hp hp1 (sourceAuxiliaryPotentialPhase hp φ)).val
        (periodOneBoundaryPotential hp hp1 (sourceAuxiliaryPotentialPhase hp φ)).property := by
  rw [sourceAuxiliarySpectrum_eq]
  erw [auxiliarySpectrum_eq]
  congr 1
  rw [toMax_sourceAuxiliaryReflectedPotential]
  exact auxiliaryPotential_intervalExtension_neumann hp hp1 (CoeffPair.toMax p φ)

end NLS.ZakharovShabat
