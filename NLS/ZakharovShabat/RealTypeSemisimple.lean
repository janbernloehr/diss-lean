import NLS.ZakharovShabat.RealType
import NLS.ZakharovShabat.PhysicalPeriodicRootSpaces
import NLS.FunctionalAnalysis.PencilRootSemisimple

/-! Real-type periodic Dirac potentials have no associated vectors on the
unchanged original domain. All finite Banach exponents are retained. -/
noncomputable section
open Complex NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem domainPairing_spectralPencil_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) (f g : Domain p) (hf : f ≠ 0)
    (he : operator hp φ f = z • domainInclusion f) :
    domainPairing hp (spectralPencil hp φ z g) f = 0 := by
  have hz := eigenvalue_im_eq_zero_of_realType hp φ hφ z f hf he
  have hc : conj z = z := conj_eq_iff_im.mpr hz
  change domainPairing hp (z • domainInclusion g-operator hp φ g) f = 0
  rw [sub_eq_add_neg, ← neg_one_smul ℂ (operator hp φ g),
    domainPairing_add_left, domainPairing_smul_left, domainPairing_smul_left,
    domainPairing_operator_conj hp φ hφ g f, he, domainPairing_smul_left,
    map_mul, hc, ← domainPairing_inclusion_conj]
  ring

/-- The original spectral pencil admits no nonzero associated eigenvector. -/
theorem periodic_no_associated_vector_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) (f : Domain p) (hf : f ≠ 0)
    (he : operator hp φ f = z • domainInclusion f) (g : Domain p) :
    spectralPencil hp φ z g ≠ domainInclusion f := by
  intro hg
  have hzero := domainPairing_spectralPencil_eigenvector hp φ hφ z f g hf he
  rw [hg] at hzero
  have hpos := domainPairing_inclusion_re_pos hp f hf
  rw [hzero,zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Every full algebraic root space of a real-type potential is its first root level. -/
theorem periodicRootSpaceTop_eq_one_of_realType (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : IsRealType φ) (z : ℂ) :
    periodicRootSpaceTop hp φ z = periodicRootSpace hp φ z 1 := by
  have ht : periodicRootSpaceTop hp φ z = pencilRootSpaceTop domainInclusion.toLinearMap
      (spectralPencil hp φ z).toLinearMap := by
    unfold periodicRootSpaceTop pencilRootSpaceTop
    exact iSup_congr fun n => periodicRootSpace_eq_pencilRootSpace hp φ z n
  rw [ht,periodicRootSpace_eq_pencilRootSpace]
  apply pencilRootSpaceTop_eq_one_of_no_associated
  intro f g hf hg
  by_contra hf0
  change z • domainInclusion f-operator hp φ f = 0 at hf
  exact periodic_no_associated_vector_of_realType hp φ hφ z f hf0
    (sub_eq_zero.mp hf).symm g hg

/-- The full original eigenspace is linearly equivalent to the first root level. -/
def periodicEigenspaceRootEquiv (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicEigenspace hp φ z ≃ₗ[ℂ] periodicRootSpace hp φ z 1 := by
  rw [periodicRootSpace_eq_pencilRootSpace]
  exact pencilKerRootEquiv domainInclusion.toLinearMap
    (spectralPencil hp φ z).toLinearMap domainInclusion_injective

/-- Actual algebraic multiplicity equals the full-domain geometric multiplicity. -/
theorem periodicAlgebraicMultiplicity_eq_geometric_of_realType (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : IsRealType φ) (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ z = Module.finrank ℂ (periodicEigenspace hp φ z) := by
  rw [periodicAlgebraicMultiplicity,periodicRootSpaceTop_eq_one_of_realType hp φ hφ z]
  exact (periodicEigenspaceRootEquiv hp φ z).finrank_eq.symm

end NLS.ZakharovShabat
