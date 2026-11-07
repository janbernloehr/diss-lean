import NLS.KdV.SingularHillMiuraCompanion
import NLS.FunctionalAnalysis.ComplexPairRotation
import NLS.ZakharovShabat.RealTypeSemisimple

/-! Exact constant operator conjugacy between the fixed Miura companion
and the actual periodic Dirac differential operator. -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

theorem miuraDiracRotation_domainInclusion (f : Domain 2) :
    complexPairRotation (Coeff 2) (domainInclusion f) =
      domainInclusion (complexPairRotation (ScalarDomain 2) f) := by
  rcases f with ⟨a,b⟩
  change (scalarInclusion a+I • scalarInclusion b,scalarInclusion a-I • scalarInclusion b) =
    (scalarInclusion (a+I • b),scalarInclusion (a-I • b))
  simp only [map_add,map_sub,map_smul]

/-- The full original-domain operator comparison, before any eigenvalue is selected. -/
theorem miuraDiracRotation_operator (u : Coeff 2) (f : Domain 2) :
    complexPairRotation (Coeff 2) (operator (by norm_num) (u,u) f) =
      singularHillMiuraCompanion u (complexPairRotation (ScalarDomain 2) f) := by
  rcases f with ⟨a,b⟩
  change (I • ZakharovShabat.derivative a+potentialMul (by norm_num) u b+
      I • (-I • ZakharovShabat.derivative b+potentialMul (by norm_num) u a),
    I • ZakharovShabat.derivative a+potentialMul (by norm_num) u b-
      I • (-I • ZakharovShabat.derivative b+potentialMul (by norm_num) u a)) =
    (I • (ZakharovShabat.derivative (a-I • b)+potentialMul (by norm_num) u (a-I • b)),
      I • (ZakharovShabat.derivative (a+I • b)-potentialMul (by norm_num) u (a+I • b)))
  simp only [map_add,map_sub,map_smul,smul_add,smul_sub,smul_smul,
    mul_neg,I_mul_I,neg_neg,one_smul,neg_one_smul]
  apply Prod.ext <;> module

def diracMiuraEigenspaceToCompanion (u : Coeff 2) (z : ℂ) :
    periodicEigenspace (by norm_num) (u,u) z →ₗ[ℂ] singularHillMiuraCompanionEigenspace u z where
  toFun f := ⟨complexPairRotation (ScalarDomain 2) f.val,by
    change singularHillMiuraCompanion u (complexPairRotation (ScalarDomain 2) f.val)-
      z • domainInclusion (complexPairRotation (ScalarDomain 2) f.val) = 0
    apply sub_eq_zero.mpr
    rw [← miuraDiracRotation_operator,
      (mem_periodicEigenspace (by norm_num) (u,u) z f.val).mp f.property,
      map_smul,miuraDiracRotation_domainInclusion]⟩
  map_add' f g := Subtype.ext ((complexPairRotation (ScalarDomain 2)).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((complexPairRotation (ScalarDomain 2)).map_smul c f.val)

theorem diracMiuraEigenspaceToCompanion_bijective (u : Coeff 2) (z : ℂ) :
    Function.Bijective (diracMiuraEigenspaceToCompanion u z) := by
  constructor
  · intro f g h
    exact Subtype.ext ((complexPairRotation (ScalarDomain 2)).injective (congrArg Subtype.val h))
  · intro g
    let f := (complexPairRotation (ScalarDomain 2)).symm g.val
    have he : operator (by norm_num) (u,u) f = z • domainInclusion f := by
      apply (complexPairRotation (Coeff 2)).injective
      rw [miuraDiracRotation_operator,map_smul,miuraDiracRotation_domainInclusion]
      change singularHillMiuraCompanion u
          (complexPairRotation (ScalarDomain 2) ((complexPairRotation (ScalarDomain 2)).symm g.val)) = _
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact sub_eq_zero.mp g.property
    refine ⟨⟨f,(mem_periodicEigenspace (by norm_num) (u,u) z f).mpr he⟩,?_⟩
    apply Subtype.ext
    exact (complexPairRotation (ScalarDomain 2)).apply_symm_apply g.val

/-- Exact full-domain Dirac-to-companion eigenspace equivalence, including zero frequency. -/
def diracMiuraCompanionEigenspaceEquiv (u : Coeff 2) (z : ℂ) :
    periodicEigenspace (by norm_num) (u,u) z ≃ₗ[ℂ] singularHillMiuraCompanionEigenspace u z :=
  LinearEquiv.ofBijective (diracMiuraEigenspaceToCompanion u z)
    (diracMiuraEigenspaceToCompanion_bijective u z)

/-- Exact original Hill/Dirac eigenspace equivalence at nonzero frequency. -/
def diracMiuraHillEigenspaceEquiv (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    periodicEigenspace (by norm_num) (u,u) z ≃ₗ[ℂ]
      singularHillEigenspace (singularHillMiuraPotential u) (z^2) :=
  (diracMiuraCompanionEigenspaceEquiv u z).trans (singularHillMiuraEigenspaceEquiv u z hz)

theorem singularHillMiuraPotential_coefficient (u : Coeff 2) (n : ℤ) :
    (singularHillMiuraPotential u).val (mode (-n)) =
      I*(Real.pi:ℂ)*n*u n+∑' k : ℤ, u (n-k)*u k := by
  change (l2DerivativeOriginalHminus u).val (mode (-n))+
    (l2ProductOriginalHminus u u).val (mode (-n)) = _
  rw [l2DerivativeOriginalHminus_coefficient,l2ProductOriginalHminus_coefficient]

/-- Real physical L2 Miura inputs give native real H-minus-one potentials. -/
theorem singularHillMiuraPotential_real (u : Coeff 2) (hu : IsRealType (u,u)) :
    (singularHillMiuraPotential u).val = (singularHillMiuraPotential u).val.conjugate := by
  have hu' : ∀ k : ℤ, u k = conj (u (-k)) := hu
  apply (Distribution.eq_conjugate_iff_coefficients _ _).mpr
  intro n
  have hh := singularHillMiuraPotential_coefficient u (-n)
  simp only [neg_neg] at hh
  rw [singularHillMiuraPotential_coefficient,hh,Complex.star_def,map_add]
  have hprod : conj (∑' k : ℤ, u (-n-k)*u k) = ∑' k : ℤ, u (n-k)*u k := by
    rw [WeightedCoeff.conj_tsum_convolution]
    simp only [← hu']
  rw [hprod]
  congr 1
  simp only [map_mul,conj_I,conj_ofReal,map_intCast,Int.cast_neg,map_neg,← hu']
  ring

/-- Actual physical algebraic multiplicities agree with those of the fixed
Dirac operator for real L2 Miura inputs, on the unchanged full domains. -/
theorem singularHillAlgebraicMultiplicity_miura_dirac (u : Coeff 2)
    (hu : IsRealType (u,u)) (z : ℂ) (hz : z ≠ 0) :
    singularHillAlgebraicMultiplicity (singularHillMiuraPotential u) (z^2) =
      periodicAlgebraicMultiplicity (by norm_num) (u,u) z := by
  rw [singularHillAlgebraicMultiplicity_miura_companion u (singularHillMiuraPotential_real u hu) z hz,
    periodicAlgebraicMultiplicity_eq_geometric_of_realType (by norm_num) (u,u) hu z]
  exact (diracMiuraCompanionEigenspaceEquiv u z).finrank_eq.symm

end NLS.KdV
