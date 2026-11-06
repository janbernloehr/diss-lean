import NLS.SequenceSpaces.PeriodOneHminusOneDoubling
import NLS.KdV.SingularHillL2Characteristic
import NLS.KdV.HillHminusOneReality

/-! # The exact original singular-operator realization of unit-period H^-1

Raw unit-period coefficients occupy the even period-two slots. No source
regularity is added. The original full H1-domain Hill operator, closed
graph and compact resolvent are therefore available for every potential
in the original H^-1 norm. On physical L2 inputs its spectrum is exactly
the already constructed entire characteristic zero set.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

def periodOneSingularPotential : PeriodOneHminusOne →L[ℂ] FourierLebesgueSpace (2 : ℝ) (-1) 2 :=
  (sobolevCoefficients (L := 2) (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp periodOneHminusDouble

theorem periodOneSingularPotential_coefficient (q : PeriodOneHminusOne) (k : ℤ) :
    (periodOneSingularPotential q).val (mode (-k)) = (periodOneHminusDouble q).val k := by
  change ((sobolevCoefficients (L := 2) (-1) 2) ((sobolevCoefficients (L := 2) (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

@[simp] theorem periodOneSingularPotential_even (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneSingularPotential q).val (mode (-(2*n))) = q.val n := by
  rw [periodOneSingularPotential_coefficient,periodOneHminusDouble_even]

@[simp] theorem periodOneSingularPotential_odd (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneSingularPotential q).val (mode (-(2*n+1))) = 0 := by
  rw [periodOneSingularPotential_coefficient,periodOneHminusDouble_odd]

theorem norm_periodOneSingularPotential_le (q : PeriodOneHminusOne) : ‖periodOneSingularPotential q‖ ≤ ‖q‖ := by
  change ‖(sobolevCoefficients (L := 2) (-1) 2).symm (periodOneHminusDouble q)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_periodOneHminusDouble_le q

theorem norm_le_two_norm_periodOneSingularPotential (q : PeriodOneHminusOne) :
    ‖q‖ ≤ 2*‖periodOneSingularPotential q‖ := by
  have he : ‖periodOneSingularPotential q‖ = ‖periodOneHminusDouble q‖ := by
    change ‖(sobolevCoefficients (L := 2) (-1) 2).symm (periodOneHminusDouble q)‖ = _
    exact (sobolevCoefficients (L := 2) (-1) 2).symm.norm_map _
  rw [he]
  exact norm_le_two_norm_periodOneHminusDouble q

theorem periodOneSingularPotential_injective : Function.Injective periodOneSingularPotential := by
  intro q p he
  apply periodOneHminusDouble_injective
  exact (sobolevCoefficients (L := 2) (-1) 2).symm.injective he

def periodOneSingularL2Coefficients (a : Coeff 2) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  ⟨Coeff.periodDouble a,by
    change Memℓp (fun k => (SpectralWeight.one k : ℂ)*Coeff.periodDouble a k) 2
    simpa only [SpectralWeight.one_apply,Complex.ofReal_one,one_mul] using! lp.memℓp (Coeff.periodDouble a)⟩

theorem periodOneSingularL2Coefficients_toCoeff (a : Coeff 2) :
    SpectralWeight.one.toCoeff (periodOneSingularL2Coefficients a) = Coeff.periodDouble a := by
  ext k
  exact SpectralWeight.toCoeff_apply _ _ k

theorem periodOneSingularPotential_L2 (a : Coeff 2) :
    periodOneSingularPotential (periodOneL2Inclusion a) = hillL2HminusOne (periodOneSingularL2Coefficients a) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [periodOneSingularPotential_coefficient,hillL2HminusOne_coefficient,
    periodOneHminusDouble_eq_L2,periodOneL2Inclusion_apply]
  rfl

theorem periodOneSingularPotential_L2_spectrum (a : Coeff 2) (z : ℂ) :
    z ∈ singularHillSpectrum (periodOneSingularPotential (periodOneL2Inclusion a)) ↔
      hillHminusRadicand (periodOneL2Inclusion a) z = 0 := by
  rw [periodOneSingularPotential_L2,singularHillSpectrum_L2_iff_discriminant _ (by
    rw [periodOneSingularL2Coefficients_toCoeff]
    exact Coeff.periodDouble_mem a),periodOneSingularL2Coefficients_toCoeff,
    hillHminusRadicand,hillHminusDiscriminant_eq_hillL2]
  exact sub_eq_zero.symm

theorem periodOneSingularPotential_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    (periodOneSingularPotential q).val = (periodOneSingularPotential q).val.conjugate := by
  apply (Distribution.eq_conjugate_iff_coefficients _ _).mpr
  intro k
  rw [periodOneSingularPotential_coefficient,
    show mode k = mode (-(-k)) from by rw [neg_neg],periodOneSingularPotential_coefficient]
  simpa only [neg_neg,Complex.star_def] using periodOneHminusDouble_real q hr (-k)

theorem isClosed_periodOneSingularHillGraph (q : PeriodOneHminusOne) :
    IsClosed (singularHillGraph (periodOneSingularPotential q)) := isClosed_singularHillGraph _

theorem isCompactOperator_periodOneSingularHillResolvent (q : PeriodOneHminusOne) (z : ℂ) :
    IsCompactOperator (singularHillBaseResolvent (periodOneSingularPotential q) z) :=
  isCompactOperator_singularHillBaseResolvent _ _

theorem isClosed_periodOneSingularHillSpectralGraph :
    IsClosed {p : PeriodOneHminusOne × ℂ | p.2 ∈ singularHillSpectrum (periodOneSingularPotential p.1)} := by
  have h := isOpen_singularHillJointResolvent.preimage
    ((periodOneSingularPotential.continuous.comp continuous_fst).prodMk continuous_snd)
  exact h.isClosed_compl

end NLS.KdV
