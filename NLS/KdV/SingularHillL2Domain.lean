import NLS.KdV.SingularHillAlgebraicMultiplicity
import NLS.KdV.HillSobolev

/-! Exact comparison of the full original H1/H-minus-one Hill eigen-equation
and the shared H2/L2 coefficient operator for L2 potentials. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Original H-minus-one realization of an arbitrary shared L2 potential,
with the SAME raw Fourier coefficients and original period-two normalization. -/
def hillL2HminusOne : WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM SpectralWeight.one.toWeight (Weight.sobolev (-1))
      (fun _ => (1:ℂ)) 1 (by norm_num) (fun k => by
        simp only [norm_one, mul_one, SpectralWeight.one_apply]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (le_add_of_nonneg_right (abs_nonneg (k:ℝ))) (by norm_num)))

/-- Every normalized original Fourier coefficient is unchanged. -/
theorem hillL2HminusOne_coefficient (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (hillL2HminusOne q).val (mode (-k)) = q.val k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (1:ℂ)*q.val k = _
  exact one_mul _

/-- An original H1 vector supplies actual absolutely summable raw coefficients. -/
def singularHillH1AsSummable (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    WeightedCoeff SpectralWeight.one.toWeight 1 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 1).symm
    (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (sobolevCoefficients 1 2 f))

/-- The summable representative has exactly the original Fourier coefficients. -/
theorem singularHillH1AsSummable_apply (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (singularHillH1AsSummable f).val k = f.val (mode (-k)) := by
  change WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (sobolevCoefficients 1 2 f) k /
    (SpectralWeight.one k:ℂ) = _
  rw [WeightedCoeff.sobolevToL1CLM_apply]
  simp only [SpectralWeight.one_apply, Complex.ofReal_one, div_one]
  rfl

/-- The full original H1-domain eigen-equation is EXACTLY the existing
summable Fourier eigenvector criterion. -/
theorem singularHillL2_eigen_iff_fourier
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f ↔
      IsHillFourierEigenvector SpectralWeight.one q z (singularHillH1AsSummable f) := by
  rw [singularHillOperator_eigen_iff]
  simp only [IsHillFourierEigenvector, SpectralWeight.convolution_apply,
    singularHillH1AsSummable_apply, hillL2HminusOne_coefficient]

/-- Every original H1 eigenvector for an L2 potential gains the FULL H2
Hilbert coefficient regularity, not merely an infinity endpoint bound. -/
theorem singularHillL2_eigen_memlp_sobolev_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f) :
    Memℓp (fun k => (Weight.sobolev 2 k:ℂ)*f.val (mode (-k))) 2 := by
  have he := hillFourierEigenvector_memlp_sobolev_two q z (singularHillH1AsSummable f)
    ((singularHillL2_eigen_iff_fourier q z f).mp hf)
  simpa only [singularHillH1AsSummable_apply] using he

/-- The original H1 realization of the shared H2 domain, with no change of coefficients. -/
def hillDomainOriginalH1 (f : HillSobolevDomain) : FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm (hillDomainToH1 f)

/-- Exact original Fourier coefficients of every H2 domain vector. -/
theorem hillDomainOriginalH1_coefficient (f : HillSobolevDomain) (k : ℤ) :
    (hillDomainOriginalH1 f).val (mode (-k)) = f.val k := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact WeightedCoeff.sobolevInclusion_apply _ f k

/-- Original realization is injective on the full shared H2 domain. -/
theorem hillDomainOriginalH1_injective : Function.Injective hillDomainOriginalH1 := by
  intro f g he
  apply Subtype.ext
  funext k
  simpa only [hillDomainOriginalH1_coefficient] using
    congrArg (fun u : FourierLebesgueSpace (2:ℝ) 1 2 => u.val (mode (-k))) he

/-- On H2 inputs the full original H1/H-minus-one eigen-equation and shared
H2/L2 eigen-equation are exactly equivalent. -/
theorem hillDomainOriginalH1_eigen_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) (f : HillSobolevDomain) :
    singularHillOperator (hillL2HminusOne q) (hillDomainOriginalH1 f) =
      z • singularHillDomainInclusion (hillDomainOriginalH1 f) ↔
      hillOperator (SpectralWeight.one.toCoeff q) f = z • hillDomainToL2 f := by
  rw [singularHillL2_eigen_iff_fourier, hillOperator_eigen_iff]
  have he : singularHillH1AsSummable (hillDomainOriginalH1 f) = hillDomainAsSummable f := by
    apply Subtype.ext
    funext k
    rw [singularHillH1AsSummable_apply, hillDomainOriginalH1_coefficient, hillDomainAsSummable_apply]
  rw [he]

/-- Zero in the H2 domain represents the original zero distribution. -/
@[simp] theorem hillDomainOriginalH1_zero : hillDomainOriginalH1 0 = 0 := by
  simp [hillDomainOriginalH1]

/-- Construct the actual H2 lift of each original H1 eigenvector. -/
def singularHillL2EigenvectorLift (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f) :
    HillSobolevDomain :=
  hillEigenvectorLift q z (singularHillH1AsSummable f) ((singularHillL2_eigen_iff_fourier q z f).mp hf)

/-- The constructed H2 vector preserves every original Fourier coefficient. -/
theorem singularHillL2EigenvectorLift_coefficient
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f) (k : ℤ) :
    (singularHillL2EigenvectorLift q z f hf).val k = f.val (mode (-k)) :=
  singularHillH1AsSummable_apply f k

/-- The lift recovers the ENTIRE original H1 distribution, not only formal data. -/
theorem hillDomainOriginalH1_singularHillL2EigenvectorLift
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f) :
    hillDomainOriginalH1 (singularHillL2EigenvectorLift q z f hf) = f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [hillDomainOriginalH1_coefficient, singularHillL2EigenvectorLift_coefficient]

/-- Exact equivalence of actual nonzero eigenvectors on the full original H1
domain and the shared H2 domain, for every complex L2 potential and energy. -/
theorem singularHillL2_exists_eigenvector_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (z : ℂ) :
    (∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (hillL2HminusOne q) f = z • singularHillDomainInclusion f) ↔
      ∃ f : HillSobolevDomain, f ≠ 0 ∧
        hillOperator (SpectralWeight.one.toCoeff q) f = z • hillDomainToL2 f := by
  constructor
  · rintro ⟨f, hf0, hf⟩
    refine ⟨singularHillL2EigenvectorLift q z f hf, ?_, ?_⟩
    · intro he
      have hh := congrArg hillDomainOriginalH1 he
      rw [hillDomainOriginalH1_singularHillL2EigenvectorLift, hillDomainOriginalH1_zero] at hh
      exact hf0 hh
    · apply (hillDomainOriginalH1_eigen_iff q z _).mp
      rw [hillDomainOriginalH1_singularHillL2EigenvectorLift]
      exact hf
  · rintro ⟨f, hf0, hf⟩
    refine ⟨hillDomainOriginalH1 f, ?_, (hillDomainOriginalH1_eigen_iff q z f).mpr hf⟩
    intro he
    exact hf0 (hillDomainOriginalH1_injective (he.trans hillDomainOriginalH1_zero.symm))

end NLS.KdV
