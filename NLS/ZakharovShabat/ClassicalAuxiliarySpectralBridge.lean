import NLS.ZakharovShabat.ClassicalPhaseMonodromy
import NLS.ZakharovShabat.ClassicalAuxiliarySpectrum
import NLS.ZakharovShabat.FiniteSourceRealization
import NLS.ZakharovShabat.AuxiliaryBoundaryCharacteristic
import NLS.Fourier.IntervalParseval

/-! # Zeros of the classical auxiliary characteristic

The phase-conjugated monodromy formula detects the original physical
auxiliary endpoint eigenvalues. Fourier realization then identifies these
zeros with the actual auxiliary coefficient spectrum of the same continuous
potential on the unit interval.
-/

noncomputable section
open Set MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Phase rotation commutes pointwise with extending a continuous curve. -/
theorem physicalAuxiliaryPotential_extend (Φ : Curve (ℂ × ℂ)) :
    physicalAuxiliaryPotential (extend Φ) = extend (classicalSourcePhase Φ) := by
  funext x
  rfl

/-- Every continuous unit-interval curve is square integrable there. -/
theorem memLp_extend_classicalCurve (Φ : Curve (ℂ × ℂ)) :
    MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_two_interval (continuous_extend Φ).fst 0 1 (by norm_num),
    memLp_two_interval (continuous_extend Φ).snd 0 1 (by norm_num)⟩

/-- The actual classical auxiliary characteristic vanishes exactly at a physical auxiliary eigenvalue. -/
theorem classicalAuxiliaryCharacteristic_eq_zero_iff_mem_classicalAuxiliaryEigenvalues
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b Φ z = 0 ↔
      z ∈ b.classicalAuxiliaryEigenvalues (extend Φ) := by
  have hrot : MemLp (extend (classicalSourcePhase Φ)) 2
      (volume.restrict (Ioc 0 1)) := memLp_extend_classicalCurve _
  rw [classicalAuxiliaryCharacteristic_eq_separated_phase,
    classicalSeparatedCharacteristic_eq_zero_iff_mem_classicalEigenvalues b _ hrot,
    b.classicalAuxiliaryEigenvalues_eq, physicalAuxiliaryPotential_extend]

/-- The same zeros are the actual auxiliary coefficient eigenvalues of the Fourier extension. -/
theorem classicalAuxiliaryCharacteristic_eq_zero_iff_mem_auxiliarySpectrum
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b Φ z = 0 ↔
      z ∈ b.auxiliarySpectrum (by simp)
        (BoundaryCondition.neumannPotentialCoefficients (extend Φ) (memLp_extend_classicalCurve Φ))
        (BoundaryCondition.neumannPotentialCoefficients_mem (extend Φ) (memLp_extend_classicalCurve Φ)) := by
  rw [classicalAuxiliaryCharacteristic_eq_zero_iff_mem_classicalAuxiliaryEigenvalues,
    b.classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum]

/-- The original physical auxiliary spectrum depends only on the potential almost everywhere. -/
theorem BoundaryCondition.classicalAuxiliaryEigenvalues_congr_ae
    (b : BoundaryCondition) {φ ψ : ℝ → ℂ × ℂ}
    (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) :
    b.classicalAuxiliaryEigenvalues φ = b.classicalAuxiliaryEigenvalues ψ := by
  rw [b.classicalAuxiliaryEigenvalues_eq, b.classicalAuxiliaryEigenvalues_eq]
  apply b.classicalEigenvalues_congr_ae
  filter_upwards [h] with x hx
  simp only [physicalAuxiliaryPotential, hx]

/-- A finite source polynomial is square integrable on the original interval. -/
theorem memLp_periodOnePair_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    MemLp (BoundaryCondition.periodOnePair a) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨memLp_two_interval (BoundaryCondition.continuous_periodOnePair a).fst
    0 1 (by norm_num), memLp_two_interval (BoundaryCondition.continuous_periodOnePair a).snd
    0 1 (by norm_num)⟩

/-- The finite source's auxiliary extension is exactly the Neumann Fourier extension of its physical polynomial. -/
theorem auxiliaryPeriodOnePotential_finite_eq (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (auxiliaryPeriodOnePotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a)).val =
      BoundaryCondition.neumannPotentialCoefficients (BoundaryCondition.periodOnePair a)
        (memLp_periodOnePair_finite a) := by
  change BoundaryCondition.intervalExtensionCLM .neumann (by norm_num) (by simp)
    (BoundaryCondition.finitePairCoeffs a) = _
  rw [BoundaryCondition.intervalExtensionCLM_finite]
  apply Prod.ext
  · ext n
    exact (BoundaryCondition.finiteIntervalExtension_coefficient_fst .neumann
      (by norm_num) a n).symm
  · ext n
    exact (BoundaryCondition.finiteIntervalExtension_coefficient_snd .neumann
      (by norm_num) a n).symm

/-- For finite source data, the classical monodromy and normalized starred product have exactly the same zeros. -/
theorem classicalAuxiliaryCharacteristic_finite_eq_zero_iff_source
    (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    classicalAuxiliaryCharacteristic b (finiteSourceCurve a) z = 0 ↔
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b
        (CoeffPair.ofFinsupp (p := 2) a) z = 0 := by
  have he : extend (finiteSourceCurve a) =ᵐ[volume.restrict (Ioc 0 1)]
      BoundaryCondition.periodOnePair a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact extend_finiteSourceCurve a x (Ioc_subset_Icc_self hx)
  rw [classicalAuxiliaryCharacteristic_eq_zero_iff_mem_classicalAuxiliaryEigenvalues,
    b.classicalAuxiliaryEigenvalues_congr_ae he,
    b.classicalAuxiliaryEigenvalues_eq_auxiliarySpectrum _ (memLp_periodOnePair_finite a)]
  let q : neumannSubspace (p := 2) :=
    ⟨BoundaryCondition.neumannPotentialCoefficients (BoundaryCondition.periodOnePair a)
      (memLp_periodOnePair_finite a),
      BoundaryCondition.neumannPotentialCoefficients_mem _ (memLp_periodOnePair_finite a)⟩
  have hq : q = auxiliaryPeriodOnePotential (by simp) (by norm_num)
      (CoeffPair.ofFinsupp (p := 2) a) := by
    apply Subtype.ext
    exact (auxiliaryPeriodOnePotential_finite_eq a).symm
  change z ∈ b.auxiliarySpectrum (by simp) q.val q.property ↔ _
  rw [hq]
  exact (auxiliaryPeriodOneCharacteristic_eq_zero_iff (by simp) (by norm_num)
    b (CoeffPair.ofFinsupp (p := 2) a) z).symm

end NLS.ZakharovShabat
