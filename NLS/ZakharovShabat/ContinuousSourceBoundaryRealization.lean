import NLS.ZakharovShabat.ContinuousSourceDiscriminantGradient
import NLS.ZakharovShabat.SourceBoundaryPoissonGradient
import NLS.SequenceSpaces.FiniteSourceDensity

/-! # Boundary realization of continuously represented source potentials

Restriction of physical Hilbert synthesis to the unit interval is bounded.
Density then identifies the completed source boundary extension with the
actual reflected physical potential, including non-polynomial inputs.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Square integrability persists on the original unit interval. -/
theorem memLp_physicalBase_unit (φ : PairSpace 2) :
    MemLp (physicalBase φ) 2 (volume.restrict (Ioc 0 1)) :=
  (memLp_physicalBase φ).mono_measure (Measure.restrict_mono
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) le_rfl)

/-- The actual unit-interval class of a physical coefficient potential. -/
def physicalRestrictionL2 (φ : PairSpace 2) : IntervalPairL2 :=
  intervalL2OfFunction (physicalBase φ) (memLp_physicalBase_unit φ)

@[simp] theorem physicalRestrictionL2_representative (φ : PairSpace 2) :
    intervalL2Representative (physicalRestrictionL2 φ) =ᵐ[volume.restrict (Ioc 0 1)] physicalBase φ :=
  intervalL2Representative_ofFunction _ _

private theorem unit_energy_le (a : Coeff 2) :
    (∫ t in (0 : ℝ)..1, ‖circlePullback (l2Synthesis a) t‖^2) ≤ 2*‖a‖^2 := by
  have hi : IntervalIntegrable (fun t => ‖circlePullback (l2Synthesis a) t‖^2) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_circlePullback (l2Synthesis a)).norm.integrable_sq)
  have hm := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := 1)
    (c := 0) (d := 2) (le_refl _) (by norm_num) (by norm_num)
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖circlePullback (l2Synthesis a) t‖)) hi
  have he := norm_sq_periodTwoL2Coefficients _ (memLp_circlePullback (l2Synthesis a))
  rw [periodTwoL2Coefficients_circlePullback] at he
  linarith

theorem norm_physicalRestrictionL2_le (φ : PairSpace 2) :
    ‖physicalRestrictionL2 φ‖ ≤ 2*‖φ‖ := by
  have he := norm_sq_intervalL2OfFunction (physicalBase φ) (memLp_physicalBase_unit φ)
  have h₁ := unit_energy_le φ.1
  have h₂ := unit_energy_le φ.2
  have hn₁ := norm_fst_le φ
  have hn₂ := norm_snd_le φ
  change ‖physicalRestrictionL2 φ‖^2 = _ at he
  dsimp only [physicalBase] at he
  nlinarith [norm_nonneg (physicalRestrictionL2 φ),norm_nonneg φ,
    (sq_le_sq₀ (norm_nonneg φ.1) (norm_nonneg φ)).mpr hn₁,
    (sq_le_sq₀ (norm_nonneg φ.2) (norm_nonneg φ)).mpr hn₂]

/-- Physical restriction is linear before bundling its norm estimate. -/
def physicalRestrictionL2Linear : PairSpace 2 →ₗ[ℂ] IntervalPairL2 where
  toFun := physicalRestrictionL2
  map_add' φ ψ := by
    apply intervalL2Representative_injective
    have h := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (physicalBase_add φ ψ)
    filter_upwards [physicalRestrictionL2_representative (φ+ψ),h,
      intervalL2Representative_add (physicalRestrictionL2 φ) (physicalRestrictionL2 ψ),
      physicalRestrictionL2_representative φ,physicalRestrictionL2_representative ψ] with t h₀ ha hb hφ hψ
    rw [h₀,ha,hb,hφ,hψ]
  map_smul' c φ := by
    change physicalRestrictionL2 (c • φ) = c • physicalRestrictionL2 φ
    apply intervalL2Representative_injective
    have h := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (physicalBase_smul c φ)
    filter_upwards [physicalRestrictionL2_representative (c • φ),h,
      intervalL2Representative_smul c (physicalRestrictionL2 φ),
      physicalRestrictionL2_representative φ] with t h₀ ha hb hφ
    rw [h₀,ha,hb,hφ]

/-- Bounded physical restriction from the period-two coefficient space. -/
def physicalRestrictionL2CLM : PairSpace 2 →L[ℂ] IntervalPairL2 :=
  physicalRestrictionL2Linear.mkContinuous 2 norm_physicalRestrictionL2_le

/-- The source extension is the actual reflected unit-interval potential. -/
theorem periodOneBoundaryPotential_eq_physicalRestriction (φ : CoeffPair 2) :
    periodOneBoundaryPotential (by simp) (by norm_num) φ =
      intervalPotentialToDirichlet (physicalRestrictionL2 (periodOnePotential φ)) := by
  let F := intervalPotentialToDirichlet.comp (physicalRestrictionL2CLM.comp (periodOnePotential (p := 2)))
  have he : (periodOneBoundaryPotential (by simp) (by norm_num) : CoeffPair 2 → dirichletSubspace (p := 2)) = F := by
    apply (CoeffPair.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
      (periodOneBoundaryPotential (by simp) (by norm_num)).continuous F.continuous
    funext a
    apply Subtype.ext
    change (periodOneBoundaryPotential (by simp) (by norm_num) (CoeffPair.ofFinsupp a)).val =
      intervalPotentialCoefficients (physicalRestrictionL2 (periodOnePotential (CoeffPair.ofFinsupp a)))
    rw [periodOneBoundaryPotential_finite_eq a (memLp_periodOnePair_finite a),
      physicalRestrictionL2,intervalPotentialCoefficients_ofFunction]
    apply dirichletPotentialCoefficients_congr_ae
    have hb : physicalBase (periodOnePotential (CoeffPair.ofFinsupp (p := 2) a))
        =ᵐ[volume.restrict (Ioc 0 1)] BoundaryCondition.periodOnePair a :=
      ae_restrict_of_ae_restrict_of_subset
        (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (physicalBase_periodOnePotential_finite a)
    exact hb.symm
  exact congrFun he φ

/-- A compatible continuous representative gives the exact classical
characteristic, with the source's original normalization. -/
theorem periodOneBoundaryCharacteristic_eq_classical_of_continuous
    (b : BoundaryCondition) (φ : CoeffPair 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) b φ z =
      classicalSeparatedCharacteristic b Φ z := by
  have hc : physicalRestrictionL2 (periodOnePotential φ) =
      intervalL2OfFunction (extend Φ) (memLp_extend_classicalCurve Φ) :=
    (intervalL2OfFunction_eq_iff _ _ _ _).mpr hΦ
  have he := periodOneBoundaryPotential_eq_physicalRestriction φ
  rw [hc] at he
  change b.characteristic (by simp) (periodOneBoundaryPotential (by simp) (by norm_num) φ).val
    (periodOneBoundaryPotential (by simp) (by norm_num) φ).property z = _
  rw [he]
  exact characteristic_eq_classicalSeparated b Φ (memLp_extend_classicalCurve Φ) z

end NLS.ZakharovShabat
