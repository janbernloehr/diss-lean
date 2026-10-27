import NLS.ZakharovShabat.ClassicalParityDomain
import NLS.ZakharovShabat.SourcePeriodTwoRestriction
import NLS.ZakharovShabat.SourceParity
import NLS.ZakharovShabat.ContinuousSourceBoundaryRealization
import NLS.Fourier.FoldedEnergy

/-! # Isometric signed extension of arbitrary unit-interval L² data -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.Fourier

theorem memLp_signedDouble_of_memLp (ε : ℂ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (signedDouble ε f) 2 (volume.restrict (Ioc 0 2)) := by
  rw [signedDouble_eq_folded]
  exact memLp_folded_of_memLp ε hf (memLp_unit_reflection hf)

/-- A sign repetition doubles the ordinary interval energy before circle normalization. -/
theorem integral_sq_signedDouble_of_memLp (ε : ℂ) (hε : ‖ε‖ = 1) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    (∫ x in (0 : ℝ)..2, ‖signedDouble ε f x‖^2) =
      2 * ∫ x in (0 : ℝ)..1, ‖f x‖^2 := by
  rw [signedDouble_eq_folded,integral_sq_folded_of_memLp ε hε hf (memLp_unit_reflection hf),
    intervalIntegral.integral_comp_sub_left (fun x => ‖f x‖^2) 1]
  norm_num
  ring

end NLS.Fourier
namespace NLS.ZakharovShabat
open NLS.Fourier

theorem memLp_parityIntervalExtension (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    MemLp (parityIntervalExtension r f) 2 (volume.restrict (Ioc 0 2)) :=
  memLp_prod_iff.mpr ⟨memLp_signedDouble_of_memLp _ hf.fst,memLp_signedDouble_of_memLp _ hf.snd⟩

/-- The normalized period-two coefficients of an arbitrary signed L² extension. -/
def sourceParityIntervalCoefficients (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) : CoeffPair 2 :=
  sourcePeriodTwoL2Coefficients (parityIntervalExtension r f) (memLp_parityIntervalExtension r f hf)

theorem sourceParityIntervalCoefficients_mem (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    sourceParityIntervalCoefficients r f hf ∈ sourceParitySubspace r := by
  rw [mem_sourceParitySubspace]
  intro n hn
  exact ⟨periodTwoCoefficient_signedDouble_parity_of_intervalIntegrable r
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.fst.integrable (by norm_num))) n hn,
    periodTwoCoefficient_signedDouble_parity_of_intervalIntegrable r
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.snd.integrable (by norm_num))) n hn⟩

/-- The coefficients synthesize the literal signed extension almost everywhere. -/
theorem physicalBase_sourceParityIntervalCoefficients (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    physicalBase (CoeffPair.toMax 2 (sourceParityIntervalCoefficients r f hf))
      =ᵐ[volume.restrict (Ioc 0 2)] parityIntervalExtension r f := by
  filter_upwards [circlePullback_periodTwoL2Coefficients _ (memLp_signedDouble_of_memLp (wave r 1) hf.fst),
    circlePullback_periodTwoL2Coefficients _ (memLp_signedDouble_of_memLp (wave r 1) hf.snd)] with x hx hy
  exact Prod.ext hx hy

/-- The original component-sum coefficient norm equals the ordinary physical interval norm. -/
theorem norm_sourceParityIntervalCoefficients (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ‖sourceParityIntervalCoefficients r f hf‖ = ‖intervalL2OfFunction f hf‖ := by
  have he : ‖sourceParityIntervalCoefficients r f hf‖^2 = ‖intervalL2OfFunction f hf‖^2 := by
    rw [sourceParityIntervalCoefficients,sourcePeriodTwoL2Coefficients,WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst,WithLp.toLp_snd]
    rw [norm_sq_periodTwoL2Coefficients,norm_sq_periodTwoL2Coefficients,norm_sq_intervalL2OfFunction]
    change (1/2 : ℝ)*(∫ x in (0 : ℝ)..2, ‖signedDouble (wave r 1) (fun t => (f t).1) x‖^2) +
      (1/2 : ℝ)*(∫ x in (0 : ℝ)..2, ‖signedDouble (wave r 1) (fun t => (f t).2) x‖^2) = _
    rw [integral_sq_signedDouble_of_memLp (wave r 1) (by simp [wave,Complex.norm_exp]) hf.fst,
      integral_sq_signedDouble_of_memLp (wave r 1) (by simp [wave,Complex.norm_exp]) hf.snd]
    ring
  nlinarith [norm_nonneg (sourceParityIntervalCoefficients r f hf),norm_nonneg (intervalL2OfFunction f hf)]

/-- Physical restriction after signed extension recovers every original L² class. -/
theorem physicalRestriction_sourceParityIntervalCoefficients (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    physicalRestrictionL2 (CoeffPair.toMax 2 (sourceParityIntervalCoefficients r f hf)) =
      intervalL2OfFunction f hf := by
  apply intervalL2Representative_injective
  have he := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2)) (physicalBase_sourceParityIntervalCoefficients r f hf)
  filter_upwards [physicalRestrictionL2_representative (CoeffPair.toMax 2 (sourceParityIntervalCoefficients r f hf)),
    he,intervalL2Representative_ofFunction f hf,ae_restrict_mem measurableSet_Ioc] with x hx hy hz hmem
  rw [hx,hy,parityIntervalExtension_left r f hmem.2,hz]

end NLS.ZakharovShabat
