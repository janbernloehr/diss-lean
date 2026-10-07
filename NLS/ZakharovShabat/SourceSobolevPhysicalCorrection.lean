import NLS.ZakharovShabat.SourceSobolevActionAnalytic
import NLS.ZakharovShabat.SourceFiniteGapSobolevHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedHamiltonian

/-! # The actual physical Hamiltonian correction on H¹

The mass, physical energy, and weighted action subtraction are now all defined
and analytic near every real H¹ source. On finite-gap sources this is precisely
the correction in the established physical trace identity. Identification with
the cubic-moment extension on all H¹ sources still requires a density or trace argument.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The physical NLS correction, with the actual convergent weighted spectral subtraction. -/
def sourceSobolevPhysicalCorrection (a : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  periodOneSobolevHamiltonian a - 2 * (periodOneSobolevMass a)^2 - sourceSobolevWeightedActionSum a

/-- All real H¹ sources lie in one open complex domain on which the literal physical
correction is analytic and its spectral subtraction is absolutely convergent. -/
theorem exists_sourceSobolevPhysicalCorrection_analytic_domain :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧
      {a | IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))} ⊆ U ∧
      AnalyticOnNhd ℂ sourceSobolevPhysicalCorrection U ∧
      ∀ a ∈ U, Summable (fun n : ℤ => ‖sourceSobolevWeightedAction a n‖) ∧
        sourceSobolevPhysicalCorrection a = periodOneSobolevHamiltonian a -
          2 * (periodOneSobolevMass a)^2 - ∑' n : ℤ, sourceSobolevWeightedAction a n := by
  obtain ⟨U,hU,hr,_,_,hA,hs⟩ := exists_sourceSobolevWeightedAction_analytic_domain
  refine ⟨U,hU,hr,?_,?_⟩
  · intro a ha
    exact ((analyticAt_periodOneSobolevHamiltonian a).sub
      (analyticAt_const.mul ((analyticAt_periodOneSobolevMass a).pow 2))).sub (hA a ha)
  · intro a ha
    exact ⟨(hs a ha).1, by rw [sourceSobolevPhysicalCorrection, (hs a ha).2]⟩

/-- Continuity in the H¹ norm of the full physical correction at each real source. -/
theorem continuousAt_sourceSobolevPhysicalCorrection
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ContinuousAt sourceSobolevPhysicalCorrection a := by
  obtain ⟨_,_,hr,hA,_⟩ := exists_sourceSobolevPhysicalCorrection_analytic_domain
  exact (hA a (hr ha)).continuousAt

@[simp] theorem sobolevSourceInclusion_sourceFiniteGapSobolevPair
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sobolevSourceInclusion (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) = φ.val := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · exact sobolevSourceInclusion_fst _ n
  · exact sobolevSourceInclusion_snd _ n

/-- The H¹ correction is the original finite-gap physical correction, with precisely
the same period-one frequencies and spectral actions. -/
theorem sourceSobolevPhysicalCorrection_sourceFiniteGapSobolevPair
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceSobolevPhysicalCorrection (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      sourceFiniteGapRenormalizedHamiltonian (by simp) (by norm_num) φ hf := by
  have hr : IsRealType (CoeffPair.toMax 2
      (sobolevSourceInclusion (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf))) := by
    rw [sobolevSourceInclusion_sourceFiniteGapSobolevPair]
    exact φ.property
  unfold sourceFiniteGapRenormalizedHamiltonian
  rw [sourceSobolevPhysicalCorrection, periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair,
    periodOneSobolevMass_sourceFiniteGapSobolevPair, sourceSobolevWeightedActionSum_eq_tsum _ hr]
  congr 1
  apply tsum_congr
  intro n
  rw [sourceSobolevWeightedAction, sobolevSourceInclusion_sourceFiniteGapSobolevPair]
  congr 1
  ring

end NLS.ZakharovShabat
