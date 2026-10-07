import NLS.ZakharovShabat.SourceClassicalNLSAgreement
import NLS.ZakharovShabat.SourceRenormalizedOrdinaryGauge
import NLS.ZakharovShabat.ClassicalNLSMass

/-! # Renormalized spectral flow agrees with arbitrary classical H¹ data

The original Hilbert source mass equals the literal physical initial mass.
The inverse classical gauge reduces renormalized solutions to ordinary NLS;
the established full-source gauge restores the renormalized spectral flow.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The spectral mass is exactly the physical mass of an arbitrary real H¹ representative. -/
theorem sourceOrdinaryMass_sobolevSource (a : realTypeSobolevSourceLocus) :
    sourceOrdinaryMass le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ =
      classicalNLSMass (periodOneSobolevSynthesis a.val.1) := by
  rw [classicalNLSMass,toLp_periodOneSobolevSynthesis,norm_l2Synthesis,Coeff.norm_periodDouble]
  unfold sourceOrdinaryMass sourceOrdinaryComplexMass
  have he : CoeffPair.exponentInclusion (le_rfl : (2 : ℝ≥0∞) ≤ 2) (sobolevSourceInclusion a.val) =
      sobolevSourceInclusion a.val := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n <;> rfl
  rw [he]
  rw [← periodOneSobolevMass_eq_sourceHilbertMass,periodOneSobolevMass_real_eq,Complex.ofReal_re]

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The full-source gauge respects the physical Hilbert realization. -/
theorem sourceFirstPeriodOneL2_hamiltonianRenormalizedFlow_gauge
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (time : ℝ) :
    sourceFirstPeriodOneL2 (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time) =
      classicalNLSGaugePhase (sourceOrdinaryMass le_rfl φ) time •
        sourceFirstPeriodOneL2 (A.hamiltonianOrdinarySourceFlow D le_rfl φ time) := by
  rw [sourceFirstPeriodOneL2,(A.hamiltonianRenormalizedSourceFlow_gauge hs hP hr D le_rfl φ time).1,
    map_smul,map_smul]
  rfl

/-- Every classical renormalized trajectory with physical initial mass and
an H¹ initial representative is the actual spectral renormalized flow. -/
theorem classicalRenormalizedNLS_toLp_eq_hamiltonianFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (a : realTypeSobolevSourceLocus) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u 0)) u)
    (hinit : u 0 = periodOneSobolevSynthesis a.val.1) (time : ℝ) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time) =
      sourceFirstPeriodOneL2 (A.hamiltonianRenormalizedSourceFlow D le_rfl
        ⟨sobolevSourceInclusion a.val,a.property⟩ time) := by
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a.val,a.property⟩
  let M := sourceOrdinaryMass le_rfl φ
  have hm : classicalNLSMass (u 0) = M := by
    rw [hinit]
    exact (sourceOrdinaryMass_sobolevSource a).symm
  have hu' : IsClassicalRenormalizedNLSTrajectory M u := by simpa only [hm] using hu
  have hzero : classicalNLSGauge (-M) u 0 = periodOneSobolevSynthesis a.val.1 := by
    simpa only [classicalNLSGauge_zero_time] using hinit
  have ho := A.classicalNLS_toLp_eq_hamiltonianFlow hs hP hr D a _ hu'.ungauge hzero time
  have hc : classicalNLSGauge M (classicalNLSGauge (-M) u) = u := by
    rw [classicalNLSGauge_add,add_neg_cancel,classicalNLSGauge_zero]
  have he := congrArg (fun v : ℝ → C(AddCircle (2 : ℝ), ℂ) =>
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (v time)) hc
  calc
    _ = classicalNLSGaugePhase M time •
        ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (classicalNLSGauge (-M) u time) := by
      simpa only [classicalNLSGauge,map_smul] using he.symm
    _ = classicalNLSGaugePhase M time • sourceFirstPeriodOneL2
        (A.hamiltonianOrdinarySourceFlow D le_rfl φ time) := congrArg _ ho
    _ = _ := (A.sourceFirstPeriodOneL2_hamiltonianRenormalizedFlow_gauge hs hP hr D φ time).symm

/-- Every original coefficient equals the actual Fourier integral of the
classical renormalized trajectory, including at negative times. -/
theorem classicalRenormalizedNLS_periodOneCoefficient_eq_hamiltonianFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (a : realTypeSobolevSourceLocus) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (u 0)) u)
    (hinit : u 0 = periodOneSobolevSynthesis a.val.1) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (A.hamiltonianRenormalizedSourceFlow D le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ time).val.fst n := by
  have he : fourierCoeff (u time) (2*n) =
      periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n := by
    rw [← periodTwoCoefficient_circle]
    exact periodTwoCoefficient_periodic_even _ (hu.periodic time)
      (((u time).continuous.comp (AddCircle.continuous_mk' (2 : ℝ))).intervalIntegrable 0 1) n
  have hi := congrArg (fun f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ))) => fourierCoeff f (2*n))
    (A.classicalRenormalizedNLS_toLp_eq_hamiltonianFlow hs hP hr D a u hu hinit time)
  exact ((fourierCoeff_toLp (u time) (2*n)).trans he).symm.trans
    (hi.trans (fourierCoeff_sourceFirstPeriodOneL2 _ n))

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
