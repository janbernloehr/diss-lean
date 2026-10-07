import NLS.ZakharovShabat.SourceClassicalNLSApproximation

/-! # Ordinary spectral flow agrees with arbitrary classical H¹ data

Two independently proved limits of H¹ finite-gap approximations coincide:
PDE stability gives the classical physical trajectory, while continuity of
the spectral flow gives its Fourier-Lebesgue source trajectory. Hilbert
synthesis identifies the limits with the correct period-one normalization.
-/
noncomputable section
open Set Filter Topology MeasureTheory NLS.Fourier
namespace NLS.ZakharovShabat

/-- Physical L² realization of the first original period-one source component. -/
def sourceFirstPeriodOneL2 (φ : realTypeSourceSubmodule 2) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ))) :=
  l2Synthesis (Coeff.periodDouble φ.val.fst)

theorem continuous_sourceFirstPeriodOneL2 : Continuous sourceFirstPeriodOneL2 := by
  exact l2Synthesis.continuous.comp (Coeff.periodDouble.continuous.comp
    (continuous_fst.comp ((CoeffPair.toMax 2).continuous.comp continuous_subtype_val)))

/-- The physical unit-period coefficient is the even ambient-circle mode. -/
theorem fourierCoeff_sourceFirstPeriodOneL2 (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    fourierCoeff (sourceFirstPeriodOneL2 φ) (2*n) = φ.val.fst n := by
  rw [sourceFirstPeriodOneL2,fourierCoeff_l2Synthesis,Coeff.periodDouble_even]

/-- The H¹ and L² realizations agree, with doubling of the ambient circle modes. -/
theorem toLp_periodOneSobolevSynthesis (a : ScalarDomain 2) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (periodOneSobolevSynthesis a) =
      l2Synthesis (Coeff.periodDouble (scalarInclusion a)) := by
  rw [periodOneSobolevSynthesis_eq,toLp_sobolevSynthesis]
  congr 1
  ext n
  rw [scalarInclusion_apply,Coeff.periodDoubleSobolev_apply]

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The constructed finite-gap continuous flow is the Hilbert realization
of its original spectral source coefficients. -/
theorem toLp_hamiltonianOrdinaryContinuousFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (A.hamiltonianOrdinaryContinuousFlow D φ hf time) =
      sourceFirstPeriodOneL2 (A.hamiltonianOrdinarySourceFlow D le_rfl φ time) := by
  rw [hamiltonianOrdinaryContinuousFlow,toLp_periodOneSobolevSynthesis]
  congr 2
  ext n
  exact scalarInclusion_apply _ n

/-- Every classical solution whose initial data are represented in H¹ agrees
with the actual spectral ordinary flow at every real time. No finite-gap
hypothesis on the initial source or uniform bound on approximants is supplied. -/
theorem classicalNLS_toLp_eq_hamiltonianFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (a : realTypeSobolevSourceLocus) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalNLSTrajectory u) (hinit : u 0 = periodOneSobolevSynthesis a.val.1) (time : ℝ) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time) =
      sourceFirstPeriodOneL2 (A.hamiltonianOrdinarySourceFlow D le_rfl
        ⟨sobolevSourceInclusion a.val,a.property⟩ time) := by
  obtain ⟨b,hf,hb⟩ := mem_closure_iff_seq_limit.mp (dense_sourceSobolevFiniteGapLocus a)
  have hlim := (A.tendstoUniformlyOn_finiteGap_classicalNLS hs.toSourcePsiIsolatingComplexExtension D
    a b hf hb u hu hinit |time|).tendsto_at (show time ∈ Icc (-|time|) |time| from
      ⟨neg_abs_le time,le_abs_self time⟩)
  have hin : Continuous (fun c : realTypeSobolevSourceLocus =>
      (⟨sobolevSourceInclusion c.val,c.property⟩ : realTypeSourceSubmodule 2)) :=
    (sobolevSourceInclusion.continuous.comp continuous_subtype_val).subtype_mk _
  have hflow := (A.analytic_hamiltonianOrdinarySourceFlow hs hP hr D le_rfl time).continuous
  have hlim' := (continuous_sourceFirstPeriodOneL2.comp (hflow.comp hin)).continuousAt.tendsto.comp hb
  have he := hlim.congr' (Filter.Eventually.of_forall (fun j =>
    A.toLp_hamiltonianOrdinaryContinuousFlow D
      ⟨sobolevSourceInclusion (b j).val,(b j).property⟩ (hf j) time))
  exact tendsto_nhds_unique he hlim'

/-- Agreement also holds for every literal physical Fourier integral. -/
theorem classicalNLS_periodOneCoefficient_eq_hamiltonianFlow
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P s)
    (hP : IsOpen P) (hr : realTypeSourceLocus 2 ⊆ P)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (a : realTypeSobolevSourceLocus) (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalNLSTrajectory u) (hinit : u 0 = periodOneSobolevSynthesis a.val.1) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (A.hamiltonianOrdinarySourceFlow D le_rfl ⟨sobolevSourceInclusion a.val,a.property⟩ time).val.fst n := by
  have he : fourierCoeff (u time) (2*n) =
      periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n := by
    rw [← periodTwoCoefficient_circle]
    exact periodTwoCoefficient_periodic_even _ (hu.periodic time)
      (((u time).continuous.comp (AddCircle.continuous_mk' (2 : ℝ))).intervalIntegrable 0 1) n
  have hi := congrArg (fun f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ))) => fourierCoeff f (2*n))
    (A.classicalNLS_toLp_eq_hamiltonianFlow hs hP hr D a u hu hinit time)
  exact ((fourierCoeff_toLp (u time) (2*n)).trans he).symm.trans
    (hi.trans (fourierCoeff_sourceFirstPeriodOneL2 _ n))

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
