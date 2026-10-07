import NLS.ZakharovShabat.ClassicalRenormalizedNLSContinuousExtension
import NLS.ZakharovShabat.ClassicalNLSContinuousExtension

/-! # The physical mass gauge for the full ordinary and renormalized flows

Classical Fourier agreement gives the exact mass phase on finite-gap data.
Density and source-norm continuity extend both component identities to
every initial source in 1 < p ≤ 2, at every real time. No gauge-equivariance
premise about the Birkhoff coordinates is imposed.
-/
noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite-gap physical integral equals the analytic source mass
throughout the exponent range in which the latter is defined. -/
theorem sourceFiniteGapPhysicalMass_eq_sourceOrdinaryMass
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapPhysicalMass hp hp1 φ hf = sourceOrdinaryMass hp2 φ := by
  have hm := sourceFiniteGapHilbertModel_eq_of_coefficients hp hp1 φ hf
    (realTypeSourceExponentInclusion hp2 φ) (fun _ => ⟨rfl,rfl⟩)
  rw [sourceFiniteGapPhysicalMass_eq_hilbertMass,hm,← sourceOrdinaryMass_exponent hp2 le_rfl]

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W P V B X : Set (CoeffPair p)}
variable {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual finite-gap Fourier coefficients retain the classical positive mass phase. -/
theorem hamiltonianRenormalizedSourceFlow_fst_eq_gauge_finiteGap
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (time : ℝ) (n : ℤ) :
    (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.fst n =
      classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time *
        (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst n := by
  rw [A.hamiltonianRenormalizedSourceFlow_fst_eq_classical hs D hp2 φ hf,
    A.hamiltonianOrdinarySourceFlow_fst_eq_classical hs D hp2 φ hf]
  change periodOneCoefficient (fun x : ℝ =>
    classicalNLSGaugePhase (sourceFiniteGapPhysicalMass hp hp1 φ hf) time *
      sourceFiniteGapClassicalTrajectory hp hp1 φ hf time (x : AddCircle (2 : ℝ))) n = _
  rw [sourceFiniteGapPhysicalMass_eq_sourceOrdinaryMass hp hp1 hp2 φ hf]
  exact fourierCoeffOn.const_smul _ _ n (by norm_num : (0 : ℝ) < 1)

/-- Density extends the exact physical gauge relation to all source data
in 1 < p ≤ 2, without requiring pointwise representatives of those data. -/
theorem hamiltonianRenormalizedSourceFlow_fst_eq_gauge
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (time : ℝ) (n : ℤ) :
    (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.fst n =
      classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time *
        (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst n := by
  let ev := (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    (WithLp.fstL p ℂ (Coeff p) (Coeff p))).restrictScalars ℝ).comp (realTypeSourceSubmodule p).subtypeL
  have hR : Continuous (fun ψ => (A.hamiltonianRenormalizedSourceFlow D hp2 ψ time).val.fst n) :=
    ev.continuous.comp ((A.analytic_hamiltonianRenormalizedSourceFlow hs hP hr D hp2 time).continuous)
  have hO : Continuous (fun ψ => (A.hamiltonianOrdinarySourceFlow D hp2 ψ time).val.fst n) :=
    ev.continuous.comp ((A.analytic_hamiltonianOrdinarySourceFlow hs hP hr D hp2 time).continuous)
  have hphase : Continuous (fun m : ℝ => classicalNLSGaugePhase m time) := by
    unfold classicalNLSGaugePhase
    fun_prop
  have hG := (hphase.comp (analytic_sourceOrdinaryMass hp2).continuous).mul hO
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  have he : (fun j => (A.hamiltonianRenormalizedSourceFlow D hp2 (ψ j) time).val.fst n) =
      fun j => classicalNLSGaugePhase (sourceOrdinaryMass hp2 (ψ j)) time *
        (A.hamiltonianOrdinarySourceFlow D hp2 (ψ j) time).val.fst n :=
    funext (fun j => A.hamiltonianRenormalizedSourceFlow_fst_eq_gauge_finiteGap
      hs.toSourcePsiIsolatingComplexExtension D hp2 (ψ j) (hf j) time n)
  have hlim := hR.continuousAt.tendsto.comp hψ
  change Tendsto (fun j => (A.hamiltonianRenormalizedSourceFlow D hp2 (ψ j) time).val.fst n)
    atTop (𝓝 _) at hlim
  rw [he] at hlim
  exact tendsto_nhds_unique hlim (hG.continuousAt.tendsto.comp hψ)

/-- The second source component has the opposite physical mass phase,
including for arbitrary rough data in the Hilbert-compatible exponent range. -/
theorem hamiltonianRenormalizedSourceFlow_snd_eq_gauge
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (time : ℝ) (n : ℤ) :
    (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.snd n =
      conj (classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time) *
        (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.snd n := by
  calc
    _ = conj ((A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.fst (-n)) :=
      (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).property n
    _ = conj (classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time *
        (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst (-n)) :=
      congrArg conj (A.hamiltonianRenormalizedSourceFlow_fst_eq_gauge hs hP hr D hp2 φ time (-n))
    _ = conj (classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time) *
        conj ((A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst (-n)) := map_mul _ _ _
    _ = _ := congrArg (fun z => conj (classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time)*z)
      ((A.hamiltonianOrdinarySourceFlow D hp2 φ time).property n).symm

/-- Both entire Fourier sequences satisfy the mass-gauge identity in the
original source space, with no finite-gap restriction. -/
theorem hamiltonianRenormalizedSourceFlow_gauge
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P)
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (time : ℝ) :
    (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.fst =
        classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time •
          (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.fst ∧
    (A.hamiltonianRenormalizedSourceFlow D hp2 φ time).val.snd =
        conj (classicalNLSGaugePhase (sourceOrdinaryMass hp2 φ) time) •
          (A.hamiltonianOrdinarySourceFlow D hp2 φ time).val.snd := by
  constructor <;> ext n
  · exact A.hamiltonianRenormalizedSourceFlow_fst_eq_gauge hs hP hr D hp2 φ time n
  · exact A.hamiltonianRenormalizedSourceFlow_snd_eq_gauge hs hP hr D hp2 φ time n

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
