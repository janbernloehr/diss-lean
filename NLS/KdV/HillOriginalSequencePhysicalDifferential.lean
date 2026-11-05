import NLS.KdV.HillOriginalRealSpectralAnalytic
import NLS.KdV.HillOriginalCartesianGardnerFamily
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- The literal original even-index H-minus-one source inclusion on its
real Banach subspace. -/
def hillOriginalRealHminusInclusion : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
  (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL

/-- Every coordinate of the ACTUAL sequence derivative is the restriction
of ANY original physically matched analytic H-minus-one Cartesian germ.
This identifies the Banach derivative with the original scalar calculus,
with its exact sqrt(2*pi*n) target normalization. -/
theorem hillOriginalRealSpectralMap_coordinate_fderiv
    (q : hillRealSourceSubmodule) (k : ℕ) (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val,q.property⟩ : RealPeriodOneHillPotential),
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian true ⟨k+1,by omega⟩ p) :
    ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k).restrictScalars ℝ).comp
      (fderiv ℝ hillOriginalRealSpectralMap q) =
      (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ) •
        (((fderiv ℂ F (hillOriginalHminusSource q.val)).restrictScalars ℝ).comp hillOriginalRealHminusInclusion) := by
  let L := hillOriginalRealHminusInclusion
  let C : ℂ := Real.sqrt (2*Real.pi*(k+1 : ℕ))
  let e := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k).restrictScalars ℝ
  have hFL : HasFDerivAt F
      ((fderiv ℂ F (hillOriginalHminusSource q.val)).restrictScalars ℝ) (L q) :=
    hF.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hFd : HasFDerivAt (fun r : hillRealSourceSubmodule => C • F (L r))
      (C • (((fderiv ℂ F (hillOriginalHminusSource q.val)).restrictScalars ℝ).comp L)) q :=
    (hFL.comp q L.hasFDerivAt).const_smul C
  have hQ : Continuous (fun r : hillRealSourceSubmodule =>
      (⟨r.val,r.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have he : (fun r : hillRealSourceSubmodule => e (hillOriginalRealSpectralMap r)) =ᶠ[𝓝 q]
      (fun r => C • F (L r)) := by
    filter_upwards [hQ.continuousAt.tendsto.eventually hFM] with r hr
    change hillOriginalBaseSpectralSequence (⟨r.val,r.property⟩ : RealPeriodOneHillPotential) k = _
    rw [hillOriginalBaseSpectralSequence_apply,←hr]
    rfl
  have hseq : HasFDerivAt (fun r : hillRealSourceSubmodule => e (hillOriginalRealSpectralMap r))
      (e.comp (fderiv ℝ hillOriginalRealSpectralMap q)) q :=
    e.hasFDerivAt.comp q (hasFDerivAt_hillOriginalRealSpectralMap q)
  exact hseq.unique (hFd.congr_of_eventuallyEq he)

/-- The derivative of the ACTUAL original sequence map has simultaneous
physical scalar representatives carrying the complete original Gardner
matrix, at every original mean-zero real L2 source and all closed gaps. -/
theorem exists_hillOriginalRealSpectralMap_physical_Gardner_differential
    (q : hillRealSourceSubmodule) (hmean : q.val.val 0 = 0) :
    ∃ Z : Bool → ℕ+ → PeriodOneHminusOne → ℂ,
      (∀ (σ : Bool) (n : ℕ+),
        AnalyticAt ℂ (Z σ n) (hillOriginalHminusSource q.val) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q.val,q.property⟩ : RealPeriodOneHillPotential),
          Z σ n (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p) ∧
      (∀ k : ℕ,
        ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℕ => ℂ) 2 k).restrictScalars ℝ).comp
          (fderiv ℝ hillOriginalRealSpectralMap q) =
          (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ) •
            (((fderiv ℂ (Z true ⟨k+1,by omega⟩) (hillOriginalHminusSource q.val)).restrictScalars ℝ).comp
              hillOriginalRealHminusInclusion)) ∧
      ∀ (σ τ : Bool) (n m : ℕ+),
        NLS.Poisson.hminusGardnerBracket (Z σ n) (Z τ m) (hillOriginalHminusSource q.val) =
          hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  obtain ⟨Z,hZ,hM⟩ := exists_hillOriginal_signedCartesian_hminus_Gardner_matrix_all_gaps
    (⟨q.val,q.property⟩ : RealPeriodOneHillPotential) hmean
  refine ⟨Z,hZ,?_,hM⟩
  intro k
  exact hillOriginalRealSpectralMap_coordinate_fderiv q k _
    (hZ true ⟨k+1,by omega⟩).1 (hZ true ⟨k+1,by omega⟩).2

end NLS.KdV
