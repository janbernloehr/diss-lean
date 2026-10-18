import NLS.ZakharovShabat.SourceWeightedEtaComplexBound
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Native weighted analyticity of eta

Both actual signs preserve every spectral weight analytically near each weighted real source. The coefficient equalities exclude the fallback on the stated domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted realization of the actual signed eta coordinate; local membership rules out the fallback. -/
def normalizedWeightedEtaSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight)
    (sign : ℂ) (ψ : CoeffPair p) : Coeff p :=
  Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign
    (normalizedWeightedSource w ψ))

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- Native weighted eta coordinates are analytic near every weighted real source, with exact evaluations. -/
theorem exists_local_normalizedWeightedEta_analytic
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ sign : ℂ, sign = 1 ∨ sign = -1 →
        AnalyticOnNhd ℂ (normalizedWeightedEtaSequence hp hp1 s w sign) U ∧
        ∀ ψ ∈ U, ‖normalizedWeightedEtaSequence hp hp1 s w sign ψ‖ ≤ M ∧
          ∀ n, normalizedWeightedEtaSequence hp hp1 s w sign ψ n =
            (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign (normalizedWeightedSource w ψ) := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ue,hUe,hφe,hUeW,M,hM,he⟩ := D.exists_local_normalizedWeightedEta_bound w φ
  obtain ⟨Ur,hUr,hφr,hroot⟩ := exists_local_sourceNormalizedActionRoot_uniform_lower hp hp1 φu
  obtain ⟨Ua,hUa,hφa,hra,_⟩ := exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φu.val φu.property
  let U := Ue ∩ normalizedWeightedSource w ⁻¹' (Ur ∩ Ua)
  have hU : IsOpen U := hUe.inter ((hUr.inter hUa).preimage (continuous_normalizedWeightedSource w))
  have hcoord (ψ : CoeffPair p) (hψ : ψ ∈ U) (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) (n : ℤ) :
      normalizedWeightedEtaSequence hp hp1 s w sign ψ n =
        (w (2*n):ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign (normalizedWeightedSource w ψ) :=
    Coeff.ofFunctionOrZero_apply_of_mem p _ (he ψ hψ.1 sign hsign).1 n
  refine ⟨U,hU,⟨hφe,hφr,hφa⟩,M,hM,?_⟩
  intro sign hsign
  refine ⟨?_,fun ψ hψ => ⟨(he ψ hψ.1 sign hsign).2,hcoord ψ hψ sign hsign⟩⟩
  apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ M (fun ψ hψ => (he ψ hψ.1 sign hsign).2)
  intro n ψ hψ
  let z := normalizedWeightedSource w ψ
  have hzW : z ∈ W := hUeW ψ hψ.1
  have hzne : sourceNormalizedActionRoot hp hp1 n z ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (hroot z hψ.2.1 n).1)
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  have hx := (ex.analyticAt _).comp (D.analytic z hzW)
  have hy := (ey.analyticAt _).comp (D.analytic z hzW)
  have hsigned : AnalyticAt ℂ (sourceBirkhoffWeightedCoordinate hp hp1 n s sign) z := by
    have h : AnalyticAt ℂ (fun χ : CoeffPair p => (Real.sqrt 8:ℂ)/2*
        (ex (sourceBirkhoffMap hp hp1 s χ)+sign*I*ey (sourceBirkhoffMap hp hp1 s χ))) z :=
      analyticAt_const.mul (hx.add (analyticAt_const.mul hy))
    apply h.congr
    filter_upwards [D.source_open.mem_nhds hzW] with χ hχ
    have hχxy := D.coordinates χ hχ n
    change (Real.sqrt 8:ℂ)/2*((sourceBirkhoffMap hp hp1 s χ).1 n+
      sign*I*(sourceBirkhoffMap hp hp1 s χ).2 n) = _
    rw [hχxy.1,hχxy.2]
    exact (sourceBirkhoffWeightedCoordinate_eq_rectangular hp hp1 n s sign χ hsign).symm
  have hinverse : AnalyticAt ℂ (fun χ =>
      (sourceNormalizedActionRoot hp hp1 n χ)⁻¹*sourceBirkhoffWeightedCoordinate hp hp1 n s sign χ*
        exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s χ)) z :=
    (((hra n z hψ.2.2).inv hzne).mul hsigned).mul
      ((analyticAt_const.mul (D.angular.beta_series.analytic_correction n z (D.source_subset hzW))).cexp')
  have hcomp : AnalyticAt ℂ (fun χ : CoeffPair p =>
      (sourceNormalizedActionRoot hp hp1 n (normalizedWeightedSource w χ))⁻¹*
        sourceBirkhoffWeightedCoordinate hp hp1 n s sign (normalizedWeightedSource w χ)*
        exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s (normalizedWeightedSource w χ))) ψ :=
    hinverse.comp (f := normalizedWeightedSource w) (x := ψ) ((normalizedWeightedSourceCLM (p := p) w).analyticAt ψ)
  have hweighted : AnalyticAt ℂ (fun χ : CoeffPair p => (w (2*n):ℂ)*
      ((sourceNormalizedActionRoot hp hp1 n (normalizedWeightedSource w χ))⁻¹*
        sourceBirkhoffWeightedCoordinate hp hp1 n s sign (normalizedWeightedSource w χ)*
        exp (-sign*I*sourceAngularBetaCorrection hp hp1 n s (normalizedWeightedSource w χ)))) ψ :=
    analyticAt_const.mul hcomp
  apply hweighted.congr
  filter_upwards [hU.mem_nhds hψ] with χ hχ
  have hχne : sourceNormalizedActionRoot hp hp1 n (normalizedWeightedSource w χ) ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (hroot _ hχ.2.1 n).1)
  exact (congrArg (fun v : ℂ => (w (2*n):ℂ)*v)
    (sourceGapWeightedEtaCoordinate_eq_inverse_normalization hp hp1 n s sign _ hχne).symm).trans
      (hcoord χ hχ sign hsign n).symm

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
