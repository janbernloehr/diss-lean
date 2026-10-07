import NLS.ZakharovShabat.SourceSobolevActionAnalytic
import NLS.ZakharovShabat.SourceActionFiniteGapDifferential

/-! # The physical weighted-action differential at finite-gap H¹ sources

Coordinate evaluation and bounded ℓ¹ summation differentiate the actual
infinite weighted action series. At finite-gap sources the action
cotangents vanish outside a fixed finite set. The derivative therefore
extends to an explicit bounded functional on the original Hilbert source
space, even though the kinetic weights grow quadratically.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Each coordinate of the weighted sequence derivative is the weighted
original action differential applied to the included H¹ direction. -/
theorem sourceSobolevWeightedActionSequence_fderiv_apply
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (h : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (fderiv ℂ sourceSobolevWeightedActionSequence a h) n =
      (2*(Real.pi : ℂ)*n)^2 *
        (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a)) (sobolevSourceInclusion h) := by
  obtain ⟨U,hU,haU,he,hA⟩ := exists_local_sourceSobolevWeightedActionSequence_analytic a ha
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 n
  have hd := (ev.hasFDerivAt.comp a (hA a haU).differentiableAt.hasFDerivAt).fderiv
  have hcoord : (fun b => ev (sourceSobolevWeightedActionSequence b)) =ᶠ[𝓝 a]
      (fun b => sourceSobolevWeightedAction b n) := by
    filter_upwards [hU.mem_nhds haU] with b hb
    exact he b hb n
  have hact := ((analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) n
    (sobolevSourceInclusion a) ha).differentiableAt.hasFDerivAt.comp a
      sobolevSourceInclusion.hasFDerivAt).const_smul ((2*(Real.pi : ℂ)*n)^2)
  have hh := hcoord.fderiv_eq.symm.trans hd
  have heval := (congrArg (fun L : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ℂ => L h) hh).symm
  have hact' : fderiv ℂ (fun b => sourceSobolevWeightedAction b n) a =
      ((2*(Real.pi : ℂ)*n)^2) •
        (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a)).comp sobolevSourceInclusion := hact.fderiv
  rw [hact'] at heval
  exact heval

/-- Bounded summation differentiates the weighted spectral series into a finite sum. -/
theorem sourceSobolevWeightedActionSum_fderiv_eq_finite_sum
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (sobolevSourceInclusion a) = 0) (h : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ sourceSobolevWeightedActionSum a h =
      ∑ n ∈ S, (2*(Real.pi : ℂ)*n)^2 *
        (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a)) (sobolevSourceInclusion h) := by
  obtain ⟨U,_,haU,_,hA⟩ := exists_local_sourceSobolevWeightedActionSequence_analytic a ha
  have hd := ((lp.tsumCLM ℂ ℤ ℂ).hasFDerivAt.comp a
    (hA a haU).differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ ((lp.tsumCLM ℂ ℤ ℂ) ∘ sourceSobolevWeightedActionSequence) a h = _
  rw [hd]
  change (∑' n : ℤ, (fderiv ℂ sourceSobolevWeightedActionSequence a h) n) = _
  simp only [sourceSobolevWeightedActionSequence_fderiv_apply a ha h]
  apply tsum_eq_sum
  intro n hn
  simp [hS n hn]

/-- The weighted differential at finite gap extends to a bounded Hilbert source functional. -/
theorem sourceSobolevWeightedActionSum_fderiv_eq_comp
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (sobolevSourceInclusion a) = 0) :
    fderiv ℂ sourceSobolevWeightedActionSum a =
      (∑ n ∈ S, (2*(Real.pi : ℂ)*n)^2 •
        fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a)).comp sobolevSourceInclusion := by
  apply ContinuousLinearMap.ext
  intro h
  rw [sourceSobolevWeightedActionSum_fderiv_eq_finite_sum a ha S hS h]
  simp

/-- Every actual real finite-gap H¹ source has one finite formula valid on all H¹ directions. -/
theorem exists_sourceSobolevWeightedActionSum_finiteGap_differential
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (hf : (⟨sobolevSourceInclusion a,ha⟩ : realTypeSourceSubmodule 2) ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ S : Finset ℤ, fderiv ℂ sourceSobolevWeightedActionSum a =
      (∑ n ∈ S, (2*(Real.pi : ℂ)*n)^2 •
        fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
          (sobolevSourceInclusion a)).comp sobolevSourceInclusion := by
  obtain ⟨S,hS⟩ := exists_sourceComplexAction_fderiv_support (by simp) (by norm_num)
    ⟨sobolevSourceInclusion a,ha⟩ hf
  exact ⟨S,sourceSobolevWeightedActionSum_fderiv_eq_comp a ha S hS⟩

end NLS.ZakharovShabat
