import NLS.KdV.HillL2AllGapSquares
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Full endpoint continuity and removal of collapsed Hill gaps -/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem tendsto_hillL2ContinuedPrimitive_lower_all
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ) :
    Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (-conj (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x))) := by
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [conj_ofReal] using (continuous_conj.tendsto (x : ℂ)).mono_left
        (nhdsWithin_le_nhds : 𝓝[{z : ℂ | z.im < 0}] (x : ℂ) ≤ 𝓝 (x : ℂ))
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa only [conj_im, neg_pos] using hz
  have hu := (tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x).comp hc
  have hl := (continuous_conj.continuousAt.tendsto.comp hu).neg
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he := hillL2ContinuedPrimitive_conj _ hr z
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne)
  have hh := congrArg (fun w : ℂ => -conj w) he
  simpa only [Function.comp_def, map_neg, conj_conj, neg_neg] using hh

theorem continuousAt_hillL2RealCutPrimitive_of_re_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hre : (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re = 0) :
    ContinuousAt (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) (x : ℂ) := by
  have hv : -conj (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
      hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x := by
    apply Complex.ext <;> simp [hre]
  exact continuousAt_realBoundaryExtension_of_limits _ _ x
    (continuous_hillL2UpperBoundaryPrimitive q hq hr).continuousAt
    (tendsto_hillL2UpperBoundaryPrimitive_all q hq hr x)
    (by simpa only [hv] using tendsto_hillL2ContinuedPrimitive_lower_all q hq hr x)

theorem continuousAt_hillL2RealCutPrimitive_label
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) :
    ContinuousAt (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q))
      (hillRealLabels q hq hr j : ℂ) := by
  apply continuousAt_hillL2RealCutPrimitive_of_re_zero q hq hr
  rw [hillL2UpperBoundaryPrimitive_label_indexed q hq hr j]
  simp

theorem analyticAt_hillL2RealCutPrimitive_collapsed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2 * n - 1) = hillRealLabels q hq hr (2 * n)) :
    AnalyticAt ℂ (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q))
      (hillRealLabels q hq hr (2 * n - 1) : ℂ) := by
  obtain ⟨hd, hη, hl, _, hsub⟩ := hillRealGapContour_geometry q hq hr n hn
  have hd0 : hillRealGapHalfLength q hq hr n = 0 := by simp [hillRealGapHalfLength, hc]
  have hcenter : hillRealGapCenter q hq hr n = hillRealLabels q hq hr (2 * n - 1) := by
    simpa only [hd0, sub_zero] using hl
  have hpunc : ball (hillRealLabels q hq hr (2 * n - 1) : ℂ) (2 * hillRealGapCollar q hq hr n) \
      {(hillRealLabels q hq hr (2 * n - 1) : ℂ)} ⊆ hillL2RealCutDomain q hq hr := by
    simpa only [hd0, zero_add, hcenter, ← hc, segment_same] using hsub
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _
    (continuousAt_hillL2RealCutPrimitive_label q hq hr (2 * n - 1))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_ball.mem_nhds
    (mem_ball_self (by positivity : 0 < 2 * hillRealGapCollar q hq hr n) :
      (hillRealLabels q hq hr (2 * n - 1) : ℂ) ∈ ball _ (2 * hillRealGapCollar q hq hr n)))]
    with z hz hzB
  exact (analyticOnNhd_hillL2RealCutPrimitive q hq hr z (hpunc ⟨hzB, hz⟩)).differentiableAt

end NLS.KdV
