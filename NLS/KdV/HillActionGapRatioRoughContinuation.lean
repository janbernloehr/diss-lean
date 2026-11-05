import NLS.KdV.HillActionGapRatioAllBase
import NLS.KdV.HillHminusPhysicalPeriodicLabels
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Physical action ratios continue from an L2 germ across a rough ball

The original physical ratio is real analytic on every real scaling line,
including through collapsed gaps. A rough analytic candidate that agrees
on an original L2 germ therefore agrees at every physical L2 source in
its entire H^-1 ball, even when the L2 norm of that source is large.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

def hillPhysicalRealScale (p : RealPeriodOneHillPotential) (t : ℝ) : RealPeriodOneHillPotential :=
  ⟨(t : ℂ) • p.val,by
    constructor
    · rw [map_smul]
      exact (Coeff.paritySubspace 0).smul_mem _ p.property.1
    · rw [map_smul]
      exact p.property.2.smul_real t⟩

theorem continuous_hillPhysicalRealScale (p : RealPeriodOneHillPotential) :
    Continuous (hillPhysicalRealScale p) := by
  apply Continuous.subtype_mk
  exact Complex.continuous_ofReal.smul continuous_const

theorem hillPhysicalHminusEmbedding_realScale (p : RealPeriodOneHillPotential) (t : ℝ) :
    (hillPhysicalHminusEmbedding (hillPhysicalRealScale p t)).val =
      (t : ℂ) • (hillPhysicalHminusEmbedding p).val := by
  apply Subtype.ext
  funext j
  simp only [hillPhysicalHminusEmbedding_apply,hillPhysicalRealScale,map_smul,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,WeightedCoeff.smul_val]

theorem analyticAt_hillActionGapRatio_realScale (p : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    AnalyticAt ℝ (fun s => hillActionGapRatio (hillPhysicalRealScale p s).val
      (hillPhysicalRealScale p s).property.1 (hillPhysicalRealScale p s).property.2 n) t := by
  let q := hillPhysicalRealScale p t
  let P : ℝ → Coeff 2 := fun s => SpectralWeight.one.toCoeff (hillPhysicalRealScale p s).val
  have hP : AnalyticAt ℝ P t := by
    let L : ℝ →L[ℝ] Coeff 2 :=
      (ContinuousLinearMap.id ℝ ℝ).smulRight (SpectralWeight.one.toCoeff p.val)
    have he : P = L := by
      funext s
      simp only [P,hillPhysicalRealScale,map_smul]
      rfl
    rw [he]
    exact L.analyticAt t
  have ha := (analyticAt_hillLocalActionGapRatio q.val q.property.1 q.property.2 n hn).restrictScalars
    (𝕜 := ℝ)
  have hlocal : AnalyticAt ℝ (fun s => hillLocalActionGapRatio q.val q.property.1 q.property.2 n (P s)) t :=
    ha.comp (f := P) hP
  have he := (continuous_hillPhysicalRealScale p).continuousAt.tendsto.eventually
    (hillLocalActionGapRatio_eventually_eq_physical q.val q.property.1 q.property.2 n hn)
  exact hlocal.congr he

theorem hillActionGapRatio_eq_on_rough_ball_of_germ
    (η : ℝ) (hη : 0 < η) (n : ℕ) (hn : 1 ≤ n)
    (R : PeriodOneHminusOne → ℂ) (hR : AnalyticOnNhd ℂ R (ball 0 η))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff
      (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (hgerm : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      R (hillPhysicalHminusEmbedding p).val = hillActionGapRatio p.val p.property.1 p.property.2 n)
    (p : RealPeriodOneHillPotential)
    (hp : (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η) :
    R (hillPhysicalHminusEmbedding p).val = hillActionGapRatio p.val p.property.1 p.property.2 n := by
  let L : ℝ →L[ℝ] PeriodOneHminusOne :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (hillPhysicalHminusEmbedding p).val
  let U : Set ℝ := L ⁻¹' ball (0 : PeriodOneHminusOne) η
  let f : ℝ → ℂ := fun t => R (L t)
  let g : ℝ → ℂ := fun t => hillActionGapRatio (hillPhysicalRealScale p t).val
    (hillPhysicalRealScale p t).property.1 (hillPhysicalRealScale p t).property.2 n
  have hf : AnalyticOnNhd ℝ f U := fun t ht =>
    ((hR (L t) ht).restrictScalars (𝕜 := ℝ)).comp (L.analyticAt t)
  have hg : AnalyticOnNhd ℝ g U := fun t _ => analyticAt_hillActionGapRatio_realScale p n hn t
  have hU : IsPreconnected U := ((convex_ball (0 : PeriodOneHminusOne) η).linear_preimage L.toLinearMap).isPreconnected
  have h0 : (0 : ℝ) ∈ U := by
    change L 0 ∈ ball 0 η
    rw [map_zero]
    exact mem_ball_self hη
  have h1 : (1 : ℝ) ∈ U := by simpa only [U,L,mem_preimage,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul] using hp
  have hscale0 : hillPhysicalRealScale p 0 = ⟨0,h0q,h0r⟩ := by
    apply Subtype.ext
    simp only [hillPhysicalRealScale,ofReal_zero,zero_smul]
  have he : Tendsto (hillPhysicalRealScale p) (𝓝 (0 : ℝ))
      (𝓝 (hillPhysicalRealScale p 0)) :=
    (continuous_hillPhysicalRealScale p).continuousAt.tendsto
  rw [hscale0] at he
  have hfg : f =ᶠ[𝓝 (0 : ℝ)] g := by
    filter_upwards [he.eventually hgerm] with t ht
    change R (L t) = _
    rw [hillPhysicalHminusEmbedding_realScale] at ht
    exact ht
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hU h0 hfg h1
  simpa only [f,g,L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
    one_smul,hillPhysicalRealScale,ofReal_one] using heq

end NLS.KdV
