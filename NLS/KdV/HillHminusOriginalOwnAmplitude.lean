import NLS.KdV.HillHminusIntrinsicActionGapRatio
import NLS.KdV.HillHminusOriginalOwnGapFactor
import NLS.KdV.HillOwnAmplitudeAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillHminusIntrinsicActionGapPrefactor (n : ℕ) (p : PeriodOneHminusOne) : ℂ :=
  Complex.sqrt (2*hillHminusIntrinsicActionGapRatio q hq hr n p)

theorem analyticAt_hillHminusIntrinsicActionGapPrefactor (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (hillHminusIntrinsicActionGapPrefactor q hq hr n) (hillOriginalHminusSource q) := by
  have hbase := (hillHminusIntrinsicActionGapRatio_eventually_eq_physical q hq hr n hn).self_of_nhds
  have hpos := (hillActionGapRatio_real_positive q hq hr n hn).1
  have hslit : 2*hillHminusIntrinsicActionGapRatio q hq hr n (hillOriginalHminusSource q) ∈ Complex.slitPlane := by
    rw [hbase,Complex.mem_slitPlane_iff]
    left
    have he : (2*hillActionGapRatio q hq hr n).re = 2*(hillActionGapRatio q hq hr n).re := by norm_num [mul_re]
    rw [he]
    exact mul_pos (by norm_num : (0 : ℝ) < 2) hpos
  have hA : AnalyticAt ℂ (fun p : PeriodOneHminusOne => 2*hillHminusIntrinsicActionGapRatio q hq hr n p) (hillOriginalHminusSource q) :=
    analyticAt_const.mul (analyticAt_hillHminusIntrinsicActionGapRatio q hq hr n hn)
  exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hslit)).comp
    (f := fun p : PeriodOneHminusOne => 2*hillHminusIntrinsicActionGapRatio q hq hr n p) hA

theorem hillHminusIntrinsicActionGapPrefactor_eventually_eq_physical (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillHminusIntrinsicActionGapPrefactor q hq hr n (hillOriginalHminusSource p.val) =
        hillActionGapPrefactor p.val p.property.1 p.property.2 n := by
  filter_upwards [hillHminusIntrinsicActionGapRatio_eventually_eq_physical q hq hr n hn] with p hp
  have hR := hillActionGapRatio_real_positive p.val p.property.1 p.property.2 n hn
  have he : hillActionGapRatio p.val p.property.1 p.property.2 n =
      ((hillActionGapRatio p.val p.property.1 p.property.2 n).re : ℂ) := by
    apply Complex.ext <;> simp [hR.2]
  rw [hillHminusIntrinsicActionGapPrefactor,hp,he,← ofReal_ofNat,← ofReal_mul,
    Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hR.1.le)),ofReal_re]
  rfl

/-- The exact ORIGINAL own Cartesian amplitude has an analytic
H-minus-one germ at EVERY original real source and positive index,
INCLUDING collapsed own gaps, with its fixed physical sign retained. -/
theorem exists_hillOriginal_ownCartesianAmplitude_hminus_physical_germ
    (p : RealPeriodOneHillPotential) (n : ℕ+) :
    ∃ F : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ F (hillOriginalHminusSource p.val) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 p,
        F (hillOriginalHminusSource r.val) =
          hillOwnCartesianAmplitude r.val r.property.1 r.property.2 n n.pos := by
  obtain ⟨G,hG,hGM⟩ := exists_hillOriginal_ownGapFactor_hminus_physical_germ p n
  let A := hillHminusIntrinsicActionGapPrefactor p.val p.property.1 p.property.2 n
  refine ⟨fun a => A a*G a,
    (analyticAt_hillHminusIntrinsicActionGapPrefactor p.val p.property.1 p.property.2 n n.pos).mul hG,?_⟩
  filter_upwards [hillHminusIntrinsicActionGapPrefactor_eventually_eq_physical p.val p.property.1 p.property.2 n n.pos,
    hGM] with r hrA hrG
  change hillHminusIntrinsicActionGapPrefactor p.val p.property.1 p.property.2 n
    (hillOriginalHminusSource r.val)*G (hillOriginalHminusSource r.val) = _
  rw [hrA,hrG]
  rfl

end NLS.KdV
