import NLS.KdV.HillHminusOneRealBands

/-! # The actual upper and lower H^-1 Hill primitives continue through bands

At a regular real point with purely imaginary boundary primitive,
minus-conjugate reflection fixes the local upper extension. Its lower
restriction is therefore the actual lower source primitive as well.
In particular both sheets glue holomorphically across every open band.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem HillHminusUpperRegularExtension.two_sided_source
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x ρ : ℝ) (hρ : 0 < ρ) (L G : ℂ → ℂ)
    (h : HillHminusUpperRegularExtension (q) x ρ L G)
    (hre : (hillHminusUpperBoundaryPrimitive (q) x).re = 0) :
    EqOn L (fun z => hillHminusContinuedRoot (z, q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) ∧
      EqOn G (fun z => hillHminusContinuedPrimitive (z, q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) := by
  have hx : (x : ℂ) ∈ ball (x : ℂ) ρ := mem_ball_self hρ
  have hGx : G x = -conj (G x) := by
    have hz : (G x).re = 0 := (congrArg Complex.re (h.boundary_eq x hx).2).symm.trans hre
    apply Complex.ext <;> simp [hz]
  have hLx : L x = -conj (L x) := by
    calc
      L x = 2 * sinh (G x) := (h.data x hx).2.2.2.2.symm
      _ = -conj (2 * sinh (G x)) := by
        conv_lhs => rw [hGx]
        simp only [sinh_neg, sinh_conj, map_mul, map_ofNat]
        ring
      _ = -conj (L x) := by rw [(h.data x hx).2.2.2.2]
  have hexp (z : ℂ) (hz : z ∈ ball (x : ℂ) ρ) :
      exp (G z) = (hillHminusDiscriminant (q) z + L z) / 2 := by
    rw [← (h.data z hz).2.2.2.1, ← (h.data z hz).2.2.2.2, ← cosh_add_sinh]
    ring
  have hreflect := traceRoot_primitive_reflection (hillHminusDiscriminant (q))
    L G (ball (x : ℂ) ρ) (convex_ball _ _).isPreconnected
    (fun z hz => by simpa only [mem_ball, dist_conj_comm, conj_ofReal] using hz)
    (fun z _ => hillHminusDiscriminant_conj _ hr z) h.root_analytic.continuousOn h.analytic.continuousOn
    (fun z hz => (h.data z hz).2.1) (fun z hz => (h.data z hz).1) hexp x hx
    (by simpa only [conj_ofReal] using hLx) (by simpa only [conj_ofReal] using hGx)
  have hP : EqOn G (fun z => hillHminusContinuedPrimitive (z, q))
      (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) := by
    intro z hz
    rcases lt_or_gt_of_ne hz.2 with hlower | hupper
    · have hzB : conj z ∈ ball (x : ℂ) ρ := by
        simpa only [mem_ball, dist_conj_comm, conj_ofReal] using hz.1
      have hzU : 0 < (conj z).im := by simpa only [conj_im, neg_pos] using hlower
      have hs := h.source ⟨hzB, hzU⟩
      have hf := hillHminusContinuedPrimitive_conj _ hr z
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.2)
      have he : -conj (G z) = -conj (hillHminusContinuedPrimitive (z, q)) :=
        (hreflect z hz.1).2.symm.trans (hs.trans hf)
      have hh := congrArg (fun w : ℂ => -conj w) he
      simpa only [map_neg, conj_conj, neg_neg] using hh
    · exact h.source ⟨hz.1, hupper⟩
  refine ⟨?_, hP⟩
  intro z hz
  calc
    L z = 2 * sinh (G z) := (h.data z hz.1).2.2.2.2.symm
    _ = 2 * sinh (hillHminusContinuedPrimitive (z, q)) := by rw [hP hz]
    _ = _ := (hillHminusContinuedPrimitive_trace _
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hz.2)).2

theorem exists_hillHminusBandExtension
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n)) (hillHminusRealLabels q hr (2 * n + 1))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L G : ℂ → ℂ,
      HillHminusUpperRegularExtension (q) x ρ L G ∧
      EqOn L (fun z => hillHminusContinuedRoot (z, q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) ∧
      EqOn G (fun z => hillHminusContinuedPrimitive (z, q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillHminusUpperRegularExtension q hr x
    (hillHminusRadicand_ne_zero_between_labels q hr (2 * n) x hx)
  exact ⟨ρ, hρ, L, G, h, h.two_sided_source q hr x ρ hρ L G
    (hillHminusUpperBoundaryPrimitive_re_eq_zero_band q hr n x hx)⟩

/-- The source primitive with its actual real band values filled in. -/
def hillHminusRealCutPrimitive (q : PeriodOneHminusOne) (z : ℂ) : ℂ :=
  if z.im = 0 then hillHminusUpperBoundaryPrimitive q z.re else hillHminusContinuedPrimitive (z, q)

theorem analyticOnNhd_hillHminusRealCutPrimitive
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    AnalyticOnNhd ℂ (hillHminusRealCutPrimitive (q))
      (hillHminusRealCutDomain q hr) := by
  intro z hz
  by_cases hne : z.im ≠ 0
  · apply ((analyticOnNhd_hillHminusContinuedPrimitive _
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hne)).comp
        (f := fun w : ℂ => (w, q))
        (analyticAt_id.prod analyticAt_const)).congr
    filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds hne] with w hw
    exact (if_neg hw).symm
  · have hz0 : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [not_ne_iff.mp hne]
    obtain ⟨n, hn⟩ := hz.resolve_left hne
    obtain ⟨ρ, hρ, L, G, h, _, hsource⟩ := exists_hillHminusBandExtension q hr n z.re hn
    have hzB : z ∈ ball (z.re : ℂ) ρ := hz0.symm ▸ mem_ball_self hρ
    apply (h.analytic z hzB).congr
    filter_upwards [isOpen_ball.mem_nhds hzB] with w hw
    by_cases hw0 : w.im = 0
    · have hwC : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw0]
      have hb := (h.boundary_eq w.re (hwC ▸ hw)).2
      simpa only [hillHminusRealCutPrimitive, if_pos hw0, ← hwC] using hb.symm
    · exact (hsource ⟨hw, hw0⟩).trans (if_neg hw0).symm

/-- Filling a real point by its actual upper limit preserves the original
source primitive wherever that source primitive was already defined. -/
theorem hillHminusRealCutPrimitive_eq_source (q : PeriodOneHminusOne) (z : ℂ)
    (hz : (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusRealCutPrimitive q z = hillHminusContinuedPrimitive (z,q) := by
  by_cases hi : z.im = 0
  · have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    let := real_upper_nhds_neBot z.re
    have hc : ContinuousAt (fun w : ℂ => hillHminusContinuedPrimitive (w,q)) z :=
      ((analyticOnNhd_hillHminusContinuedPrimitive (z,q) hz).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)).continuousAt
    have ht : Tendsto (fun w : ℂ => hillHminusContinuedPrimitive (w,q))
        (𝓝[{w : ℂ | 0 < w.im}] (z.re : ℂ)) (𝓝 (hillHminusContinuedPrimitive (z,q))) := by
      rw [he]
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hillHminusRealCutPrimitive,if_pos hi,hillHminusUpperBoundaryPrimitive] using ht.limUnder_eq
  · exact if_neg hi

/-- On the original source domain, the band-filled formula is jointly
analytic in energy and complex H^-1 potential with exactly the old branch. -/
theorem analyticOnNhd_hillHminusRealCutPrimitive_source :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusRealCutPrimitive t.2 t.1)
      hillHminusContinuationDomain := by
  intro t ht
  apply (analyticOnNhd_hillHminusContinuedPrimitive t ht).congr
  filter_upwards [isOpen_hillHminusContinuationDomain.mem_nhds ht] with a ha
  exact (hillHminusRealCutPrimitive_eq_source a.2 a.1 ha).symm

def hillHminusRealCutRoot (q : PeriodOneHminusOne) (z : ℂ) : ℂ :=
  2*sinh (hillHminusRealCutPrimitive q z)

theorem hillHminusRealCutRoot_eq_source (q : PeriodOneHminusOne) (z : ℂ)
    (hz : (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusRealCutRoot q z = hillHminusContinuedRoot (z,q) := by
  rw [hillHminusRealCutRoot,hillHminusRealCutPrimitive_eq_source q z hz]
  exact (hillHminusContinuedPrimitive_trace (z,q) hz).2

theorem hillHminusRealCutPrimitive_trace
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    2*cosh (hillHminusRealCutPrimitive q z) = hillHminusDiscriminant q z := by
  by_cases hi : z.im = 0
  · have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hreg : hillHminusRadicand q (z.re : ℂ) ≠ 0 := by
      rw [he]
      exact hillHminusRadicand_ne_zero_on_realCutDomain q hr z hz
    have ht := (hillHminusUpperBoundary_data q hr z.re hreg).2.2.2.1
    simpa only [hillHminusRealCutPrimitive,if_pos hi,he] using ht
  · rw [hillHminusRealCutPrimitive,if_neg hi]
    exact (hillHminusContinuedPrimitive_trace (z,q)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hi)).1

theorem analyticOnNhd_hillHminusRealCutRoot
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    AnalyticOnNhd ℂ (hillHminusRealCutRoot q) (hillHminusRealCutDomain q hr) := by
  intro z hz
  exact analyticAt_const.mul (Complex.analyticAt_sinh.comp
    (analyticOnNhd_hillHminusRealCutPrimitive q hr z hz))

theorem hillHminusRealCutRoot_sq
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    hillHminusRealCutRoot q z^2 = hillHminusRadicand q z := by
  have ht := hillHminusRealCutPrimitive_trace q hr z hz
  have hh := cosh_sq_sub_sinh_sq (hillHminusRealCutPrimitive q z)
  rw [hillHminusRealCutRoot,hillHminusRadicand,← ht]
  linear_combination -4*hh

theorem hillHminusRealCutRoot_ne_zero
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) : hillHminusRealCutRoot q z ≠ 0 := by
  intro hzero
  have hs := hillHminusRealCutRoot_sq q hr z hz
  rw [hzero,zero_pow (by norm_num : 2 ≠ 0)] at hs
  exact hillHminusRadicand_ne_zero_on_realCutDomain q hr z hz hs.symm

theorem exp_hillHminusRealCutPrimitive
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    exp (hillHminusRealCutPrimitive q z) =
      (hillHminusDiscriminant q z+hillHminusRealCutRoot q z)/2 := by
  rw [hillHminusRealCutRoot,← hillHminusRealCutPrimitive_trace q hr z hz]
  rw [show (2*cosh (hillHminusRealCutPrimitive q z)+2*sinh (hillHminusRealCutPrimitive q z))/2 =
    cosh (hillHminusRealCutPrimitive q z)+sinh (hillHminusRealCutPrimitive q z) by ring]
  exact (cosh_add_sinh _).symm

theorem HillHminusUpperRegularExtension.realCutPrimitive_germ
    {q : PeriodOneHminusOne} {x ρ : ℝ} {L G : ℂ → ℂ}
    (h : HillHminusUpperRegularExtension q x ρ L G)
    (hsource : EqOn G (fun z => hillHminusContinuedPrimitive (z,q))
      (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}))
    (z : ℂ) (hz : z ∈ ball (x : ℂ) ρ) : hillHminusRealCutPrimitive q =ᶠ[𝓝 z] G := by
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw
  by_cases hi : w.im = 0
  · have he : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hi]
    have hb := (h.boundary_eq w.re (he ▸ hw)).2
    simpa only [hillHminusRealCutPrimitive,if_pos hi,← he] using hb
  · exact (if_neg hi).trans (hsource ⟨hw,hi⟩).symm

theorem hasDerivAt_hillHminusRealCutPrimitive
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    HasDerivAt (hillHminusRealCutPrimitive q)
      (deriv (hillHminusDiscriminant q) z/hillHminusRealCutRoot q z) z := by
  by_cases hi : z.im ≠ 0
  · have hs := mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hi
    have heq : hillHminusRealCutPrimitive q =ᶠ[𝓝 z]
        (fun w => hillHminusContinuedPrimitive (w,q)) := by
      filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds hi] with w hw
      exact if_neg hw
    rw [hillHminusRealCutRoot_eq_source q z hs]
    exact (hasDerivAt_hillHminusContinuedPrimitive (z,q) hs).congr_of_eventuallyEq heq
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [not_ne_iff.mp hi]
    obtain ⟨n,hn⟩ := hz.resolve_left hi
    obtain ⟨ρ,hρ,L,G,h,_,hsource⟩ := exists_hillHminusBandExtension q hr n z.re hn
    have hzB : z ∈ ball (z.re : ℂ) ρ := he.symm ▸ mem_ball_self hρ
    have heq := h.realCutPrimitive_germ hsource z hzB
    have hroot : hillHminusRealCutRoot q z = L z := by
      rw [hillHminusRealCutRoot,heq.eq_of_nhds]
      exact (h.data z hzB).2.2.2.2
    rw [hroot]
    exact ((h.data z hzB).2.2.1).congr_of_eventuallyEq heq

/-- The original minus-conjugate reflection survives the actual gluing
through real bands. No new root sign or logarithm period is chosen. -/
theorem hillHminusRealCutPrimitive_conj
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    hillHminusRealCutPrimitive q (conj z) = -conj (hillHminusRealCutPrimitive q z) := by
  by_cases hi : z.im = 0
  · obtain ⟨n,hn⟩ := hz.resolve_left (not_ne_iff.mpr hi)
    have hre := hillHminusUpperBoundaryPrimitive_re_eq_zero_band q hr n z.re hn
    have he : conj z = z := by apply Complex.ext <;> simp [hi]
    rw [he,hillHminusRealCutPrimitive,if_pos hi]
    apply Complex.ext
    · simpa only [neg_re,conj_re] using (by linarith :
        (hillHminusUpperBoundaryPrimitive q z.re).re = -(hillHminusUpperBoundaryPrimitive q z.re).re)
    · simp only [neg_im,conj_im,neg_neg]
  · have hs := mem_hillHminusContinuationDomain_of_im_ne_zero q hr z hi
    have hsc := mem_hillHminusContinuationDomain_conj q hr z hs
    rw [hillHminusRealCutPrimitive_eq_source q (conj z) hsc,
      hillHminusRealCutPrimitive_eq_source q z hs,hillHminusContinuedPrimitive_conj q hr z hs]

theorem hillHminusRealCutRoot_conj
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) :
    hillHminusRealCutRoot q (conj z) = -conj (hillHminusRealCutRoot q z) := by
  rw [hillHminusRealCutRoot,hillHminusRealCutRoot,
    hillHminusRealCutPrimitive_conj q hr z hz,sinh_neg,sinh_conj,map_mul,map_ofNat]
  ring

end NLS.KdV
