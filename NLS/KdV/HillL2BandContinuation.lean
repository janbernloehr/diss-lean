import NLS.KdV.HillL2GlobalGapBoundaryValues

/-! # The actual upper and lower Hill primitives continue through bands

At a regular real point with purely imaginary boundary primitive,
minus-conjugate reflection fixes the local upper extension. Its lower
restriction is therefore the actual lower source primitive as well.
In particular both sheets glue holomorphically across every open band.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem HillL2UpperRegularExtension.two_sided_source
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x ρ : ℝ) (hρ : 0 < ρ) (L G : ℂ → ℂ)
    (h : HillL2UpperRegularExtension (SpectralWeight.one.toCoeff q) x ρ L G)
    (hre : (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re = 0) :
    EqOn L (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) ∧
      EqOn G (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
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
      exp (G z) = (hillL2Discriminant (SpectralWeight.one.toCoeff q) z + L z) / 2 := by
    rw [← (h.data z hz).2.2.2.1, ← (h.data z hz).2.2.2.2, ← cosh_add_sinh]
    ring
  have hreflect := traceRoot_primitive_reflection (hillL2Discriminant (SpectralWeight.one.toCoeff q))
    L G (ball (x : ℂ) ρ) (convex_ball _ _).isPreconnected
    (fun z hz => by simpa only [mem_ball, dist_conj_comm, conj_ofReal] using hz)
    (fun z _ => hillL2Discriminant_conj _ hr z) h.root_analytic.continuousOn h.analytic.continuousOn
    (fun z hz => (h.data z hz).2.1) (fun z hz => (h.data z hz).1) hexp x hx
    (by simpa only [conj_ofReal] using hLx) (by simpa only [conj_ofReal] using hGx)
  have hP : EqOn G (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) := by
    intro z hz
    rcases lt_or_gt_of_ne hz.2 with hlower | hupper
    · have hzB : conj z ∈ ball (x : ℂ) ρ := by
        simpa only [mem_ball, dist_conj_comm, conj_ofReal] using hz.1
      have hzU : 0 < (conj z).im := by simpa only [conj_im, neg_pos] using hlower
      have hs := h.source ⟨hzB, hzU⟩
      have hf := hillL2ContinuedPrimitive_conj _ hr z
        (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.2)
      have he : -conj (G z) = -conj (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)) :=
        (hreflect z hz.1).2.symm.trans (hs.trans hf)
      have hh := congrArg (fun w : ℂ => -conj w) he
      simpa only [map_neg, conj_conj, neg_neg] using hh
    · exact h.source ⟨hz.1, hupper⟩
  refine ⟨?_, hP⟩
  intro z hz
  calc
    L z = 2 * sinh (G z) := (h.data z hz.1).2.2.2.2.symm
    _ = 2 * sinh (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)) := by rw [hP hz]
    _ = _ := (hillL2ContinuedPrimitive_trace _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.2)).2

theorem exists_hillL2BandExtension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n)) (hillRealLabels q hq hr (2 * n + 1))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ L G : ℂ → ℂ,
      HillL2UpperRegularExtension (SpectralWeight.one.toCoeff q) x ρ L G ∧
      EqOn L (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) ∧
      EqOn G (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
        (ball (x : ℂ) ρ ∩ {z : ℂ | z.im ≠ 0}) := by
  obtain ⟨ρ, hρ, L, G, h⟩ := exists_hillL2UpperRegularExtension q hq hr x
    (hillL2Radicand_ne_zero_between_labels q hq hr (2 * n) x hx)
  exact ⟨ρ, hρ, L, G, h, h.two_sided_source q hq hr x ρ hρ L G
    (hillL2UpperBoundaryPrimitive_re_eq_zero_band q hq hr n x hx)⟩

/-- The source primitive with its actual real band values filled in. -/
def hillL2RealCutPrimitive (q : Coeff 2) (z : ℂ) : ℂ :=
  if z.im = 0 then hillL2UpperBoundaryPrimitive q z.re else hillL2ContinuedPrimitive (z, q)

/-- Both half-planes and all open real spectral bands. Characteristic
endpoints and real gap interiors are excluded. -/
def hillL2RealCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) : Set ℂ :=
  {z | z.im ≠ 0 ∨ ∃ n : ℕ,
    z.re ∈ Ioo (hillRealLabels q hq hr (2 * n)) (hillRealLabels q hq hr (2 * n + 1))}

theorem isOpen_hillL2RealCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    IsOpen (hillL2RealCutDomain q hq hr) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases hz with hne | ⟨n, hn⟩
  · exact Filter.mem_of_superset ((isOpen_ne_fun continuous_im continuous_const).mem_nhds hne)
      (fun w hw => Or.inl hw)
  · exact Filter.mem_of_superset ((isOpen_Ioo.preimage continuous_re).mem_nhds hn)
      (fun w hw => Or.inr ⟨n, hw⟩)

theorem analyticOnNhd_hillL2RealCutPrimitive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q))
      (hillL2RealCutDomain q hq hr) := by
  intro z hz
  by_cases hne : z.im ≠ 0
  · apply ((analyticOnNhd_hillL2ContinuedPrimitive _
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hne)).comp
        (f := fun w : ℂ => (w, SpectralWeight.one.toCoeff q))
        (analyticAt_id.prod analyticAt_const)).congr
    filter_upwards [(isOpen_ne_fun continuous_im continuous_const).mem_nhds hne] with w hw
    exact (if_neg hw).symm
  · have hz0 : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [not_ne_iff.mp hne]
    obtain ⟨n, hn⟩ := hz.resolve_left hne
    obtain ⟨ρ, hρ, L, G, h, _, hsource⟩ := exists_hillL2BandExtension q hq hr n z.re hn
    have hzB : z ∈ ball (z.re : ℂ) ρ := hz0.symm ▸ mem_ball_self hρ
    apply (h.analytic z hzB).congr
    filter_upwards [isOpen_ball.mem_nhds hzB] with w hw
    by_cases hw0 : w.im = 0
    · have hwC : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw0]
      have hb := (h.boundary_eq w.re (hwC ▸ hw)).2
      simpa only [hillL2RealCutPrimitive, if_pos hw0, ← hwC] using hb.symm
    · exact (hsource ⟨hw, hw0⟩).trans (if_neg hw0).symm

end NLS.KdV
