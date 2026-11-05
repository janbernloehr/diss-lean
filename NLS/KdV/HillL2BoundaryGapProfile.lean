import NLS.KdV.HillL2RegularBoundary
import NLS.KdV.HillRealGapIntegrals
import NLS.ComplexAnalysis.RealCoshTrace

/-! # Boundary profiles on every real Hill band and gap

The actual upper primitive is purely imaginary in every open band.
Its real part is the positive arcosh profile in every open gap, with
one constant integer phase throughout that gap. These results have no
high-index restriction. Identifying that integer with `-n` and filling
the branch endpoints are separate steps.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2UpperBoundaryPrimitive_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (x : ℝ) (hx : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0) :
    2 * cosh (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
      ((hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re : ℂ) := by
  rw [(hillL2UpperBoundary_data q hq hr x hx).2.2.2.1]
  apply Complex.ext
  · rfl
  · exact hillL2Discriminant_real _ hr x

theorem hillL2UpperBoundaryPrimitive_re_eq_zero_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n)) (hillRealLabels q hq hr (2 * n + 1))) :
    (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re = 0 := by
  have hreg := hillL2Radicand_ne_zero_between_labels q hq hr (2 * n) x hx
  have hb := hillL2Discriminant_open_band_bounds q hq hr n x hx
  exact re_eq_zero_of_real_cosh_trace_band _ _
    (hillL2UpperBoundaryPrimitive_trace q hq hr x hreg) (abs_le.mpr ⟨hb.1.le, hb.2.le⟩)

theorem hillL2UpperBoundaryPrimitive_gap_profile
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    0 < (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re ∧
      (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).re =
        hillRealGapProfile (SpectralWeight.one.toCoeff q) n x ∧
      Real.sin (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im = 0 := by
  have hreg : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0 := by
    intro he
    have hp := hillL2Radicand_pos_gap q hq hr n hn x hx
    simp only [he, zero_re, lt_self_iff_false] at hp
  have hgt := hillL2Discriminant_signed_gap_gt_two q hq hr n hn x hx
  have hs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow]; norm_num
  have habs : |(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re| =
      (-1 : ℝ) ^ n * (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re := by
    calc
      _ = |(-1 : ℝ) ^ n * (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re| := by
        rw [abs_mul, hs, one_mul]
      _ = _ := abs_of_pos (by linarith)
  have hp := re_eq_arcosh_of_real_cosh_trace_gap _ _
    (hillL2UpperBoundaryPrimitive_trace q hq hr x hreg)
    (hillL2UpperBoundaryPrimitive_re_nonneg q hq hr x hreg) (by rw [habs]; exact hgt)
  simpa only [habs, hillRealGapProfile] using hp

/-- Every open intrinsic gap has one actual logarithmic phase. This
does not yet identify the phase integer with the spectral index. -/
theorem exists_hillL2UpperBoundaryPrimitive_gap_phase
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillRealLabels q hq hr (2 * n - 1) < hillRealLabels q hq hr (2 * n)) :
    ∃ k : ℤ, ∀ x ∈ Ioo (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n)),
      hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x =
        (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) + I * (k : ℂ) * Real.pi := by
  let a := (hillRealLabels q hq hr (2 * n - 1) + hillRealLabels q hq hr (2 * n)) / 2
  have ha : a ∈ Ioo (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n)) := by
    constructor <;> dsimp [a] <;> linarith
  let f : ℝ → ℝ := fun x => (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im
  have hreg (x : ℝ) (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n - 1))
      (hillRealLabels q hq hr (2 * n))) : hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0 := by
    apply hillL2Radicand_ne_zero_between_labels q hq hr (2 * n - 1) x
    simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using hx
  have hf : ContinuousOn f (Ioo (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :=
    continuous_im.comp_continuousOn (fun x hx =>
      (hillL2UpperBoundary_data q hq hr x (hreg x hx)).2.2.1.continuousAt.continuousWithinAt)
  have hsin (x : ℝ) (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n - 1))
      (hillRealLabels q hq hr (2 * n))) : Real.sin (f x) = 0 :=
    (hillL2UpperBoundaryPrimitive_gap_profile q hq hr n hn x hx).2.2
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp (hsin a ha)
  have hphase := phase_eq_on_of_sin_eq_zero f _ isPreconnected_Ioo hf hsin a ha
  refine ⟨k, fun x hx => ?_⟩
  apply Complex.ext
  · simpa only [add_re, ofReal_re, mul_re, mul_im, I_re, I_im, intCast_re, intCast_im,
      ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, neg_zero, zero_add, add_zero] using
      (hillL2UpperBoundaryPrimitive_gap_profile q hq hr n hn x hx).2.1
  · have he : f x = (k : ℝ) * Real.pi := (hphase x hx).trans hk.symm
    simpa only [f, add_im, ofReal_im, mul_re, mul_im, I_re, I_im, intCast_re, intCast_im,
      ofReal_re, zero_mul, mul_zero, sub_zero, zero_add, add_zero, one_mul] using he

/-- The literal unshifted primitive jump has the exact real profile
on every open gap interior, including low gaps. -/
theorem hillL2ContinuedPrimitive_gap_vertical_jump
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2 * n - 1)) (hillRealLabels q hq hr (2 * n))) :
    Tendsto (fun ε : ℝ =>
      hillL2ContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, SpectralWeight.one.toCoeff q) -
        hillL2ContinuedPrimitive ((x : ℂ) - (ε : ℂ) * I, SpectralWeight.one.toCoeff q))
      (𝓝[>] 0) (𝓝 (2 * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ))) := by
  have hreg := hillL2Radicand_ne_zero_between_labels q hq hr (2 * n - 1) x
    (by simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using hx)
  have hlim := (tendsto_hillL2UpperBoundaryPrimitive q hq hr x hreg).comp
    (tendsto_real_upper_vertical x)
  have hsum := hlim.add (continuous_conj.continuousAt.tendsto.comp hlim)
  dsimp only [Function.comp_def] at hsum
  have heq : (fun ε : ℝ =>
      hillL2ContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, SpectralWeight.one.toCoeff q) +
        conj (hillL2ContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, SpectralWeight.one.toCoeff q))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ =>
        hillL2ContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, SpectralWeight.one.toCoeff q) -
          hillL2ContinuedPrimitive ((x : ℂ) - (ε : ℂ) * I, SpectralWeight.one.toCoeff q)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have him : 0 < ((x : ℂ) + (ε : ℂ) * I).im := by simpa using hε
    have he := hillL2ContinuedPrimitive_conj _ hr ((x : ℂ) + (ε : ℂ) * I)
      (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr _ him.ne')
    have hc : conj ((x : ℂ) + (ε : ℂ) * I) = (x : ℂ) - (ε : ℂ) * I := by simp [sub_eq_add_neg]
    rw [hc] at he
    rw [he, sub_neg_eq_add]
  have hvalue : hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x +
      conj (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x) =
      2 * (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by
    apply Complex.ext
    · have hp := (hillL2UpperBoundaryPrimitive_gap_profile q hq hr n hn x hx).2.1
      simpa only [add_re, conj_re, two_mul, ofReal_re] using congrArg (fun u : ℝ => u + u) hp
    · simp
  exact hvalue ▸ hsum.congr' heq

end NLS.KdV
