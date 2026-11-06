import NLS.KdV.HillHminusOneRegularBoundary
import NLS.KdV.HillHminusOneRealGapProfile
import NLS.KdV.HillHminusOneRealBands
import NLS.ComplexAnalysis.RealCoshTrace

/-! # Boundary profiles on every real Hill band and gap

The actual upper primitive is purely imaginary in every open band.
Its real part is the positive arcosh profile in every open gap, with
one constant integer phase throughout that gap. These results have no
high-index restriction. Identifying that integer with `-n` and filling
the branch endpoints are separate steps.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusUpperBoundaryPrimitive_gap_profile
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :
    0 < (hillHminusUpperBoundaryPrimitive q x).re ∧
      (hillHminusUpperBoundaryPrimitive q x).re =
        hillHminusRealGapProfile q n x ∧
      Real.sin (hillHminusUpperBoundaryPrimitive q x).im = 0 := by
  have hreg : hillHminusRadicand q x ≠ 0 := by
    intro he
    have hp := hillHminusRadicand_pos_gap q hr n hn x hx
    simp only [he, zero_re, lt_self_iff_false] at hp
  have hgt := hillHminusDiscriminant_signed_gap_gt_two q hr n hn x hx
  have hs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow]; norm_num
  have habs : |(hillHminusDiscriminant q x).re| =
      (-1 : ℝ) ^ n * (hillHminusDiscriminant q x).re := by
    calc
      _ = |(-1 : ℝ) ^ n * (hillHminusDiscriminant q x).re| := by
        rw [abs_mul, hs, one_mul]
      _ = _ := abs_of_pos (by linarith)
  have hp := re_eq_arcosh_of_real_cosh_trace_gap _ _
    (hillHminusUpperBoundaryPrimitive_trace q hr x hreg)
    (hillHminusUpperBoundaryPrimitive_re_nonneg q hr x hreg) (by rw [habs]; exact hgt)
  simpa only [habs, hillHminusRealGapProfile] using hp

/-- Every open intrinsic gap has one actual logarithmic phase. This
does not yet identify the phase integer with the spectral index. -/
theorem exists_hillHminusUpperBoundaryPrimitive_gap_phase
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillHminusRealLabels q hr (2 * n - 1) < hillHminusRealLabels q hr (2 * n)) :
    ∃ k : ℤ, ∀ x ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n)),
      hillHminusUpperBoundaryPrimitive q x =
        (hillHminusRealGapProfile q n x : ℂ) + I * (k : ℂ) * Real.pi := by
  let a := (hillHminusRealLabels q hr (2 * n - 1) + hillHminusRealLabels q hr (2 * n)) / 2
  have ha : a ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n)) := by
    constructor <;> dsimp [a] <;> linarith
  let f : ℝ → ℝ := fun x => (hillHminusUpperBoundaryPrimitive q x).im
  have hreg (x : ℝ) (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1))
      (hillHminusRealLabels q hr (2 * n))) : hillHminusRadicand q x ≠ 0 := by
    apply hillHminusRadicand_ne_zero_between_labels q hr (2 * n - 1) x
    simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using hx
  have hf : ContinuousOn f (Ioo (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :=
    continuous_im.comp_continuousOn (fun x hx =>
      (hillHminusUpperBoundary_data q hr x (hreg x hx)).2.2.1.continuousAt.continuousWithinAt)
  have hsin (x : ℝ) (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1))
      (hillHminusRealLabels q hr (2 * n))) : Real.sin (f x) = 0 :=
    (hillHminusUpperBoundaryPrimitive_gap_profile q hr n hn x hx).2.2
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp (hsin a ha)
  have hphase := phase_eq_on_of_sin_eq_zero f _ isPreconnected_Ioo hf hsin a ha
  refine ⟨k, fun x hx => ?_⟩
  apply Complex.ext
  · simpa only [add_re, ofReal_re, mul_re, mul_im, I_re, I_im, intCast_re, intCast_im,
      ofReal_im, zero_mul, mul_zero, sub_zero, zero_sub, neg_zero, zero_add, add_zero] using
      (hillHminusUpperBoundaryPrimitive_gap_profile q hr n hn x hx).2.1
  · have he : f x = (k : ℝ) * Real.pi := (hphase x hx).trans hk.symm
    simpa only [f, add_im, ofReal_im, mul_re, mul_im, I_re, I_im, intCast_re, intCast_im,
      ofReal_re, zero_mul, mul_zero, sub_zero, zero_add, add_zero, one_mul] using he

/-- The literal unshifted primitive jump has the exact real profile
on every open gap interior, including low gaps. -/
theorem hillHminusContinuedPrimitive_gap_vertical_jump
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n - 1)) (hillHminusRealLabels q hr (2 * n))) :
    Tendsto (fun ε : ℝ =>
      hillHminusContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, q) -
        hillHminusContinuedPrimitive ((x : ℂ) - (ε : ℂ) * I, q))
      (𝓝[>] 0) (𝓝 (2 * (hillHminusRealGapProfile q n x : ℂ))) := by
  have hreg := hillHminusRadicand_ne_zero_between_labels q hr (2 * n - 1) x
    (by simpa only [show 2 * n - 1 + 1 = 2 * n by omega] using hx)
  have hlim := (tendsto_hillHminusUpperBoundaryPrimitive q hr x hreg).comp
    (tendsto_real_upper_vertical x)
  have hsum := hlim.add (continuous_conj.continuousAt.tendsto.comp hlim)
  dsimp only [Function.comp_def] at hsum
  have heq : (fun ε : ℝ =>
      hillHminusContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, q) +
        conj (hillHminusContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, q))) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ =>
        hillHminusContinuedPrimitive ((x : ℂ) + (ε : ℂ) * I, q) -
          hillHminusContinuedPrimitive ((x : ℂ) - (ε : ℂ) * I, q)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have him : 0 < ((x : ℂ) + (ε : ℂ) * I).im := by simpa using hε
    have he := hillHminusContinuedPrimitive_conj _ hr ((x : ℂ) + (ε : ℂ) * I)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hr _ him.ne')
    have hc : conj ((x : ℂ) + (ε : ℂ) * I) = (x : ℂ) - (ε : ℂ) * I := by simp [sub_eq_add_neg]
    rw [hc] at he
    rw [he, sub_neg_eq_add]
  have hvalue : hillHminusUpperBoundaryPrimitive q x +
      conj (hillHminusUpperBoundaryPrimitive q x) =
      2 * (hillHminusRealGapProfile q n x : ℂ) := by
    apply Complex.ext
    · have hp := (hillHminusUpperBoundaryPrimitive_gap_profile q hr n hn x hx).2.1
      simpa only [add_re, conj_re, two_mul, ofReal_re] using congrArg (fun u : ℝ => u + u) hp
    · simp
  exact hvalue ▸ hsum.congr' heq

end NLS.KdV
