import NLS.KdV.HillHminusOneRegularBoundary
import NLS.ComplexAnalysis.RealCoshTrace

/-! # The actual real H^-1 Hill trace in every open spectral band

Intrinsic ordering excludes characteristic roots between consecutive
labels. The physical endpoint parity and the intermediate value theorem
then place the actual trace strictly between -2 and 2 in every open
band, including the band adjacent to the lowest energy.
-/

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminusDiscriminant_zero_in_band
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) (n : ℕ) :
    ∃ x ∈ Ioo (hillHminusRealLabels q hreal (2*n)) (hillHminusRealLabels q hreal (2*n+1)),
      hillHminusDiscriminant (q) x = 0 := by
  let a := hillHminusRealLabels q hreal (2*n)
  let b := hillHminusRealLabels q hreal (2*n+1)
  let s : ℂ := (-1)^n
  let g : ℝ → ℝ := fun x => (s*hillHminusDiscriminant (q) x).re
  have hs : s^2 = 1 := by
    dsimp only [s]
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have hsne : s ≠ 0 := pow_ne_zero n (by norm_num)
  have hsreal : s = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp [s]
  have haD : hillHminusDiscriminant (q) a = 2*s := by
    simpa only [a,show (2*n+1)/2 = n by omega] using hillHminusRealLabels_trace_parity q hreal (2*n)
  have hbD : hillHminusDiscriminant (q) b = -2*s := by
    have h := hillHminusRealLabels_trace_parity q hreal (2*n+1)
    rw [show (2*n+1+1)/2 = n+1 by omega,pow_succ] at h
    change hillHminusDiscriminant (q) b = _ at h
    dsimp only [s]
    rw [h]
    ring
  have ha : g a = 2 := by
    dsimp only [g]
    rw [haD,show s*(2*s) = 2*s^2 by ring,hs]
    norm_num
  have hb : g b = -2 := by
    dsimp only [g]
    rw [hbD,show s*(-2*s) = -2*s^2 by ring,hs]
    norm_num
  have hab : a < b := hillHminusRealLabels_band_strict q hreal n
  have hD : Continuous (fun x : ℝ => hillHminusDiscriminant (q) x) :=
    (analyticOnNhd_hillHminusDiscriminant _).continuous.comp Complex.continuous_ofReal
  have hg : Continuous g := Complex.continuous_re.comp
    ((continuous_const : Continuous (fun _ : ℝ => s)).mul hD)
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc' hab.le hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g b) (g a) by rw [ha,hb]; norm_num)
  have hxa : a < x := lt_of_le_of_ne hx.1 (by intro he; rw [← he,ha] at hzero; norm_num at hzero)
  have hxb : x < b := lt_of_le_of_ne hx.2 (by intro he; rw [he,hb] at hzero; norm_num at hzero)
  have hprod : s*hillHminusDiscriminant (q) x = 0 := by
    apply Complex.ext
    · exact hzero
    · rw [hsreal]
      simp only [mul_im,hillHminusDiscriminant_real _ hreal,ofReal_im,
        mul_zero,zero_mul,add_zero,zero_im]
  exact ⟨x,⟨hxa,hxb⟩,(mul_eq_zero.mp hprod).resolve_left hsne⟩

theorem hillHminusDiscriminant_open_band_bounds
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hreal (2*n)) (hillHminusRealLabels q hreal (2*n+1))) :
    -2 < (hillHminusDiscriminant (q) x).re ∧
      (hillHminusDiscriminant (q) x).re < 2 := by
  let H : ℝ → ℝ := fun t => (hillHminusDiscriminant (q) t).re^2-4
  have hD : Continuous (fun t : ℝ => hillHminusDiscriminant (q) t) :=
    (analyticOnNhd_hillHminusDiscriminant _).continuous.comp Complex.continuous_ofReal
  have hH : Continuous H := ((Complex.continuous_re.comp hD).pow 2).sub continuous_const
  obtain ⟨y,hy,hyD⟩ := exists_hillHminusDiscriminant_zero_in_band q hreal n
  have hyH : H y = -4 := by simp [H,hyD]
  have hneg : H x < 0 := by
    by_contra hh
    have hc : IsPreconnected (H '' Ioo (hillHminusRealLabels q hreal (2*n))
        (hillHminusRealLabels q hreal (2*n+1))) := isPreconnected_Ioo.image H hH.continuousOn
    have hzmem : (0 : ℝ) ∈ H '' Ioo (hillHminusRealLabels q hreal (2*n))
        (hillHminusRealLabels q hreal (2*n+1)) :=
      hc.Icc_subset ⟨y,hy,rfl⟩ ⟨x,hx,rfl⟩ ⟨by rw [hyH]; norm_num,not_lt.mp hh⟩
    obtain ⟨z,hz,hzH⟩ := hzmem
    apply hillHminusRadicand_ne_zero_between_labels q hreal (2*n) z hz
    apply Complex.ext
    · simpa [H,hillHminusRadicand,pow_two,mul_re,hillHminusDiscriminant_real _ hreal] using hzH
    · simp [hillHminusRadicand,pow_two,mul_im,hillHminusDiscriminant_real _ hreal]
  dsimp only [H] at hneg
  constructor <;> nlinarith

theorem hillHminusUpperBoundaryPrimitive_trace
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q)
    (x : ℝ) (hx : hillHminusRadicand (q) x ≠ 0) :
    2 * cosh (hillHminusUpperBoundaryPrimitive (q) x) =
      ((hillHminusDiscriminant (q) x).re : ℂ) := by
  rw [(hillHminusUpperBoundary_data q hr x hx).2.2.2.1]
  apply Complex.ext
  · rfl
  · exact hillHminusDiscriminant_real _ hr x

theorem hillHminusUpperBoundaryPrimitive_re_eq_zero_band
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2 * n)) (hillHminusRealLabels q hr (2 * n + 1))) :
    (hillHminusUpperBoundaryPrimitive (q) x).re = 0 := by
  have hreg := hillHminusRadicand_ne_zero_between_labels q hr (2 * n) x hx
  have hb := hillHminusDiscriminant_open_band_bounds q hr n x hx
  exact re_eq_zero_of_real_cosh_trace_band _ _
    (hillHminusUpperBoundaryPrimitive_trace q hr x hreg) (abs_le.mpr ⟨hb.1.le, hb.2.le⟩)


end NLS.KdV
