import NLS.KdV.HillHminusOneRealBands
import NLS.ComplexAnalysis.RealSimpleZeroSigns

/-! # The actual Hill characteristic sign in gaps and the lower exterior

Real band bounds and simple endpoint orders fix the sign on the entire
real spectral complement. In particular the normalized trace exceeds
two on every open gap and below the lowest energy. No high-frequency
cutoff or assumed canonical product is needed.
-/

noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusRadicand_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (hillHminusRadicand q x).im = 0 := by
  simp [hillHminusRadicand,pow_two,mul_im,hillHminusDiscriminant_real q hr]

theorem hillHminusRadicand_re (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (x : ℝ) :
    (hillHminusRadicand q x).re = (hillHminusDiscriminant q x).re^2-4 := by
  simp [hillHminusRadicand,pow_two,mul_re,hillHminusDiscriminant_real q hr]

theorem hillHminusRealLabels_signed_pair_trace
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℝ)^n*(hillHminusDiscriminant q
      (hillHminusRealLabels q hr (2*n-1))).re = 2 ∧
    (-1 : ℝ)^n*(hillHminusDiscriminant q
      (hillHminusRealLabels q hr (2*n))).re = 2 := by
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have hsreal : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
  have hval (x : ℝ) (he : hillHminusDiscriminant q x = 2*(-1 : ℂ)^n) :
      (-1 : ℝ)^n*(hillHminusDiscriminant q x).re = 2 := by
    rw [hsreal] at he
    have hh := congrArg Complex.re he
    simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] at hh
    norm_num at hh
    rw [hh]
    nlinarith
  exact ⟨hval _ (hillHminusRealLabels_pair_trace q hr n hn).1,
    hval _ (hillHminusRealLabels_pair_trace q hr n hn).2⟩

theorem hillHminusRadicand_neg_band
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n)) (hillHminusRealLabels q hr (2*n+1))) :
    (hillHminusRadicand q x).re < 0 := by
  rw [hillHminusRadicand_re _ hr]
  have h := hillHminusDiscriminant_open_band_bounds q hr n x hx
  nlinarith [h.1,h.2]

theorem hillHminusRadicand_pos_gap
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    0 < (hillHminusRadicand q x).re := by
  have hp : 2*(n-1)+1 = 2*n-1 := by omega
  have hba := hillHminusRealLabels_band_strict q hr (n-1)
  rw [hp] at hba
  have hac := hx.1.trans hx.2
  have ho := (hillHminusRealLabels_open_gap_orders q hr n hn hac.ne).1
  apply positive_right_of_negative_left (hillHminusRadicand q)
    (analyticOnNhd_hillHminusRadicand _) (hillHminusRadicand_real _ hr)
    (hillHminusRealLabels q hr (2*(n-1))) (hillHminusRealLabels q hr (2*n-1))
    (hillHminusRealLabels q hr (2*n)) hba hac ho ?_ ?_ x hx
  · intro t ht
    apply hillHminusRadicand_neg_band q hr (n-1) t
    simpa only [hp] using ht
  · intro t ht
    apply hillHminusRadicand_ne_zero_between_labels q hr (2*n-1) t
    simpa only [show 2*n-1+1 = 2*n by omega] using ht

theorem hillHminusDiscriminant_signed_gap_gt_two
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    2 < (-1 : ℝ)^n*(hillHminusDiscriminant q x).re := by
  let g : ℝ → ℝ := fun t => (-1 : ℝ)^n*(hillHminusDiscriminant q t).re
  have hD : Continuous (fun t : ℝ => hillHminusDiscriminant q t) :=
    (analyticOnNhd_hillHminusDiscriminant _).continuous.comp Complex.continuous_ofReal
  have hg : Continuous g := (Complex.continuous_re.comp hD).const_mul _
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have haD := (hillHminusRealLabels_pair_trace q hr n hn).1
  have hsreal : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
  rw [hsreal] at haD
  have haR := congrArg Complex.re haD
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] at haR
  norm_num at haR
  have ha : g (hillHminusRealLabels q hr (2*n-1)) = 2 := by
    dsimp only [g]
    rw [haR]
    nlinarith
  apply above_pos_level_of_square_gt g hg (hillHminusRealLabels q hr (2*n-1)) x 2
    hx.1 (by norm_num) ha
  intro t ht
  have hp := hillHminusRadicand_pos_gap q hr n hn t ⟨ht.1,ht.2.trans_lt hx.2⟩
  rw [hillHminusRadicand_re _ hr] at hp
  dsimp only [g]
  rw [mul_pow,hs,one_mul]
  nlinarith

theorem hillHminusDiscriminant_signed_gap_ge_two
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    2 ≤ (-1 : ℝ)^n*(hillHminusDiscriminant q x).re := by
  by_cases hl : x = hillHminusRealLabels q hr (2*n-1)
  · rw [hl,(hillHminusRealLabels_signed_pair_trace q hr n hn).1]
  by_cases hu : x = hillHminusRealLabels q hr (2*n)
  · rw [hu,(hillHminusRealLabels_signed_pair_trace q hr n hn).2]
  exact (hillHminusDiscriminant_signed_gap_gt_two q hr n hn x
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hl),lt_of_le_of_ne hx.2 hu⟩).le

end NLS.KdV
