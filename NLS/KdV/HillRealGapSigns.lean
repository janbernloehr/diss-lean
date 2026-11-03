import NLS.KdV.HillRealBands
import NLS.ComplexAnalysis.RealSimpleZeroSigns

/-! # The actual Hill characteristic sign in gaps and the lower exterior

Real band bounds and simple endpoint orders fix the sign on the entire
real spectral complement. In particular the normalized trace exceeds
two on every open gap and below the lowest energy. No high-frequency
cutoff or assumed canonical product is needed.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2Radicand_real (q : Coeff 2) (hr : IsRealHillPotential q) (x : ℝ) :
    (hillL2Radicand q x).im = 0 := by
  simp [hillL2Radicand,pow_two,mul_im,hillL2Discriminant_real q hr]

theorem hillL2Radicand_re (q : Coeff 2) (hr : IsRealHillPotential q) (x : ℝ) :
    (hillL2Radicand q x).re = (hillL2Discriminant q x).re^2-4 := by
  simp [hillL2Radicand,pow_two,mul_re,hillL2Discriminant_real q hr]

theorem hillRealLabels_signed_pair_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q)
      (hillRealLabels q hq hr (2*n-1))).re = 2 ∧
    (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q)
      (hillRealLabels q hq hr (2*n))).re = 2 := by
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have hsreal : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
  have hval (x : ℝ) (he : hillL2Discriminant (SpectralWeight.one.toCoeff q) x = 2*(-1 : ℂ)^n) :
      (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re = 2 := by
    rw [hsreal] at he
    have hh := congrArg Complex.re he
    simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] at hh
    norm_num at hh
    rw [hh]
    nlinarith
  exact ⟨hval _ (hillRealLabels_pair_trace q hq hr n hn).1,
    hval _ (hillRealLabels_pair_trace q hq hr n hn).2⟩

theorem hillL2Radicand_neg_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n)) (hillRealLabels q hq hr (2*n+1))) :
    (hillL2Radicand (SpectralWeight.one.toCoeff q) x).re < 0 := by
  rw [hillL2Radicand_re _ hr]
  have h := hillL2Discriminant_open_band_bounds q hq hr n x hx
  nlinarith [h.1,h.2]

theorem hillL2Radicand_pos_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    0 < (hillL2Radicand (SpectralWeight.one.toCoeff q) x).re := by
  have hp : 2*(n-1)+1 = 2*n-1 := by omega
  have hba := hillRealLabels_band_strict q hq hr (n-1)
  rw [hp] at hba
  have hac := hx.1.trans hx.2
  have ho := (hillRealLabels_open_gap_orders q hq hr n hn hac.ne).1
  apply positive_right_of_negative_left (hillL2Radicand (SpectralWeight.one.toCoeff q))
    (analyticOnNhd_hillL2Radicand _) (hillL2Radicand_real _ hr)
    (hillRealLabels q hq hr (2*(n-1))) (hillRealLabels q hq hr (2*n-1))
    (hillRealLabels q hq hr (2*n)) hba hac ho ?_ ?_ x hx
  · intro t ht
    apply hillL2Radicand_neg_band q hq hr (n-1) t
    simpa only [hp] using ht
  · intro t ht
    apply hillL2Radicand_ne_zero_between_labels q hq hr (2*n-1) t
    simpa only [show 2*n-1+1 = 2*n by omega] using ht

theorem hillL2Radicand_pos_below
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x < hillLowestEnergy q hq hr) :
    0 < (hillL2Radicand (SpectralWeight.one.toCoeff q) x).re := by
  have hband := hillRealLabels_band_strict q hq hr 0
  change hillLowestEnergy q hq hr < hillRealLabels q hq hr 1 at hband
  apply positive_left_of_negative_right (hillL2Radicand (SpectralWeight.one.toCoeff q))
    (analyticOnNhd_hillL2Radicand _) (hillL2Radicand_real _ hr)
    (x-1) (hillLowestEnergy q hq hr) (hillRealLabels q hq hr 1)
    (by linarith) hband (hillLowestEnergy_order_one q hq hr) ?_ ?_ x ⟨by linarith,hx⟩
  · intro t ht hd
    have h := hillLowestEnergy_le_root q hq hr t hd
    simp only [ofReal_re] at h
    linarith [ht.2]
  · intro t ht
    exact hillL2Radicand_neg_band q hq hr 0 t ht

theorem hillL2Discriminant_signed_gap_gt_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    2 < (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re := by
  let g : ℝ → ℝ := fun t => (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) t).re
  have hD : Continuous (fun t : ℝ => hillL2Discriminant (SpectralWeight.one.toCoeff q) t) :=
    (analyticOnNhd_hillL2Discriminant _).continuous.comp Complex.continuous_ofReal
  have hg : Continuous g := (Complex.continuous_re.comp hD).const_mul _
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have haD := (hillRealLabels_pair_trace q hq hr n hn).1
  have hsreal : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
  rw [hsreal] at haD
  have haR := congrArg Complex.re haD
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero] at haR
  norm_num at haR
  have ha : g (hillRealLabels q hq hr (2*n-1)) = 2 := by
    dsimp only [g]
    rw [haR]
    nlinarith
  apply above_pos_level_of_square_gt g hg (hillRealLabels q hq hr (2*n-1)) x 2
    hx.1 (by norm_num) ha
  intro t ht
  have hp := hillL2Radicand_pos_gap q hq hr n hn t ⟨ht.1,ht.2.trans_lt hx.2⟩
  rw [hillL2Radicand_re _ hr] at hp
  dsimp only [g]
  rw [mul_pow,hs,one_mul]
  nlinarith

theorem hillL2Discriminant_gt_two_below
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x < hillLowestEnergy q hq hr) :
    2 < (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re := by
  have hD : Continuous (fun t : ℝ => (hillL2Discriminant (SpectralWeight.one.toCoeff q) t).re) :=
    Complex.continuous_re.comp
      ((analyticOnNhd_hillL2Discriminant _).continuous.comp Complex.continuous_ofReal)
  have he : hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillLowestEnergy q hq hr) = 2 := by
    simpa [hillLowestEnergy] using
      hillRealLabels_trace_parity q hq hr 0
  apply above_pos_level_of_square_gt_left _ hD x (hillLowestEnergy q hq hr) 2 hx
    (by norm_num) (by simp [he])
  intro t ht
  have hp := hillL2Radicand_pos_below q hq hr t ht.2
  rw [hillL2Radicand_re _ hr] at hp
  nlinarith

theorem hillL2Discriminant_signed_gap_ge_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    2 ≤ (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re := by
  by_cases hl : x = hillRealLabels q hq hr (2*n-1)
  · rw [hl,(hillRealLabels_signed_pair_trace q hq hr n hn).1]
  by_cases hu : x = hillRealLabels q hq hr (2*n)
  · rw [hu,(hillRealLabels_signed_pair_trace q hq hr n hn).2]
  exact (hillL2Discriminant_signed_gap_gt_two q hq hr n hn x
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hl),lt_of_le_of_ne hx.2 hu⟩).le

end NLS.KdV
