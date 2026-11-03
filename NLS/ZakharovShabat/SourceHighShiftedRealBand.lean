import NLS.ZakharovShabat.SourceRealBandGeometry
import NLS.ComplexAnalysis.ShiftedSquareRootBounds

/-! # A common high real energy lies in the same shifted source band

Actual high canonical endpoint pairs and the proved fixed-shift square
root estimate select the band index, without an assumed root sign.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_high_shifted_real_band (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (hc : c.im = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
      let w : ℂ := ((Real.pi*(n:ℝ)+Real.pi/2 : ℝ):ℂ)
      let z := sqrt (w^2+c)
      0 < z.re ∧ z.im = 0 ∧ z.re ∈ sourceRealBand hp hp1 ψ (n:ℤ) := by
  obtain ⟨M,hM,hsmall⟩ := exists_high_disc_sqrt_shift_small c (Real.pi/2) (Real.pi/8) (by positivity)
  let K := canonicalPeriodicCutoff hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  refine ⟨max M (K+1),lt_of_lt_of_le hM (le_max_left _ _),?_⟩
  intro n hn
  let w : ℂ := ((Real.pi*(n:ℝ)+Real.pi/2 : ℝ):ℂ)
  let z := sqrt (w^2+c)
  have hw : w ∈ closedBall ((Real.pi:ℂ)*n) (Real.pi/2) := by
    simp only [mem_closedBall,dist_eq_norm]
    rw [show w-(Real.pi:ℂ)*n = ((Real.pi/2:ℝ):ℂ) by dsimp [w];push_cast;ring]
    simp [abs_of_pos Real.pi_pos]
  have hnorm := (hsmall n ((le_max_left _ _).trans hn) w hw).2
  have hre : |z.re-(Real.pi*(n:ℝ)+Real.pi/2)| < Real.pi/8 := by
    have he := (abs_re_le_norm (z-w)).trans_lt hnorm
    simpa only [sub_re,w,ofReal_re] using he
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hre
  have hzpos : 0 < z.re := by
    nlinarith [Real.pi_pos,(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hsquare : z^2 = w^2+c := complex_sqrt_sq _
  have him : (2*z.re)*z.im = 0 := by
    have he := congrArg Complex.im hsquare
    simp only [pow_two,mul_im,w,ofReal_im,mul_zero,zero_mul,add_zero,add_im,hc] at he
    linear_combination he
  have hzim : z.im = 0 := (mul_eq_zero.mp him).resolve_left (by positivity)
  have hdist := (canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)).1.distant
  have hnk : K < n := by omega
  have hpair := hdist (n:ℤ) (by simpa only [Int.natAbs_natCast] using hnk)
  have hpair' := hdist ((n:ℤ)+1) (by
    have he : (n:ℤ)+1 = ((n+1:ℕ):ℤ) := by push_cast;ring
    rw [he,Int.natAbs_natCast]
    omega)
  have hr := (abs_re_le_norm
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-(Real.pi:ℂ)*n)).trans_lt
      (by simpa only [refinedResonantDisk,mem_ball,dist_eq_norm,Int.cast_natCast] using! hpair.right_mem)
  have hl := (abs_re_le_norm
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) ((n:ℤ)+1)-
      (Real.pi:ℂ)*((n:ℤ)+1))).trans_lt
      (by simpa only [refinedResonantDisk,mem_ball,dist_eq_norm,Int.cast_add,Int.cast_natCast,Int.cast_one] using! hpair'.left_mem)
  simp [Complex.sub_re,Complex.mul_re] at hr hl
  change |(canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n:ℤ)).re-
    Real.pi*(n:ℝ)| < Real.pi/4 at hr
  change |(canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) ((n:ℤ)+1)).re-
    Real.pi*((n:ℝ)+1)| < Real.pi/4 at hl
  obtain ⟨_,hr⟩ := abs_lt.mp hr
  obtain ⟨hl,_⟩ := abs_lt.mp hl
  refine ⟨hzpos,hzim,?_,?_⟩
  · change (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) (n:ℤ)).re < z.re
    nlinarith [Real.pi_pos]
  · change z.re < (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) ((n:ℤ)+1)).re
    nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
