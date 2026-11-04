import NLS.KdV.HillL2WholeGapSquares
import NLS.KdV.ClassicalHillFreeSquareComparison

/-! # Actual L2 high squares compared with the exact free model

The radius is fixed before the error tolerance. The actual L2 trace
estimate and the squared-cosh inverse give uniform free and quadratic
model comparisons on full closed high energy discs.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillL2_free_square_comparison (q : Coeff 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∃ V : Set (Coeff 2),
        0 < N ∧ IsOpen V ∧ q ∈ V ∧
        ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
          AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
          (∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
            K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
          ∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            ‖K t-classicalHillFreeShiftedSquare n t.1‖ ≤ epsilon*r^2 := by
  obtain ⟨U,W,hU,_,h0,h1,G,hG,_,hleft,_⟩ := exists_squaredCosh_inverse
  obtain ⟨L,delta,hL,hdelta,hLip⟩ := exists_local_lipschitz_bound_of_analyticAt G 1
    (hG 1 h1)
  obtain ⟨bu,hbu,hbuU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  obtain ⟨bt,hbt,hcontrol⟩ := Metric.continuousAt_iff.mp
    ((analyticOnNhd_squaredCosh 0 (mem_univ _)).continuousAt : ContinuousAt squaredCosh (0 : ℂ)) delta hdelta
  let B : ℝ := min 1 (min bu bt)/2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hB1 : B ≤ 1 := by have := min_le_left 1 (min bu bt); dsimp only [B]; linarith
  have hBbu : B < bu := by
    have := (min_le_right 1 (min bu bt)).trans (min_le_left bu bt)
    dsimp only [B]
    linarith
  have hBbt : B < bt := by
    have := (min_le_right 1 (min bu bt)).trans (min_le_right bu bt)
    dsimp only [B]
    linarith
  have hsmall (w : ℂ) (hw : ‖w‖ < B) : w ∈ U ∧ squaredCosh w ∈ ball 1 delta := by
    refine ⟨hbuU (by simpa only [mem_ball,dist_zero_right] using hw.trans hBbu),?_⟩
    have hh := hcontrol (by simpa only [dist_zero_right] using hw.trans hBbt)
    simpa only [mem_ball,squaredCosh_zero] using hh
  obtain ⟨r0,N0,V0,hr0,hr0pi,hN0,hV0,hq0,hfamily⟩ :=
    exists_hillL2_whole_disc_small_squares q B hB
  let r : ℝ := min r0 (min B 1)/2
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrr0 : r ≤ r0 := by have := min_le_left r0 (min B 1); dsimp only [r]; linarith
  have hrpi : r ≤ Real.pi/4 := hrr0.trans hr0pi
  have hrB : r ≤ B/2 := by
    have := (min_le_right r0 (min B 1)).trans (min_le_left B 1)
    dsimp only [r]
    linarith
  have hr1 : r ≤ 1/2 := by
    have := (min_le_right r0 (min B 1)).trans (min_le_right B 1)
    dsimp only [r]
    linarith
  have hrsq : r^2 < B := by nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  obtain ⟨Ne,Ve,_,hVe,hqe,happrox⟩ := exists_hillL2_disc_trace_approximation q r hr hrpi
    (2*epsilon*r^2/L) (by positivity)
  refine ⟨max N0 Ne,V0 ∩ Ve,hN0.trans_le (le_max_left _ _),hV0.inter hVe,⟨hq0,hqe⟩,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch⟩ := hfamily n ((le_max_left N0 Ne).trans hn)
  have hsub : hillL2GapSquareDisc n r ×ˢ (V0 ∩ Ve) ⊆ hillL2GapSquareDisc n r0 ×ˢ V0 := by
    intro t ht
    refine ⟨closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hrr0 (by positivity)) ht.1,ht.2.1⟩
  refine ⟨K,hK.mono hsub,fun t ht => (hbound t (hsub ht)).trans_le hB1,
    fun t ht => hrel t (hsub ht),fun t ht => hzero t (hsub ht),
    fun t ht => hmatch t ⟨hsub ht.1,ht.2⟩,?_⟩
  intro t ht
  have hfreq : Complex.sqrt t.1 ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) r := by
    have hh := sqrt_mem_closedBall_of_energy_disc (Real.pi*(n : ℕ)) r (by positivity) t.1
      (by simpa only [hillL2GapSquareDisc,classicalHillGapSquareDisc,ofReal_mul,ofReal_natCast] using ht.1)
    simpa only [ofReal_mul,ofReal_natCast] using hh
  have hmodelnorm : ‖classicalHillFreeShiftedSquare n t.1‖ < B := by
    have hh : ‖Complex.sqrt t.1-(Real.pi : ℂ)*(n : ℕ)‖ ≤ r := by
      simpa only [mem_closedBall,dist_eq_norm] using hfreq
    rw [classicalHillFreeShiftedSquare,norm_neg,norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_lt hrsq
  have hKsmall := hsmall (K t) (hbound t (hsub ht))
  have hmodelsmall := hsmall (classicalHillFreeShiftedSquare n t.1) hmodelnorm
  have hfree := squaredCosh_classicalHillFreeShiftedSquare n t.1
  have htrace := hrel t (hsub ht)
  have hnorm : ‖squaredCosh (K t)-squaredCosh (classicalHillFreeShiftedSquare n t.1)‖ ≤ epsilon*r^2/L := by
    rw [htrace,hfree,div_sub_div_same,← mul_sub,norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    have hh := happrox t.2 ht.2.2 (n : ℤ) (by simpa only [Int.natAbs_natCast] using (le_max_right N0 Ne).trans hn)
      (Complex.sqrt t.1) (by simpa only [Int.cast_natCast] using hfreq)
    have hs : (Complex.sqrt t.1)^2 = t.1 := by
      have hs := Complex.cpow_nat_inv_pow t.1 (Nat.succ_ne_zero 1)
      norm_num at hs
      simpa only [Complex.sqrt,one_div] using hs
    simp only [hs] at hh
    rw [classicalHillDiscriminant_zero]
    norm_num
    rw [show 2*epsilon*r^2/L = 2*(epsilon*r^2/L) by ring] at hh
    linarith
  have hh := hLip _ hKsmall.2 _ hmodelsmall.2
  rw [hleft _ hKsmall.1,hleft _ hmodelsmall.1] at hh
  calc
    _ ≤ L*‖squaredCosh (K t)-squaredCosh (classicalHillFreeShiftedSquare n t.1)‖ := hh
    _ ≤ L*(epsilon*r^2/L) := mul_le_mul_of_nonneg_left hnorm hL.le
    _ = epsilon*r^2 := by field_simp

/-- The radius precedes the tolerance in the comparison with the
polynomial whose endpoint-deflated quotient is -1/(4*n^2*pi^2). -/
theorem exists_hillL2_quadratic_square_comparison (q : Coeff 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Real.pi/4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∃ V : Set (Coeff 2),
        0 < N ∧ IsOpen V ∧ q ∈ V ∧
        ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ K : ℂ × Coeff 2 → ℂ,
          AnalyticOnNhd ℂ K (hillL2GapSquareDisc n r ×ˢ V) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V, ‖K t‖ < 1) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            squaredCosh (K t) = (-1 : ℂ)^(n : ℕ)*hillL2Discriminant t.2 t.1/2) ∧
          (∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            K t = 0 ↔ hillL2Radicand t.2 t.1 = 0) ∧
          (∀ t ∈ (hillL2GapSquareDisc n r ×ˢ V) ∩ hillL2ContinuationDomain,
            K t = (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2) ∧
          ∀ t ∈ hillL2GapSquareDisc n r ×ˢ V,
            ‖K t-classicalHillFreeQuadraticModel n t.1‖ ≤ epsilon*r^2 := by
  obtain ⟨r,hr,hrpi,hfamily⟩ := exists_hillL2_free_square_comparison q
  refine ⟨r,hr,hrpi,?_⟩
  intro epsilon hepsilon
  obtain ⟨Nk,V,hNk,hV,hq,hKfamily⟩ := hfamily (epsilon/2) (by positivity)
  obtain ⟨Ng,_,hNg⟩ := NLS.ZakharovShabat.exists_free_center_cutoff (5*r/(2*epsilon)) 0
  refine ⟨max Nk Ng,V,hNk.trans_le (le_max_left _ _),hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hbound,hrel,hzero,hmatch,herror⟩ := hKfamily n ((le_max_left Nk Ng).trans hn)
  refine ⟨K,hK,hbound,hrel,hzero,hmatch,?_⟩
  intro t ht
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hrc : r ≤ c := by
    have hnreal : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.property
    dsimp only [c]
    nlinarith [Real.pi_pos]
  have hcut : 5*r/(2*epsilon) ≤ c := by
    have hnreal : (Ng : ℝ) ≤ (n : ℕ) := by exact_mod_cast (le_max_right Nk Ng).trans hn
    dsimp only [c]
    nlinarith [Real.pi_pos]
  have hratio : 5*r/(4*c) ≤ epsilon/2 := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2*epsilon)).mp hcut
    apply (div_le_iff₀ (by positivity : 0 < 4*c)).mpr
    nlinarith
  have hfree := norm_free_square_sub_quadratic_le c r hc hr hrc t.1
    (by simpa only [hillL2GapSquareDisc,classicalHillGapSquareDisc,c,ofReal_mul,ofReal_natCast] using ht.1)
  have hfree' : ‖classicalHillFreeShiftedSquare n t.1-classicalHillFreeQuadraticModel n t.1‖ ≤
      (epsilon/2)*r^2 := by
    calc
      _ ≤ 5*r^3/(4*c) := by
        simpa only [classicalHillFreeShiftedSquare,classicalHillFreeQuadraticModel,c,ofReal_mul,ofReal_natCast] using hfree
      _ = (5*r/(4*c))*r^2 := by ring
      _ ≤ (epsilon/2)*r^2 := mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  calc
    _ ≤ ‖K t-classicalHillFreeShiftedSquare n t.1‖+
        ‖classicalHillFreeShiftedSquare n t.1-classicalHillFreeQuadraticModel n t.1‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (epsilon/2)*r^2+(epsilon/2)*r^2 := add_le_add (herror t ht) hfree'
    _ = epsilon*r^2 := by ring

end NLS.KdV
