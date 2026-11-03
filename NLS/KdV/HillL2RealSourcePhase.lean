import NLS.KdV.HillL2PrimitiveReflection
import NLS.ComplexAnalysis.LogarithmStripNormalization

/-! # The exact real phase of the rough Hill source primitive

At an admissible real energy the whole real source segment has a purely
imaginary primitive and a nonzero root. Thus its phase stays between
the same consecutive integer multiples of pi as the free primitive.
The two enclosing high-circle crossings have the expected indexed phases.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2ContinuedPrimitive_im_interval
    (q : Coeff 2) (hreal : IsRealHillPotential q) (x : ℝ)
    (ht : ((x : ℂ),q) ∈ hillL2ContinuationDomain) (k : ℤ)
    (hfree : -Real.sqrt x ∈ Ioo ((k : ℝ)*Real.pi) (((k : ℝ)+1)*Real.pi)) :
    (hillL2ContinuedPrimitive (x,q)).im ∈
      Ioo ((k : ℝ)*Real.pi) (((k : ℝ)+1)*Real.pi) := by
  let P : ℝ → ℂ := fun s => hillL2ContinuedPrimitive (x,(s : ℂ) • q)
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ((x : ℂ),(s : ℂ) • q) ∈ hillL2ContinuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero,hillL2ContinuationDomain] using
      hillL2SourceFamily.continuationDomain_segment ((x : ℂ),q) ht s hs
  have hP : ContinuousOn P (Icc (0 : ℝ) 1) :=
    analyticOnNhd_hillL2ContinuedPrimitive.continuousOn.comp (by fun_prop) hpath
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (P s).im ≠ (k : ℝ)*Real.pi ∧ (P s).im ≠ ((k : ℝ)+1)*Real.pi := by
    have hre : (P s).re = 0 :=
      hillL2ContinuedPrimitive_re_eq_zero _ (hreal.smul_real s) x (hpath s hs)
    have hnz : sinh (P s) ≠ 0 := by
      intro he
      have hz := (hillL2ContinuedPrimitive_trace _ (hpath s hs)).2
      change 2*sinh (P s) = _ at hz
      rw [he,mul_zero] at hz
      exact hillL2ContinuedRoot_ne_zero _ (hpath s hs) hz.symm
    constructor
    · intro he
      exact hnz (sinh_eq_zero_of_re_zero_im_int_pi (P s) k hre he)
    · intro he
      apply hnz (sinh_eq_zero_of_re_zero_im_int_pi (P s) (k+1) hre _)
      simpa only [Int.cast_add,Int.cast_one] using he
  have h0 : (P 0).im = -Real.sqrt x := by
    simp only [P,ofReal_zero,zero_smul,hillL2ContinuedPrimitive_base,
      mul_im,neg_re,I_re,neg_zero,neg_im,I_im,zero_mul,neg_one_mul,zero_add,
      Complex.re_sqrt_ofReal]
  have h := real_mem_Ioo_of_preconnected_avoids (fun s => (P s).im) (Icc (0 : ℝ) 1)
    isPreconnected_Icc (continuous_im.comp_continuousOn hP) _ _ hne 0
    (by constructor <;> norm_num) (by rwa [h0]) 1 (by constructor <;> norm_num)
  simpa only [P,ofReal_one,one_smul] using h

theorem hill_high_real_crossing_sqrt_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.pi*((n : ℝ)-1) < Real.sqrt (freeHillValue n-3*(n : ℝ)/4) ∧
    Real.sqrt (freeHillValue n-3*(n : ℝ)/4) < Real.pi*n ∧
    Real.pi*n < Real.sqrt (freeHillValue n+3*(n : ℝ)/4) ∧
    Real.sqrt (freeHillValue n+3*(n : ℝ)/4) < Real.pi*((n : ℝ)+1) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hpim := mul_nonneg (sub_nonneg.mpr hpi.le)
    (show 0 ≤ 2*(n : ℝ)-1 by linarith)
  have hpip := mul_nonneg (sub_nonneg.mpr hpi.le)
    (show 0 ≤ 2*(n : ℝ)+1 by linarith)
  have hleft : (Real.pi*((n : ℝ)-1))^2 < freeHillValue n-3*(n : ℝ)/4 := by
    dsimp only [freeHillValue]
    push_cast
    nlinarith
  have hright : freeHillValue n+3*(n : ℝ)/4 < (Real.pi*((n : ℝ)+1))^2 := by
    dsimp only [freeHillValue]
    push_cast
    nlinarith
  have hlpos : 0 ≤ freeHillValue n-3*(n : ℝ)/4 := by
    nlinarith [sq_nonneg (Real.pi*((n : ℝ)-1))]
  have hrpos : 0 ≤ freeHillValue n+3*(n : ℝ)/4 := by linarith
  have hlsq := Real.sq_sqrt hlpos
  have hrsq := Real.sq_sqrt hrpos
  have hcenter : freeHillValue n = (Real.pi*(n : ℝ))^2 := by
    simp only [freeHillValue,Int.cast_natCast,mul_pow]
  have hpn : 0 < Real.pi*(n : ℝ) := by positivity
  have hpm : 0 ≤ Real.pi*((n : ℝ)-1) := mul_nonneg Real.pi_pos.le (by linarith)
  have hpp : 0 < Real.pi*((n : ℝ)+1) := by positivity
  refine ⟨?_,?_,?_,?_⟩
  · apply (sq_lt_sq₀ hpm (Real.sqrt_nonneg _)).mp
    rwa [hlsq]
  · apply (sq_lt_sq₀ (Real.sqrt_nonneg _) hpn.le).mp
    rw [hlsq,← hcenter]
    linarith
  · apply (sq_lt_sq₀ hpn.le (Real.sqrt_nonneg _)).mp
    rw [hrsq,← hcenter]
    linarith
  · apply (sq_lt_sq₀ (Real.sqrt_nonneg _) hpp.le).mp
    rwa [hrsq]

theorem hillL2ContinuedPrimitive_high_real_crossing_phases
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    (hillL2ContinuedPrimitive ((freeHillValue n-3*(n : ℝ)/4 : ℝ),SpectralWeight.one.toCoeff q)).im ∈
      Ioo (-Real.pi*n) (-Real.pi*((n : ℝ)-1)) ∧
    (hillL2ContinuedPrimitive ((freeHillValue n+3*(n : ℝ)/4 : ℝ),SpectralWeight.one.toCoeff q)).im ∈
      Ioo (-Real.pi*((n : ℝ)+1)) (-Real.pi*n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsrc (x : ℝ) (hx : |x-freeHillValue n| = 3*(n : ℝ)/4) :
      ((x : ℂ),SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain := by
    apply mem_hillL2ContinuationDomain_of_high_distance q hq n hn hcut x
    · rw [mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,hx]
      linarith
    · rw [← ofReal_sub,norm_real,Real.norm_eq_abs,hx]
      linarith
  obtain ⟨hml,hmr,hpl,hpr⟩ := hill_high_real_crossing_sqrt_bounds n hn
  constructor
  · have hs := hsrc (freeHillValue n-3*(n : ℝ)/4) (by
      rw [sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)])
    have hb : -Real.sqrt (freeHillValue n-3*(n : ℝ)/4) ∈
        Ioo (((-(n : ℤ) : ℤ) : ℝ)*Real.pi) ((((-(n : ℤ) : ℤ) : ℝ)+1)*Real.pi) := by
      constructor <;> push_cast <;> nlinarith
    have h := hillL2ContinuedPrimitive_im_interval _ hreal _ hs (-(n : ℤ)) hb
    convert! h using 2 <;> push_cast <;> ring
  · have hs := hsrc (freeHillValue n+3*(n : ℝ)/4) (by
      rw [add_sub_cancel_left,abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)])
    have hb : -Real.sqrt (freeHillValue n+3*(n : ℝ)/4) ∈
        Ioo (((-(n : ℤ)-1 : ℤ) : ℝ)*Real.pi) ((((-(n : ℤ)-1 : ℤ) : ℝ)+1)*Real.pi) := by
      constructor <;> push_cast <;> nlinarith
    have h := hillL2ContinuedPrimitive_im_interval _ hreal _ hs (-(n : ℤ)-1) hb
    convert! h using 2 <;> push_cast <;> ring

end NLS.KdV
