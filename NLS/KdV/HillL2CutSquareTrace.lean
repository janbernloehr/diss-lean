import NLS.KdV.HillL2CutPrimitiveSquare
import NLS.KdV.HillRealGapIntegrals
import NLS.ComplexAnalysis.CoshSquareCoordinate

/-! # Trace and real-gap values of the filled Hill primitive square

The even entire hyperbolic cosine identifies the square extension with
the actual trace throughout the disc. Its only zeros are the actual gap
endpoints. On the open real gap it is exactly the square of the positive
arcosh profile in the source's real action formula.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.square_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8),
      coshSquareCoordinate (hillL2CutPrimitiveSquare n p.left p.right F z) =
        (-1 : ℂ)^n*hillL2Discriminant (SpectralWeight.one.toCoeff q) z/2 := by
  obtain ⟨hX,hm,_,_⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  apply continuous_eqOn_of_dense_on_open (segment ℝ (p.left : ℂ) p.right)ᶜ _
    (dense_complex_segment_complement _ _) isOpen_ball
    (fun z => coshSquareCoordinate (hillL2CutPrimitiveSquare n p.left p.right F z))
    (fun z => (-1 : ℂ)^n*hillL2Discriminant (SpectralWeight.one.toCoeff q) z/2)
    (analyticOnNhd_coshSquareCoordinate.continuous.comp_continuousOn hX.continuousOn)
    (((analyticOnNhd_hillL2Discriminant _).continuous.const_mul _).div_const 2).continuousOn
  intro z hz
  dsimp only
  rw [hm hz]
  dsimp only
  rw [coshSquareCoordinate_sq,cosh_add_I_nat_pi]
  linear_combination (-1 : ℂ)^n*(h.trace_eq z hz).1/2

theorem HillL2NormalizedCutPrimitive.square_zero_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (z : ℂ) (hz : z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)) :
    hillL2CutPrimitiveSquare n p.left p.right F z = 0 ↔ z = p.left ∨ z = p.right := by
  obtain ⟨_,_,hl,hr⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  constructor
  · intro he
    have ht := h.square_trace q hq hreal n hn hcut p hopen R F z hz
    rw [he] at ht
    have hC0 : coshSquareCoordinate 0 = 1 := by simp [coshSquareCoordinate]
    rw [hC0] at ht
    have hD : (-1 : ℂ)^n*hillL2Discriminant (SpectralWeight.one.toCoeff q) z = 2 := by
      linear_combination -2*ht
    have hs : ((-1 : ℂ)^n)^2 = 1 := by
      rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
      norm_num
    have hsq := congrArg (fun w : ℂ => w^2) hD
    rw [mul_pow,hs,one_mul] at hsq
    have hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 := by
      dsimp only [hillL2Radicand]
      rw [hsq]
      norm_num
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact (p.zeros_iff z (openHillStrip_subset n (hillClosedBall_subset_openStrip n (by omega)
      (ball_subset_closedBall (ball_subset_ball (by linarith) hz))))).mp hd
  · rintro (rfl | rfl)
    · exact hl
    · exact hr

theorem HillL2NormalizedCutPrimitive.square_gap_profile
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : x ∈ Ioo p.left p.right) :
    0 < (hillL2CutPrimitiveSquare n p.left p.right F x).re ∧
    hillL2CutPrimitiveSquare n p.left p.right F x =
      ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x)^2 : ℝ) := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloc := p.localization q hq n (by omega) hcut
  have hxΩ : (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [(abs_le.mp hloc.1).1,(abs_le.mp hloc.2).2,hx.1,hx.2]
  have hXreal : X x = ((X x).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact h.square_im_eq_zero q hq hreal n hn hcut p hopen R F x hxΩ
  obtain ⟨p',hl,hr⟩ := hillRealLabels_high_pair q hq hreal n hn hcut
  have hu := p.endpoints_unique _ n (by omega) p'
  have hxlabels : x ∈ Ioo (hillRealLabels q hq hreal (2*n-1)) (hillRealLabels q hq hreal (2*n)) := by
    simpa only [hl,hr,← hu.1,← hu.2] using hx
  have hgt := hillL2Discriminant_signed_gap_gt_two q hq hreal n (by omega) x hxlabels
  have ht := h.square_trace q hq hreal n hn hcut p hopen R F x hxΩ
  change coshSquareCoordinate (X x) = _ at ht
  have hDreal : hillL2Discriminant (SpectralWeight.one.toCoeff q) x =
      ((hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact hillL2Discriminant_real _ hreal x
  have hsign : (-1 : ℂ)^n = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp
  rw [hXreal,hDreal,hsign,← ofReal_mul] at ht
  rw [← ofReal_ofNat 2,← ofReal_div] at ht
  have htre : (coshSquareCoordinate ((X x).re : ℂ)).re =
      (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re/2 := by
    simpa only [ofReal_re] using congrArg Complex.re ht
  have hpos : 0 < (X x).re := by
    by_contra he
    have hb := coshSquareCoordinate_re_le_one_of_nonpos (X x).re (not_lt.mp he)
    rw [htre] at hb
    linarith
  have hcosh : Real.cosh (Real.sqrt (X x).re) =
      (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re/2 := by
    rwa [coshSquareCoordinate_ofReal _ hpos.le,ofReal_re] at htre
  have hp : hillRealGapProfile (SpectralWeight.one.toCoeff q) n x = Real.sqrt (X x).re := by
    dsimp only [hillRealGapProfile]
    rw [← hcosh,Real.arcosh_cosh (Real.sqrt_nonneg _)]
  refine ⟨hpos,?_⟩
  rw [hp,Real.sq_sqrt hpos.le]
  exact hXreal

end NLS.KdV
