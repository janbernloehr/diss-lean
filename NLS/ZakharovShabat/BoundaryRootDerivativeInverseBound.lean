import NLS.ZakharovShabat.BoundaryCharacteristicDiscLp
import NLS.ZakharovShabat.SourcePsiFullProductVariation
import NLS.ZakharovShabat.SourceOmittedProductBoundaryNormalization
import NLS.SequenceSpaces.FiniteExponentTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Bounded inverse derivatives at real displaced boundary roots

The entire boundary product has derivative close to the free cosine at
distant real roots. Its inverse root derivatives are therefore uniformly
bounded, after adding the finite central block. This supplies the bounded
multiplier needed to turn a Hilbert matrix kernel into a root variation.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
private theorem cos_displacedRoot_sub_free_le (a : Coeff p)
    (hr : ∀ n : ℤ, (displacedRoots a n).im = 0) (n : ℤ) :
    ‖cos (displacedRoots a n) - cos ((Real.pi : ℂ) * n)‖ ≤ ‖a n‖ := by
  have hz : ((displacedRoots a n).re : ℂ) = displacedRoots a n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (hr n).symm)
  have hc : (((Real.pi : ℂ) * n).re : ℂ) = (Real.pi : ℂ) * n := by
    apply Complex.ext <;> simp
  calc
    ‖cos (displacedRoots a n) - cos ((Real.pi : ℂ) * n)‖ =
        |Real.cos (displacedRoots a n).re - Real.cos (((Real.pi : ℂ) * n).re)| := by
      conv_lhs => rw [← hz, ← hc]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_cos, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |(displacedRoots a n).re - ((Real.pi : ℂ) * n).re| := Real.abs_cos_sub_cos_le _ _
    _ ≤ ‖displacedRoots a n - (Real.pi : ℂ) * n‖ := by
      simpa only [sub_re] using
        Complex.abs_re_le_norm (displacedRoots a n - (Real.pi : ℂ) * n)
    _ = ‖a n‖ := by simp [displacedRoots]

/-- Inverse derivatives of a real displaced-root boundary product are bounded over all indices. -/
theorem exists_bound_inv_deriv_displacedBoundaryProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p)
    (hr : ∀ n : ℤ, (displacedRoots a n).im = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ,
      ‖(deriv (displacedBoundaryProduct a) (displacedRoots a n))⁻¹‖ ≤ B := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bound_freeSineQuotient (Real.pi / 2)
  let A := restoredSineProductMajorant hp1 hp C a
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  obtain ⟨N,hN⟩ := Coeff.exists_natAbs_norm_lt hp0 a
    (show 0 < min (Real.pi/4) (1/4 : ℝ) by positivity)
  obtain ⟨M,hM⟩ := Coeff.exists_natAbs_norm_lt hp0 A
    (show 0 < Real.pi/16 by positivity)
  let K := max N M
  have htail (n : ℤ) (hn : K ≤ n.natAbs) :
      ‖(deriv (displacedBoundaryProduct a) (displacedRoots a n))⁻¹‖ ≤ 2 := by
    have han := hN n ((le_max_left _ _).trans hn)
    have hAn := hM n ((le_max_right _ _).trans hn)
    have hdisc : ‖displacedRoots a n - (Real.pi : ℂ) * n‖ ≤ Real.pi/4 := by
      simpa only [displacedRoots, add_sub_cancel_left] using
        (han.le.trans (min_le_left _ _))
    have hd := norm_deriv_displacedBoundaryProduct_sub_cos_le hp1 hp a hC hbound n
      (displacedRoots a n) hdisc
    have hderr : ‖deriv (displacedBoundaryProduct a) (displacedRoots a n) -
        cos (displacedRoots a n)‖ < 1/4 := by
      apply hd.trans_lt
      have hh := mul_lt_mul_of_pos_left hAn (by positivity : 0 < 4/Real.pi)
      have he : (4/Real.pi)*(Real.pi/16) = (1/4 : ℝ) := by field_simp; ring
      exact hh.trans_eq he
    have hc := cos_displacedRoot_sub_free_le a hr n
    have hsmall : ‖deriv (displacedBoundaryProduct a) (displacedRoots a n) -
        cos ((Real.pi : ℂ)*n)‖ < 1/2 := by
      have ht := norm_sub_le_norm_sub_add_norm_sub
        (deriv (displacedBoundaryProduct a) (displacedRoots a n))
        (cos (displacedRoots a n)) (cos ((Real.pi : ℂ)*n))
      have haquarter := han.trans_le (min_le_right _ _)
      linarith
    have hfree : ‖cos ((Real.pi : ℂ)*n)‖ = 1 := by
      rw [cos_freeCenter_eq_natAbs_sign]
      simp
    have ht := norm_sub_norm_le (cos ((Real.pi : ℂ)*n))
      (deriv (displacedBoundaryProduct a) (displacedRoots a n))
    rw [hfree, norm_sub_rev] at ht
    rw [norm_inv]
    calc
      _ ≤ (1/2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      _ = 2 := by norm_num
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  let B := 2 + ∑ n ∈ s, ‖(deriv (displacedBoundaryProduct a) (displacedRoots a n))⁻¹‖
  refine ⟨B, by dsimp [B]; positivity, fun n => ?_⟩
  by_cases hn : K ≤ n.natAbs
  · exact (htail n hn).trans (le_add_of_nonneg_right
      (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  · have hmem : n ∈ s := by simp only [s, Finset.mem_Icc]; omega
    have hs := Finset.single_le_sum (fun j (_ : j ∈ s) =>
      norm_nonneg ((deriv (displacedBoundaryProduct a) (displacedRoots a j))⁻¹)) hmem
    exact hs.trans (by dsimp [B]; linarith)

end NLS.ZakharovShabat
