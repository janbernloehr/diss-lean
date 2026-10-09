import NLS.ZakharovShabat.TriangularFourierBoundary
import NLS.SequenceSpaces.PairNorm

/-! # Odd finite Fourier blocks for the triangular boundary equation -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Constant opposite coefficients on a finite band and its reflection. -/
def oddFourierCoefficients (S : Finset ℤ) (c : ℝ) : ℤ →₀ ℂ :=
  Finsupp.onFinset (S ∪ S.image Neg.neg)
    (fun n => (if n ∈ S then (c : ℂ) else 0) - (if -n ∈ S then (c : ℂ) else 0))
    (by
      intro n hn
      by_cases h : n ∈ S
      · exact Finset.mem_union_left _ h
      · have hm : -n ∈ S := by by_contra hm; simp [h,hm] at hn
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-n,hm,neg_neg n⟩))

@[simp] theorem oddFourierCoefficients_apply (S : Finset ℤ) (c : ℝ) (n : ℤ) :
    oddFourierCoefficients S c n =
      (if n ∈ S then (c : ℂ) else 0) - (if -n ∈ S then (c : ℂ) else 0) := rfl

theorem support_oddFourierCoefficients_subset (S : Finset ℤ) (c : ℝ) :
    (oddFourierCoefficients S c).support ⊆ S ∪ S.image Neg.neg :=
  Finsupp.support_onFinset_subset

/-- The source norm is controlled by the band cardinality, with the exact exponent. -/
theorem norm_oddFourierCoefficients_source_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (S : Finset ℤ) {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hcard : (2*S.card : ℝ) ≤ B^p.toReal) :
    ‖CoeffPair.ofFinsupp (p := p) (oddFourierCoefficients S c,0)‖ ≤ B*c := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hp0).mp
  rw [CoeffPair.norm_rpow_eq_tsum hp]
  simp only [CoeffPair.ofFinsupp_fst,CoeffPair.ofFinsupp_snd,Finsupp.zero_apply,
    norm_zero,Real.zero_rpow hp0.ne',add_zero]
  let T := S ∪ S.image Neg.neg
  rw [tsum_eq_sum (s := T) (fun n hn => by
    have ha : oddFourierCoefficients S c n = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hn (support_oddFourierCoefficients_subset S c h))
    simp only [ha,norm_zero,Real.zero_rpow hp0.ne'])]
  have hnorm (n : ℤ) : ‖oddFourierCoefficients S c n‖ ≤ c := by
    by_cases hn : n ∈ S <;> by_cases hm : -n ∈ S <;>
      simp [oddFourierCoefficients_apply,hn,hm,abs_of_nonneg hc,hc]
  calc
    _ ≤ ∑ _n ∈ T, c^p.toReal := Finset.sum_le_sum (fun n _ =>
      Real.rpow_le_rpow (norm_nonneg _) (hnorm n) hp0.le)
    _ = (T.card : ℝ)*c^p.toReal := by simp
    _ ≤ (2*S.card : ℝ)*c^p.toReal := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (Finset.card_union_le S (S.image Neg.neg)).trans
        (by have := Finset.card_image_le (s := S) (f := Neg.neg); omega)
    _ ≤ B^p.toReal*c^p.toReal := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (B*c)^p.toReal := (Real.mul_rpow hB hc).symm

/-- The positive real kernel produced by pairing opposite Fourier indices. -/
def triangularBoundaryKernel (H n : ℝ) : ℝ := Real.pi*n/(H^2+(Real.pi*n)^2)

private theorem triangular_paired_reciprocal {H : ℝ} (hH : 0 < H) (n : ℤ) (c : ℝ) :
    (c : ℂ)/((H : ℂ)-(Real.pi : ℂ)*n*I) - (c : ℂ)/((H : ℂ)+(Real.pi : ℂ)*n*I) =
      2*I*(c : ℂ)*(triangularBoundaryKernel H n : ℂ) := by
  have hminus := triangular_denominator_ne_zero hH n
  have hplus : (H : ℂ)+(Real.pi : ℂ)*n*I ≠ 0 := by
    simpa only [Int.cast_neg,mul_neg,neg_mul,sub_neg_eq_add] using triangular_denominator_ne_zero hH (-n)
  have hreal : H^2+(Real.pi*(n : ℝ))^2 ≠ 0 := by positivity
  have hden := Complex.ofReal_ne_zero.mpr hreal
  unfold triangularBoundaryKernel
  push_cast at hden ⊢
  simp only [mul_pow] at hden ⊢
  field_simp [hminus,hplus,hden]
  ring_nf
  simp

/-- The full finite boundary functional is the positive kernel sum for a positive band. -/
theorem triangularBoundarySum_oddFourierCoefficients (S : Finset ℤ)
    (hS : ∀ n ∈ S, 0 < n) (c : ℝ) {H : ℝ} (hH : 0 < H) :
    triangularBoundarySum (oddFourierCoefficients S c) H =
      2*I*(c : ℂ)*((∑ n ∈ S, triangularBoundaryKernel H n : ℝ) : ℂ) := by
  have hneg (n : ℤ) (hn : n ∈ S) : -n ∉ S := by
    intro hm
    have := hS n hn
    have := hS (-n) hm
    omega
  have hdis : Disjoint S (S.image Neg.neg) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨m,hmS,rfl⟩ := Finset.mem_image.mp hm
    exact hneg m hmS hn
  change (oddFourierCoefficients S c).sum (fun n z => z/((H : ℂ)-(Real.pi : ℂ)*n*I)) = _
  rw [Finsupp.sum_of_support_subset _ (support_oddFourierCoefficients_subset S c) _ (by intros; simp),
    Finset.sum_union hdis,Finset.sum_image (by intro a _ b _ h; exact neg_injective h),← Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [oddFourierCoefficients_apply,if_pos hn,if_neg (hneg n hn),neg_neg,
    sub_zero,zero_sub,Int.cast_neg,mul_neg,neg_mul,sub_neg_eq_add,neg_div,← sub_eq_add_neg] using
    triangular_paired_reciprocal hH n c

end NLS.ZakharovShabat
