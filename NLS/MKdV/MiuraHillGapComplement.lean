import NLS.MKdV.MiuraGapIdentification
import NLS.MKdV.MiuraHillBoundaryExtension
import NLS.ZakharovShabat.RealDeletedPeriodicProduct
import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcs

/-! # The full physical Hill gap complement under squaring

The excluded lowest cut is the real ray below the ground eigenvalue;
each positive closed cut is the interval between its independently
constructed physical Hill labels. Squaring the right frequency
half-plane gives exactly this domain.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraHillGapComplement (a : ScalarDomain 2) (ha : ∀ n, a.val n = conj (a.val (-n))) : Set ℂ :=
  {μ | (μ.im = 0 → miuraHillLabels a ha 0 < μ.re) ∧
    ∀ n : ℕ, 1 ≤ n → μ.im = 0 →
      μ.re ∉ Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n))}

theorem miura_real_positive_rootDomain_iff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val ↔
      (miuraNLSRight a 0).re < x ∧ ∀ n : ℕ, 1 ≤ n →
        x ∉ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re := by
  have hmem (n : ℤ) (h : x ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re) :
      (x : ℂ) ∈ sourcePeriodicSegment (by simp) (by norm_num) (realDiagonalH1Source a ha).val n :=
    sourcePeriodicSegment_mem_of_realIcc _ _ _ (realDiagonalH1Source a ha).property n x h
  have hL0 : (miuraNLSLeft a 0).re ≤ 0 := by
    have h := congrArg Complex.re (miuraNLSEndpoints_reflection a 0).1
    simp only [neg_zero,neg_re] at h
    rw [h]
    exact neg_nonpos.mpr (miuraNLSRight_zero_nonnegative a)
  constructor
  · intro hr
    constructor
    · by_contra he
      exact hr 0 (hmem 0 ⟨hL0.trans hx.le,le_of_not_gt he⟩)
    · intro n _ hn
      exact hr n (hmem n hn)
  · rintro ⟨h0,hpos⟩ n hn
    have hi : x ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re :=
      sourcePeriodicSegment_re_mem_Icc _ _ _ n x hn
    rcases lt_trichotomy n 0 with hneg | rfl | hpositive
    · have hR := miuraNLSRight_neg a ha hneg
      linarith [hi.2]
    · exact h0.not_ge hi.2
    · lift n to ℕ using hpositive.le
      exact hpos n (by omega) hi

theorem miuraHillGapComplement_sq_iff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (hzr : 0 < z.re) :
    z^2 ∈ miuraHillGapComplement a ha ↔
      z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val := by
  by_cases hzi : z.im = 0
  · have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hzi]
    have hR0 := miuraNLSRight_zero_nonnegative a
    have h0 : miuraHillLabels a ha 0 < z.re^2 ↔ (miuraNLSRight a 0).re < z.re := by
      rw [miuraHillLabels_ground a ha]
      exact sq_lt_sq₀ hR0 hzr.le
    have hgap (n : ℕ) (hn : 1 ≤ n) :
        z.re^2 ∈ Icc (miuraHillLabels a ha (2*n-1)) (miuraHillLabels a ha (2*n)) ↔
          z.re ∈ Icc (miuraNLSLeft a n).re (miuraNLSRight a n).re := by
      rw [miuraHillLabels_left a ha n hn,miuraHillLabels_right a ha n hn]
      have hL := (miuraNLSLeft_pos a ha (show (0 : ℤ) < n by omega)).le
      have hR := hL.trans (miuraNLSEndpoints_within a n)
      exact and_congr (sq_le_sq₀ hL hzr.le) (sq_le_sq₀ hzr.le hR)
    rw [← he,miura_real_positive_rootDomain_iff a ha z.re hzr]
    simp only [miuraHillGapComplement,Set.mem_ofPred_eq,← ofReal_pow,ofReal_re,ofReal_im,
      eq_self,true_implies]
    constructor
    · rintro ⟨hc,hg⟩
      exact ⟨h0.mp hc,fun n hn hx => hg n hn ((hgap n hn).mpr hx)⟩
    · rintro ⟨hc,hg⟩
      exact ⟨h0.mpr hc,fun n hn hx => hg n hn ((hgap n hn).mp hx)⟩
  · have hi : (z^2).im ≠ 0 := by
      simp only [pow_two,mul_im]
      intro he
      apply mul_ne_zero hzr.ne' hzi
      nlinarith
    constructor
    · intro _
      exact sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (realDiagonalH1Source a ha).property z hzi
    · intro _
      exact ⟨fun h => (hi h).elim,fun _ _ h => (hi h).elim⟩

theorem sqrt_re_pos_of_slitPlane (μ : ℂ) (hμ : μ ∈ slitPlane) : 0 < (Complex.sqrt μ).re := by
  have hn : 0 ≤ (Complex.sqrt μ).re := by
    rw [Complex.sqrt,cpow_inv_two_re]
    positivity
  by_contra he
  have hz : (Complex.sqrt μ).re = 0 := le_antisymm (le_of_not_gt he) hn
  have hre := congrArg Complex.re (NLS.ComplexAnalysis.complex_sqrt_sq μ)
  have him := congrArg Complex.im (NLS.ComplexAnalysis.complex_sqrt_sq μ)
  simp only [pow_two,mul_re,mul_im,hz,zero_mul,mul_zero,zero_add] at hre him
  rcases mem_slitPlane_iff.mp hμ with hp | hi
  · nlinarith [sq_nonneg (Complex.sqrt μ).im]
  · exact hi him.symm

theorem miuraHillGapComplement_sqrt (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) (hμ : μ ∈ miuraHillGapComplement a ha) :
    μ ∈ slitPlane ∧ 0 < (Complex.sqrt μ).re ∧
      Complex.sqrt μ ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val := by
  have hs : μ ∈ slitPlane := by
    by_cases hi : μ.im = 0
    · exact mem_slitPlane_iff.mpr (Or.inl ((miuraHillLabels_nonnegative a ha 0).trans_lt (hμ.1 hi)))
    · exact mem_slitPlane_iff.mpr (Or.inr hi)
  have hp := sqrt_re_pos_of_slitPlane μ hs
  have he := miuraHillGapComplement_sq_iff a ha (Complex.sqrt μ) hp
  rw [NLS.ComplexAnalysis.complex_sqrt_sq] at he
  exact ⟨hs,hp,he.mp hμ⟩

theorem miuraHillGapComplement_iff_sqrt (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (μ : ℂ) :
    μ ∈ miuraHillGapComplement a ha ↔ μ ∈ slitPlane ∧
      Complex.sqrt μ ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (realDiagonalH1Source a ha).val := by
  constructor
  · intro hμ
    have h := miuraHillGapComplement_sqrt a ha μ hμ
    exact ⟨h.1,h.2.2⟩
  · rintro ⟨hs,hz⟩
    have he := (miuraHillGapComplement_sq_iff a ha (Complex.sqrt μ) (sqrt_re_pos_of_slitPlane μ hs)).mpr hz
    simpa only [NLS.ComplexAnalysis.complex_sqrt_sq] using he

theorem isOpen_miuraHillGapComplement (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : IsOpen (miuraHillGapComplement a ha) := by
  apply isOpen_iff_mem_nhds.mpr
  intro μ hμ
  have h := (miuraHillGapComplement_iff_sqrt a ha μ).mp hμ
  have hN : ∀ᶠ w in 𝓝 μ, Complex.sqrt w ∈ sourceCanonicalRootDomain (by simp) (by norm_num)
      (realDiagonalH1Source a ha).val :=
    (Complex.differentiableAt_sqrt h.1).continuousAt.tendsto.eventually
      ((isOpen_sourceCanonicalRootDomain_of_realType _ _ _ (realDiagonalH1Source a ha).property).mem_nhds h.2)
  filter_upwards [isOpen_slitPlane.mem_nhds h.1,hN] with w hw hz
  exact (miuraHillGapComplement_iff_sqrt a ha w).mpr ⟨hw,hz⟩

end NLS.MKdV
