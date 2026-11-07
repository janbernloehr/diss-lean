import NLS.KdV.PseudomeasureRealPairs
import NLS.ComplexAnalysis.LexicographicOrder

/-! Intrinsic lexicographically ordered high pairs of the original complex singular operator. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- Two actual original spectral values with their full algebraic repetitions. -/
structure EndpointHillComplexPair (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (n : ℕ) where
  left : ℂ
  right : ℂ
  ordered : complexLexLE left right
  left_mem : left ∈ reducedHillStrip n
  right_mem : right ∈ reducedHillStrip n
  left_spectral : left ∈ endpointHillSpectrum r hr1 q
  right_spectral : right ∈ endpointHillSpectrum r hr1 q
  left_localized : ‖left-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4
  right_localized : ‖right-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4
  spectrum_iff : ∀ z ∈ reducedHillStrip n, z ∈ endpointHillSpectrum r hr1 q ↔ z = left ∨ z = right
  multiplicities : ∀ z ∈ reducedHillStrip n,
    endpointHillAlgebraicMultiplicity r hr hr1 q z = ({left,right}:Multiset ℂ).count z

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)

/-- A native real pair is the same actual physical pair in the source complex order. -/
def EndpointHillRealPair.toComplex (p : EndpointHillRealPair r hr hr1 q n) :
    EndpointHillComplexPair r hr hr1 q n :=
  ⟨p.left, p.right, (complexLexLE_ofReal_iff p.left p.right).mpr p.ordered,
    p.left_mem, p.right_mem, p.left_spectral, p.right_spectral,
    (by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using p.left_localized),
    (by simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using p.right_localized),
    p.spectrum_iff, p.multiplicities⟩

/-- An actual complex high pair exists, with lexicographic order and all algebraic repetitions. -/
theorem exists_endpointHillComplexPair (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    Nonempty (EndpointHillComplexPair r hr hr1 q n) := by
  obtain ⟨x, hx, y, hy, hx0, hy0, horder⟩ := exists_two_analytic_zeros
    (endpointReducedDeterminant_strip_hasFiniteSupport r hr hr1 n hn q hs)
    (endpointReducedDeterminant_strip_two_zeros r hr hr1 n hn q hs)
  have hxsp := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn x hx q hs).mpr hx0
  have hysp := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn y hy q hs).mpr hy0
  have hxl := endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs x hx hx0
  have hyl := endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs y hy hy0
  have hm (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      endpointHillAlgebraicMultiplicity r hr hr1 q z = ({x,y}:Multiset ℂ).count z := by
    rw [endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt r hr hr1 n hn q hs z hz]
    simpa only [if_pos hz] using horder z
  have hspec (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      z ∈ endpointHillSpectrum r hr1 q ↔ z = x ∨ z = y := by
    rw [← endpointHillAlgebraicMultiplicity_pos_iff r hr hr1 q z, hm z hz]
    simpa using (Multiset.count_pos (s := ({x,y}:Multiset ℂ)) (a := z))
  rcases le_total (complexLexKey x) (complexLexKey y) with hle | hle
  · exact ⟨⟨x, y, hle, hx, hy, hxsp, hysp, hxl, hyl, hspec, hm⟩⟩
  · exact ⟨⟨y, x, hle, hy, hx, hysp, hxsp, hyl, hxl,
      (by simpa only [or_comm] using hspec),
      (by simpa only [Multiset.pair_comm y x] using hm)⟩⟩

/-- The actual spectral set and source order uniquely determine both endpoints. -/
theorem EndpointHillComplexPair.endpoints_unique (p s : EndpointHillComplexPair r hr hr1 q n) :
    p.left = s.left ∧ p.right = s.right := by
  have hpl := (s.spectrum_iff p.left p.left_mem).mp p.left_spectral
  have hpr := (s.spectrum_iff p.right p.right_mem).mp p.right_spectral
  have hsl := (p.spectrum_iff s.left s.left_mem).mp s.left_spectral
  have hsr := (p.spectrum_iff s.right s.right_mem).mp s.right_spectral
  have h₁ : complexLexLE p.left s.left := by
    rcases hsl with h | h
    · rw [h]; exact le_rfl
    · rw [h]; exact p.ordered
  have h₂ : complexLexLE s.left p.left := by
    rcases hpl with h | h
    · rw [h]; exact le_rfl
    · rw [h]; exact s.ordered
  have h₃ : complexLexLE p.right s.right := by
    rcases hpr with h | h
    · rw [h]; exact s.ordered
    · rw [h]; exact le_rfl
  have h₄ : complexLexLE s.right p.right := by
    rcases hsr with h | h
    · rw [h]; exact p.ordered
    · rw [h]; exact le_rfl
  exact ⟨complexLexKey_injective (le_antisymm h₁ h₂), complexLexKey_injective (le_antisymm h₃ h₄)⟩

/-- The entire physical pair is independent of its construction. -/
theorem EndpointHillComplexPair.unique (p s : EndpointHillComplexPair r hr hr1 q n) : p = s := by
  obtain ⟨hl, hrr⟩ := p.endpoints_unique r hr hr1 n q s
  cases p; cases s
  dsimp at hl hrr
  cases hl; cases hrr
  rfl

/-- Choose the actual ordered pair only after its existence is proved. -/
def endpointHillComplexPair (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    EndpointHillComplexPair r hr hr1 q n :=
  Classical.choice (exists_endpointHillComplexPair r hr hr1 n q hn hs)

/-- Distinct high mode numbers give strict separation in real part. -/
theorem EndpointHillComplexPair.right_re_lt_left (hn : 1 ≤ n)
    (v : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (m : ℕ) (hnm : n < m) (p : EndpointHillComplexPair r hr hr1 q n)
    (s : EndpointHillComplexPair r hr hr1 v m) : p.right.re < s.left.re := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (n:ℝ)+1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hnm)
  have hsn : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hsm : Real.sqrt (m:ℝ) ≤ m := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hpi : (1:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hscale := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ (m:ℝ)^2-(n:ℝ)^2 by nlinarith)
  have hp := (Complex.abs_re_le_norm (p.right-(freeHillValue n:ℂ))).trans p.right_localized
  have hs := (Complex.abs_re_le_norm (s.left-(freeHillValue m:ℂ))).trans s.left_localized
  simp only [Complex.sub_re, Complex.ofReal_re, freeHillValue, Int.cast_natCast] at hp hs
  nlinarith [(abs_le.mp hp).2, (abs_le.mp hs).1]

/-- The actual complex pair has the source endpoint gap bound; no reality is used. -/
theorem EndpointHillComplexPair.gap_le_weight_norm (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    ‖p.right-p.left‖ ≤ 2*Real.sqrt 6*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  have hl := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.left p.left_mem q hs).mp p.left_spectral
  have hrr := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.right p.right_mem q hs).mp p.right_spectral
  have he := endpointReduced_roots_separation_sqrt r hr hr1 n hn q hs p.right p.left
    p.right_mem p.left_mem hrr hl
  have hb := mul_le_mul_of_nonneg_left
    (endpointCouplingRadius_le_weight_norm r hr hr1 n hn q hs) (Real.sqrt_nonneg 6)
  nlinarith

/-- Ordinary signed-mode Sobolev weights control actual complex high gaps uniformly. -/
theorem EndpointHillComplexPair.weighted_gap_le (hn : 1 ≤ n)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    Weight.sobolev (-r) n*‖p.right-p.left‖ ≤ 6*Real.sqrt 6*‖q‖ := by
  have hW : Weight.sobolev r (2*(n:ℤ)) ≤ 3*Weight.sobolev r n := by
    apply (sobolev_two_mode_le r hr hr1 n hn).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    simp only [Weight.sobolev_apply, Int.cast_natCast, abs_of_nonneg (show (0:ℝ) ≤ n by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hr
  have hinv : Weight.sobolev (-r) n = (Weight.sobolev r n)⁻¹ := by
    simp only [Weight.sobolev_apply]
    exact Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+|((n:ℤ):ℝ)|) r
  rw [hinv, ← div_eq_inv_mul, div_le_iff₀ ((Weight.sobolev r).positive n)]
  have hscale := mul_le_mul_of_nonneg_left hW (show 0 ≤ 2*Real.sqrt 6*‖q‖ by positivity)
  have hgap := p.gap_le_weight_norm r hr hr1 n q hn hs
  nlinarith

end NLS.KdV
