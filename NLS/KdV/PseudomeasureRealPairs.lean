import NLS.KdV.PseudomeasureRealSpectrum
import NLS.ComplexAnalysis.ZeroMultiset
import NLS.KdV.PseudomeasureRootSeparation

/-!
# Ordered actual high pairs for singular endpoint potentials

These pairs are constructed from the actual zeros and retain the exact physical
algebraic multiplicities, with repetition at a collapsed gap. Each pair exhausts
its full corrected closed strip. The article-level downstream developments prove
the central count and global canonical enumeration without assuming them here.
-/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- An intrinsic ordered physical pair on a corrected strip, including multiplicities. -/
structure EndpointHillRealPair (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (n : ℕ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  left_mem : (left : ℂ) ∈ reducedHillStrip n
  right_mem : (right : ℂ) ∈ reducedHillStrip n
  left_spectral : (left : ℂ) ∈ endpointHillSpectrum r hr1 q
  right_spectral : (right : ℂ) ∈ endpointHillSpectrum r hr1 q
  left_localized : |left-freeHillValue n| ≤ Real.sqrt (n:ℝ)/4
  right_localized : |right-freeHillValue n| ≤ Real.sqrt (n:ℝ)/4
  spectrum_iff : ∀ z ∈ reducedHillStrip n,
    z ∈ endpointHillSpectrum r hr1 q ↔ z = (left:ℂ) ∨ z = (right:ℂ)
  multiplicities : ∀ z ∈ reducedHillStrip n,
    endpointHillAlgebraicMultiplicity r hr hr1 q z = ({(left:ℂ),(right:ℂ)} : Multiset ℂ).count z

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The actual analytic-order count has finite support on the entire unbounded
corrected strip, by physical spectral discreteness and the proved localization. -/
theorem endpointReducedDeterminant_strip_hasFiniteSupport :
    (fun z : ℂ => if z ∈ reducedHillStrip n then
      analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z else 0).HasFiniteSupport := by
  apply (finite_endpointHillSpectrum_norm_le r hr hr1 q
    (Real.sqrt (n:ℝ)/4+‖(freeHillValue n:ℂ)‖)).subset
  intro z hz
  obtain ⟨hzS, hz0⟩ := analyticZeroCount_support_subset
    (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) (reducedHillStrip n) hz
  refine ⟨(mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn z hzS q hs).mpr hz0, ?_⟩
  calc
    ‖z‖ ≤ ‖z-(freeHillValue n:ℂ)‖+‖(freeHillValue n:ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add
      (endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs z hzS hz0) le_rfl

include hn hs in
/-- A real singular endpoint potential has one ordered physical pair on each
allowed tail strip, with exact actual algebraic multiplicities on that whole strip. -/
theorem exists_endpointHillRealPair
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    Nonempty (EndpointHillRealPair r hr hr1 q n) := by
  obtain ⟨x, hx, y, hy, hx0, hy0, horder⟩ := exists_two_analytic_zeros
    (endpointReducedDeterminant_strip_hasFiniteSupport r hr hr1 n hn q hs)
    (endpointReducedDeterminant_strip_two_zeros r hr hr1 n hn q hs)
  have hxi := endpointReducedDeterminant_zero_im_eq_zero r hr hr1 n hn q hq hs x hx hx0
  have hyi := endpointReducedDeterminant_zero_im_eq_zero r hr hr1 n hn q hq hs y hy hy0
  have hxc : (x.re:ℂ) = x := by apply Complex.ext <;> simp [hxi]
  have hyc : (y.re:ℂ) = y := by apply Complex.ext <;> simp [hyi]
  have hxsp := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn x hx q hs).mpr hx0
  have hysp := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn y hy q hs).mpr hy0
  have hxl : |x.re-freeHillValue n| ≤ Real.sqrt (n:ℝ)/4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (x-(freeHillValue n:ℂ))).trans
        (endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs x hx hx0)
  have hyl : |y.re-freeHillValue n| ≤ Real.sqrt (n:ℝ)/4 := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      (Complex.abs_re_le_norm (y-(freeHillValue n:ℂ))).trans
        (endpointReducedDeterminant_zero_localization r hr hr1 n hn q hs y hy hy0)
  have hm (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      endpointHillAlgebraicMultiplicity r hr hr1 q z = ({x,y}:Multiset ℂ).count z := by
    rw [endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt r hr hr1 n hn q hs z hz]
    simpa only [if_pos hz] using horder z
  have hspec (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      z ∈ endpointHillSpectrum r hr1 q ↔ z = x ∨ z = y := by
    rw [← endpointHillAlgebraicMultiplicity_pos_iff r hr hr1 q z, hm z hz]
    simpa using (Multiset.count_pos (s := ({x,y}:Multiset ℂ)) (a := z))
  rcases le_total x.re y.re with hle | hle
  · exact ⟨⟨x.re,y.re,hle,hxc.symm ▸ hx,hyc.symm ▸ hy,hxc.symm ▸ hxsp,hyc.symm ▸ hysp,
      hxl,hyl,(by simpa only [hxc,hyc] using hspec),(by simpa only [hxc,hyc] using hm)⟩⟩
  · exact ⟨⟨y.re,x.re,hle,hyc.symm ▸ hy,hxc.symm ▸ hx,hyc.symm ▸ hysp,hxc.symm ▸ hxsp,
      hyl,hxl,(by simpa only [hxc,hyc,or_comm] using hspec),
      (by simpa only [hxc,hyc,Multiset.pair_comm y x] using hm)⟩⟩

/-- Ordering and the actual spectral set uniquely determine both endpoints. -/
theorem EndpointHillRealPair.endpoints_unique
    (p s : EndpointHillRealPair r hr hr1 q n) : p.left = s.left ∧ p.right = s.right := by
  have hpl := (s.spectrum_iff p.left p.left_mem).mp p.left_spectral
  have hpr := (s.spectrum_iff p.right p.right_mem).mp p.right_spectral
  have hsl := (p.spectrum_iff s.left s.left_mem).mp s.left_spectral
  have hsr := (p.spectrum_iff s.right s.right_mem).mp s.right_spectral
  simp only [Complex.ofReal_inj] at hpl hpr hsl hsr
  rcases hpl with hpl | hpl <;> rcases hpr with hpr | hpr <;>
    rcases hsl with hsl | hsl <;> rcases hsr with hsr | hsr <;>
    constructor <;> linarith [p.ordered,s.ordered]

/-- The entire intrinsic physical pair is unique, independently of its construction. -/
theorem EndpointHillRealPair.unique (p s : EndpointHillRealPair r hr hr1 q n) : p = s := by
  obtain ⟨hl, hr⟩ := p.endpoints_unique r hr hr1 n q s
  cases p
  cases s
  dsimp at hl hr
  cases hl
  cases hr
  rfl

include hn hs in
/-- The actual ordered high pair, chosen only after existence has been proved. -/
def endpointHillRealPair
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    EndpointHillRealPair r hr hr1 q n :=
  Classical.choice (exists_endpointHillRealPair r hr hr1 n hn q hs hq)

/-- Actual algebraic multiplicity at the left endpoint, including collapsed gaps. -/
theorem EndpointHillRealPair.left_multiplicity (p : EndpointHillRealPair r hr hr1 q n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q p.left =
      if p.left = p.right then 2 else 1 := by
  rw [p.multiplicities p.left p.left_mem]
  by_cases he : p.left = p.right
  · simp [he]
  · simp [he]

/-- Actual algebraic multiplicity at the right endpoint, including collapsed gaps. -/
theorem EndpointHillRealPair.right_multiplicity (p : EndpointHillRealPair r hr hr1 q n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q p.right =
      if p.left = p.right then 2 else 1 := by
  rw [p.multiplicities p.right p.right_mem]
  by_cases he : p.left = p.right
  · simp [he]
  · simp [he, Ne.symm he]

/-- A collapsed local gap is exactly a double physical eigenvalue. -/
theorem EndpointHillRealPair.collapsed_iff_multiplicity_two (p : EndpointHillRealPair r hr hr1 q n) :
    p.left = p.right ↔ endpointHillAlgebraicMultiplicity r hr hr1 q p.left = 2 := by
  rw [p.left_multiplicity r hr hr1 n q]
  by_cases he : p.left = p.right <;> simp [he]

/-- The width of the actual ordered local spectral pair. -/
def EndpointHillRealPair.gap (p : EndpointHillRealPair r hr hr1 q n) : ℝ := p.right-p.left

/-- The midpoint of the actual ordered local spectral pair. -/
def EndpointHillRealPair.midpoint (p : EndpointHillRealPair r hr hr1 q n) : ℝ := (p.left+p.right)/2

/-- The actual local gap width is nonnegative. -/
theorem EndpointHillRealPair.gap_nonneg (p : EndpointHillRealPair r hr hr1 q n) :
    0 ≤ p.gap r hr hr1 n q := sub_nonneg.mpr p.ordered

/-- The actual local gap width vanishes exactly at a collapsed pair. -/
theorem EndpointHillRealPair.gap_eq_zero_iff (p : EndpointHillRealPair r hr hr1 q n) :
    p.gap r hr hr1 n q = 0 ↔ p.left = p.right := by
  exact sub_eq_zero.trans eq_comm

/-- Localization of both actual eigenvalues gives the high-pair width bound. -/
theorem EndpointHillRealPair.gap_le (p : EndpointHillRealPair r hr hr1 q n) :
    p.gap r hr hr1 n q ≤ Real.sqrt (n:ℝ)/2 := by
  have hl := abs_le.mp p.left_localized
  have hr := abs_le.mp p.right_localized
  dsimp [EndpointHillRealPair.gap]
  linarith

/-- The actual midpoint retains the tight single-root localization bound. -/
theorem EndpointHillRealPair.midpoint_localized (p : EndpointHillRealPair r hr hr1 q n) :
    |p.midpoint r hr hr1 n q-freeHillValue n| ≤ Real.sqrt (n:ℝ)/4 := by
  have hl := abs_le.mp p.left_localized
  have hr := abs_le.mp p.right_localized
  apply abs_le.mpr
  dsimp [EndpointHillRealPair.midpoint]
  constructor <;> linarith

include hn hs in
/-- The actual determinant orders equal the multiplicities of the intrinsic physical pair. -/
theorem EndpointHillRealPair.analytic_orders (p : EndpointHillRealPair r hr hr1 q n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z =
      ({(p.left:ℂ),(p.right:ℂ)}:Multiset ℂ).count z := by
  rw [← endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt r hr hr1 n hn q hs z hz]
  exact p.multiplicities z hz

/-- The geometric dimension at the left endpoint distinguishes open and collapsed gaps. -/
theorem EndpointHillRealPair.left_geometric_multiplicity (p : EndpointHillRealPair r hr hr1 q n)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    Module.finrank ℂ (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) p.left) =
      if p.left = p.right then 2 else 1 := by
  rw [← endpointHillAlgebraicMultiplicity_eq_geometric r hr hr1 q hq p.left]
  exact p.left_multiplicity r hr hr1 n q

/-- The geometric dimension at the right endpoint distinguishes open and collapsed gaps. -/
theorem EndpointHillRealPair.right_geometric_multiplicity (p : EndpointHillRealPair r hr hr1 q n)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate) :
    Module.finrank ℂ (singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) p.right) =
      if p.left = p.right then 2 else 1 := by
  rw [← endpointHillAlgebraicMultiplicity_eq_geometric r hr hr1 q hq p.right]
  exact p.right_multiplicity r hr hr1 n q

include hn hs in
/-- The intrinsic left endpoint is an actual zero of the effective determinant. -/
theorem EndpointHillRealPair.left_zero (p : EndpointHillRealPair r hr hr1 q n) :
    endpointReducedDeterminant r hr hr1 n (q,p.left) = 0 :=
  (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.left p.left_mem q hs).mp p.left_spectral

include hn hs in
/-- The intrinsic right endpoint is an actual zero of the effective determinant. -/
theorem EndpointHillRealPair.right_zero (p : EndpointHillRealPair r hr hr1 q n) :
    endpointReducedDeterminant r hr hr1 n (q,p.right) = 0 :=
  (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.right p.right_mem q hs).mp p.right_spectral

/-- The left endpoint has a nonzero eigenvector in the entire original H1 domain. -/
theorem EndpointHillRealPair.left_has_eigenvector (p : EndpointHillRealPair r hr hr1 q n) :
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
        (p.left:ℂ) • singularHillDomainInclusion f :=
  (mem_endpointHillSpectrum_iff r hr hr1 q p.left).mp p.left_spectral

/-- The right endpoint has a nonzero eigenvector in the entire original H1 domain. -/
theorem EndpointHillRealPair.right_has_eigenvector (p : EndpointHillRealPair r hr hr1 q n) :
    ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
        (p.right:ℂ) • singularHillDomainInclusion f :=
  (mem_endpointHillSpectrum_iff r hr hr1 q p.right).mp p.right_spectral

include hn hs in
/-- The source's square-root-six estimate now bounds the actual physical local gap. -/
theorem EndpointHillRealPair.gap_le_couplingRadius (p : EndpointHillRealPair r hr hr1 q n) :
    p.gap r hr hr1 n q ≤ Real.sqrt 6*endpointCouplingRadius r hr hr1 n q := by
  have he := endpointReduced_roots_separation_sqrt r hr hr1 n hn q hs p.right p.left
    p.right_mem p.left_mem (p.right_zero r hr hr1 n hn q hs) (p.left_zero r hr hr1 n hn q hs)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr p.ordered)] at he
  exact he

include hn hs in
/-- The actual local gap has the source's endpoint growth bound in the potential norm. -/
theorem EndpointHillRealPair.gap_le_weight_norm (p : EndpointHillRealPair r hr hr1 q n) :
    p.gap r hr hr1 n q ≤ 2*Real.sqrt 6*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  have h := mul_le_mul_of_nonneg_left
    (endpointCouplingRadius_le_weight_norm r hr hr1 n hn q hs) (Real.sqrt_nonneg 6)
  calc
    _ ≤ _ := p.gap_le_couplingRadius r hr hr1 n hn q hs
    _ ≤ _ := by nlinarith

include hn hs in
/-- The normalized actual high gap is bounded in the original endpoint potential norm. -/
theorem EndpointHillRealPair.normalized_gap_le (p : EndpointHillRealPair r hr hr1 q n) :
    (Weight.sobolev r (2*(n:ℤ)))⁻¹*p.gap r hr hr1 n q ≤ 2*Real.sqrt 6*‖q‖ := by
  have hW := (Weight.sobolev r).positive (2*(n:ℤ))
  rw [← div_eq_inv_mul, div_le_iff₀ hW]
  calc
    _ ≤ _ := p.gap_le_weight_norm r hr hr1 n hn q hs
    _ = _ := by ring

include hn hs in
/-- In the ordinary mode-number Sobolev weight, the actual high gaps have
uniform endpoint bound. The factor three compares n with its double frequency. -/
theorem EndpointHillRealPair.weighted_gap_le (p : EndpointHillRealPair r hr hr1 q n) :
    Weight.sobolev (-r) n*p.gap r hr hr1 n q ≤ 6*Real.sqrt 6*‖q‖ := by
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
  have hgap := p.gap_le_weight_norm r hr hr1 n hn q hs
  nlinarith

include hn in
/-- All actual high pairs are strictly ordered across distinct mode numbers,
also for different potentials when both physical pairs have been constructed. -/
theorem EndpointHillRealPair.right_lt_left
    (v : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (m : ℕ) (hnm : n < m)
    (p : EndpointHillRealPair r hr hr1 q n) (s : EndpointHillRealPair r hr hr1 v m) :
    p.right < s.left := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (n:ℝ)+1 ≤ m := by exact_mod_cast (Nat.succ_le_of_lt hnm)
  have hsn : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hsm : Real.sqrt (m:ℝ) ≤ m := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hpi : (1:ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hsq : (n:ℝ)^2+((n:ℝ)+(m:ℝ)) ≤ (m:ℝ)^2 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_right hpi
    (show 0 ≤ (m:ℝ)^2-(n:ℝ)^2 by nlinarith)
  have hp := (abs_le.mp p.right_localized).2
  have hs := (abs_le.mp s.left_localized).1
  simp only [freeHillValue, Int.cast_natCast] at hp hs
  nlinarith

end NLS.KdV
