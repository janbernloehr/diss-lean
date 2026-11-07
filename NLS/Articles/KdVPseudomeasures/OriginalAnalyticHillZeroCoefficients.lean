import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCompactness
import NLS.Articles.KdVPseudomeasures.OriginalHillNumeratorSimpleZeros
import NLS.KdV.HminusOneHillPsiZeroNoncollision

/-! Indexed real zero coefficients are continuous in the ORIGINAL
H-minus-one norm and admit actual analytic complexifications matching
their values at EVERY original real source. Each retained index pair
has an open connected complex domain containing the ENTIRE real form.
Different retained labels of one numerator cannot collide on their
WHOLE complex domain overlap. The domains may depend on the pair;
the common all-pair extension, Banach sequence analyticity, normalized
product and finer squared-gap estimate remain open. -/
noncomputable section
open Set Complex NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_originalHillPsiRealZero (n m : ℕ+) : Continuous (originalHillPsiRealZero n m) := by
  have hmap : Continuous (fun q : OriginalHminusOnePotential =>
      (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ :
        {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a})) :=
    (periodOneOriginalExtract.continuous.comp continuous_subtype_val).subtype_mk
      (fun q => originalPeriodOneCoefficients_real q)
  exact (continuous_hillHminusCanonicalPsiRealZero n m).comp hmap

theorem continuous_originalHillPositiveGapEndpoints (m : ℕ+) :
    Continuous (fun q : OriginalHminusOnePotential => originalHillLabels q (2*(m:ℕ)-1)) ∧
      Continuous (fun q : OriginalHminusOnePotential => originalHillLabels q (2*(m:ℕ))) := by
  have hmap : Continuous (fun q : OriginalHminusOnePotential =>
      (⟨originalPeriodOneCoefficients q,originalPeriodOneCoefficients_real q⟩ :
        {a : PeriodOneHminusOne // IsRealPeriodOneHminusOne a})) :=
    (periodOneOriginalExtract.continuous.comp continuous_subtype_val).subtype_mk
      (fun q => originalPeriodOneCoefficients_real q)
  exact ⟨(continuous_hillHminusPositiveGapEndpoints m).1.comp hmap,
    (continuous_hillHminusPositiveGapEndpoints m).2.comp hmap⟩

theorem original_Hill_indexed_zero_coefficient_complexification (n m : ℕ+) (hmn : m ≠ n) :
    IsOpen (hillHminusPsiZeroDomain n m) ∧ IsConnected (hillHminusPsiZeroDomain n m) ∧
      hillHminusPsiZeroDomain n m ⊆ hillHminusCanonicalPsiDomain ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusPsiZeroDomain n m) ∧
      AnalyticOnNhd ℂ (hillHminusCanonicalRetainedPsiZero n m) (hillHminusPsiZeroDomain n m) ∧
      (∀ q : OriginalHminusOnePotential, hillHminusCanonicalRetainedPsiZero n m (originalPeriodOneCoefficients q) =
        (originalHillPsiRealZero n m q:ℂ)) ∧
      ∀ a ∈ hillHminusPsiZeroDomain n m,
        hillHminusCanonicalPsi n (hillHminusCanonicalRetainedPsiZero n m a,a) = 0 ∧
          deriv (fun E : ℂ => hillHminusCanonicalPsi n (E,a)) (hillHminusCanonicalRetainedPsiZero n m a) ≠ 0 :=
  ⟨isOpen_hillHminusPsiZeroDomain n m,isConnected_hillHminusPsiZeroDomain n m hmn,
    hillHminusPsiZeroDomain_subset n m,
    fun q => real_mem_hillHminusPsiZeroDomain n m hmn _ (originalPeriodOneCoefficients_real q),
    analyticOnNhd_hillHminusCanonicalRetainedPsiZero n m,
    fun q => hillHminusCanonicalRetainedPsiZero_eq_real n m hmn _ (originalPeriodOneCoefficients_real q),
    hillHminusCanonicalRetainedPsiZero_is_simple_root n m⟩

theorem original_Hill_indexed_zero_coefficients_ne_on_complex_overlap
    (n m k : ℕ+) (hmk : m ≠ k) (a : PeriodOneHminusOne)
    (hm : a ∈ hillHminusPsiZeroDomain n m) (hk : a ∈ hillHminusPsiZeroDomain n k) :
    hillHminusCanonicalRetainedPsiZero n m a ≠ hillHminusCanonicalRetainedPsiZero n k a :=
  hillHminusCanonicalRetainedPsiZero_ne n m k hmk a hm hk

end NLS.Articles.KdVPseudomeasures
