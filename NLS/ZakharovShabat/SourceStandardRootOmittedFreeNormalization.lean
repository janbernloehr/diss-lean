import NLS.ZakharovShabat.SourceNormalizedActionFree
import NLS.ZakharovShabat.SourceDeletedFreeSine
import NLS.ZakharovShabat.FreeSineQuotientAnalytic

/-!
# Free normalization and the paired convergence convention

The actual omitted root product equals the filled free sine quotient.
The individual factor errors already have a divergent harmonic tail at
zero source. Absolute convergence in Lemma 10.5 concerns the paired blocks,
exactly as regrouped in the source proof.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free product is the filled sine quotient, with the literal deleted-product normalization. -/
theorem sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) z = freeSineQuotient n z := by
  rw [sourceStandardRootOmittedProduct_zero_source_eq_deleted hp hp1 n z,
    congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z]

/-- The omitted free root is filled by its nonzero cosine value. -/
theorem sourceStandardRootOmittedProduct_zero_source_center (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) ((Real.pi:ℂ)*n) =
      Complex.cos ((Real.pi:ℂ)*n) := by
  rw [sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient hp hp1 n,freeSineQuotient_center]

/-- Unpaired free factor errors have exactly harmonic size at every nonzero spectral point. -/
theorem sourceStandardRootRelativeError_zero_source_positive_norm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (j : ℕ) :
    ‖sourceStandardRootRelativeError hp hp1 (0 : CoeffPair p) ((j+1 : ℕ) : ℤ) z‖ =
      (‖z‖/Real.pi)*(1/((j:ℝ)+1)) := by
  have hd : (Real.pi:ℂ)*(((j+1 : ℕ) : ℤ):ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast (show j+1 ≠ 0 by omega))
  have he : sourceStandardRootRelativeError hp hp1 (0 : CoeffPair p) ((j+1 : ℕ) : ℤ) z =
      -z/((Real.pi:ℂ)*(((j+1 : ℕ) : ℤ):ℂ)) := by
    rw [sourceStandardRootRelativeError,sourceStandardRoot_zero_source]
    field_simp
    ring
  have hn : ‖(((j+1 : ℕ) : ℤ):ℂ)‖ = (j:ℝ)+1 := by
    rw [Complex.norm_intCast,Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _)]
    push_cast
    rfl
  rw [he,norm_div,norm_neg,norm_mul,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hj : (j:ℝ)+1 ≠ 0 := by positivity
  field_simp [Real.pi_ne_zero,hj]

/-- Absolute summability of individual free factor errors fails; the paired convention is essential. -/
theorem not_summable_norm_sourceStandardRootRelativeError_zero_source (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (hz : z ≠ 0) :
    ¬Summable (fun j : ℕ =>
      ‖sourceStandardRootRelativeError hp hp1 (0 : CoeffPair p) ((j+1 : ℕ) : ℤ) z‖) := by
  intro hs
  simp_rw [sourceStandardRootRelativeError_zero_source_positive_norm hp hp1 z] at hs
  have hc : ‖z‖/Real.pi ≠ 0 := div_ne_zero (norm_ne_zero_iff.mpr hz) Real.pi_ne_zero
  have hh : Summable (fun j : ℕ => 1/((j:ℝ)+1)) := by
    simpa only [← mul_assoc,inv_mul_cancel₀ hc,one_mul] using hs.mul_left (‖z‖/Real.pi)⁻¹
  have hshift : Summable (fun j : ℕ => 1/((j+1 : ℕ):ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hshift)

/-- The imaginary test point lies in every actual free omitted domain. -/
theorem sourceStandardRootOmittedDomain_zero_source_contains_I (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Complex.I ∈ sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) n := by
  intro m _ hm
  simp only [sourcePeriodicSegment,map_zero,canonicalPeriodicLeft_zero,
    canonicalPeriodicRight_zero,segment_same] at hm
  have he : Complex.I = (Real.pi:ℂ)*m := hm
  have him := congrArg Complex.im he
  norm_num at him

/-- Every free omitted product extends analytically through all collapsed gaps. -/
theorem sourceStandardRootOmittedProduct_zero_source_entire (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p)) univ := by
  have he : sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) = freeSineQuotient n :=
    funext (sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient hp hp1 n)
  rw [he]
  exact analyticOnNhd_freeSineQuotient n

/-- The value at the omitted free point has norm one, including at negative indices. -/
theorem sourceStandardRootOmittedProduct_zero_source_center_norm (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ‖sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) ((Real.pi:ℂ)*n)‖ = 1 := by
  rw [sourceStandardRootOmittedProduct_zero_source_center hp hp1 n,norm_cos_freeCenter]

/-- Every unomitted free spectral point remains a zero of the product. -/
theorem sourceStandardRootOmittedProduct_zero_source_other_center (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n) :
    sourceStandardRootOmittedProduct hp hp1 n (0 : CoeffPair p) ((Real.pi:ℂ)*m) = 0 := by
  have hz : (Real.pi:ℂ)*m ≠ (Real.pi:ℂ)*n := by
    intro he
    have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have he' := mul_left_cancel₀ hπ he
    exact hmn (by exact_mod_cast he')
  rw [sourceStandardRootOmittedProduct_zero_source_eq_freeSineQuotient hp hp1 n,
    freeSineQuotient_eq_div n _ hz]
  have hs : Complex.sin ((Real.pi:ℂ)*m) = 0 := by
    rw [mul_comm]
    exact Complex.sin_int_mul_pi m
  simp [hs]

end NLS.ZakharovShabat
