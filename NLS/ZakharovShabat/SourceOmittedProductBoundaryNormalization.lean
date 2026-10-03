import NLS.ZakharovShabat.DeletedProductSampledValues
import NLS.ZakharovShabat.SourceDeletedPairOmittedSquare
import NLS.ZakharovShabat.SourceStandardRootOmittedParitySign
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-! # Omitted-product normalization at actual boundary roots

The sign on the closed real gap selects the correct square root of the
deleted periodic product, including when the gap collapses. Its deviation
from the signed free reference is therefore controlled by the squared error.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A real number with the chosen unit sign is no farther from that sign
than its square is from one. -/
theorem norm_sub_unit_sign_le_norm_sq_sub_one (w : ℂ) (s : ℝ)
    (hw : w.im = 0) (hs : s^2 = 1) (hsgn : 0 ≤ s*w.re) :
    ‖w-(s : ℂ)‖ ≤ ‖w^2-1‖ := by
  have hre : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hw]
  have hsum : 1 ≤ ‖w+(s : ℂ)‖ := by
    rw [hre,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [sq_abs (w.re+s),abs_nonneg (w.re+s),sq_nonneg w.re]
  have hsC : (s : ℂ)^2 = 1 := by exact_mod_cast hs
  have he : (w-(s : ℂ))*(w+(s : ℂ)) = w^2-1 := by
    linear_combination -hsC
  calc
    ‖w-(s : ℂ)‖ ≤ ‖w-(s : ℂ)‖*‖w+(s : ℂ)‖ := le_mul_of_one_le_right (norm_nonneg _) hsum
    _ = ‖w^2-1‖ := by rw [← norm_mul,he]

/-- Reciprocal differences are controlled near any unit-norm reference. -/
theorem norm_inv_sub_inv_le_of_unit_near (a b : ℂ) (hb : ‖b‖ = 1)
    (hab : ‖a-b‖ ≤ (1 : ℝ)/2) :
    ‖a⁻¹-b⁻¹‖ ≤ 2*‖a-b‖ := by
  have hlo : 1/2 ≤ ‖a‖ := by
    have h := norm_sub_norm_le b a
    rw [norm_sub_rev b a,hb] at h
    linarith
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
  rw [inv_sub_inv ha0 hb0,norm_div,norm_mul,hb,mul_one,norm_sub_rev]
  apply (div_le_iff₀ (by linarith : 0 < ‖a‖)).mpr
  nlinarith [norm_nonneg (a-b)]

/-- Inversion preserves an ℓp perturbation of a unit-norm sequence.
Only finitely many terms can lie outside the perturbative region. -/
theorem memlp_inv_sub_inv_of_unit_reference
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (f g : ℤ → ℂ) (hg : ∀ n, ‖g n‖ = 1) (hfg : Memℓp (fun n => f n-g n) p) :
    Memℓp (fun n => (f n)⁻¹-(g n)⁻¹) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let e : Coeff p := ⟨_,hfg⟩
  obtain ⟨N,hN⟩ := Coeff.exists_natAbs_norm_lt (by linarith : 0 < p.toReal) e (by norm_num : 0 < (1 : ℝ)/2)
  have hm := memlp_of_natAbs_eventual_bound p.toReal (by linarith)
    (fun n => (f n)⁻¹-(g n)⁻¹) (fun n => 2*‖e n‖)
    (by simpa only [ENNReal.ofReal_toReal hp] using (lp.memℓp e).norm.const_mul (2 : ℝ)) N
    (fun n hn => norm_inv_sub_inv_le_of_unit_near (f n) (g n) (hg n) (hN n hn).le)
  simpa only [ENNReal.ofReal_toReal hp] using hm

/-- The absolute-index parity is exactly the signed free cosine. -/
theorem cos_freeCenter_eq_natAbs_sign (n : ℤ) :
    cos ((Real.pi : ℂ)*n) = (-1 : ℂ)^n.natAbs := by
  have h (k : ℕ) : cos ((Real.pi : ℂ)*k) = (-1 : ℂ)^k := by
    have he : (Real.pi : ℂ)*k = (((k : ℝ)*Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [he,← Complex.ofReal_cos,Real.cos_nat_mul_pi]
    push_cast
    rfl
  cases n with
  | ofNat n => exact h n
  | negSucc n =>
    have he : (Int.negSucc n : ℂ) = -((n+1 : ℕ) : ℂ) := by push_cast; ring
    rw [he,mul_neg,Complex.cos_neg]
    exact h (n+1)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual real boundary root avoids all unselected periodic gaps. -/
theorem canonicalPeriodOneBoundaryRoot_mem_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ n ∈ sourceStandardRootOmittedDomain hp hp1 φ n := by
  obtain ⟨W,_,_,hreal,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  have hre : ((canonicalPeriodOneBoundaryRoots hp hp1 b φ n).re : ℂ) =
      canonicalPeriodOneBoundaryRoots hp hp1 b φ n := by
    apply Complex.ext
    · rfl
    · exact (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n).symm
  have hseg := sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hφ n _
    (canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n)
  rw [hre] at hseg
  intro m hm hmem
  exact Set.disjoint_left.mp (hdisjoint φ (hreal hφ) n m (Ne.symm hm)) hseg hmem

/-- The actual boundary sample has the index-parity sign even at a collapsed gap. -/
theorem sourceStandardRootOmittedProduct_boundary_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let P := sourceStandardRootOmittedProduct hp hp1 n φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)
    P.im = 0 ∧ 0 < (-1 : ℝ)^n.natAbs*P.re := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
  have hμ : (μ.re : ℂ) = μ := by
    apply Complex.ext
    · rfl
    · exact (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n).symm
  have hgap := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ n
  have hi := sourceStandardRootOmittedProduct_im_eq_zero_on_realGap_closedGap hp hp1 φ hφ n μ.re hgap
  have hs := sourceStandardRootOmittedProduct_signed_re_pos_on_realGap_closedGap hp hp1 φ hφ n μ.re hgap
  rw [hμ] at hi hs
  exact ⟨hi,hs⟩

/-- The squared omitted product differs from one by an ℓp sequence at either
actual boundary-root sequence of any real source. -/
theorem memlp_sourceStandardRootOmittedProduct_boundary_sq_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => (sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))^2-1) p := by
  have h := memlp_sampled_canonicalDeletedPeriodicProduct_sub_one hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ)
    (lp.memℓp (sourceBoundaryDisplacement hp hp1 b φ))
  simpa only [sourceStandardRootOmittedProduct_sq_eq_canonicalDeletedPeriodicProduct hp hp1 φ _ _
    (canonicalPeriodOneBoundaryRoot_mem_omittedDomain hp hp1 b φ hφ _)] using h

/-- The correct signed omitted-root product has its full ℓp normalization
error at every finite p>1, including endpoints and collapsed gaps. -/
theorem memlp_sourceStandardRootOmittedProduct_boundary_sub_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)-(-1 : ℂ)^n.natAbs) p := by
  apply (memlp_sourceStandardRootOmittedProduct_boundary_sq_sub_one hp hp1 b φ hφ).mono'
  intro n
  have hs := sourceStandardRootOmittedProduct_boundary_sign hp hp1 b φ hφ n
  have hsq : ((-1 : ℝ)^n.natAbs)^2 = 1 := by
    rw [← pow_mul,mul_comm n.natAbs 2,pow_mul]
    norm_num
  simpa only [Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one] using
    norm_sub_unit_sign_le_norm_sq_sub_one _ _ hs.1 hsq hs.2.le

/-- The inverse omitted product has the same signed ℓp normalization. -/
theorem memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => (sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹-(-1 : ℂ)^n.natAbs) p := by
  have h := memlp_inv_sub_inv_of_unit_reference hp hp1
    (fun n => sourceStandardRootOmittedProduct hp hp1 n φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))
    (fun n => (-1 : ℂ)^n.natAbs) (by intro n; simp)
    (memlp_sourceStandardRootOmittedProduct_boundary_sub_sign hp hp1 b φ hφ)
  simpa only [← inv_pow,inv_neg,inv_one] using h

/-- All actual inverse omitted products are bounded simultaneously over the
signed boundary sequence, including its finite central block. -/
theorem exists_bound_sourceStandardRootOmittedProduct_boundary_inv
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ‖(sourceStandardRootOmittedProduct hp hp1 n φ
        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹‖ ≤ C := by
  let e : Coeff p := ⟨_,memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_sign hp hp1 b φ hφ⟩
  refine ⟨‖e‖+1,by positivity,?_⟩
  intro n
  have h := norm_add_le (e n) ((-1 : ℂ)^n.natAbs)
  have he : e n+(-1 : ℂ)^n.natAbs =
      (sourceStandardRootOmittedProduct hp hp1 n φ
        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹ := sub_add_cancel _ _
  rw [he,show ‖(-1 : ℂ)^n.natAbs‖ = 1 by simp] at h
  exact h.trans (add_le_add (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' e n) le_rfl)

/-- The omitted product differs from its exact free cosine by an ℓp sequence. -/
theorem memlp_sourceStandardRootOmittedProduct_boundary_sub_free
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)-cos ((Real.pi : ℂ)*n)) p := by
  simp only [cos_freeCenter_eq_natAbs_sign]
  exact memlp_sourceStandardRootOmittedProduct_boundary_sub_sign hp hp1 b φ hφ

/-- The inverse normalization used in the closed-gap differential formula
has its exact signed free limit at every finite source exponent above one. -/
theorem memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_free
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => (sourceStandardRootOmittedProduct hp hp1 n φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹-cos ((Real.pi : ℂ)*n)) p := by
  simp only [cos_freeCenter_eq_natAbs_sign]
  exact memlp_sourceStandardRootOmittedProduct_boundary_inv_sub_sign hp hp1 b φ hφ

end NLS.ZakharovShabat
