import NLS.ZakharovShabat.AppendixDSineProducts

/-! # The omitted-root interpolation products in Lemma E.1

The displayed formula must omit the diagonal index, as the source's residue
calculation does. The product means its symmetric cutoff limit. Its exact
value is a ratio of deleted entire products, with no assumed summability.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cardinal product, with the index n omitted from numerator and denominator. -/
def appendixEInterpolationKernel (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  appendixDDeletedProduct n (z,a)/appendixDDeletedProduct n (displacedRoots a n,a)

/-- Simplicity makes the deleted denominator nonzero, including at p=1. -/
theorem appendixEInterpolation_denominator_ne_zero (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n : ℤ) :
    appendixDDeletedProduct n (displacedRoots a n,a) ≠ 0 :=
  appendixDDeletedProduct_ne_zero_of_off_other hp n _ a
    (fun _ hk he => hk (ha he.symm))

/-- The literal omitted-index symmetric product converges to the cardinal kernel. -/
theorem tendsto_appendixEInterpolationKernel (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n : ℤ) (z : ℂ) :
    Tendsto (fun M : ℕ => ∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
      (displacedRoots a m-z)/(displacedRoots a m-displacedRoots a n))
      atTop (𝓝 (appendixEInterpolationKernel a n z)) := by
  have h := (tendsto_appendixDDeletedProduct hp n (z,a)).div
    (tendsto_appendixDDeletedProduct hp n (displacedRoots a n,a))
    (appendixEInterpolation_denominator_ne_zero hp a ha n)
  have he (M : ℕ) :
      (-(∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
        (displacedRoots a m-z)/singleSpectralDenominator m)) /
      (-(∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
        (displacedRoots a m-displacedRoots a n)/singleSpectralDenominator m)) =
      ∏ m ∈ (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n,
        (displacedRoots a m-z)/(displacedRoots a m-displacedRoots a n) := by
    rw [neg_div_neg_eq,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro m _
    field_simp
  exact h.congr' (Filter.Eventually.of_forall he)

/-- Restoring the omitted factor fixes the derivative sign at a simple root. -/
theorem deriv_appendixDProduct_at_root (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    deriv (fun z => appendixDProduct (z,a)) (displacedRoots a n) =
      -appendixDDeletedProduct n (displacedRoots a n,a)/singleSpectralDenominator n := by
  have hd : DifferentiableAt ℂ (fun z => appendixDDeletedProduct n (z,a)) (displacedRoots a n) :=
    (((analyticOnNhd_appendixDDeletedProduct hp n) _ (mem_univ _)).comp
      (analyticAt_id.prod analyticAt_const)).differentiableAt
  have h := (((hasDerivAt_const (displacedRoots a n) (displacedRoots a n)).sub
    (hasDerivAt_id (displacedRoots a n))).div_const (singleSpectralDenominator n)).mul hd.hasDerivAt
  have he : (fun z => appendixDProduct (z,a)) =
      (fun z => ((displacedRoots a n-z)/singleSpectralDenominator n)*appendixDDeletedProduct n (z,a)) := by
    funext z
    exact appendixDProduct_eq_deleted hp n (z,a)
  rw [he]
  simpa only [Pi.mul_def,Pi.sub_def,id_eq,sub_self,zero_div,zero_mul,add_zero,zero_sub,
    neg_div,neg_mul,one_mul,div_mul_eq_mul_div] using h.deriv

/-- The source product has nonzero derivative at every root of a simple sequence. -/
theorem deriv_appendixDProduct_ne_zero (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n : ℤ) :
    deriv (fun z => appendixDProduct (z,a)) (displacedRoots a n) ≠ 0 := by
  rw [deriv_appendixDProduct_at_root hp a n]
  exact div_ne_zero (neg_ne_zero.mpr (appendixEInterpolation_denominator_ne_zero hp a ha n))
    (singleSpectralDenominator_ne_zero n)

/-- The derivative-normalized residue coefficient equals the printed cardinal product. -/
theorem appendixEInterpolationKernel_eq_deriv (hp : p ≠ ⊤) (a : Coeff p)
    (n : ℤ) (z : ℂ) (hz : z ≠ displacedRoots a n) :
    appendixEInterpolationKernel a n z =
      appendixDProduct (z,a)/deriv (fun w => appendixDProduct (w,a)) (displacedRoots a n)/
        (z-displacedRoots a n) := by
  rw [appendixDProduct_eq_deleted hp n,deriv_appendixDProduct_at_root hp a n,
    appendixEInterpolationKernel]
  field_simp [sub_ne_zero.mpr hz]
  ring

/-- The kernel takes value one at its own root and zero at every other root. -/
theorem appendixEInterpolationKernel_root (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n k : ℤ) :
    appendixEInterpolationKernel a n (displacedRoots a k) = if k = n then 1 else 0 := by
  classical
  by_cases h : k = n
  · subst k
    simp [appendixEInterpolationKernel,appendixEInterpolation_denominator_ne_zero hp a ha n]
  · simp [appendixEInterpolationKernel,appendixDDeletedProduct_root hp n k h a,h]

omit [Fact (1 ≤ p)] in
/-- Including the printed diagonal factor gives zero under Lean's totalized division.
The omitted-index correction is therefore essential, rather than a normalization convention. -/
theorem appendixE_all_index_cutoff_eq_zero (a : Coeff p) (n : ℤ) (z : ℂ)
    (M : ℕ) (hM : n.natAbs ≤ M) :
    (∏ m ∈ Finset.Icc (-(M:ℤ)) (M:ℤ),
      (displacedRoots a m-z)/(displacedRoots a m-displacedRoots a n)) = 0 := by
  apply Finset.prod_eq_zero (i := n)
  · simp only [Finset.mem_Icc]
    omega
  · simp

end NLS.ZakharovShabat
