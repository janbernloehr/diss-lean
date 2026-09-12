import NLS.SequenceSpaces.Truncation
import NLS.SequenceSpaces.Convolution
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Finitely supported coefficients inside `ℓp`

The explicit dense linear inclusion provides the domain on which interval
extension estimates are proved before extending them by continuity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞}

/-- The canonical linear inclusion of finite coefficients into `ℓp`. -/
def ofFinsupp : (ℤ →₀ ℂ) →ₗ[ℂ] Coeff p where
  toFun a := ⟨fun n => a n, (memℓp_zero_iff.mpr a.hasFiniteSupport).of_exponent_ge bot_le⟩
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl

@[simp] theorem ofFinsupp_apply (a : ℤ →₀ ℂ) (n : ℤ) : ofFinsupp (p := p) a n = a n := rfl

/-- Finite coefficient inclusion has dense range at every finite Banach exponent. -/
theorem denseRange_ofFinsupp [Fact (1 ≤ p)] (hp : p ≠ ⊤) : DenseRange (ofFinsupp (p := p)) := by
  apply (dense_finiteSupport hp).mono
  rintro a ⟨s, hs⟩
  refine ⟨Finsupp.onFinset s a (fun n hn => by by_contra h; exact hn (hs n h)), ?_⟩
  exact lp.ext rfl

/-- Finite coefficient energy in the Hilbert sequence norm. -/
theorem norm_ofFinsupp_sq (a : ℤ →₀ ℂ) :
    ‖ofFinsupp (p := 2) a‖ ^ 2 = ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (ofFinsupp (p := 2) a)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, ofFinsupp_apply] at h
  rw [h]
  exact tsum_eq_sum fun n hn => by simp [Finsupp.notMem_support_iff.mp hn]

/-- Convolution with finite input is the finite translated sum of the second factor. -/
theorem convolution_ofFinsupp_apply [Fact (1 ≤ p)] (a : ℤ →₀ ℂ) (b : Coeff 1) (n : ℤ) :
    convolution (ofFinsupp (p := p) a) b n = a.sum (fun k z => z * b (n - k)) := by
  rw [convolution_apply]
  have he := (Equiv.subLeft n).tsum_eq (fun k : ℤ => a (n - k) * b k)
  simp only [Equiv.subLeft_apply, sub_sub_cancel] at he
  simp only [ofFinsupp_apply]
  rw [← he]
  exact tsum_eq_sum fun k hk => by simp [Finsupp.notMem_support_iff.mp hk]

end NLS.Coeff
