import NLS.ZakharovShabat.SourceGapActionLowerBound
import NLS.ZakharovShabat.SourceOpenGapDensity
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic

/-! # Sharp real lower bounds for the normalized action and root

The actual normalized action is at least one quarter on the whole real
source space, including collapsed gaps. Consequently the normalized root
is at least one, its reciprocal has norm at most one, and its deviation
from one is controlled by half the normalized-action deviation.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace NLS.ZakharovShabat
open scoped ComplexOrder
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized actual action is at least its free value, including at collapsed gaps. -/
theorem sourceNormalizedActionComplexExtension_re_ge_quarter (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (1/4:ℝ) ≤ (sourceNormalizedActionComplexExtension hp hp1 n φ.val).re := by
  have hc : Continuous (fun ψ : realTypeSourceSubmodule p =>
      (sourceNormalizedActionComplexExtension hp hp1 n ψ.val).re) := by
    apply continuous_iff_continuousAt.mpr
    intro ψ
    exact Complex.continuous_re.continuousAt.comp
      ((differentiableAt_sourceNormalizedActionComplexExtension_of_realType
        hp hp1 ψ.val ψ.property n).continuousAt.comp continuous_subtype_val.continuousAt)
  have hclosed := isClosed_le (continuous_const : Continuous (fun _ : realTypeSourceSubmodule p => (1/4:ℝ))) hc
  have hsub : sourceOpenGapRealLocus hp hp1 n ⊆
      {ψ : realTypeSourceSubmodule p | (1/4:ℝ) ≤ (sourceNormalizedActionComplexExtension hp hp1 n ψ.val).re} := by
    intro ψ hψ
    have hg : sourcePeriodicGapDisplacement hp hp1 ψ.val n ≠ 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply, sourceOpenGapRealLocus, Set.mem_ofPred_eq] using hψ
    obtain ⟨U,_,hψU,_,hf⟩ := exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 ψ.val ψ.property n
    let ρ := sourceNormalizedActionComplexExtension hp hp1 n ψ.val
    have hi : ρ.im = 0 := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n ψ.val ψ.property
    have hpρ : 0 ≤ ρ.re := (sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n ψ.val ψ.property).le
    have he : ρ = (ρ.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
    have hn : ‖ρ‖ = ρ.re := by rw [he,Complex.norm_real,Real.norm_of_nonneg hpρ]; rfl
    have h := source_gap_norm_sq_le_four_action hp hp1 ψ n
    rw [hf ψ.val hψU,norm_mul,norm_pow] at h
    change _ ≤ 4*(_*‖ρ‖) at h
    rw [hn] at h
    have hpos := pow_pos (norm_pos_iff.mpr hg) 2
    change (1/4:ℝ) ≤ ρ.re
    nlinarith
  exact closure_minimal hsub hclosed (dense_sourceOpenGapRealLocus hp hp1 n φ)

/-- The actual normalized root is the nonnegative real square root on all real sources. -/
theorem sourceNormalizedActionRoot_eq_real_sqrt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceNormalizedActionRoot hp hp1 n φ.val =
      (Real.sqrt (4*(sourceNormalizedActionComplexExtension hp hp1 n φ.val).re):ℂ) := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n φ.val
  have hi := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ.val φ.property
  have hpF := sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n φ.val φ.property
  have he : F = (F.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
  change Complex.sqrt (4*F) = _
  rw [he,show (4:ℂ)*(F.re:ℂ) = ((4*F.re:ℝ):ℂ) by push_cast; rfl]
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hpF.le))]
  rfl

/-- The actual normalized root has real part at least one, with no gap-opening premise. -/
theorem sourceNormalizedActionRoot_re_ge_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    1 ≤ (sourceNormalizedActionRoot hp hp1 n φ.val).re := by
  rw [sourceNormalizedActionRoot_eq_real_sqrt,Complex.ofReal_re]
  have h := sourceNormalizedActionComplexExtension_re_ge_quarter hp hp1 φ n
  have hn : 0 ≤ 4*(sourceNormalizedActionComplexExtension hp hp1 n φ.val).re := by linarith
  nlinarith [Real.sq_sqrt hn,Real.sqrt_nonneg (4*(sourceNormalizedActionComplexExtension hp hp1 n φ.val).re)]

/-- Real normalization improves the scalar root-error bound by a factor two. -/
theorem sourceNormalizedActionRoot_deviation_le_half (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ‖sourceNormalizedActionRoot hp hp1 n φ.val-1‖ ≤
      ‖4*sourceNormalizedActionComplexExtension hp hp1 n φ.val-1‖/2 := by
  let ρ := sourceNormalizedActionComplexExtension hp hp1 n φ.val
  have hi : ρ.im = 0 := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ.val φ.property
  have he : ρ = (ρ.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
  have hρ : (1/4:ℝ) ≤ ρ.re := sourceNormalizedActionComplexExtension_re_ge_quarter hp hp1 φ n
  have hr : 1 ≤ Real.sqrt (4*ρ.re) := by
    simpa only [sourceNormalizedActionRoot_eq_real_sqrt,Complex.ofReal_re] using sourceNormalizedActionRoot_re_ge_one hp hp1 φ n
  rw [sourceNormalizedActionRoot_eq_real_sqrt]
  change ‖(Real.sqrt (4*ρ.re):ℂ)-1‖ ≤ ‖4*ρ-1‖/2
  rw [he]
  simp only [Complex.ofReal_re]
  have hc : (4:ℂ)*(ρ.re:ℂ)-1 = ((4*ρ.re-1:ℝ):ℂ) := by push_cast; rfl
  have hl : (Real.sqrt (4*ρ.re):ℂ)-1 = ((Real.sqrt (4*ρ.re)-1:ℝ):ℂ) := by push_cast; rfl
  rw [hc,hl,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr hr),Real.norm_of_nonneg (by linarith : 0 ≤ 4*ρ.re-1)]
  nlinarith [sq_nonneg (Real.sqrt (4*ρ.re)-1),Real.sq_sqrt (by linarith : 0 ≤ 4*ρ.re)]

/-- The reciprocal normalized root is bounded by one on the entire real source space. -/
theorem sourceNormalizedActionRoot_inverse_norm_le_one (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ‖(sourceNormalizedActionRoot hp hp1 n φ.val)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  exact inv_le_one_of_one_le₀
    ((sourceNormalizedActionRoot_re_ge_one hp hp1 φ n).trans (Complex.re_le_norm _))

end NLS.ZakharovShabat
