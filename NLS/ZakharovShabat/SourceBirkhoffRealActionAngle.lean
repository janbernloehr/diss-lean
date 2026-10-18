import NLS.ZakharovShabat.SourceSection14Original

/-! # Positive-root real action-angle coordinates

The real gap is nonnegative, so the normalized analytic amplitude equals
`√(2 I)`. This identifies the literal real coordinates at every source.
The formulas are independent of the admissible eta integral, and any angle
value is allowed at a collapsed gap because its action vanishes.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal ComplexOrder
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized complex amplitude is the nonnegative real square root of twice
the action, including at collapsed gaps. -/
theorem sourceRealActionAmplitude_eq_sqrt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceNormalizedActionRoot hp hp1 n φ.val *
      sourcePeriodicGapDisplacement hp hp1 φ.val n / (Real.sqrt 2 : ℂ) =
        (Real.sqrt (2 * (sourceIndexedAction hp hp1 n φ.val).re) : ℂ) := by
  let F := sourceNormalizedActionComplexExtension hp hp1 n φ.val
  let g := sourcePeriodicGapDisplacement hp hp1 φ.val n
  have hFi : F.im = 0 :=
    sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n φ.val φ.property
  have hFp : 0 < F.re :=
    sourceNormalizedActionComplexExtension_re_pos_of_realType hp hp1 n φ.val φ.property
  have hFe : F = (F.re : ℂ) := by
    apply Complex.ext <;> simp [hFi]
  have hξ : sourceNormalizedActionRoot hp hp1 n φ.val = (Real.sqrt (4*F.re) : ℂ) := by
    change Complex.sqrt (4*F) = _
    rw [hFe]
    rw [show (4:ℂ)*(F.re:ℂ) = ((4*F.re:ℝ):ℂ) by push_cast; rfl]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hFp.le))]
    rfl
  have he := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
    (isRealType_periodOnePotential φ.val φ.property) n
  have hgi : g.im = 0 := by
    simp only [g,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_im,he.1,he.2,sub_self]
  have hge : g = (g.re : ℂ) := by
    apply Complex.ext <;> simp [hgi]
  have hgp : 0 ≤ g.re := by
    simp only [g,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,sub_re,sub_nonneg]
    exact re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem φ.val)).2.1 n)
  obtain ⟨U,_,hφU,_,hf⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn hp hp1 φ.val φ.property n
  have hI : sourceIndexedAction hp hp1 n φ.val = g^2*F := by
    rw [sourceIndexedAction_eq_sourceRealAction hp hp1 n φ.val φ.property,
      ← sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
    exact hf φ.val hφU
  have hIr : (sourceIndexedAction hp hp1 n φ.val).re = g.re^2*F.re := by
    rw [hI,hge,hFe]
    simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re]
  have hrad : 0 ≤ Real.sqrt (4*F.re)*g.re/Real.sqrt 2 := by positivity
  have hsq : (Real.sqrt (4*F.re)*g.re/Real.sqrt 2)^2 =
      2*(sourceIndexedAction hp hp1 n φ.val).re := by
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 4*F.re),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),hIr]
    ring
  have hroot : Real.sqrt (4*F.re)*g.re/Real.sqrt 2 =
      Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re) := by
    rw [← hsq,Real.sqrt_sq hrad]
  rw [hξ]
  change (Real.sqrt (4*F.re):ℂ)*g/(Real.sqrt 2:ℂ) = _
  rw [hge,← Complex.ofReal_mul,← Complex.ofReal_div,hroot]

namespace SourceSection14OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The literal real action-angle formulas hold at every gap, open or collapsed. -/
theorem real_rectangular_formula (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    let r := Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)
    let θ := (sourceAngularOriginalTheta hp hp1 n s φ.val).re
    (sourceRealBirkhoffMap hp hp1 s φ).1 n = r*Real.cos θ ∧
      (sourceRealBirkhoffMap hp hp1 s φ).2 n = r*Real.sin θ := by
  dsimp only
  have hφV := D.complex.real_subset φ.property
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0
  · have hI := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n φ.val φ.property).2.2.mpr hg
    obtain ⟨hx,hy⟩ := D.complex.real_closed_gap_zero φ.val hφV φ.property n hg
    change ((sourceBirkhoffMap hp hp1 s φ.val).1 n).re = _ ∧
      ((sourceBirkhoffMap hp hp1 s φ.val).2 n).re = _
    simp [hx,hy,hI]
  · obtain ⟨hx,hy⟩ := D.rectangular_formula φ.val hφV n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
    have ha := sourceRealActionAmplitude_eq_sqrt hp hp1 φ n
    simp only [sourcePeriodicGapDisplacement_apply] at ha
    dsimp only at hx hy
    rw [ha] at hx hy
    have hθi := D.previous.theta_original_im_eq_zero φ.val (D.complex.source_subset hφV)
      φ.property n (by simpa only [sourcePeriodicGapDisplacement_apply] using hg)
    have hθ : sourceAngularOriginalTheta hp hp1 n s φ.val =
        ((sourceAngularOriginalTheta hp hp1 n s φ.val).re : ℂ) := by
      apply Complex.ext <;> simp [hθi]
    rw [hθ,← Complex.ofReal_cos] at hx
    rw [hθ,← Complex.ofReal_sin] at hy
    change ((sourceBirkhoffMap hp hp1 s φ.val).1 n).re = _ ∧
      ((sourceBirkhoffMap hp hp1 s φ.val).2 n).re = _
    constructor
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using congrArg Complex.re hx
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using congrArg Complex.re hy


/-- Any normalized eta integral gives the same real rectangular coordinates.
At a collapsed gap no condition is imposed on the chosen eta value. -/
theorem real_rectangular_formula_of_eta (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (v : ℂ)
    (hv : sourcePeriodicGapDisplacement hp hp1 φ.val n ≠ 0 →
      v ∈ sourceAngularOriginalEtaIntegralValues hp hp1 n s φ.val) :
    let r := Real.sqrt (2*(sourceIndexedAction hp hp1 n φ.val).re)
    let θ := (v+sourceAngularBetaCorrection hp hp1 n s φ.val).re
    (sourceRealBirkhoffMap hp hp1 s φ).1 n = r*Real.cos θ ∧
      (sourceRealBirkhoffMap hp hp1 s φ).2 n = r*Real.sin θ := by
  dsimp only
  have h := D.real_rectangular_formula φ n
  dsimp only at h
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0
  · have hI := (sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n φ.val φ.property).2.2.mpr hg
    simpa only [hI,Complex.zero_re,mul_zero,Real.sqrt_zero,zero_mul] using h
  · obtain ⟨k,hk⟩ := D.previous.theta_original_integral_choice_period φ.val
      (D.complex.source_subset (D.complex.real_subset φ.property)) n
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hg) (hv hg)
    have hkr := congrArg Complex.re hk
    simp only [Complex.sub_re,Complex.mul_re,Complex.intCast_re,Complex.intCast_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,sub_zero] at hkr
    have he : (v+sourceAngularBetaCorrection hp hp1 n s φ.val).re =
        (sourceAngularOriginalTheta hp hp1 n s φ.val).re+(k:ℝ)*(2*Real.pi) := by linarith
    rw [he,Real.cos_add_int_mul_two_pi,Real.sin_add_int_mul_two_pi]
    exact h

end SourceSection14OriginalData
end NLS.ZakharovShabat
