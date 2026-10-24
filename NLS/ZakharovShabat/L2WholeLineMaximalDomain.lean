import NLS.ZakharovShabat.L2WholeLineAdjointRegularity
import NLS.ZakharovShabat.L2WholeLineGreenIdentity
import NLS.ZakharovShabat.PhysicalOperatorSupport

/-! # The actual maximal whole-line differential domain

Compact-test integration by parts gives the converse to adjoint regularity.
Thus the actual Hilbert adjoint domain is exactly the L2 classes with a
locally absolutely continuous representative and an L2 physical image.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex Function
open scoped ContDiff
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- A locally AC representative with an L2 physical image satisfies the
actual weak operator equation. The boundary terms vanish by test support. -/
theorem wholeLineWeakEquation_of_AC_representative
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (f g : WholeLineL2) (F : ℝ → ℂ × ℂ)
    (he : wholeLineL2Pair f =ᵐ[volume] F)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b)
    (hp : physicalOperator (l2WholeLinePotential u) F =ᵐ[volume] wholeLineL2Pair g) :
    WholeLineWeakEquation u f g := by
  intro h
  let H : ℝ → ℂ × ℂ := fun t => (h t).ofLp
  have hH : ContDiff ℝ ∞ H :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℂ ℂ).contDiff.comp h.property.1
  have hHc : HasCompactSupport H := h.property.2.comp_left rfl
  let R : ℝ → ℂ := fun t => inner ℂ (wholeLineTestPhysicalExpression u h t) (f t) - inner ℂ (h t) (g t)
  have hi : Integrable (fun t => inner ℂ (wholeLineTestPhysicalExpression u h t) (f t)) volume := by
    apply (L2.integrable_inner (wholeLineTestOperator u h) f).congr
    filter_upwards [wholeLineTestOperator_ae u h] with t ht
    rw [ht]
  have hj : Integrable (fun t => inner ℂ (h t) (g t)) volume := by
    apply (L2.integrable_inner (wholeLineTestInclusion h) g).congr
    filter_upwards [wholeLineTestInclusion_ae h] with t ht
    rw [ht]
  have hR : Integrable R volume := hi.sub hj
  have hz (t : ℝ) (ht : t ∉ tsupport H) : R t = 0 := by
    have h0 : H t = 0 := image_eq_zero_of_notMem_tsupport ht
    have hh0 : h t = 0 := congrArg (WithLp.toLp 2) h0
    have ho := physicalOperator_eq_zero_of_notMem_tsupport (l2WholeLinePotential u) H ht
    change inner ℂ (WithLp.toLp 2 (physicalOperator (l2WholeLinePotential u) H t)) (f t) -
      inner ℂ (h t) (g t) = 0
    rw [ho,hh0]
    simp
  obtain ⟨C,hC,hbound⟩ := hHc.isBounded.exists_pos_norm_lt
  have hends : H (-C) = 0 ∧ H C = 0 := by
    constructor
    · apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hb := hbound (-C) ht
      simp only [norm_neg,Real.norm_eq_abs,abs_of_pos hC,lt_self_iff_false] at hb
    · apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hb := hbound C ht
      simp only [Real.norm_eq_abs,abs_of_pos hC,lt_self_iff_false] at hb
  have hsupp : support R ⊆ Ioc (-C) C := by
    intro t ht
    have hm : t ∈ tsupport H := by
      by_contra hn
      exact ht (hz t hn)
    have hb := hbound t hm
    rw [Real.norm_eq_abs] at hb
    exact ⟨(abs_lt.mp hb).1,(abs_lt.mp hb).2.le⟩
  let B : ℝ → ℂ := fun t => wholeLineBoundaryForm (H t) (F t)
  have hF1 := absolutelyContinuousOnInterval_clm (hac (-C) C) (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hF2 := absolutelyContinuousOnInterval_clm (hac (-C) C) (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hH1 : AbsolutelyContinuousOnInterval (fun t => (H t).1) (-C) C :=
    (hH.fst.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hH2 : AbsolutelyContinuousOnInterval (fun t => (H t).2) (-C) C :=
    (hH.snd.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hB : AbsolutelyContinuousOnInterval B (-C) C := by
    have h1 := ((absolutelyContinuousOnInterval_clm hH1 Complex.conjCLE.toContinuousLinearMap).const_smul (-I)).smul hF1
    have h2 := ((absolutelyContinuousOnInterval_clm hH2 Complex.conjCLE.toContinuousLinearMap).const_smul I).smul hF2
    simpa [B,wholeLineBoundaryForm,Pi.add_def,Pi.smul_def,smul_eq_mul] using! h1.add h2
  have hd : ∀ᵐ t : ℝ, t ∈ uIcc (-C) C → HasDerivAt B (R t) t := by
    filter_upwards [he,hp,ae_l2WholeLinePotential_real u hu,
      ae_differentiableAt_complex hF1,ae_differentiableAt_complex hF2] with t ht hpt hr hd1 hd2
    intro hmem
    have hder := (((hH.fst.differentiable (by norm_num) t).hasDerivAt.star.const_mul (-I)).mul
      (hd1 hmem).hasDerivAt).add
      (((hH.snd.differentiable (by norm_num) t).hasDerivAt.star.const_mul I).mul (hd2 hmem).hasDerivAt)
    convert! hder using 1
    change (f t).ofLp = F t at ht
    change physicalOperator (l2WholeLinePotential u) F t = (g t).ofLp at hpt
    simp only [R,wholeLineTestPhysicalExpression,WithLp.prod_inner_apply,RCLike.inner_apply']
    rw [ht,← hpt]
    simp only [physicalOperator,H]
    rw [hr]
    simp
    ring
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hB hR.intervalIntegrable hd
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp] at h
  have hzero : (∫ t : ℝ, R t) = 0 := by
    simpa only [B,wholeLineBoundaryForm,hends.1,hends.2,Prod.fst_zero,Prod.snd_zero,
      star_zero,mul_zero,zero_mul,add_zero,sub_zero] using h
  apply sub_eq_zero.mp
  rw [← integral_sub hi hj]
  exact hzero

/-- For real physical potentials the actual adjoint domain is exactly
the maximal locally AC differential domain, with its actual L2 image. -/
theorem mem_wholeLineMinimalOperator_adjoint_domain_iff_AC
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u)) (f : WholeLineL2) :
    f ∈ (wholeLineMinimalOperator u).adjoint.domain ↔
      ∃ (F : ℝ → ℂ × ℂ) (g : WholeLineL2), wholeLineL2Pair f =ᵐ[volume] F ∧
        (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
        physicalOperator (l2WholeLinePotential u) F =ᵐ[volume] wholeLineL2Pair g := by
  constructor
  · intro hf
    obtain ⟨F,he,hac,hp⟩ := wholeLineMinimalOperator_adjoint_exists_AC_representative u hu ⟨f,hf⟩
    exact ⟨F,_,he,hac,hp⟩
  · rintro ⟨F,g,he,hac,hp⟩
    exact (wholeLineWeakEquation_of_AC_representative u hu f g F he hac hp).mem_adjoint_domain

/-- The actual adjoint acts by the original differential expression on
every locally AC representative in its maximal domain. -/
theorem wholeLineMinimalOperator_adjoint_eq_of_AC_representative
    (u : IntervalPairL2) (hu : IsClassicalRealType (intervalL2Representative u))
    (f g : WholeLineL2) (F : ℝ → ℂ × ℂ)
    (he : wholeLineL2Pair f =ᵐ[volume] F)
    (hac : ∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b)
    (hp : physicalOperator (l2WholeLinePotential u) F =ᵐ[volume] wholeLineL2Pair g) :
    (wholeLineMinimalOperator u).adjoint
      ⟨f,(wholeLineWeakEquation_of_AC_representative u hu f g F he hac hp).mem_adjoint_domain⟩ = g :=
  (wholeLineWeakEquation_of_AC_representative u hu f g F he hac hp).adjoint_eq

end NLS.ZakharovShabat
