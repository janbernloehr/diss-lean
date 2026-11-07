import NLS.SequenceSpaces.WeightedReciprocalKernel
import NLS.SequenceSpaces.Compact
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-! Every strictly stronger Sobolev weight embeds compactly in the
original weighted coefficient norm, for every Banach exponent. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS

theorem analyticOnNhd_postcompose_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : F →L[ℂ] G) (f : E → F) (U : Set E) (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (fun x => J (f x)) U :=
  fun a ha => (J.analyticAt _).comp (hf a ha)

theorem isCompactOperator_fderiv_compact_clm
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : F →L[ℂ] G) (hJ : IsCompactOperator J) (f : E → F) (a : E)
    (hf : DifferentiableAt ℂ f a) : IsCompactOperator (fderiv ℂ (fun x => J (f x)) a) := by
  change IsCompactOperator (fderiv ℂ (J ∘ f) a)
  rw [(J.hasFDerivAt.comp a hf.hasFDerivAt).fderiv]
  exact hJ.comp_clm (fderiv ℂ f a)

namespace Coeff

theorem isCompactOperator_multiplier_of_finite_symbol
    {p q : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤q)] (hq : q≠⊤) (a : Coeff q) :
    IsCompactOperator (multiplierCLM (p := p) (exponentInclusion (show q≤⊤ from le_top) a)) := by
  apply isCompactOperator_multiplierCLM
  intro ε hε
  obtain ⟨S,hS⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hq a) ε hε
  refine ⟨S,?_⟩
  intro n hn
  have H := hS S le_rfl
  rw [dist_eq_norm] at H
  have hrow := lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1≤q)))
    (truncate S a-a) n
  simpa only [exponentInclusion_apply,lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hn,
    zero_sub,norm_neg] using hrow.trans H.le

end Coeff
namespace Weight

theorem exists_finite_exponent_negative_sobolev (d : ℝ) (hd : 0<d) :
    ∃ q : ℝ≥0∞, ∃ _ : Fact (1≤q), q≠⊤ ∧ Memℓp (fun n : ℤ => (sobolev (-d) n : ℂ)) q := by
  let q := ENNReal.ofReal (2/d+1)
  have hqR : 0<2/d+1 := by positivity
  have hq : 1≤q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ)≤2/d+1 by linarith [div_pos (by norm_num : (0 : ℝ)<2) hd])
  have ht : q.toReal=2/d+1 := ENNReal.toReal_ofReal hqR.le
  refine ⟨q,⟨hq⟩,ENNReal.ofReal_ne_top,?_⟩
  apply memlp_negative_sobolev (by rw [ht];exact hqR) d
  rw [ht]
  have he : d*(2/d+1)=2+d := by field_simp
  rw [he]
  linarith

end Weight
namespace WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem isCompactOperator_sobolevInclusion_strict {s t : ℝ} (h : s<t) :
    IsCompactOperator (sobolevInclusion (p := p) h.le) := by
  obtain ⟨q,instQ,hq,hm⟩ := Weight.exists_finite_exponent_negative_sobolev (t-s) (sub_pos.mpr h)
  let : Fact (1≤q) := instQ
  let a : Coeff q := ⟨fun n => (Weight.sobolev (-(t-s)) n : ℂ),hm⟩
  let m : Coeff ⊤ := Coeff.exponentInclusion (show q≤⊤ from le_top) a
  let J := (weightIsometry (Weight.sobolev t) p).toContinuousLinearEquiv.toContinuousLinearMap
  let K := (weightIsometry (Weight.sobolev s) p).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc : IsCompactOperator (Coeff.multiplierCLM (p := p) m) :=
    Coeff.isCompactOperator_multiplier_of_finite_symbol hq a
  have he : sobolevInclusion (p := p) h.le=K.comp ((Coeff.multiplierCLM m).comp J) := by
    apply ContinuousLinearMap.ext
    intro v
    apply Subtype.ext
    funext n
    rw [sobolevInclusion_apply]
    change v.val n=((Weight.sobolev (-(t-s)) n : ℂ)*((Weight.sobolev t n : ℂ)*v.val n))/(Weight.sobolev s n : ℂ)
    rw [←mul_assoc,←Complex.ofReal_mul,←Weight.sobolev_add,show -(t-s)+t=s by ring]
    exact (mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)).symm
  rw [he]
  exact (hc.comp_clm J).clm_comp K

end WeightedCoeff
end NLS
