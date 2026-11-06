import NLS.Articles.KdVConvexity.ArnoldH1Regularity
import NLS.Articles.KdVConvexity.PhysicalHilbertActions
import NLS.Articles.KdVConvexity.GlobalArnoldSurjectivity
import NLS.KdV.HillNativeH1Recovery

/-! # The whole original positive cubic-weighted action domain has actual H1 sources -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem original_cubic_weight_summability_iff (f : ℕ+ → ℂ) :
    Summable (fun n : ℕ+ => (1+(n : ℝ))^3*‖f n‖) ↔
      Summable (fun n : ℕ+ => (n : ℝ)^3*‖f n‖) := by
  constructor
  · intro hs
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hs
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) 3) (norm_nonneg _)
  · intro hs
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) (hs.mul_left 8)
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hc : (1+(n : ℝ))^3 ≤ 8*(n : ℝ)^3 := by
      calc
        _ ≤ (2*(n : ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ = _ := by ring
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f n))

/-- The original real positive ell^(3,1) action domain, as a subset of the
original positive-index ell2 space. No strictly positive coordinates or
finite-support condition is imposed. -/
def originalPositiveActionDomain : Set ActionSpace :=
  {a | a ∈ positiveQuadrant ∧ Summable (fun n : ℕ+ => (1+(n : ℝ))^3*‖a n‖)}

theorem exists_H1_source_of_original_positive_actions
    (a : ActionSpace) (ha : a ∈ originalPositiveActionDomain) :
    ∃ p : RealHillWeightedPotential hillH1SpectralWeight,
      p.val.val 0=0 ∧ physicalHilbertActions hillH1SpectralWeight p=a := by
  obtain ⟨q,hr,hm,hact⟩ := exists_source_of_positive_ell2_actions a ha.1
  have hq : Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*q.val k) 2 :=
    source_H1_of_cubic_weighted_Arnold_summable q hr (by
      simpa only [hact] using (original_cubic_weight_summability_iff (fun n => a n)).mp ha.2)
  obtain ⟨p,hp⟩ := exists_native_H1_of_rough_H1 q hr hq
  have hraw (k : ℤ) : p.val.val k=q.val k := by
    have he := congrArg (fun u : PeriodOneHminusOne => u.val k) hp
    simpa only [hillWeightedNativeHminusSource_apply] using he
  refine ⟨p,(hraw 0).trans hm,?_⟩
  ext n
  have hh := physicalHilbertActions_intrinsic_Arnold hillH1SpectralWeight p n
  have he : physicalHilbertActions hillH1SpectralWeight p n=hillHminusRealGapContourMoment q hr n 0 := by
    simpa only [hp] using! hh
  exact he.trans (hact n)

theorem physicalHilbertActions_H1_mem_original_domain
    (p : RealHillWeightedPotential hillH1SpectralWeight) :
    physicalHilbertActions hillH1SpectralWeight p ∈ originalPositiveActionDomain := by
  refine ⟨physicalHilbertActions_mem_positiveQuadrant _ p,?_⟩
  apply (original_cubic_weight_summability_iff (fun n => physicalHilbertActions hillH1SpectralWeight p n)).mpr
  have hs := summable_norm_linear_physicalHilbertActions_H1 p
  have hc : (8*Real.pi^3 : ℝ) ≠ 0 := by positivity
  have he (n : ℕ+) :
      ‖((8*(n : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*physicalHilbertActions hillH1SpectralWeight p n‖/(8*Real.pi^3)=
        (n : ℝ)^3*‖physicalHilbertActions hillH1SpectralWeight p n‖ := by
    rw [norm_mul,norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    field_simp
  exact (hs.div_const (8*Real.pi^3)).congr he

end NLS.Articles.KdVConvexity
