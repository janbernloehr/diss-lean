import NLS.ZakharovShabat.SourceDiagonalNormalizedLaurentAction
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Analytic square roots of the physical action ratio

The regularized ratio has positive real value on every physical diagonal.
Its principal square root therefore extends analytically through closed
actions, with the literal physical Laurent normalization retained.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceDiagonalActionRoot (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  Complex.sqrt (sourceDiagonalActionRatio hp hp1 n ψ)

theorem sourceDiagonalActionRoot_sq (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) :
    (sourceDiagonalActionRoot hp hp1 n ψ)^2 = sourceDiagonalActionRatio hp hp1 n ψ := by
  have h := Complex.cpow_nat_inv_pow (sourceDiagonalActionRatio hp hp1 n ψ) (Nat.succ_ne_zero 1)
  norm_num only [Nat.reduceAdd] at h
  simpa only [sourceDiagonalActionRoot,Complex.sqrt,one_div] using h

/-- The actual square root is real and strictly positive even at a closed gap. -/
theorem sourceDiagonalActionRoot_real_positive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : 0 < n) :
    (sourceDiagonalActionRoot hp hp1 n φ.val).im = 0 ∧
      0 < (sourceDiagonalActionRoot hp hp1 n φ.val).re := by
  obtain ⟨hi,hpρ⟩ := sourceDiagonalActionRatio_real_positive hp hp1 φ n hn
  have he : sourceDiagonalActionRatio hp hp1 n φ.val =
      ((sourceDiagonalActionRatio hp hp1 n φ.val).re : ℂ) :=
    Complex.ext rfl (by simpa only [ofReal_im] using hi)
  unfold sourceDiagonalActionRoot
  rw [he,Complex.sqrt_of_nonneg (by exact_mod_cast hpρ.le)]
  exact ⟨by simp,by simpa only [ofReal_re] using Real.sqrt_pos.mpr hpρ⟩

/-- Full complex Banach analyticity of the regularized ratio and its root,
with exact physical action factorization on a neighborhood of each diagonal. -/
theorem exists_local_sourceDiagonalActionRoot_analytic_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realDiagonalSourceLocus p) (n : ℤ) (hn : 0 < n) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (sourceDiagonalActionRatio hp hp1 n) U ∧
      AnalyticOnNhd ℂ (sourceDiagonalActionRoot hp hp1 n) U ∧
      ∀ ψ ∈ U, (1/2 : ℂ)*sourceDiagonalLaurentAction hp hp1 n 0 ψ =
        (sourceDiagonalActionRoot hp hp1 n ψ)^2*sourceComplexAction hp hp1 n ψ := by
  obtain ⟨A,hA,hφA,hAn,hfactor⟩ :=
    exists_local_sourceNormalizedDiagonalLaurentAction_analytic_factor hp hp1 φ n (ne_of_gt hn)
  obtain ⟨B,hB,hφB,hBn,hordinary⟩ :=
    exists_local_sourceNormalizedAction_analytic_factor hp hp1 φ.val φ.property.1 n
  have hne : sourceNormalizedActionComplexExtension hp hp1 n φ.val ≠ 0 :=
    sourceNormalizedActionComplexExtension_ne_zero_of_realType hp hp1 n φ.val φ.property.1
  have hρ : AnalyticAt ℂ (sourceDiagonalActionRatio hp hp1 n) φ.val :=
    (hAn φ.val hφA).div (analyticAt_const.mul (hBn φ.val hφB)) (mul_ne_zero (by norm_num) hne)
  have hpos := (sourceDiagonalActionRatio_real_positive hp hp1 φ n hn).2
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ.val,
      ψ ∈ A ∩ B ∧ sourceNormalizedActionComplexExtension hp hp1 n ψ ≠ 0 ∧
        0 < (sourceDiagonalActionRatio hp hp1 n ψ).re := by
    filter_upwards [(hA.inter hB).mem_nhds ⟨hφA,hφB⟩,
      (hBn φ.val hφB).continuousAt.eventually_ne hne,
      (continuous_re.continuousAt.comp hρ.continuousAt).eventually (lt_mem_nhds hpos)] with ψ hψ hψne hψpos
    exact ⟨hψ,hψne,hψpos⟩
  obtain ⟨U,hUsub,hU,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  have hρU : AnalyticOnNhd ℂ (sourceDiagonalActionRatio hp hp1 n) U := by
    intro ψ hψ
    obtain ⟨hψAB,hψne,_⟩ := hUsub hψ
    exact (hAn ψ hψAB.1).div (analyticAt_const.mul (hBn ψ hψAB.2)) (mul_ne_zero (by norm_num) hψne)
  refine ⟨U,hU,hφU,hρU,?_,?_⟩
  · intro ψ hψ
    have hs : sourceDiagonalActionRatio hp hp1 n ψ ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (hUsub hψ).2.2)
    exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)).comp (hρU ψ hψ)
  · intro ψ hψ
    obtain ⟨hψAB,hψne,_⟩ := hUsub hψ
    rw [sourceDiagonalActionRoot_sq,hfactor ψ hψAB.1,hordinary ψ hψAB.2,sourcePeriodicGapDisplacement_apply]
    unfold sourceDiagonalActionRatio
    field_simp

end NLS.ZakharovShabat
