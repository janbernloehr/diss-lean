import NLS.ZakharovShabat.SourceHamiltonianOpenActionDerivative
import NLS.ZakharovShabat.SourceFiniteGapClosedFrequency

/-! # Hamiltonian action derivatives at closed finite-gap actions

A nonzero gap-opening sequence preserves finite gap support and tends to
the original source. Continuity of the analytic action derivative and of
the actual moment sum removes the open-action restriction.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4:ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W W₀ B X : Set (CoeffPair 4)} {t : (k : ℤ) → CoeffPair 4 → DeletedCoeff 4 k}
variable {Y P : Set (CoeffPair 2)} {u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Every finite-gap action, including closed gaps and the zero source,
has the physical frequency as its Hamiltonian coordinate derivative. -/
theorem sourceHamiltonian_fderiv_finiteGap_hilbert
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B X t)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) P u)
    (H : Coeff 2 → ℂ) (V : Set (Coeff 2)) (hH : AnalyticOnNhd ℂ H V)
    (hcenter : ∀ ψ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val ∈ V)
    (hrec : ∀ ψ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ.val) = A.renormalizedHamiltonian ψ.val)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    fderiv ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) t
      (realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ).val) (lp.single 2 n 1) =
      C.renormalizedFrequency n φ.val := by
  by_cases hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n = 0
  · obtain ⟨W₂,B₂,X₂,s₂,D₂⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
    let r := fun k : ℕ => 1/((k:ℝ)+1)
    let γ := fun k : ℕ => D₂.hilbertGapOpening φ n (r k)
    let ψ := realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) φ
    let χ := fun k => realTypeSourceExponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4) (γ k)
    let I := fun ξ : CoeffPair 4 => sourceActionSequence (q := 2) (by simp) (by norm_num) t ξ
    have hlim : Tendsto (fun k => (γ k).val) atTop (𝓝 φ.val) := D₂.tendsto_hilbertGapOpening_sequence φ n
    have hχ : Tendsto (fun k => (χ k).val) atTop (𝓝 ψ.val) :=
      (CoeffPair.exponentInclusion (by norm_num : (2:ℝ≥0∞) ≤ 4)).continuous.continuousAt.tendsto.comp hlim
    have hi : Tendsto (fun k => I (χ k).val) atTop (𝓝 (I ψ.val)) :=
      (D.actionSequence_analytic ψ.val (D.real_subset ψ.property)).continuousAt.tendsto.comp hχ
    have hd : Tendsto (fun k => (fderiv ℂ H (I (χ k).val)) (lp.single 2 n 1)) atTop
        (𝓝 ((fderiv ℂ H (I ψ.val)) (lp.single 2 n 1))) :=
      ((hH.fderiv (I ψ.val) (hcenter ψ)).continuousAt.clm_apply continuousAt_const).tendsto.comp hi
    have hm : Tendsto (fun k => ∑' j : ℤ, C.moment n j 2 (γ k).val) atTop
        (𝓝 (∑' j : ℤ, C.moment n j 2 φ.val)) := by
      apply C.positive_moment_sum_tendsto_of_eventually_fixed_gap_support
        (fun k => (γ k).val) φ.val (C.realType_subset_domain φ.property) hlim (insert n hf.toFinset)
      exact Eventually.of_forall fun k => ⟨C.realType_subset_domain (γ k).property,
        D₂.hilbertGapOpening_gap_support φ hf n (r k)⟩
    have hfreq : Tendsto (fun k => C.renormalizedFrequency n (γ k).val) atTop
        (𝓝 (C.renormalizedFrequency n φ.val)) := hm.const_mul (-(4/(2*Real.pi):ℂ))
    have he : (fun k => (fderiv ℂ H (I (χ k).val)) (lp.single 2 n 1)) =
        fun k => C.renormalizedFrequency n (γ k).val := by
      funext k
      exact sourceHamiltonian_fderiv_open_finiteGap A D C hs H hrec (γ k)
        (D₂.hilbertGapOpening_mem_finiteGap φ hf n (r k)) n
        (D₂.hilbertGapOpening_gap_ne_zero φ n hn (r k) (by dsimp [r]; positivity))
        (hH _ (hcenter (χ k))).differentiableAt
    rw [he] at hd
    exact tendsto_nhds_unique hd hfreq
  · exact sourceHamiltonian_fderiv_open_finiteGap A D C hs H hrec φ hf n hn
      (hH _ (hcenter _)).differentiableAt

end NLS.ZakharovShabat
