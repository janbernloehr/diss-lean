import NLS.ZakharovShabat.SourceDiagonalActionRootSequence
import NLS.ZakharovShabat.SourceDiagonalActionRootAsymptotics
import NLS.SequenceSpaces.Compact

/-! # Compact variation of the physical action-root symbol

The existing analytic bounded root sequence has its free high-frequency
limit on every real diagonal. Its difference from the free symbol is a
compact multiplier, including all collapsed positive gaps.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceDiagonalActionRootSequence_apply
    (φ : realDiagonalSourceLocus 2) (n : ℤ) :
    sourceDiagonalActionRootSequence φ.val n = sourceDiagonalScaledActionRoot n φ.val := by
  obtain ⟨_,_,hφ,_,he⟩ := exists_local_sourceDiagonalActionRootSequence_analytic φ
  exact he φ.val hφ n

theorem tendsto_sourceDiagonalActionRootSequence_positive
    (φ : realDiagonalSourceLocus 2) :
    Tendsto (fun n : ℕ => sourceDiagonalActionRootSequence φ.val (n+1)) atTop
      (𝓝 ((Real.sqrt (1/(2*Real.pi)) : ℝ) : ℂ)) := by
  apply (tendsto_sourceDiagonalActionRoot_scaled_positive φ).congr
  intro n
  rw [sourceDiagonalActionRootSequence_apply,sourceDiagonalScaledActionRoot,
    if_pos (by omega : (0 : ℤ) < n+1)]

theorem isCompactOperator_sourceDiagonalActionRootSequence_sub_free
    (φ : realDiagonalSourceLocus 2) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsCompactOperator (Coeff.multiplierCLM (p := p)
      (sourceDiagonalActionRootSequence φ.val-sourceDiagonalActionRootSequence 0)) := by
  let φ₀ : realDiagonalSourceLocus 2 := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  have ht := (tendsto_sourceDiagonalActionRootSequence_positive φ).sub
    (tendsto_sourceDiagonalActionRootSequence_positive φ₀)
  rw [sub_self] at ht
  apply Coeff.isCompactOperator_multiplierCLM
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht ε hε
  refine ⟨Finset.Icc 1 (N+1 : ℤ),fun n hn => ?_⟩
  by_cases hpos : 0 < n
  · have hnN : N ≤ n.toNat-1 := by
      simp only [Finset.mem_Icc,not_and] at hn
      have h := hn (by omega)
      omega
    have he : ((n.toNat-1 : ℕ) : ℤ)+1 = n := by omega
    have h := hN (n.toNat-1) hnN
    simpa only [he,dist_zero_right,lp.coeFn_sub,Pi.sub_apply,φ₀] using h.le
  · rw [lp.coeFn_sub,Pi.sub_apply,sourceDiagonalActionRootSequence_apply φ n,
      sourceDiagonalActionRootSequence_apply φ₀ n]
    simp only [sourceDiagonalScaledActionRoot,if_neg hpos,sub_self,norm_zero]
    exact hε.le

end NLS.ZakharovShabat
