import NLS.ZakharovShabat.SourcePsiMidpointDenominator
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity
import NLS.ZakharovShabat.UniformSmallCriticalDisplacements
import NLS.ZakharovShabat.SourcePsiCriticalRootComparison

/-! # Uniform critical-root separation on distant selected discs

A locally bounded critical displacement controls the finite omitted head.
Uniformly small critical tails control every other omitted index. Thus one
selected-index cutoff works for all omitted indices on a source neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual critical root is separated from every other distant selected disc. -/
theorem exists_local_sourceCritical_tail_lattice_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ ∃ K : ℕ,
      ∀ ψ ∈ V, ∀ k : ℤ, K ≤ k.natAbs → ∀ n : ℤ, n ≠ k →
        ∀ z ∈ closedBall ((Real.pi:ℂ)*k) (Real.pi/8),
          (Real.pi/2)*|((n-k : ℤ) : ℝ)| ≤ ‖sourceCriticalRoot hp hp1 ψ n-z‖ := by
  obtain ⟨N,_,U,hU,_,hφU,_,hsmall⟩ :=
    exists_uniform_small_canonicalCriticalDisplacements hp hp1 (periodOnePotential φ.val)
      (by positivity : 0 < Real.pi/8)
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp
    ((continuousAt_sourceCriticalDisplacement_of_realType hp hp1 φ.val φ.property).preimage_mem_nhds
      (ball_mem_nhds _ (by norm_num : (0:ℝ)<1)))
  let D := ‖sourceCriticalDisplacement hp hp1 φ.val‖+1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨L,hL⟩ := exists_nat_gt (2*(D+Real.pi/8)/Real.pi)
  have hLπ : 2*(D+Real.pi/8) ≤ Real.pi*(L : ℝ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp hL
    nlinarith
  let V := periodOnePotential ⁻¹' U ∩ ball φ.val η
  refine ⟨V,(hU.preimage (periodOnePotential (p := p)).continuous).inter isOpen_ball,
    ⟨hφU,mem_ball_self hη⟩,N+L,?_⟩
  intro ψ hψ k hk n hnk z hz
  have hnorm : ‖sourceCriticalDisplacement hp hp1 ψ‖ ≤ D := by
    have he : ‖sourceCriticalDisplacement hp hp1 ψ-sourceCriticalDisplacement hp hp1 φ.val‖ < 1 := by
      simpa only [mem_preimage,mem_ball,dist_eq_norm] using hηball hψ.2
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (sourceCriticalDisplacement hp hp1 ψ) (sourceCriticalDisplacement hp hp1 φ.val) 0
    simp only [sub_zero] at ht
    dsimp [D]
    linarith
  have hpoint : ‖sourceCriticalRoot hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans hnorm
    simpa only [sourceCriticalRoot,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] using h
  apply shifted_root_free_disc_distance_lower n k _ _ ?_ z hz
  by_cases hn : N < n.natAbs
  · have hs : ‖sourceCriticalRoot hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ Real.pi/8 := by
      exact (hsmall (periodOnePotential ψ) hψ.1 (periodOnePotential_mem ψ) n hn).le
    have hd : 1 ≤ |((n-k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnk)
    nlinarith [Real.pi_pos]
  · have htri : k.natAbs ≤ (k-n).natAbs+n.natAbs := by
      simpa only [sub_add_cancel] using Int.natAbs_add_le (k-n) n
    have hdist : L ≤ (n-k).natAbs := by
      have heq : (k-n).natAbs = (n-k).natAbs := by
        rw [← Int.natAbs_neg (n-k),neg_sub]
      rw [heq] at htri
      omega
    have habs : (L : ℝ) ≤ |((n-k : ℤ) : ℝ)| := by
      have hcast : (L : ℝ) ≤ ((n-k).natAbs : ℝ) := by exact_mod_cast hdist
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hcast
    nlinarith [mul_le_mul_of_nonneg_left habs Real.pi_pos.le]

end NLS.ZakharovShabat
