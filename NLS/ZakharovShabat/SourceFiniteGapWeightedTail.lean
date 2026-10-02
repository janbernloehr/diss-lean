import NLS.ZakharovShabat.SourceFiniteGapWeightedClosing
import NLS.ZakharovShabat.WeightedEvenLeadingTail
import NLS.SequenceSpaces.QuadraticTailBootstrap

/-! # Repeating the finite-gap tail recurrence in a spectral weight

Every available weighted realization of a finite-gap source satisfies
the same quadratic recurrence. Physical cutoffs are twice the source
cutoffs, and all constants use the actual weighted pair norm.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite-gap Fourier-tail recurrence in an arbitrary available
spectral weight. The left cutoff is four times the smaller tail cutoff. -/
theorem sourceFiniteGap_weighted_fourierTail_recurrence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ‖weightedPairFourierTail w.toWeight (2*(4*N)) ψ‖^p.toReal ≤
        offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
          (‖ψ‖^(2*p.toReal)/(4*N : ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^(2*p.toReal)) := by
  have heven (k : ℤ) : ψ.fst.val (2*k+1) = 0 ∧ ψ.snd.val (2*k+1) = 0 := by
    constructor
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.fst.val (2*k+1)) hψ
      simpa using h
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.snd.val (2*k+1)) hψ
      simpa using h
  obtain ⟨N₁,hN₁,hrem⟩ := sourceFiniteGap_weighted_remainder_eq_neg_leading hp hp1 φ hfinite w ψ hψ
  obtain ⟨N₂,_,U,_,_,hU,_,hbound⟩ := exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w ψ
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN
  have hb := (hbound ψ hU (4*N) (by omega)).2
  rw [hrem (4*N) (by omega),norm_neg,norm_weightedResonantLeadingTail_eq_of_even hp w ψ heven,
    show 4*N/2 = 2*N by omega] at hb
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb

/-- Geometric decay holds in every spectral weight already carried by
the finite-gap source, with the same admissible rates as at weight one. -/
theorem sourceFiniteGap_weighted_fourierTail_geometric
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val)
    (q : ℝ) (hq : (4 : ℝ)^(-min 1 (p.toReal-1)) < q) (hq1 : q < 1) :
    ∃ M : ℕ, 0 < M ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖weightedPairFourierTail w.toWeight (2*(4^k*M)) ψ‖^p.toReal ≤ C*q^k := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  obtain ⟨N₀,_,hrec⟩ := sourceFiniteGap_weighted_fourierTail_recurrence hp hp1 φ hfinite w ψ hψ
  let v (N : ℕ) := ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^p.toReal
  let B := offDiagonalSummationConstant p * ‖ψ‖^p.toReal
  let A := B*‖ψ‖^(2*p.toReal)
  have hB : 0 ≤ B := mul_nonneg (offDiagonalSummationConstant_nonneg p) (by positivity)
  have hcut : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hlim : Tendsto v atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => ‖weightedPairFourierTail w.toWeight (2*N) ψ‖) atTop (𝓝 0) := by
      simpa only [norm_zero,Function.comp_def] using ((tendsto_weightedPairFourierTail hp w.toWeight ψ).comp hcut).norm
    exact hn.rpow_const_nhds_zero (zero_lt_one.trans hpR)
  apply exists_four_adic_bound_of_quadratic_tail v A B (min 1 (p.toReal-1)) q N₀
    (fun N => by dsimp [v]; positivity) hlim (mul_nonneg hB (by positivity)) hB
    (lt_min (by norm_num) (by linarith)) hq hq1
  intro N hN
  have he : ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^(2*p.toReal) = (v N)^2 := by
    dsimp only [v]
    rw [mul_comm (2 : ℝ),Real.rpow_mul (norm_nonneg _),Real.rpow_two]
  have hb := hrec N hN
  rw [he] at hb
  convert hb using 1
  dsimp only [A,B,v]
  ring

end NLS.ZakharovShabat
