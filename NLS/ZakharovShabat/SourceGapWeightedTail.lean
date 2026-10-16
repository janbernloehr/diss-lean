import NLS.ZakharovShabat.SourceWeightedCenterGapBound
import NLS.ZakharovShabat.SourceBirkhoffWeightedMembership
import NLS.ZakharovShabat.WeightedResonantCenterClosingTail
import NLS.ZakharovShabat.WeightedEvenLeadingTail
import NLS.SequenceSpaces.ForcedQuadraticTailSummability

/-! # Fourier tails with actual spectral gap forcing

The weighted center bound and the actual quadratic remainder estimate give
an explicit recurrence at quadrupled cutoffs for every real source and
any weighted realization it already has. The gap term is retained.
Geometrically weighted summability then transfers from gap tails to
Fourier tails below the algebraic remainder rate, without losing that weight.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The p-power tail of the actual source gaps, weighted at the physical frequency 2n. -/
def sourceWeightedGapPowerTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : CoeffPair p) (M : ℕ) : ℝ :=
  ∑' n : ℤ, if M ≤ n.natAbs then
    ‖(w (2*n) : ℂ)*sourcePeriodicGapDisplacement hp hp1 φ n‖^p.toReal else 0

/-- The actual weighted gap power tail is nonnegative at every cutoff. -/
theorem sourceWeightedGapPowerTail_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : CoeffPair p) (M : ℕ) :
    0 ≤ sourceWeightedGapPowerTail hp hp1 w φ M := by
  apply tsum_nonneg
  intro n
  split_ifs <;> positivity

/-- The joint center-closing energy is bounded by the actual gap power tail. -/
theorem exists_sourceWeightedResonantCenterClosingTail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      ‖weightedResonantCenterClosingTail hp w ψ M‖^p.toReal ≤
        (2*(2:ℝ)^p.toReal)*sourceWeightedGapPowerTail hp hp1 w φ.val M := by
  have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hbase : weightedBaseToPair w ψ = periodOnePotential φ.val := by
    rw [← unitBaseEquiv_forgetPairWeight,hψ,unitBaseEquiv_eq,
      weightedBaseToPair_sourceWeightedPeriodOne]
  have hgs := (sourceWeightedGap_mem hp hp1 w φ.val ψ hbase).summable hp0
  obtain ⟨N₁,hN₁,hgap⟩ := exists_sourceWeightedResonantCenter_gap_bound hp hp1 φ w ψ hψ
  obtain ⟨N₂,_,U,_,_,hU,_,hrem⟩ := exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w ψ
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro M hM
  let Q := fun n : ℤ => if M ≤ n.natAbs then
    ‖(w (2*n) : ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖^p.toReal else 0
  have hQ (n : ℤ) : 0 ≤ Q n := by dsimp [Q]; split_ifs <;> positivity
  have hQs : Summable Q := hgs.of_nonneg_of_le hQ (by
    intro n
    dsimp [Q]
    split_ifs
    · rfl
    · positivity)
  let t := weightedResonantCenterClosingTail hp w ψ M
  have hcoord := weightedResonantCenterClosingTail_apply_of_mem hp w ψ M
    (hrem ψ hU M (by omega)).1
  have hpoint (n : ℤ) : ‖t.fst n‖^p.toReal + ‖t.snd n‖^p.toReal ≤ (2*(2:ℝ)^p.toReal)*Q n := by
    change ‖(weightedResonantCenterClosingTail hp w ψ M).fst n‖^p.toReal +
      ‖(weightedResonantCenterClosingTail hp w ψ M).snd n‖^p.toReal ≤ _
    rw [(hcoord n).1,(hcoord n).2]
    by_cases hn : M ≤ n.natAbs
    · simp only [if_pos hn,Q]
      have hb := hgap n (by omega)
      have hpow (b : ℂ) (hb : ‖b‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖) :
          ‖(w (2*n):ℂ)*b‖^p.toReal ≤
            (2:ℝ)^p.toReal*‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖^p.toReal := by
        have hmul : ‖(w (2*n):ℂ)*b‖ ≤ 2*‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖ := by
          simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),
            mul_left_comm (w (2*n)) 2] using mul_le_mul_of_nonneg_left hb (w.positive (2*n)).le
        have h := Real.rpow_le_rpow (norm_nonneg _) hmul (ENNReal.toReal_nonneg (a := p))
        rwa [Real.mul_rpow (by norm_num) (norm_nonneg _)] at h
      have hm := hpow _ hb.2
      have hp := hpow _ hb.1
      nlinarith
    · simp only [if_neg hn,Q,norm_zero,Real.zero_rpow hp0.ne',mul_zero,add_zero,le_refl]
  rw [CoeffPair.norm_rpow_eq_tsum hp]
  calc
    _ ≤ ∑' n, (2*(2:ℝ)^p.toReal)*Q n :=
      (t.fst.property.summable hp0 |>.add (t.snd.property.summable hp0)).tsum_le_tsum hpoint
        (hQs.mul_left _)
    _ = _ := tsum_mul_left

private theorem add_rpow_le_two_rpow (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (a+b)^r ≤ (2:ℝ)^r*(a^r+b^r) := by
  have hmax : a+b ≤ 2*max a b := by have h₁ := le_max_left a b; have h₂ := le_max_right a b; linarith
  calc
    _ ≤ (2*max a b)^r := Real.rpow_le_rpow (add_nonneg ha hb) hmax hr
    _ = (2:ℝ)^r*(max a b)^r := Real.mul_rpow (by norm_num) (ha.trans (le_max_left _ _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

/-- Quantitative Fourier-tail recurrence including nonzero spectral gaps.
Physical Fourier cutoffs are twice the source gap cutoffs. -/
theorem source_weighted_fourierTail_forced_recurrence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ‖weightedPairFourierTail w.toWeight (2*(4*N)) ψ‖^p.toReal ≤
        (2:ℝ)^p.toReal *
          ((2*(2:ℝ)^p.toReal)*sourceWeightedGapPowerTail hp hp1 w φ.val (4*N) +
            offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
              (‖ψ‖^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^(2*p.toReal))) := by
  have heven (k : ℤ) : ψ.fst.val (2*k+1) = 0 ∧ ψ.snd.val (2*k+1) = 0 := by
    constructor
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.fst.val (2*k+1)) hψ
      simpa using h
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.snd.val (2*k+1)) hψ
      simpa using h
  obtain ⟨N₁,hN₁,hclosing⟩ := exists_sourceWeightedResonantCenterClosingTail_bound hp hp1 φ w ψ hψ
  obtain ⟨N₂,_,U,_,_,hU,_,hrem⟩ := exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w ψ
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN
  have hlead : ‖weightedResonantLeadingTailCLM hp w (4*N) ψ‖ ≤
      ‖weightedResonantCenterClosingTail hp w ψ (4*N)‖ +
        ‖weightedResonantCenterRemainder hp w ψ (4*N)‖ := by
    have he : weightedResonantLeadingTailCLM hp w (4*N) ψ =
        weightedResonantCenterClosingTail hp w ψ (4*N)-weightedResonantCenterRemainder hp w ψ (4*N) := by
      simp only [weightedResonantCenterClosingTail,add_sub_cancel_right]
    rw [he]
    exact norm_sub_le _ _
  have hpw := (Real.rpow_le_rpow (norm_nonneg _) hlead (ENNReal.toReal_nonneg (a := p))).trans
    (add_rpow_le_two_rpow _ _ _ (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg)
  have hbound := hpw.trans (mul_le_mul_of_nonneg_left
    (add_le_add (hclosing (4*N) (by omega)) (hrem ψ hU (4*N) (by omega)).2) (by positivity))
  change ‖weightedResonantLeadingTail w ψ (4*N)‖^p.toReal ≤ _ at hbound
  rw [norm_weightedResonantLeadingTail_eq_of_even hp w ψ heven,
    show 4*N/2 = 2*N by omega] at hbound
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hbound

/-- Every summable geometric weight on the actual gap tails transfers to the
Fourier tails, provided it is below the algebraic remainder rate. -/
theorem source_weighted_fourierTail_summable_of_gap_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ r : ℝ, 0 < r →
      r*(4:ℝ)^(-min 1 (p.toReal-1)) < 1 →
      Summable (fun k => r^k*sourceWeightedGapPowerTail hp hp1 w φ.val (4*(4^k*M))) →
      Summable (fun k => r^k*‖weightedPairFourierTail w.toWeight (2*(4^k*M)) ψ‖^p.toReal) := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  obtain ⟨M,hM,hrec⟩ := source_weighted_fourierTail_forced_recurrence hp hp1 φ w ψ hψ
  refine ⟨M,hM,?_⟩
  intro r hr hrα hgs
  let v := fun N => ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^p.toReal
  let C := (2:ℝ)^p.toReal
  let g := fun N => (C*(2*C))*sourceWeightedGapPowerTail hp hp1 w φ.val N
  let B := C*offDiagonalSummationConstant p*‖ψ‖^p.toReal
  let A := B*‖ψ‖^(2*p.toReal)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by dsimp [C]; positivity)
    (offDiagonalSummationConstant_nonneg p)) (by positivity)
  have hcut : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop_mono (fun N => by dsimp; omega) tendsto_id
  have hlim : Tendsto v atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => ‖weightedPairFourierTail w.toWeight (2*N) ψ‖) atTop (𝓝 0) := by
      simpa only [norm_zero,Function.comp_def] using
        ((tendsto_weightedPairFourierTail hp w.toWeight ψ).comp hcut).norm
    exact hn.rpow_const_nhds_zero (zero_lt_one.trans hpR)
  apply summable_four_adic_of_forced_quadratic_tail v g A B (min 1 (p.toReal-1)) r M M
    (fun N => by dsimp [v]; positivity)
    (fun N => mul_nonneg (by dsimp [C]; positivity) (sourceWeightedGapPowerTail_nonneg hp hp1 w φ.val N))
    hlim (mul_nonneg hB (by positivity)) (lt_min (by norm_num) (by linarith))
    hr hrα (by omega) le_rfl
  · apply (hgs.mul_left (C*(2*C))).congr
    intro k
    dsimp [g]
    ring
  · intro N hN
    have he : ‖weightedPairFourierTail w.toWeight (2*N) ψ‖^(2*p.toReal) = (v N)^2 := by
      dsimp only [v]
      rw [mul_comm (2:ℝ),Real.rpow_mul (norm_nonneg _),Real.rpow_two]
    have h := hrec N hN
    rw [he] at h
    convert h using 1
    dsimp only [v,g,A,B,C]
    ring

end NLS.ZakharovShabat
