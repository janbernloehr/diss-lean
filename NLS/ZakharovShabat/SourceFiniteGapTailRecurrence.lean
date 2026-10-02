import NLS.ZakharovShabat.SourceFiniteGapAdaptedCoordinates
import NLS.ZakharovShabat.SourceFourierTail
import NLS.SequenceSpaces.QuadraticTailBootstrap

/-! # Quadratic Fourier-tail recurrence for actual finite-gap sources

The adapted truncation identity turns the off-diagonal remainder
estimate into an estimate for the original source tail. The smaller
physical cutoff is converted back to the original source frequency.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a finite-gap source the actual remainder is the negative source tail. -/
theorem sourceResonantCenterRemainder_eq_neg_tail_of_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ M : ℕ, N ≤ M →
      sourceResonantCenterRemainder hp φ.val M = -sourceFourierTail M φ.val := by
  obtain ⟨N,hN,htrunc⟩ := sourceAdaptedClosingMap_eq_truncate_of_finiteGap hp hp1 φ hfinite
  refine ⟨N,hN,?_⟩
  intro M hM
  rw [← sourceAdaptedClosingMap_sub_source,htrunc M hM]
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change Coeff.truncate (Coeff.lowFrequencies M) φ.val.fst n-φ.val.fst n =
      -(φ.val.fst n-Coeff.truncate (Coeff.lowFrequencies M) φ.val.fst n)
    ring
  · change Coeff.truncate (Coeff.lowFrequencies M) φ.val.snd n-φ.val.snd n =
      -(φ.val.snd n-Coeff.truncate (Coeff.lowFrequencies M) φ.val.snd n)
    ring

/-- Exact constants from the actual spectral remainder estimate.
The factor four is forced by period doubling and the half-cutoff tail. -/
theorem sourceFiniteGap_fourierTail_recurrence
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ‖sourceFourierTail (4*N) φ.val‖^p.toReal ≤
        offDiagonalSummationConstant p * ‖φ.val‖^p.toReal *
          (‖φ.val‖^(2*p.toReal)/(4*N : ℝ)^(min 1 (p.toReal-1)) +
            ‖sourceFourierTail N φ.val‖^(2*p.toReal)) := by
  obtain ⟨N₁,hN₁,hrem⟩ := sourceResonantCenterRemainder_eq_neg_tail_of_finiteGap hp hp1 φ hfinite
  obtain ⟨N₂,_,U,_,_,hφ,_,hbound⟩ := exists_uniform_weightedResonantCenterRemainder_bound
    hp hp1 SpectralWeight.one (sourceWeightedPeriodOne φ.val)
  refine ⟨max N₁ N₂,by omega,?_⟩
  intro N hN
  have hb := (hbound (sourceWeightedPeriodOne φ.val) hφ (4*N) (by omega)).2
  rw [← norm_sourceResonantCenterRemainder, hrem (4*N) (by omega), norm_neg,
    norm_sourceWeightedPeriodOne, show 4*N/2 = 2*N by omega,
    norm_weightedPairFourierTail_sourceWeightedPeriodOne] at hb
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hb

/-- The actual finite-gap Fourier tails decay geometrically on
quadrupled cutoffs, at every rate above the forcing rate. -/
theorem sourceFiniteGap_fourierTail_geometric
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (q : ℝ) (hq : (4 : ℝ)^(-min 1 (p.toReal-1)) < q) (hq1 : q < 1) :
    ∃ M : ℕ, 0 < M ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      ‖sourceFourierTail (4^k*M) φ.val‖^p.toReal ≤ C*q^k := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  obtain ⟨N₀,_,hrec⟩ := sourceFiniteGap_fourierTail_recurrence hp hp1 φ hfinite
  let v (N : ℕ) := ‖sourceFourierTail N φ.val‖^p.toReal
  let B := offDiagonalSummationConstant p * ‖φ.val‖^p.toReal
  let A := B*‖φ.val‖^(2*p.toReal)
  have hB : 0 ≤ B := mul_nonneg (offDiagonalSummationConstant_nonneg p) (by positivity)
  have hlim : Tendsto v atTop (𝓝 0) := by
    have hn : Tendsto (fun N : ℕ => ‖sourceFourierTail N φ.val‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using (tendsto_sourceFourierTail hp φ.val).norm
    exact hn.rpow_const_nhds_zero (zero_lt_one.trans hpR)
  apply exists_four_adic_bound_of_quadratic_tail v A B (min 1 (p.toReal-1)) q N₀
    (fun N => by dsimp [v]; positivity) hlim (mul_nonneg hB (by positivity)) hB
    (lt_min (by norm_num) (by linarith)) hq hq1
  intro N hN
  have he : ‖sourceFourierTail N φ.val‖^(2*p.toReal) = (v N)^2 := by
    dsimp only [v]
    rw [mul_comm (2 : ℝ),Real.rpow_mul (norm_nonneg _),Real.rpow_two]
  have hb := hrec N hN
  rw [he] at hb
  convert hb using 1
  dsimp only [A,B,v]
  ring

/-- Every real finite-gap source has a strictly contracting geometric
tail bound, with all constants and the starting cutoff constructed. -/
theorem exists_sourceFiniteGap_fourierTail_decay
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ M : ℕ, 0 < M ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, ‖sourceFourierTail (4^k*M) φ.val‖^p.toReal ≤ C*q^k := by
  let r := (4 : ℝ)^(-min 1 (p.toReal-1))
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (neg_neg_of_pos (lt_min (by norm_num) (by linarith)))
  let q := (1+r)/2
  have hq : r < q := by dsimp only [q]; linarith
  have hq1 : q < 1 := by dsimp only [q]; linarith
  exact ⟨q,hr.trans hq,hq1,sourceFiniteGap_fourierTail_geometric hp hp1 φ hfinite q hq hq1⟩

end NLS.ZakharovShabat
