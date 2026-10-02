import NLS.ZakharovShabat.SourceFiniteGapWeightedTail
import NLS.SequenceSpaces.GeometricTailRegularity

/-! # A repeatable weighted regularity gain at finite-gap sources

The tail bootstrap applies to the weighted coefficients themselves.
It therefore adds a positive Sobolev weight to every spectral weight
already carried by a realization of the same finite-gap source.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Gain a further Sobolev weight on both physical Fourier components.
The gain range does not depend on the previously available weight. -/
theorem sourceFiniteGap_weighted_mem_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val)
    (s : ℝ) (hs : 0 ≤ s) (hsp : s*p.toReal < min 1 (p.toReal-1)) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*((w n : ℂ)*ψ.fst.val n)) p ∧
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*((w n : ℂ)*ψ.snd.val n)) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  let β := (α+s*p.toReal)/2
  have hsp0 : 0 ≤ s*p.toReal := mul_nonneg hs hp0.le
  have hβ0 : 0 < β := by dsimp [β,α]; linarith
  have hβlo : s*p.toReal < β := by dsimp [β,α]; linarith
  have hβhi : β < α := by dsimp [β]; dsimp only [α] at *; linarith
  let q := (4 : ℝ)^(-β)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlo : (4 : ℝ)^(-α) < q :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hrq : (4 : ℝ)^(s*p.toReal)*q < 1 := by
    dsimp only [q]
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨M,hM,C,_,hb⟩ := sourceFiniteGap_weighted_fourierTail_geometric hp hp1 φ hfinite w ψ hψ q hqlo hq1
  have hfst (N : ℕ) : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.toWeight p ψ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight N ψ‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail, ← WeightedCoeff.norm_eq]
    exact WithLp.norm_fst_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N ψ)
  have hsnd (N : ℕ) : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.toWeight p ψ.snd)‖ ≤
      ‖weightedPairFourierTail w.toWeight N ψ‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail, ← WeightedCoeff.norm_eq]
    exact WithLp.norm_snd_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N ψ)
  constructor
  · apply Coeff.mem_sobolev_of_geometric_tail hp0 (WeightedCoeff.weightEquiv w.toWeight p ψ.fst)
      (2*M) (by omega) C q s hq0.le hs hrq
    intro k
    have h := (Real.rpow_le_rpow (norm_nonneg _) (hfst (2*(4^k*M))) hp0.le).trans (hb k)
    simpa only [mul_assoc,mul_left_comm] using h
  · apply Coeff.mem_sobolev_of_geometric_tail hp0 (WeightedCoeff.weightEquiv w.toWeight p ψ.snd)
      (2*M) (by omega) C q s hq0.le hs hrq
    intro k
    have h := (Real.rpow_le_rpow (norm_nonneg _) (hsnd (2*(4^k*M))) hp0.le).trans (hb k)
    simpa only [mul_assoc,mul_left_comm] using h

end NLS.ZakharovShabat
