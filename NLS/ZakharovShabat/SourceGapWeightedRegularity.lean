import NLS.ZakharovShabat.SourceGapWeightedTail
import NLS.SequenceSpaces.SummableGeometricTails

/-! # A repeatable regularity gain from actual weighted gaps

The forced quadratic tail recurrence and exact tail-summability bridge
add a Sobolev weight to any available weighted realization of a real source.
The gaps need not vanish, and the gain is at the requested order.
-/

noncomputable section

namespace NLS.ZakharovShabat
open Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An additional Sobolev gap weight transfers to both physical Fourier components
whenever the gain is below min(1,p-1)/p. -/
theorem source_weighted_mem_sobolev_of_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val)
    (s : ℝ) (hs : 0 < s) (hsp : s*p.toReal < min 1 (p.toReal-1))
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev s n:ℂ)*
      ((w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n)) p) :
    Memℓp (fun n => (Weight.sobolev s n:ℂ)*((w n:ℂ)*ψ.fst.val n)) p ∧
    Memℓp (fun n => (Weight.sobolev s n:ℂ)*((w n:ℂ)*ψ.snd.val n)) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let r := (4:ℝ)^(s*p.toReal)
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrα : r*(4:ℝ)^(-min 1 (p.toReal-1)) < 1 := by
    dsimp [r]
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨M,hM,htransfer⟩ := source_weighted_fourierTail_summable_of_gap_tail hp hp1 φ w ψ hψ
  let f := fun n => ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖^p.toReal
  have hfs : Summable (fun n : ℤ => (1+|(n:ℝ)|)^(s*p.toReal)*f n) := by
    apply (hgap.summable hp0).congr
    intro n
    dsimp only [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev s).positive n),
      Real.mul_rpow ((Weight.sobolev s).positive n).le (norm_nonneg _),
      Weight.sobolev_apply,← Real.rpow_mul (by positivity)]
  have hgs : Summable (fun k => r^k*sourceWeightedGapPowerTail hp hp1 w φ.val (4*(4^k*M))) := by
    have h := summable_geometric_tails_of_summable_sobolev f
      (fun n => Real.rpow_nonneg (norm_nonneg _) _) (4*M) (by omega) (s*p.toReal)
      (mul_pos hs hp0) hfs
    simpa only [r,sourceWeightedGapPowerTail,f,mul_assoc,mul_left_comm] using h
  have htails := htransfer r hr hrα hgs
  have hfst (N : ℕ) : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.toWeight p ψ.fst)‖ ≤
      ‖weightedPairFourierTail w.toWeight N ψ‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail,← WeightedCoeff.norm_eq]
    exact WithLp.norm_fst_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N ψ)
  have hsnd (N : ℕ) : ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.toWeight p ψ.snd)‖ ≤
      ‖weightedPairFourierTail w.toWeight N ψ‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail,← WeightedCoeff.norm_eq]
    exact WithLp.norm_snd_le (WeightedCoeff w.toWeight p) (weightedPairFourierTail w.toWeight N ψ)
  constructor
  · apply Coeff.mem_sobolev_of_summable_geometric_tails hp0 (WeightedCoeff.weightEquiv w.toWeight p ψ.fst)
      (2*M) (by omega) s hs.le
    apply htails.of_nonneg_of_le (fun k => by positivity)
    intro k
    have h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (hfst (2*(4^k*M))) hp0.le) (pow_nonneg hr.le k)
    simpa only [r,mul_assoc,mul_left_comm] using h
  · apply Coeff.mem_sobolev_of_summable_geometric_tails hp0 (WeightedCoeff.weightEquiv w.toWeight p ψ.snd)
      (2*M) (by omega) s hs.le
    apply htails.of_nonneg_of_le (fun k => by positivity)
    intro k
    have h := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (hsnd (2*(4^k*M))) hp0.le) (pow_nonneg hr.le k)
    simpa only [r,mul_assoc,mul_left_comm] using h
end NLS.ZakharovShabat
