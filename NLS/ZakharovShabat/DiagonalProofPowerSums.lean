import NLS.ZakharovShabat.DiagonalProofRegions
import Mathlib.Analysis.MeanInequalitiesPow

/-! # The four diagonal regional power sums of Lemma 6.8

The actual source moments are bounded by powered Young and contractive
exponent inclusion. This gives the concavity step below two, the exact
N^(-1) and N^(-(p-1)) regimes, and a common exponent-only constant.
The full Holder moment tail is summable and recombines the exact regions.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- The printed far moment has the precise powered-Young kernel budget. -/
theorem diagonalFarMoment_sum_le_kernel (hp : p ≠ ⊤) (hqt : q ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (diagonalFarMoment q a n)^(p.toReal/q.toReal) else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (diagonalFarMoment q a n)^(p.toReal/q.toReal) else 0) ≤
      (‖a‖*‖Coeff.fourierTail ((N+1)/2) (Coeff.puncturedLattice r hr)‖)^p.toReal := by
  simpa only [diagonalFarMoment_power_eq (hr.trans_le hrq) hqt] using
    diagonalFarRow_sum_le hp hr hrp hrq a N

/-- The printed near moment has the precise retained-tail Young budget. -/
theorem diagonalNearMoment_sum_le_kernel (hp : p ≠ ⊤) (hqt : q ≠ ⊤)
    (hr : 1 < r) (hrp : r ≤ p) (hrq : r ≤ q) (a : Coeff p) (N : ℕ) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then (diagonalNearMoment q a n)^(p.toReal/q.toReal) else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then (diagonalNearMoment q a n)^(p.toReal/q.toReal) else 0) ≤
      (‖Coeff.fourierTail N a‖*‖Coeff.puncturedLattice r hr‖)^p.toReal := by
  simpa only [diagonalNearMoment_power_eq (hr.trans_le hrq) hqt] using
    diagonalNearRow_sum_le hp hr hrp hrq a N

/-- The concave-exponent step in the far region is the contractive exponent inclusion. -/
theorem diagonalFarMoment_concave_le (hp : p ≠ ⊤) (hp1 : 1 < p) (hqt : q ≠ ⊤)
    (hpq : p ≤ q) (a : Coeff p) (n : ℤ) :
    (diagonalFarMoment q a n)^(p.toReal/q.toReal) ≤ diagonalFarMoment p a n := by
  have he : diagonalFarRow (hp1.trans_le hpq) a n =
      Coeff.exponentInclusion hpq (diagonalFarRow hp1 a n) := by
    ext l
    simp only [diagonalFarRow_apply,Coeff.exponentInclusion_apply,Coeff.puncturedLattice_apply]
  rw [diagonalFarMoment_power_eq (hp1.trans_le hpq) hqt,diagonalFarMoment_eq hp1 hp,he]
  exact Real.rpow_le_rpow (norm_nonneg _) (Coeff.norm_exponentInclusion_le hpq _) ENNReal.toReal_nonneg

/-- The same concave-exponent inequality holds for the literal near sum. -/
theorem diagonalNearMoment_concave_le (hp : p ≠ ⊤) (hp1 : 1 < p) (hqt : q ≠ ⊤)
    (hpq : p ≤ q) (a : Coeff p) (n : ℤ) :
    (diagonalNearMoment q a n)^(p.toReal/q.toReal) ≤ diagonalNearMoment p a n := by
  have he : diagonalNearRow (hp1.trans_le hpq) a n =
      Coeff.exponentInclusion hpq (diagonalNearRow hp1 a n) := by
    ext l
    simp only [diagonalNearRow_apply,Coeff.exponentInclusion_apply,Coeff.puncturedLattice_apply]
  rw [diagonalNearMoment_power_eq (hp1.trans_le hpq) hqt,diagonalNearMoment_eq hp1 hp,he]
  exact Real.rpow_le_rpow (norm_nonneg _) (Coeff.norm_exponentInclusion_le hpq _) ENNReal.toReal_nonneg

/-- A common exponent-only constant for all four regional estimates. -/
def diagonalRegionConstant (p : ℝ≥0∞) : ℝ := (8*max p.toReal p.conjExponent.toReal)^p.toReal

omit [Fact (1 ≤ p)] in
theorem diagonalRegionConstant_pos (hp : p ≠ ⊤) (hp1 : 1 < p) : 0 < diagonalRegionConstant p := by
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hm : 0 < max p.toReal p.conjExponent.toReal := hP.trans_le (le_max_left _ _)
  unfold diagonalRegionConstant
  positivity

omit [Fact (1 ≤ p)] in
/-- Raising the reciprocal decay preserves the precise source exponent. -/
theorem diagonalRegion_decay_power (A s : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) (N : ℕ) :
    (A*(8*s*(N : ℝ)^(-(1/s))))^p.toReal =
      (8*s)^p.toReal*A^p.toReal/(N : ℝ)^(p.toReal/s) := by
  rw [Real.mul_rpow hA (by positivity),Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (Nat.cast_nonneg N),
    show -(1/s)*p.toReal = -(p.toReal/s) by ring,
    Real.rpow_neg (Nat.cast_nonneg N)]
  ring

local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- Both literal regional power sums converge, with the two source decay regimes and the exact potential tail. -/
theorem diagonalMoment_region_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p)
    (N : ℕ) (hN : 0 < N) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (diagonalFarMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ∧
    Summable (fun n : ℤ => if N ≤ n.natAbs then
      (diagonalNearMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (diagonalFarMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      diagonalRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) ∧
    (∑' n : ℤ, if N ≤ n.natAbs then
      (diagonalNearMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      diagonalRegionConstant p*‖Coeff.fourierTail N a‖^p.toReal := by
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  have hq : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  obtain ⟨s,hc,hs,he⟩ := exists_diagonalInnerConjugate hp hp1
  obtain ⟨hf,hfb⟩ := diagonalFarMoment_sum_le_kernel hp hq hr (min_le_left _ _) (min_le_right _ _) a N
  obtain ⟨hn,hnb⟩ := diagonalNearMoment_sum_le_kernel hp hq hr (min_le_left _ _) (min_le_right _ _) a N
  have hs0 := hc.pos
  have hmax : 0 ≤ max p.toReal p.conjExponent.toReal := ENNReal.toReal_nonneg.trans (le_max_left _ _)
  have hpow : (8*s)^p.toReal ≤ diagonalRegionConstant p :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hs (by norm_num)) ENNReal.toReal_nonneg
  refine ⟨hf,hn,hfb.trans ?_,hnb.trans ?_⟩
  · calc
      _ ≤ (‖a‖*(8*s*(N : ℝ)^(-(1/s))))^p.toReal :=
        Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left (norm_diagonalHalfKernel_le hr hc N hN) (norm_nonneg _)) ENNReal.toReal_nonneg
      _ = (8*s)^p.toReal*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) := by
        rw [diagonalRegion_decay_power _ _ (norm_nonneg _) hs0.le,he]
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
  · have hker : ‖Coeff.puncturedLattice (diagonalInnerExponent p) hr‖ ≤ 8*s :=
      (Coeff.norm_puncturedLattice_le_four_conjugate hr hc).trans (by linarith)
    calc
      _ ≤ (‖Coeff.fourierTail N a‖*(8*s))^p.toReal :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hker (norm_nonneg _)) ENNReal.toReal_nonneg
      _ = (8*s)^p.toReal*‖Coeff.fourierTail N a‖^p.toReal := by
        rw [Real.mul_rpow (norm_nonneg _) (by positivity),mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by positivity)

/-- The printed split at two is exactly the conjugate-exponent split. -/
theorem diagonal_conjugate_regimes (hp : p ≠ ⊤) (hp1 : 1 < p) :
    p.toReal/p.conjExponent.toReal = p.toReal-1 ∧
    (2 ≤ p.toReal ↔ p.conjExponent ≤ p) ∧
    (p.toReal ≤ 2 ↔ p ≤ p.conjExponent) := by
  have hq : p.conjExponent ≠ ⊤ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hc : p.toReal.HolderConjugate p.conjExponent.toReal := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  refine ⟨hc.div_conj_eq_sub_one,?_,?_⟩
  · rw [← ENNReal.toReal_le_toReal hq hp,← one_le_div hc.symm.pos,hc.div_conj_eq_sub_one]
    constructor <;> intro h <;> linarith
  · rw [← ENNReal.toReal_le_toReal hp hq,← div_le_one hc.symm.pos,hc.div_conj_eq_sub_one]
    constructor <;> intro h <;> linarith

/-- The far bound has exactly N^(-1) decay when p is at least two. -/
theorem diagonalFarMoment_sum_ge_two (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : 2 ≤ p.toReal)
    (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (diagonalFarMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      diagonalRegionConstant p*‖a‖^p.toReal/N := by
  simpa only [min_eq_left (by linarith : 1 ≤ p.toReal-1),Real.rpow_one] using
    (diagonalMoment_region_bounds hp hp1 a N hN).2.2.1

/-- The far bound has exactly N^(-(p-1)) decay between one and two. -/
theorem diagonalFarMoment_sum_le_two (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p.toReal ≤ 2)
    (a : Coeff p) (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, if N ≤ n.natAbs then
      (diagonalFarMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0) ≤
      diagonalRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(p.toReal-1) := by
  simpa only [min_eq_right (by linarith : p.toReal-1 ≤ 1)] using
    (diagonalMoment_region_bounds hp hp1 a N hN).2.2.1

/-- The full reciprocal-moment power tail appearing after Holder's inequality. -/
def diagonalMomentPowerTail (p : ℝ≥0∞) (N : ℕ) (a : Coeff p) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then
    (∑' m : ℤ, (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal)^(p.toReal/p.conjExponent.toReal)
  else 0

/-- The literal moment power is the actual reciprocal row norm raised to p. -/
theorem diagonalMomentPower_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (n : ℤ) :
    (∑' m : ℤ, (‖a (n+m)‖ / |((m-n : ℤ) : ℝ)|)^p.conjExponent.toReal)^(p.toReal/p.conjExponent.toReal) =
      ‖complementaryRowEnvelope ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) a n‖^p.toReal := by
  rw [norm_complementaryRowEnvelope_eq _ ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne,
    ← Real.rpow_mul (tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))]
  congr 1
  ring

/-- Every displayed outer Holder sum is finite, including cutoff zero. -/
theorem summable_diagonalMomentPowerTail (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (N : ℕ) :
    Summable (diagonalMomentPowerTail p N a) := by
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  obtain ⟨d,hd,hb⟩ := exists_reciprocalRowMajorant hp hr (min_le_left _ _) (min_le_right _ _) a
  have hs := (diagonalRow_power_sum_le hp
    (fun n => ‖complementaryRowEnvelope (hr.trans_le (min_le_right _ _)) a n‖) N
    (fun _ => norm_nonneg _) d (fun n _ => hd n) _ hb).1
  change Summable (fun n => diagonalMomentPowerTail p N a n)
  simpa only [diagonalMomentPowerTail,diagonalMomentPower_eq hp hp1] using hs

/-- Recombining the exact regional sums gives the full reciprocal-moment budget. -/
theorem diagonalMomentPowerTail_sum_le (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p)
    (N : ℕ) (hN : 0 < N) :
    (∑' n : ℤ, diagonalMomentPowerTail p N a n) ≤
      (2:ℝ)^(p.toReal-1)*diagonalRegionConstant p *
        (‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖Coeff.fourierTail N a‖^p.toReal) := by
  have hP : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal (by simp) hp).mpr hp1.le
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hqt := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  obtain ⟨hf,hn,hfb,hnb⟩ := diagonalMoment_region_bounds hp hp1 a N hN
  let F : ℤ → ℝ := fun n => if N ≤ n.natAbs then
    (diagonalFarMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0
  let H : ℤ → ℝ := fun n => if N ≤ n.natAbs then
    (diagonalNearMoment p.conjExponent a n)^(p.toReal/p.conjExponent.toReal) else 0
  let C := (2:ℝ)^(p.toReal-1)
  have hpoint (n : ℤ) : diagonalMomentPowerTail p N a n ≤ C*(F n+H n) := by
    by_cases hcut : N ≤ n.natAbs
    · simp only [diagonalMomentPowerTail,F,H,if_pos hcut,diagonalMomentPower_eq hp hp1,
        diagonalFarMoment_power_eq hq hqt,diagonalNearMoment_power_eq hq hqt]
      rw [norm_complementaryRowEnvelope_eq_convolutionRow hq,← diagonalFarRow_add_near hq a n]
      apply (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) (by positivity : 0 ≤ p.toReal)).trans
      exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
        (⟨‖diagonalFarRow hq a n‖,norm_nonneg _⟩ : ℝ≥0)
        (⟨‖diagonalNearRow hq a n‖,norm_nonneg _⟩ : ℝ≥0) hP
    · simp only [diagonalMomentPowerTail,F,H,if_neg hcut,add_zero,mul_zero,le_refl]
  have hsum : Summable (fun n => C*(F n+H n)) := (hf.add hn).mul_left C
  calc
    _ ≤ ∑' n, C*(F n+H n) := (summable_diagonalMomentPowerTail hp hp1 a N).tsum_le_tsum hpoint hsum
    _ = C*((∑' n, F n)+(∑' n,H n)) := by rw [tsum_mul_left,hf.tsum_add hn]
    _ ≤ C*(diagonalRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) +
        diagonalRegionConstant p*‖Coeff.fourierTail N a‖^p.toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add hfb hnb) (by positivity)
    _ = _ := by dsimp [C]; ring

end NLS.ZakharovShabat
