import NLS.ZakharovShabat.OffDiagonalProofHolder
import NLS.ZakharovShabat.OffDiagonalPower

/-! # Summing the literal off-diagonal proof bound

The actual regional rows, rather than larger replacement regions, control
the weighted remainders and yield convergent tails with both potential factors.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The exact regional row norm, restricted to the requested signed outer tail. -/
def offDiagonalProofRowTail (hp : p ≠ ⊤) (i : OffDiagonalProofRegion) (a : Coeff p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then ‖offDiagonalProofRow
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) i a n‖ else 0

/-- This power is the displayed regional moment power on the same outer tail. -/
theorem offDiagonalProofRowTail_power (hp : p ≠ ⊤) (hp1 : 1 < p)
    (i : OffDiagonalProofRegion) (a : Coeff p) (N : ℕ) (n : ℤ) :
    (offDiagonalProofRowTail hp i a N n)^p.toReal = if N ≤ n.natAbs then
      (offDiagonalProofMoment p.conjExponent i a n)^(p.toReal/p.conjExponent.toReal) else 0 := by
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hqt := ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  unfold offDiagonalProofRowTail
  split_ifs
  · exact (offDiagonalProofMoment_power_eq hq hqt i a n).symm
  · exact Real.zero_rpow (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp).ne'

/-- The source's two far regions have the same exact norm, despite their overlap. -/
theorem offDiagonalProofFarRow_norm_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (a : Coeff p) (n : ℤ) :
    ‖offDiagonalProofRow ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) .farK a n‖ =
      ‖offDiagonalProofRow ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top) .farL a n‖ := by
  exact doubleReciprocalFarRow_swap _
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne a _ n

/-- The source regional majorant after bounding the actual even vector. -/
def offDiagonalProofBound (hp : p ≠ ⊤) (w : SpectralWeight) (d a : WeightedCoeff w.toWeight p)
    (N : ℕ) (n : ℤ) : ℝ :=
  (2*‖d‖)*(2*‖d‖*offDiagonalProofRowTail hp .farL (WeightedCoeff.weightEquiv w.toWeight p a) N n +
    ‖WeightedCoeff.fourierTail w.toWeight N d‖*offDiagonalProofRowTail hp .near (WeightedCoeff.weightEquiv w.toWeight p a) N n)

theorem offDiagonalProofBound_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) : 0 ≤ offDiagonalProofBound hp w d a N n := by
  unfold offDiagonalProofBound offDiagonalProofRowTail
  positivity

/-- The actual physical double series satisfies the literal regional bound. -/
theorem weighted_norm_tsum_offDiagonal_proof_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a f : WeightedCoeff w.toWeight p) (N : ℕ) (n : ℤ) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ resonantStrip n) (hf : w.shiftedNorm n f ≤ 2*‖d‖) :
    w (2*n)*‖∑' l : ℤ, ∑' k : ℤ, d.val (n+l)*a.val (l+k)*
      complementarySymbol n z l*complementarySymbol n z k*f.val k‖ ≤ offDiagonalProofBound hp w d a N n := by
  have hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have h := norm_tsum_offDiagonal_proof_regions_le hq w d a f N n hn z hz
  rw [(summable_norm_weightedOffDiagonalTerm hq w d a f n z hz).of_norm.tsum_prod,
    tsum_weightedOffDiagonalTerm_eq,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le,
    offDiagonalProofFarRow_norm_eq hp hp1] at h
  have hscale (D T F H U : ℝ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hF : 0 ≤ F) (hH : 0 ≤ H)
      (hU : U ≤ 2*D) : U*(D*(F+F)+T*H) ≤ (2*D)*(2*D*F+T*H) := by
    calc
      _ ≤ (2*D)*(D*(F+F)+T*H) := mul_le_mul_of_nonneg_right hU (by positivity)
      _ = _ := by ring
  have hb := hscale ‖d‖ ‖WeightedCoeff.fourierTail w.toWeight N d‖
    ‖offDiagonalProofRow hq .farL (WeightedCoeff.weightEquiv w.toWeight p a) n‖
    ‖offDiagonalProofRow hq .near (WeightedCoeff.weightEquiv w.toWeight p a) n‖
    (w.shiftedNorm n f) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hf
  simpa only [offDiagonalProofBound,offDiagonalProofRowTail,if_pos hn] using h.trans hb


/-- One exponent-only constant for the complete literal off-diagonal proof. -/
def offDiagonalProofConstant (p : ℝ≥0∞) : ℝ :=
  (4:ℝ)^p.toReal*2^(p.toReal-1)*offDiagonalProofRegionConstant p

omit [Fact (1 ≤ p)] in
theorem offDiagonalProofConstant_pos (hp : p ≠ ⊤) (hp1 : 1 < p) : 0 < offDiagonalProofConstant p := by
  have hC := offDiagonalProofRegionConstant_pos hp hp1
  unfold offDiagonalProofConstant
  positivity

/-- Recombining the actual regional moments preserves both weighted potential-tail factors. -/
theorem offDiagonalProofBound_summable_and_le (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 0 < N) :
    Summable (fun n : ℤ => (offDiagonalProofBound hp w d a N n)^p.toReal) ∧
    (∑' n : ℤ, (offDiagonalProofBound hp w d a N n)^p.toReal) ≤
      offDiagonalProofConstant p*‖d‖^p.toReal*
        (‖d‖^p.toReal*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) +
          ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal*‖WeightedCoeff.fourierTail w.toWeight N a‖^p.toReal) := by
  let A := WeightedCoeff.weightEquiv w.toWeight p a
  let F := offDiagonalProofRowTail hp .farL A N
  let H := offDiagonalProofRowTail hp .near A N
  have hb := offDiagonalProofMoment_region_bounds hp hp1 A N hN
  have hsF : Summable (fun n => (F n)^p.toReal) := by
    simpa only [F,offDiagonalProofRowTail_power hp hp1] using hb.1 .farL
  have hsH : Summable (fun n => (H n)^p.toReal) := by
    simpa only [H,offDiagonalProofRowTail_power hp hp1] using hb.1 .near
  have hF : (∑' n,(F n)^p.toReal) ≤ offDiagonalProofRegionConstant p*‖A‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) := by
    simpa only [F,offDiagonalProofRowTail_power hp hp1] using hb.2.1 .farL (by decide)
  have hH : (∑' n,(H n)^p.toReal) ≤ offDiagonalProofRegionConstant p*‖Coeff.fourierTail N A‖^p.toReal := by
    simpa only [H,offDiagonalProofRowTail_power hp hp1] using hb.2.2
  have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr hp1.le
  obtain ⟨hs,hsum⟩ := summable_two_region_power hP (norm_nonneg d)
    (norm_nonneg (WeightedCoeff.fourierTail w.toWeight N d)) F H
    (fun n => by dsimp [F,offDiagonalProofRowTail]; positivity)
    (fun n => by dsimp [H,offDiagonalProofRowTail]; positivity) hsF hsH
  refine ⟨hs,hsum.trans ?_⟩
  have ha : ‖A‖ = ‖a‖ := (WeightedCoeff.norm_eq w.toWeight p a).symm
  have ht : ‖Coeff.fourierTail N A‖ = ‖WeightedCoeff.fourierTail w.toWeight N a‖ := by
    rw [← WeightedCoeff.weightEquiv_fourierTail]
    exact (WeightedCoeff.norm_eq w.toWeight p _).symm
  rw [ha] at hF
  rw [ht] at hH
  calc
    _ ≤ (4:ℝ)^p.toReal*2^(p.toReal-1)*‖d‖^p.toReal*
        (‖d‖^p.toReal*(offDiagonalProofRegionConstant p*‖a‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1))) +
        ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal*
          (offDiagonalProofRegionConstant p*‖WeightedCoeff.fourierTail w.toWeight N a‖^p.toReal)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left hF (by positivity)) (mul_le_mul_of_nonneg_left hH (by positivity))
    _ = _ := by unfold offDiagonalProofConstant; ring

/-- Common bounds on the actual potential components give the full-cutoff pair-shaped estimate. -/
theorem offDiagonalProofBound_sum_le_of_norm_bounds (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (d a : WeightedCoeff w.toWeight p) (N : ℕ) (hN : 0 < N)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R) (hd : ‖d‖ ≤ B) (ha : ‖a‖ ≤ B)
    (htd : ‖WeightedCoeff.fourierTail w.toWeight N d‖ ≤ R)
    (hta : ‖WeightedCoeff.fourierTail w.toWeight N a‖ ≤ R) :
    (∑' n : ℤ, (offDiagonalProofBound hp w d a N n)^p.toReal) ≤
      offDiagonalProofConstant p*‖d‖^p.toReal*(B^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + R^(2*p.toReal)) := by
  have hP := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hprod : ‖d‖^p.toReal*‖a‖^p.toReal ≤ B^(2*p.toReal) := by
    calc
      _ ≤ B^p.toReal*B^p.toReal := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) hd hP.le) (Real.rpow_le_rpow (norm_nonneg _) ha hP.le) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add' hB (by positivity : p.toReal+p.toReal ≠ 0)]; congr 1; ring
  have htail : ‖WeightedCoeff.fourierTail w.toWeight N d‖^p.toReal*
      ‖WeightedCoeff.fourierTail w.toWeight N a‖^p.toReal ≤ R^(2*p.toReal) := by
    calc
      _ ≤ R^p.toReal*R^p.toReal := mul_le_mul
        (Real.rpow_le_rpow (norm_nonneg _) htd hP.le) (Real.rpow_le_rpow (norm_nonneg _) hta hP.le) (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add' hR (by positivity : p.toReal+p.toReal ≠ 0)]; congr 1; ring
  apply (offDiagonalProofBound_summable_and_le hp hp1 w d a N hN).2.trans
  exact mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hprod (by positivity)) htail)
    (mul_nonneg (offDiagonalProofConstant_pos hp hp1).le (by positivity))

end NLS.ZakharovShabat
