import NLS.KdV.HillHighMomentSigns
import NLS.KdV.HillWeightedActionContinuity
import NLS.SequenceSpaces.LocalSeriesContinuity

/-! # Summability and Sobolev continuity of the actual hierarchy moment sums

High actual spectral labels and the real mean-value relation compare the
m-th moments to the weighted action terms whenever the weight dominates
n^m. Locally small weighted action tails then give continuity of the full
moment sum, including possible signed low moments and all gap collisions.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate

theorem hillRealLabels_high_right_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    hillRealLabels q hq hr (2*n) ≤ (Real.pi^2+1)*(n : ℝ)^2 := by
  obtain ⟨p, _, hR⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hloc := abs_le.mp (p.localization q hq n (by omega) (by linarith [norm_nonneg q])).2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [hR]
  dsimp only [freeHillValue] at hloc
  simp only [Int.cast_natCast] at hloc
  nlinarith [hloc.2]

theorem hillRealGapIntegral_high_power_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    hillRealGapIntegral q hq hr n m ≤
      (Real.pi^2+1)^m * (n : ℝ)^(2*m) * hillRealGapIntegral q hq hr n 0 := by
  have hL := (hillRealLabels_high_left_pos q hq hr n hn hcut).le
  have hR := hillRealLabels_high_right_le q hq hr n hn hcut
  have hRpos : 0 ≤ hillRealLabels q hq hr (2*n) :=
    hL.trans (monotone_hillRealLabels q hq hr (by omega))
  have hpow := pow_le_pow_left₀ hRpos hR m
  rw [mul_pow, ← pow_mul] at hpow
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  exact (hillRealGapIntegral_bounds_of_nonneg_left q hq hr n (by omega) m hL).2.trans
    (mul_le_mul_of_nonneg_right hpow hI)

def hillHierarchyMomentTerm (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (m n : ℕ) : ℝ :=
  (2*Real.pi*(n : ℝ)) * hillRealGapIntegral (hillPeriodOneUnitPotential w p.val)
    (hillPeriodOneUnitPotential_even w p.val) (hillPeriodOneUnitPotential_real w p.val p.property) n m

theorem hillHierarchyMomentTerm_high_bound
    (w : SpectralWeight) (p : RealHillWeightedPotential w) (m n : ℕ)
    (hn : 2 ≤ n) (hcut : 16*‖p.val‖ ≤ (n : ℝ))
    (hGrowth : (n : ℝ)^m ≤ w (2*(n : ℤ))) :
    0 ≤ hillHierarchyMomentTerm w p m n ∧
      hillHierarchyMomentTerm w p m n ≤ (Real.pi^2+1)^m * hillWeightedActionTerm w p n := by
  let q := hillPeriodOneUnitPotential w p.val
  have hcutq : 16*‖q‖ ≤ (n : ℝ) :=
    (mul_le_mul_of_nonneg_left (norm_hillPeriodOneUnitPotential_le w p.val) (by norm_num)).trans hcut
  have hsign := hillRealGapIntegral_high_nonneg q (hillPeriodOneUnitPotential_even w p.val)
    (hillPeriodOneUnitPotential_real w p.val p.property) n hn hcutq m
  have hb := hillRealGapIntegral_high_power_bound q (hillPeriodOneUnitPotential_even w p.val)
    (hillPeriodOneUnitPotential_real w p.val p.property) n hn hcutq m
  have hI : 0 ≤ hillPeriodOneAction w p.val p.property n :=
    hillPeriodOneAction_nonneg w p.val p.property n (by omega)
  have hpow : (n : ℝ)^(2*m) ≤ w (2*(n : ℤ))^2 := by
    rw [Nat.mul_comm 2 m, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg n) m) hGrowth 2
  refine ⟨mul_nonneg (by positivity) hsign, ?_⟩
  change (2*Real.pi*(n : ℝ)) * hillRealGapIntegral q _ _ n m ≤ _
  have hb' : hillRealGapIntegral q (hillPeriodOneUnitPotential_even w p.val)
      (hillPeriodOneUnitPotential_real w p.val p.property) n m ≤
      (Real.pi^2+1)^m * w (2*(n : ℤ))^2 * hillPeriodOneAction w p.val p.property n := by
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (by positivity)) hI)
  calc
    _ ≤ (2*Real.pi*(n : ℝ)) *
        ((Real.pi^2+1)^m * w (2*(n : ℤ))^2 * hillPeriodOneAction w p.val p.property n) :=
      mul_le_mul_of_nonneg_left hb' (by positivity)
    _ = _ := by unfold hillWeightedActionTerm; ring


theorem summable_hillHierarchyMomentTerm
    (w : SpectralWeight) (p : RealHillWeightedPotential w) (m : ℕ)
    (hGrowth : ∀ n : ℕ, 1 ≤ n → (n : ℝ)^m ≤ w (2*(n : ℤ))) :
    Summable (hillHierarchyMomentTerm w p m) := by
  obtain ⟨A, hA⟩ := exists_nat_ge (16*‖p.val‖)
  let N := max 2 A
  have hb (k : ℕ) := hillHierarchyMomentTerm_high_bound w p m (k+N)
    (by dsimp [N]; omega) (hA.trans (by exact_mod_cast (show A ≤ k+N by dsimp [N]; omega)))
    (hGrowth (k+N) (by dsimp [N]; omega))
  have hsMajor : Summable (fun k : ℕ => (Real.pi^2+1)^m * hillWeightedActionTerm w p (k+N)) :=
    ((summable_nat_add_iff N).mpr (summable_hillWeightedActionTerm w p)).mul_left _
  have hs := Summable.of_nonneg_of_le (fun k => (hb k).1) (fun k => (hb k).2) hsMajor
  exact (summable_nat_add_iff N).mp hs

theorem exists_hillHierarchyMomentTerm_small_tail
    (w : SpectralWeight) (q : RealHillWeightedPotential w) (m : ℕ)
    (hGrowth : ∀ n : ℕ, 1 ≤ n → (n : ℝ)^m ≤ w (2*(n : ℤ)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set (RealHillWeightedPotential w), 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, 0 ≤ (∑' k : ℕ, hillHierarchyMomentTerm w p m (k+N)) ∧
        (∑' k : ℕ, hillHierarchyMomentTerm w p m (k+N)) ≤ ε := by
  let D := (Real.pi^2+1)^m
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨N₀, U₀, hN₀, hU₀, hqU₀, htail⟩ :=
    exists_hillWeightedActionTerm_small_tail w q (ε/D) (div_pos hε hD)
  obtain ⟨A, hA⟩ := exists_nat_ge (16*(‖q.val‖+1))
  let N := max N₀ A
  let U : Set (RealHillWeightedPotential w) := U₀ ∩ {p | ‖p.val‖ < ‖q.val‖+1}
  have hU : IsOpen U := hU₀.inter (isOpen_lt continuous_subtype_val.norm continuous_const)
  refine ⟨N, U, hN₀.trans (le_max_left _ _), hU, ⟨hqU₀, by dsimp; linarith⟩, ?_⟩
  intro p hp
  have hpn : ‖p.val‖ < ‖q.val‖+1 := hp.2
  have hcutN : 16*‖p.val‖ ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left hpn.le (by norm_num : (0 : ℝ) ≤ 16)).trans
      (hA.trans (by exact_mod_cast le_max_right N₀ A))
  have hb (k : ℕ) := hillHierarchyMomentTerm_high_bound w p m (k+N)
    (by dsimp [N]; omega) (hcutN.trans (by exact_mod_cast (show N ≤ k+N by omega)))
    (hGrowth (k+N) (by dsimp [N]; omega))
  have hs : Summable (fun k : ℕ => hillHierarchyMomentTerm w p m (k+N)) :=
    (summable_nat_add_iff N).mpr (summable_hillHierarchyMomentTerm w p m hGrowth)
  have hsA : Summable (fun k : ℕ => D*hillWeightedActionTerm w p (k+N)) :=
    ((summable_nat_add_iff N).mpr (summable_hillWeightedActionTerm w p)).mul_left D
  refine ⟨tsum_nonneg (fun k => (hb k).1), ?_⟩
  have hsum := hs.tsum_le_tsum (fun k => (hb k).2) hsA
  rw [tsum_mul_left] at hsum
  have hmono := nat_tsum_tail_antitone_of_nonneg (hillWeightedActionTerm w p)
    (summable_hillWeightedActionTerm w p) (hillWeightedActionTerm_nonneg w p) (le_max_left N₀ A)
  have hbudget := (htail p hp.1).2
  calc
    _ ≤ D*(∑' k : ℕ, hillWeightedActionTerm w p (k+N)) := hsum
    _ ≤ D*(∑' k : ℕ, hillWeightedActionTerm w p (k+N₀)) := mul_le_mul_of_nonneg_left hmono hD.le
    _ ≤ D*(ε/D) := mul_le_mul_of_nonneg_left hbudget hD.le
    _ = ε := by field_simp

theorem continuous_hillHierarchyMomentTerm (w : SpectralWeight) (m n : ℕ) :
    Continuous (fun p : RealHillWeightedPotential w => hillHierarchyMomentTerm w p m n) := by
  by_cases hn : n = 0
  · subst n
    simp only [hillHierarchyMomentTerm, Nat.cast_zero, mul_zero, zero_mul]
    exact continuous_const
  · have hQ : Continuous (fun p : RealHillWeightedPotential w => hillPeriodOneUnitPotential w p.val) :=
      (continuous_hillPeriodOneUnitPotential w).comp continuous_subtype_val
    have h := continuous_hillRealGapIntegral_family
      (fun p : RealHillWeightedPotential w => hillPeriodOneUnitPotential w p.val) hQ
      (fun p => hillPeriodOneUnitPotential_even w p.val)
      (fun p => hillPeriodOneUnitPotential_real w p.val p.property) n (by omega) m
    simpa only [hillHierarchyMomentTerm] using h.const_mul (2*Real.pi*(n : ℝ))

theorem continuous_tsum_hillHierarchyMomentTerm (w : SpectralWeight) (m : ℕ)
    (hGrowth : ∀ n : ℕ, 1 ≤ n → (n : ℝ)^m ≤ w (2*(n : ℤ))) :
    Continuous (fun p : RealHillWeightedPotential w => ∑' n : ℕ, hillHierarchyMomentTerm w p m n) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply continuousAt_tsum_of_locally_small_nat_tails (fun p n => hillHierarchyMomentTerm w p m n) q
    (fun p => summable_hillHierarchyMomentTerm w p m hGrowth)
    (fun n => (continuous_hillHierarchyMomentTerm w m n).continuousAt)
  intro ε hε
  obtain ⟨N, U, _, hU, hqU, htail⟩ := exists_hillHierarchyMomentTerm_small_tail w q m hGrowth ε hε
  refine ⟨N, ?_⟩
  filter_upwards [hU.mem_nhds hqU] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (htail p hp).1]
  exact (htail p hp).2


end NLS.KdV
