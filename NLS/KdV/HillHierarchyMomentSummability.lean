import NLS.KdV.HillL2SquareGapPeriods
import NLS.KdV.HillHighMomentComparison

/-! # Absolute convergence of actual Hill hierarchy moment sums

Sobolev growth of the Fourier weight controls every fixed polynomial
moment level. The finitely many low gaps cause no restriction; high
mean-value comparison and the checked weighted action series give
absolute convergence. No Hamiltonian trace value is assumed.
-/

noncomputable section
open Set Complex
namespace NLS.KdV

def hillPeriodOneHierarchyMoment (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n m : ℕ) : ℂ :=
  hillL2RealContourMoment (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr) n m

theorem norm_hillPeriodOneHierarchyMoment_high_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) (m : ℕ) (hw : (n : ℝ) ^ m ≤ w (2 * (n : ℤ))) :
    ‖hillPeriodOneHierarchyMoment w q hr n m‖ ≤
      (2 * Real.pi ^ 2) ^ m * w (2 * (n : ℤ)) ^ 2 * hillPeriodOneAction w q hr n := by
  let Q := hillPeriodOneUnitPotential w q
  let J := hillRealGapIntegral Q (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr) n m
  let A := hillPeriodOneAction w q hr n
  have hA : 0 ≤ A := hillPeriodOneAction_nonneg w q hr n (by omega)
  have hc := hillRealGapIntegral_high_comparison Q (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr) n hn
    (by linarith [norm_hillPeriodOneUnitPotential_le w q]) m
  change (1 / 2 : ℝ) ^ m * freeHillValue n ^ m * A ≤ J ∧
    J ≤ 2 ^ m * freeHillValue n ^ m * A at hc
  have hfree : 0 ≤ freeHillValue n := by unfold freeHillValue; positivity
  have hJ : 0 ≤ J := (show 0 ≤ (1 / 2 : ℝ) ^ m * freeHillValue n ^ m * A by positivity).trans hc.1
  have hnorm : ‖hillPeriodOneHierarchyMoment w q hr n m‖ = J := by
    rw [hillPeriodOneHierarchyMoment, hillL2RealContourMoment_eq_gapIntegral _ _ _ n (by omega)]
    exact (Complex.norm_real _).trans ((Real.norm_eq_abs _).trans (abs_of_nonneg hJ))
  have he : 2 ^ m * freeHillValue n ^ m = (2 * Real.pi ^ 2) ^ m * ((n : ℝ) ^ m) ^ 2 := by
    simp only [freeHillValue, Int.cast_natCast, mul_pow]
    ring
  rw [hnorm]
  calc
    J ≤ 2 ^ m * freeHillValue n ^ m * A := hc.2
    _ = (2 * Real.pi ^ 2) ^ m * ((n : ℝ) ^ m) ^ 2 * A := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hw 2) (by positivity)) hA

theorem summable_hillPeriodOneHierarchyMoment_norm (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (m : ℕ)
    (hw : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ m ≤ w (2 * (n : ℤ))) :
    Summable (fun k : ℕ => ‖(2 * (k + 1 : ℕ) * Real.pi : ℂ) *
      hillPeriodOneHierarchyMoment w q hr (k + 1) m‖) := by
  let f : ℕ → ℝ := fun n => ‖(2 * (n : ℂ) * Real.pi) * hillPeriodOneHierarchyMoment w q hr n m‖
  let a : ℕ → ℝ := fun n => w (2 * (n : ℤ)) ^ 2 * (2 * Real.pi * (n : ℝ)) * hillPeriodOneAction w q hr n
  have ha : Summable a := (summable_nat_add_iff 1).mp (by
    simpa only [a] using summable_hillPeriodOneAction_weighted w q hr)
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (8 * ‖q‖)
  let N := max 2 N₁
  have hbound (k : ℕ) : f (k + N) ≤ (2 * Real.pi ^ 2) ^ m * a (k + N) := by
    have hn : 2 ≤ k + N := by dsimp [N]; omega
    have hcut : 8 * ‖q‖ ≤ ((k + N : ℕ) : ℝ) := hN₁.trans (by exact_mod_cast (show N₁ ≤ k + N by dsimp [N]; omega))
    have hb := norm_hillPeriodOneHierarchyMoment_high_le w q hr (k + N) hn hcut m (hw (k + N) (by omega))
    have hnreal : (0 : ℝ) ≤ (k + N : ℕ) := by positivity
    have hfactor : ‖(2 * ((k + N : ℕ) : ℂ) * Real.pi)‖ = 2 * Real.pi * (k + N : ℕ) := by
      rw [show (2 * ((k + N : ℕ) : ℂ) * Real.pi) = ((2 * Real.pi * (k + N : ℕ) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    dsimp only [f, a]
    rw [norm_mul, hfactor]
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * Real.pi * (k + N : ℕ) by positivity)
    calc
      _ ≤ (2 * Real.pi * (k + N : ℕ)) *
          ((2 * Real.pi ^ 2) ^ m * w (2 * ((k + N : ℕ) : ℤ)) ^ 2 * hillPeriodOneAction w q hr (k + N)) := hh
      _ = _ := by ring
  have htail : Summable (fun k : ℕ => f (k + N)) := Summable.of_nonneg_of_le
    (fun k => norm_nonneg _) hbound (((summable_nat_add_iff N).mpr ha).mul_left _)
  have hfull : Summable f := (summable_nat_add_iff N).mp htail
  simpa only [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hfull

theorem summable_hillPeriodOneHierarchyMoment_sobolev (m : ℕ)
    (q : WeightedCoeff (SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toWeight 2)
    (hr : IsRealHillPotential ((SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toCoeff q)) :
    Summable (fun k : ℕ => ‖(2 * (k + 1 : ℕ) * Real.pi : ℂ) *
      hillPeriodOneHierarchyMoment (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr (k + 1) m‖) := by
  apply summable_hillPeriodOneHierarchyMoment_norm
  intro n hn
  simp only [SpectralWeight.sobolev_apply, Weight.sobolev_apply, Int.cast_mul,
    Int.cast_ofNat, Int.cast_natCast, abs_of_nonneg (by positivity : 0 ≤ 2 * (n : ℝ)), Real.rpow_natCast]
  exact pow_le_pow_left₀ (by positivity) (by linarith : (n : ℝ) ≤ 1 + 2 * (n : ℝ)) m

def hillPeriodOneSquareGapPeriod (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n m : ℕ) : ℂ :=
  let Q := hillPeriodOneUnitPotential w q
  let hQ := hillPeriodOneUnitPotential_even w q
  let hR := hillPeriodOneUnitPotential_real w q hr
  ((Real.pi : ℂ) * I)⁻¹ * ∮ z in C((hillRealGapCenter Q hQ hR n : ℂ),
      hillRealGapHalfLength Q hQ hR n + hillRealGapCollar Q hQ hR n),
    z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff Q) z ^ 2

theorem hillPeriodOneSquareGapPeriod_eq (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    hillPeriodOneSquareGapPeriod w q hr n m =
      (2 * (n : ℂ) * Real.pi) * hillPeriodOneHierarchyMoment w q hr n m :=
  hillL2SquareGapPeriod_eq_weightedMoment _ _ _ n hn m

/-- Absolute convergence of the literal squared-primitive gap periods
on the Sobolev coefficient domain at each hierarchy level. -/
theorem summable_hillPeriodOneSquareGapPeriod_sobolev (m : ℕ)
    (q : WeightedCoeff (SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toWeight 2)
    (hr : IsRealHillPotential ((SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toCoeff q)) :
    Summable (fun k : ℕ => ‖hillPeriodOneSquareGapPeriod
      (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr (k + 1) m‖) := by
  have he : (fun k : ℕ => ‖hillPeriodOneSquareGapPeriod
      (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr (k + 1) m‖) =
      (fun k : ℕ => ‖(2 * (k + 1 : ℕ) * Real.pi : ℂ) * hillPeriodOneHierarchyMoment
        (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr (k + 1) m‖) := by
    funext k
    rw [hillPeriodOneSquareGapPeriod_eq _ q hr (k + 1) (by omega)]
  rw [he]
  exact summable_hillPeriodOneHierarchyMoment_sobolev m q hr

end NLS.KdV
