import NLS.KdV.HillCanonicalRealLabels
import NLS.KdV.HillPhysicalGapBounds

/-! # Weighted bounds for intrinsic real Hill gaps

The exact source period-one embedding and intrinsic ordered labels define
the gaps directly from the potential. The checked individual and summed
high-gap bounds therefore require no supplied characteristic root family.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

def hillPeriodOneUnitPotential (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    WeightedCoeff SpectralWeight.one.toWeight 2 := hillForgetWeight w 2 (hillPeriodOnePotential w q)

theorem toCoeff_hillPeriodOneUnitPotential (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q) =
      w.toCoeff (hillPeriodOnePotential w q) := toCoeff_hillForgetWeight w 2 _

theorem norm_hillPeriodOneUnitPotential_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : ‖hillPeriodOneUnitPotential w q‖ ≤ ‖q‖ := by
  exact (norm_hillForgetWeight_le w 2 _).trans_eq (norm_hillPeriodOnePotential w q)

theorem hillPeriodOneUnitPotential_even (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q) ∈ Coeff.paritySubspace 0 := by
  rw [toCoeff_hillPeriodOneUnitPotential, toCoeff_hillPeriodOnePotential]
  exact Coeff.periodDouble_mem _

theorem hillPeriodOneUnitPotential_real (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) :
    IsRealHillPotential (SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q)) := by
  rw [toCoeff_hillPeriodOneUnitPotential]
  intro k
  have h := hillPeriodOnePotential_reality w q
    (fun j => by simpa only [SpectralWeight.toCoeff_apply, starRingEnd_apply] using hreal j) k
  simpa only [SpectralWeight.toCoeff_apply, starRingEnd_apply] using h

def hillPeriodOneLabels (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) : ℕ → ℝ :=
  hillRealLabels (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hreal)

def hillPeriodOneGap (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) : ℝ :=
  hillPeriodOneLabels w q hreal (2*n)-hillPeriodOneLabels w q hreal (2*n-1)

theorem hillPeriodOneUnitPotential_eq_of_coeff_eq (w v : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (p : WeightedCoeff v.doubleIndex.toWeight 2)
    (he : ∀ k : ℤ, q.val k = p.val k) :
    hillPeriodOneUnitPotential w q = hillPeriodOneUnitPotential v p := by
  have hc : w.doubleIndex.toCoeff q = v.doubleIndex.toCoeff p := by
    ext k
    simpa only [SpectralWeight.toCoeff_apply] using he k
  have hu : SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q) =
      SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential v p) := by
    rw [toCoeff_hillPeriodOneUnitPotential, toCoeff_hillPeriodOneUnitPotential,
      toCoeff_hillPeriodOnePotential, toCoeff_hillPeriodOnePotential, hc]
  apply Subtype.ext
  funext k
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a k) hu

/-- The auxiliary spectral weight does not change the intrinsic labels
of the same physical period-one Fourier coefficients. -/
theorem hillPeriodOneLabels_eq_of_coeff_eq (w v : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (p : WeightedCoeff v.doubleIndex.toWeight 2)
    (hrealq : IsRealHillPotential (w.doubleIndex.toCoeff q))
    (hrealp : IsRealHillPotential (v.doubleIndex.toCoeff p))
    (he : ∀ k : ℤ, q.val k = p.val k) :
    hillPeriodOneLabels w q hrealq = hillPeriodOneLabels v p hrealp := by
  unfold hillPeriodOneLabels
  exact hillRealLabels_congr _ _ _ _ _ _ (hillPeriodOneUnitPotential_eq_of_coeff_eq w v q p he)

theorem hillPeriodOneGap_eq_of_coeff_eq (w v : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (p : WeightedCoeff v.doubleIndex.toWeight 2)
    (hrealq : IsRealHillPotential (w.doubleIndex.toCoeff q))
    (hrealp : IsRealHillPotential (v.doubleIndex.toCoeff p))
    (he : ∀ k : ℤ, q.val k = p.val k) (n : ℕ) :
    hillPeriodOneGap w q hrealq n = hillPeriodOneGap v p hrealp n := by
  unfold hillPeriodOneGap
  rw [hillPeriodOneLabels_eq_of_coeff_eq w v q p hrealq hrealp he]

theorem hillPeriodOneGap_nonneg (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) :
    0 ≤ hillPeriodOneGap w q hreal n := by
  apply sub_nonneg.mpr
  exact monotone_hillRealLabels _ _ _ (by omega : 2*n-1 ≤ 2*n)

theorem norm_hillPeriodOneLabels_gap (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) :
    ‖(hillPeriodOneLabels w q hreal (2*n) : ℂ)-(hillPeriodOneLabels w q hreal (2*n-1) : ℂ)‖ =
      hillPeriodOneGap w q hreal n := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (hillPeriodOneGap_nonneg w q hreal n)

theorem hillPeriodOneLabels_root (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (j : ℕ) :
    hillL2Discriminant (w.toCoeff (hillPeriodOnePotential w q)) (hillPeriodOneLabels w q hreal j)^2 = 4 := by
  have h := (hillRealLabels_spec (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hreal)).root j
  rw [hillL2Radicand, toCoeff_hillPeriodOneUnitPotential] at h
  exact sub_eq_zero.mp h

theorem hillPeriodOneLabels_high_strip (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    (hillPeriodOneLabels w q hreal (2*n-1) : ℂ) ∈ reducedHillStrip n ∧
      (hillPeriodOneLabels w q hreal (2*n) : ℂ) ∈ reducedHillStrip n := by
  have hc : 16*‖hillPeriodOneUnitPotential w q‖ ≤ (n : ℝ) := by
    linarith [norm_hillPeriodOneUnitPotential_le w q]
  obtain ⟨p,hl,hr⟩ := hillRealLabels_high_pair (hillPeriodOneUnitPotential w q)
    (hillPeriodOneUnitPotential_even w q) (hillPeriodOneUnitPotential_real w q hreal) n hn hc
  change (hillRealLabels _ _ _ (2*n-1) : ℂ) ∈ reducedHillStrip n ∧
    (hillRealLabels _ _ _ (2*n) : ℂ) ∈ reducedHillStrip n
  rw [hl,hr]
  exact ⟨openHillStrip_subset n (hillClosedBall_subset_openStrip n (by omega) p.left_mem),
    openHillStrip_subset n (hillClosedBall_subset_openStrip n (by omega) p.right_mem)⟩

/-- The individual bound for the intrinsic physical gap in the exact
source weight, with no supplied endpoint roots. -/
theorem hillPeriodOne_canonical_gap_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 16*‖q‖ ≤ (n : ℝ)) :
    w (2*(n : ℤ))*hillPeriodOneGap w q hreal n ≤ 6*‖q‖ := by
  obtain ⟨hm,hp⟩ := hillPeriodOneLabels_high_strip w q hreal n hn hcut
  have h := hillPeriodOne_physical_gap_le w q n (by omega)
    (by linarith [norm_nonneg q]) _ _ hp hm
    (hillPeriodOneLabels_root w q hreal (2*n)) (hillPeriodOneLabels_root w q hreal (2*n-1))
  rwa [norm_hillPeriodOneLabels_gap] at h

/-- Corrected Appendix A.7 for the canonical ordered gaps themselves. -/
theorem hillPeriodOne_canonical_gap_tail_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hreal : IsRealHillPotential (w.doubleIndex.toCoeff q)) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 16*‖q‖ ≤ (N : ℝ)) :
    Summable (fun k : ℕ => (w (2*((k+N : ℕ) : ℤ)))^2*hillPeriodOneGap w q hreal (k+N)^2) ∧
      (∑' k : ℕ, (w (2*((k+N : ℕ) : ℤ)))^2*hillPeriodOneGap w q hreal (k+N)^2) ≤
        9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
          2304*‖q‖^4/(N : ℝ) := by
  have hstrip (n : ℕ) (hn : N ≤ n) := hillPeriodOneLabels_high_strip w q hreal n (hN.trans hn)
    (hcut.trans (by exact_mod_cast hn))
  have h := hillPeriodOne_physical_gap_tail_bound w q N (by omega) (by linarith [norm_nonneg q])
    (fun n => (hillPeriodOneLabels w q hreal (2*n) : ℂ))
    (fun n => (hillPeriodOneLabels w q hreal (2*n-1) : ℂ))
    (fun n hn => (hstrip n hn).2) (fun n hn => (hstrip n hn).1)
    (fun n _ => hillPeriodOneLabels_root w q hreal (2*n))
    (fun n _ => hillPeriodOneLabels_root w q hreal (2*n-1))
  simpa only [norm_hillPeriodOneLabels_gap] using h

end NLS.KdV
