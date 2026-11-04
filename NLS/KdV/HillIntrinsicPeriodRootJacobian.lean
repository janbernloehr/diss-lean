import NLS.KdV.HillRootCoordinateAffineVariation
import NLS.KdV.HillRootSlopeNonvanishing
import NLS.KdV.HillAbelianHilbertPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianHilbertPeriod_add_single
    (n m k : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (hk : 1 ≤ k) (a : Coeff 2) (s : ℂ) :
    hillAbelianHilbertPeriod q hq hr n k (a+lp.single 2 (m : ℤ) s) =
      hillAbelianHilbertPeriod q hq hr n k a+(m : ℂ)*s*
        hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianRootSlope n m E a) := by
  have hP (b : Coeff 2) : hillAbelianHilbertPeriod q hq hr n k b =
      hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianHilbertPsi n (E,b)) := rfl
  rw [hP,hP]
  simp_rw [hillAbelianHilbertPsi_add_single n m hm hmn]
  have hN : AnalyticOnNhd ℂ (fun E => hillAbelianHilbertPsi n (E,a)) univ := by
    intro E _
    exact (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  rw [hillIntrinsicGapPeriod_add q hq hr k hk _ _ hN
    (analyticOnNhd_const.mul (analyticOnNhd_hillAbelianRootSlope n m a)),
    hillIntrinsicGapPeriod_const_mul]

theorem hasDerivAt_hillAbelianHilbertPeriod_single
    (n m k : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (hk : 1 ≤ k) (a : Coeff 2) :
    HasDerivAt (fun s : ℂ => hillAbelianHilbertPeriod q hq hr n k (a+lp.single 2 (m : ℤ) s))
      ((m : ℂ)*hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianRootSlope n m E a)) 0 := by
  have he : (fun s : ℂ => hillAbelianHilbertPeriod q hq hr n k (a+lp.single 2 (m : ℤ) s)) =
      (fun s : ℂ => hillAbelianHilbertPeriod q hq hr n k a+(m : ℂ)*s*
        hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianRootSlope n m E a)) := by
    funext s
    exact hillAbelianHilbertPeriod_add_single q hq hr n m k hm hmn hk a s
  rw [he]
  convert! (((hasDerivAt_id (0 : ℂ)).const_mul (m : ℂ)).mul_const
    (hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianRootSlope n m E a))).const_add
      (hillAbelianHilbertPeriod q hq hr n k a) using 1
  simp only [mul_one]

theorem fderiv_hillAbelianHilbertPeriod_single
    (n m k : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (hk : 1 ≤ k) (a : Coeff 2) :
    fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) a (lp.single 2 (m : ℤ) 1) =
      (m : ℂ)*hillIntrinsicGapPeriod q hq hr k (fun E => hillAbelianRootSlope n m E a) := by
  let S := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)
  have hc : HasDerivAt (fun s : ℂ => a+lp.single 2 (m : ℤ) s) (lp.single 2 (m : ℤ) 1) 0 := by
    convert! (S.hasFDerivAt (x := (0 : ℂ))).hasDerivAt.const_add a using 1
  have hf := (analyticOnNhd_hillAbelianHilbertPeriod q hq hr n k hk a (mem_univ _)).differentiableAt
  have hff : HasFDerivAt (hillAbelianHilbertPeriod q hq hr n k)
      (fderiv ℂ (hillAbelianHilbertPeriod q hq hr n k) a) (a+lp.single 2 (m : ℤ) (0 : ℂ)) := by
    simpa only [lp.single_zero,add_zero] using hf.hasFDerivAt
  have hd := hff.comp_hasDerivAt 0 hc
  have hknown := hasDerivAt_hillAbelianHilbertPeriod_single q hq hr n m k hm hmn hk a
  simpa only [lp.single_zero,add_zero] using hd.unique hknown

theorem fderiv_hillAbelianHilbertPeriod_diagonal_ne_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    fderiv ℂ (hillAbelianHilbertPeriod q hq hr n m)
      (hillGapRootHilbertCoordinates q hq hr roots hroots) (lp.single 2 (m : ℤ) 1) ≠ 0 := by
  rw [fderiv_hillAbelianHilbertPeriod_single q hq hr n m m hm hmn hm]
  exact mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega))
    (hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm)

end NLS.KdV
