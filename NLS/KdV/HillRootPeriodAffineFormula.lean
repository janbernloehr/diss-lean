import NLS.KdV.HillIntrinsicPeriodLinearity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillIntrinsicGapPeriod_rootUpdate_affine
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (a : Coeff 2) (s : ℂ) :
    hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s))) =
      s*hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E a)+
        hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0))) := by
  have he : (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s))) =
      (fun E => s*hillAbelianRootSlope n m E a+
        hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0))) := by
    funext E
    rw [hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E a s,
      hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E a 0]
    ring
  rw [he,hillIntrinsicGapPeriod_add q hq hr m hm _ _
    (analyticOnNhd_const.mul (analyticOnNhd_hillAbelianRootSlope n m a))
    (analyticOnNhd_hillAbelianHilbertPsi_rootUpdate_energy n m a 0),hillIntrinsicGapPeriod_const_mul]

def hillAbelianPeriodRoot (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n m : ℕ) : ℂ :=
  -hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n
      (E,hillAbelianRootUpdate m (hillGapRootHilbertCoordinates q hq hr roots hroots,0)))/
    hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E
      (hillGapRootHilbertCoordinates q hq hr roots hroots))

theorem hillAbelianPeriodRoot_im_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) (n m : ℕ) (hm : 1 ≤ m) :
    (hillAbelianPeriodRoot q hq hr roots hroots n m).im = 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  have ha : star a = a := hillGapRootHilbertCoordinates_star q hq hr roots hroots
  have hu : star (hillAbelianRootUpdate m (a,0)) = hillAbelianRootUpdate m (a,0) := by
    have h := hillAbelianRootUpdate_star m a 0
    simpa only [ha,map_zero] using h.symm
  have hA := hillIntrinsicGapPeriod_im_eq_zero q hq hr m hm (fun E => hillAbelianRootSlope n m E a)
    (fun E => by simpa only [ha] using hillAbelianRootSlope_conj n m E a)
  have hB := hillIntrinsicGapPeriod_im_eq_zero q hq hr m hm
    (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0)))
    (fun E => by simpa only [hu] using hillAbelianHilbertPsi_conj n E (hillAbelianRootUpdate m (a,0)))
  change (-hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,0)))/
    hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E a)).im = 0
  simp [Complex.div_im,hA,hB]

theorem hillAbelianPeriodRoot_period_eq_zero
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n
      (E,hillAbelianRootUpdate m (hillGapRootHilbertCoordinates q hq hr roots hroots,
        hillAbelianPeriodRoot q hq hr roots hroots n m))) = 0 := by
  have hA := hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm
  change hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E
    (hillGapRootHilbertCoordinates q hq hr roots hroots)) ≠ 0 at hA
  rw [hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn,hillAbelianPeriodRoot]
  field_simp
  ring

end NLS.KdV
