import NLS.KdV.HillEnergyCriticalProduct

/-! # The exact energy critical zero set and uniqueness in every open or closed Hill gap. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem hillEnergyCriticalProduct_eq_zero_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    hillEnergyCriticalProduct q hq hr z = 0 ↔ ∃ k : ℕ, (hillGapCriticalPoint q hq hr (k+1) : ℂ) = z := by
  have h := tprod_one_add_ne_zero_iff (fun k => hillEnergyCriticalFactor q hq hr (k+1) z-1)
    (summable_norm_hillEnergyCriticalFactor_sub_one q hq hr z)
  have he (k : ℕ) : 1+(hillEnergyCriticalFactor q hq hr (k+1) z-1) = hillEnergyCriticalFactor q hq hr (k+1) z := by ring
  simp only [he] at h
  have hzero : hillEnergyCriticalProduct q hq hr z = 0 ↔ ∃ k : ℕ, hillEnergyCriticalFactor q hq hr (k+1) z = 0 := by
    simpa only [hillEnergyCriticalProduct,not_forall,not_not] using not_congr h
  rw [hzero]
  apply exists_congr
  intro k
  have hd : (freeHillValue (k+1 : ℕ) : ℂ) ≠ 0 := by
    apply ofReal_ne_zero.mpr
    unfold freeHillValue
    exact mul_ne_zero (pow_ne_zero _ Real.pi_ne_zero) (pow_ne_zero _ (by exact_mod_cast (show (k+1 : ℤ) ≠ 0 by omega)))
  simp only [hillEnergyCriticalFactor,div_eq_zero_iff,hd,or_false,sub_eq_zero]

theorem hillL2Discriminant_critical_iff_gapCriticalPoint
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z = 0 ↔
      ∃ k : ℕ, (hillGapCriticalPoint q hq hr (k+1) : ℂ) = z := by
  rw [hillL2Discriminant_derivative_eq_energyCriticalProduct,neg_eq_zero]
  exact hillEnergyCriticalProduct_eq_zero_iff q hq hr z

theorem hillL2Discriminant_critical_unique_in_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (x : ℂ) = 0 ↔ x = hillGapCriticalPoint q hq hr n := by
  constructor
  · intro hcrit
    obtain ⟨k,hk⟩ := (hillL2Discriminant_critical_iff_gapCriticalPoint q hq hr x).mp hcrit
    have he : hillGapCriticalPoint q hq hr (k+1) = x := ofReal_injective hk
    have hg := (hillGapCriticalPoint_spec q hq hr (k+1) (by omega)).1
    rcases lt_trichotomy (k+1) n with hlt | heq | hgt
    · have hb := hillRealLabels_band_strict q hq hr (k+1)
      have hm := monotone_hillRealLabels q hq hr (by omega : 2*(k+1)+1 ≤ 2*n-1)
      linarith [hg.2,hx.1]
    · simpa only [heq] using he.symm
    · have hb := hillRealLabels_band_strict q hq hr n
      have hm := monotone_hillRealLabels q hq hr (by omega : 2*n+1 ≤ 2*(k+1)-1)
      linarith [hg.1,hx.2]
  · intro he
    rw [he]
    exact (hillGapCriticalPoint_spec q hq hr n hn).2


end NLS.KdV
