import NLS.KdV.HillEnergyRootIdentification
import NLS.Articles.KdVEstimates.PhysicalIntegerEstimates

/-! # Both integer estimates for the article Arnold actions with the identified energy canonical-root denominator. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
namespace NLS.Articles.KdVEstimates
open NLS.KdV

def sourceArnoldAction
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  ((Real.pi : ℂ)⁻¹ *
    ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
      z * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillEnergyCanonicalRootProduct q hq hr z).re

theorem sourceArnoldAction_eq_gapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    sourceArnoldAction q hq hr n = hillRealGapIntegral q hq hr n 0 := by
  have h := hillL2RealContourMoment_arnold_energyProduct q hq hr n hn 0
  rw [hillL2RealContourMoment_eq_gapIntegral q hq hr n hn 0] at h
  simpa only [sourceArnoldAction,Nat.cast_zero,zero_add,one_mul,pow_one,ofReal_re] using
    congrArg Complex.re h.symm

def sourceArnoldActionMass (M j : ℕ) (p : RealHillWeightedPotential (hillIntegerWeight M)) : ℝ :=
  ∑' k : ℕ, (2*Real.pi*(k+1 : ℕ))^(2*j+1)*
    sourceArnoldAction (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) (k+1)

theorem sourceArnoldActionMass_eq_native (M j : ℕ) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    sourceArnoldActionMass M j p = hillNativeActionMass M j p := by
  have he (k : ℕ) := sourceArnoldAction_eq_gapIntegral
    (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
    (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
    (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) (k+1) (by omega)
  simpa only [sourceArnoldActionMass,he] using (hasSum_hillNativePositiveActions M j hj p).tsum_eq

theorem theorem2_arnold (m : ℕ) (hm : 1 ≤ m) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0 = 0 →
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      (sourceArnoldActionMass m m p ≤ c^2*(‖p.val‖^2+(1+‖b.val‖)^(2*m)*‖b.val‖^2)) ∧
      (‖p.val‖^2 ≤ d^2*(sourceArnoldActionMass m m p+
        (1+sourceArnoldActionMass m (m-1) p)^m*sourceArnoldActionMass m (m-1) p)) := by
  obtain ⟨c,d,hc,hd,hbound⟩ := theorem2_native m hm
  refine ⟨c,d,hc,hd,?_⟩
  intro p hp
  simpa only [sourceArnoldActionMass_eq_native m m le_rfl,
    sourceArnoldActionMass_eq_native m (m-1) (by omega)] using hbound p hp

end NLS.Articles.KdVEstimates
