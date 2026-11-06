import NLS.KdV.HillActionHamiltonianDirections
import NLS.Fourier.UnitWaveCurves
import NLS.Fourier.CircleUnitCoefficients

/-! # Uniqueness of physical weak Gardner Hamiltonian directions

Unit Fourier waves belong to the periodic test class. Their actual physical
pairings recover every even coefficient, so the weak identity uniquely
determines a period-one L2 Hamiltonian tangent.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis NLS.Fourier
namespace NLS.KdV

/-- The source derivative has the same physical representative as the
source Fourier synthesis, with the first-order-system sign removed. -/
theorem hillPhysicalDirection_lower_eq_synthesis (h : Coeff 2) :
    (fun x => -(hillPhysicalDirection h).ofLp.2 x)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      circlePullback (l2Synthesis h) := by
  have hr := physicalRestrictionL2_representative (hillFirstOrderDirection h)
  have hn := circle_ae_pullback (Lp.coeFn_neg (l2Synthesis h))
  have hn1 := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1:ℝ)≤2)) hn
  filter_upwards [hr,hn1] with x hx hneg
  have hs := congrArg Prod.snd hx
  change (hillPhysicalDirection h).ofLp.2 x=circlePullback (l2Synthesis (-h)) x at hs
  change circlePullback (-l2Synthesis h) x= -circlePullback (l2Synthesis h) x at hneg
  rw [hs,map_neg,hneg,neg_neg]

/-- These are literal normalized physical Fourier integrals, including
the zero and negative indices. No completeness assumption is supplied. -/
theorem hillPhysicalCurvePairing_unitWaveCurve (h : Coeff 2) (k : ℤ) :
    hillPhysicalCurvePairing (unitWaveCurve (-k)) h=circleUnitCoefficients (l2Synthesis h) k := by
  rw [hillPhysicalCurvePairing_apply,circleUnitCoefficients_apply,periodOneCoefficient,
    ← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_lower_eq_synthesis h,ae_restrict_mem measurableSet_Ioc] with x hx hxi
  rw [hx,extend_unitWaveCurve_of_mem (-k) ⟨hxi.1.le,hxi.2⟩]
  rw [show 2*(-k)=-(2*k) by ring]
  ring

private theorem circleUnitCoefficients_periodDouble (a : Coeff 2) :
    circleUnitCoefficients (l2Synthesis (Coeff.periodDouble a))=a := by
  change periodTwoToUnit (by norm_num) (by simp)
    (l2Synthesis.symm (l2Synthesis (Coeff.periodDouble a)))=a
  rw [LinearIsometryEquiv.symm_apply_apply,periodTwoToUnit_periodDouble]

theorem hillPhysicalCurvePairing_unitWaveCurve_even (h : Coeff 2)
    (hh : h∈Coeff.paritySubspace 0) (k : ℤ) :
    hillPhysicalCurvePairing (unitWaveCurve (-k)) h=h (2*k) := by
  have he : Coeff.periodDouble (Coeff.periodHalve h)=h :=
    (Coeff.periodDouble_periodHalve h).trans ((Coeff.parityProjection_eq_self_iff 0 h).mpr hh)
  conv_lhs => rw [← he]
  rw [hillPhysicalCurvePairing_unitWaveCurve,circleUnitCoefficients_periodDouble]
  rfl

/-- The physical unit-wave pairings separate period-one L2 tangents. -/
theorem eq_of_hillPhysicalCurvePairing_unitWaveCurve_eq (v w : Coeff 2)
    (hv : v∈Coeff.paritySubspace 0) (hw : w∈Coeff.paritySubspace 0)
    (he : ∀ k : ℤ, hillPhysicalCurvePairing (unitWaveCurve (-k)) v=
      hillPhysicalCurvePairing (unitWaveCurve (-k)) w) : v=w := by
  ext k
  by_cases hk : k%2=0
  · have hkd : k=2*(k/2) := by omega
    have hh := he (k/2)
    rw [hillPhysicalCurvePairing_unitWaveCurve_even v hv,hillPhysicalCurvePairing_unitWaveCurve_even w hw] at hh
    simpa only [← hkd] using hh
  · rw [(Coeff.mem_paritySubspace 0 v).mp hv k (by simpa using hk),
      (Coeff.mem_paritySubspace 0 w).mp hw k (by simpa using hk)]

/-- The physical Gardner identity against the full periodic AC test class
with continuous periodic derivative, retaining period-one support and mean. -/
def IsHillHamiltonianDirection (q : Coeff 2) (A : Coeff 2 → ℂ) (v : Coeff 2) : Prop :=
  v∈Coeff.paritySubspace 0 ∧ v 0=0 ∧
    ∀ f g : Curve ℂ, AbsolutelyContinuousOnInterval (extend f) 0 1 →
      deriv (extend f)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend g →
      extend f 0=extend f 1 → extend g 0=extend g 1 →
      hillPhysicalCurvePairing f v=-(fderiv ℂ A q) (Coeff.periodDouble (unitCurveCoefficientsCLM g))

/-- A physical weak Hamiltonian vector is unique; the periodic Fourier
waves and their actual derivatives are proved members of the test class. -/
theorem IsHillHamiltonianDirection.unique {q : Coeff 2} {A : Coeff 2 → ℂ} {v w : Coeff 2}
    (hv : IsHillHamiltonianDirection q A v) (hw : IsHillHamiltonianDirection q A w) : v=w := by
  apply eq_of_hillPhysicalCurvePairing_unitWaveCurve_eq v w hv.1 hw.1
  intro k
  let f := unitWaveCurve (-k)
  let g := (I*(Real.pi:ℂ)*(2*(-k):ℤ)) • f
  exact (hv.2.2 f g (absolutelyContinuousOnInterval_unitWaveCurve (-k))
    (ae_deriv_extend_unitWaveCurve (-k)) (unitWaveCurve_endpoints (-k))
    (unitWaveCurve_derivative_endpoints (-k))).trans
      (hw.2.2 f g (absolutelyContinuousOnInterval_unitWaveCurve (-k))
        (ae_deriv_extend_unitWaveCurve (-k)) (unitWaveCurve_endpoints (-k))
        (unitWaveCurve_derivative_endpoints (-k))).symm

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual contour tangent is the uniquely determined physical action
Hamiltonian vector, including at sources with a closed selected gap. -/
theorem hillL2TracePeriodDirection_is_action_hamiltonian
    (m : ℕ) (hm : 1≤m) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ)) :
    IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) A (hillL2TracePeriodDirection q hq hr m) :=
  ⟨hillL2TracePeriodDirection_mem_parity q hq hr m hm,hillL2TracePeriodDirection_zero q hq hr m hm,
    fun f g hf hfg hfe hge => hillL2TracePeriodDirection_action_hamiltonian_identity q hq hr m hm A hA hmatch f g hf hfg hfe hge⟩

theorem existsUnique_hillRealGapAction_hamiltonian_direction
    (m : ℕ) (hm : 1≤m) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ)) :
    ∃! v : Coeff 2, IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) A v := by
  have hy := hillL2TracePeriodDirection_is_action_hamiltonian q hq hr m hm A hA hmatch
  exact ⟨hillL2TracePeriodDirection q hq hr m,hy,fun _ hv => hv.unique hy⟩

end NLS.KdV
