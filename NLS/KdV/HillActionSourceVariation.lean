import NLS.KdV.HillLocalContourAction
import NLS.KdV.HillGardnerPeriodDirections
import NLS.KdV.HillRealSourceJetUniqueness

/-! # Universal physical action derivatives and spectral stationarity -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Every differentiable physical action extension has the actual contour
derivative on the original period-one tangent space, including closed gaps. -/
theorem fderiv_hillRealGapAction_extension_apply
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (h : Coeff 2) (hh : h∈Coeff.paritySubspace 0) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) h=
      -(Real.pi : ℂ)⁻¹ * ∮ E in C((hillRealGapCenter q hq hr n : ℂ),
        hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n),
        (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q)) h/
          hillEnergyCanonicalRootProduct q hq hr E := by
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillLocalContourAction q hq hr n (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hillLocalContourAction_eventually_eq_physical q hq hr n hn] with p hp hpJ
    exact hp.trans hpJ.symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr C (hillLocalContourAction q hq hr n)
    hC (analyticAt_hillLocalContourAction q hq hr n hn).differentiableAt he h hh]
  exact fderiv_hillLocalContourAction_apply q hq hr n hn h

/-- Actual actions are stationary along all actual trace-gradient directions. -/
theorem fderiv_hillLocalContourAction_gardnerDirection_eq_zero
    (n : ℕ) (hn : 1≤n) (b : ℂ) :
    (fderiv ℂ (hillLocalContourAction q hq hr n) (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  rw [fderiv_hillLocalContourAction_apply q hq hr n hn]
  simp only [fderiv_hillL2Discriminant_gardnerDirection_eq_zero,zero_div]
  simp [circleIntegral]

/-- Normalized trace-period tangents belong to the physical period-one
Fourier tangent space, without a gap-opening hypothesis. -/
theorem hillL2TracePeriodDirection_mem_parity (m : ℕ) (hm : 1≤m) :
    hillL2TracePeriodDirection q hq hr m∈Coeff.paritySubspace 0 := by
  rw [Coeff.mem_paritySubspace]
  intro k hk
  have he := apply_hillL2TracePeriodDirection q hq hr m hm (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k)
  have hz (E : ℂ) : hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E k=0 :=
    (Coeff.mem_paritySubspace 0 _).mp (hillL2DiscriminantGardnerDirection_mem_parity _ E) k hk
  change hillL2TracePeriodDirection q hq hr m k= _ at he
  have hEval (v : Coeff 2) : (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k) v=v k := rfl
  simp only [hEval,hz,zero_div] at he
  simpa [circleIntegral] using he

theorem hillL2TracePeriodDirection_zero (m : ℕ) (hm : 1≤m) :
    hillL2TracePeriodDirection q hq hr m 0=0 := by
  have he := apply_hillL2TracePeriodDirection q hq hr m hm (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0)
  change hillL2TracePeriodDirection q hq hr m 0= _ at he
  have hEval (v : Coeff 2) : (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0) v=v 0 := rfl
  simp only [hEval,hillL2DiscriminantGardnerDirection_zero,zero_div] at he
  simpa [circleIntegral] using he

/-- The actual action derivative vanishes on every normalized contour
tangent. Hamiltonian identification of those tangents remains separate. -/
theorem fderiv_hillLocalContourAction_tracePeriodDirection_eq_zero
    (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    (fderiv ℂ (hillLocalContourAction q hq hr n) (SpectralWeight.one.toCoeff q))
      (hillL2TracePeriodDirection q hq hr m)=0 := by
  rw [apply_hillL2TracePeriodDirection q hq hr m hm]
  simp only [fderiv_hillLocalContourAction_gardnerDirection_eq_zero q hq hr n hn,zero_div]
  simp [circleIntegral]

end NLS.KdV
