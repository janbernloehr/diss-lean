import NLS.KdV.HillGardnerDeflatedRoot

/-! # Energy variation of the actual filled deflated root -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual radicand factorization differentiates on the filled gap,
including either endpoint and collapsed gaps. -/
theorem hillDeflatedEnergyCanonicalRoot_energy_factor (k : ℕ) (hk : 1≤k)
    (E : ℂ) (hE : E∈hillGapFilledDomain q hq hr k) :
    let p := SpectralWeight.one.toCoeff q
    let τ : ℂ := hillRealGapCenter q hq hr k
    let d : ℂ := hillRealGapHalfLength q hq hr k
    let U := hillDeflatedEnergyCanonicalRoot q hq hr k
    hillL2Discriminant p E*deriv (hillL2Discriminant p) E=
      (E-τ)*(U E)^2+((E-τ)^2-d^2)*U E*deriv U E := by
  let p := SpectralWeight.one.toCoeff q
  let τ : ℂ := hillRealGapCenter q hq hr k
  let d : ℂ := hillRealGapHalfLength q hq hr k
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  have he : (fun z : ℂ => hillL2Radicand p z)=ᶠ[𝓝 E]
      (fun z : ℂ => ((z-τ)^2-d^2)*(U z)^2) := by
    filter_upwards [(isOpen_hillGapFilledDomain q hq hr k).mem_nhds hE] with z hz
    rw [hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr k hk z hz]
    dsimp only [τ,d,hillRealGapCenter,hillRealGapHalfLength,U]
    push_cast
    ring
  have hΔ := (analyticOnNhd_hillL2Discriminant p E (mem_univ _)).differentiableAt.hasDerivAt
  have hU := (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k E hE).differentiableAt.hasDerivAt
  have hL : HasDerivAt (hillL2Radicand p) (2*hillL2Discriminant p E*deriv (hillL2Discriminant p) E) E := by
    change HasDerivAt (fun z : ℂ => hillL2Discriminant p z^2-4) _ E
    simpa only [Pi.pow_apply,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one] using
      (hΔ.pow 2).sub_const 4
  have hR := ((((hasDerivAt_id E).sub_const τ).pow 2).sub_const (d^2)).mul (hU.pow 2)
  have hv := (hL.congr_of_eventuallyEq he.symm).unique hR
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.add_one_sub_one,pow_one,mul_one] at hv
  change hillL2Discriminant p E*deriv (hillL2Discriminant p) E=_
  linear_combination hv/2

/-- The local complex extension and the canonical root have the same
energy derivative at the physical base, throughout the intrinsic ball. -/
theorem deriv_hillLocalDeflatedComplexRoot_base (k : ℕ) (hk : 1≤k) (E : ℂ)
    (hE : E∈ball (hillRealGapCenter q hq hr k : ℂ)
      (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)) :
    deriv (fun z : ℂ => hillLocalDeflatedComplexRoot q hq hr k (z,SpectralWeight.one.toCoeff q)) E=
      deriv (hillDeflatedEnergyCanonicalRoot q hq hr k) E := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_ball.mem_nhds hE] with z hz
  exact hillLocalDeflatedComplexRoot_base q hq hr k hk z hz

end NLS.KdV
