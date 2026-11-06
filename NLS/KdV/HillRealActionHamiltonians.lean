import NLS.KdV.HillRealActionDifferential
import NLS.Fourier.UnitCurveConjugation

/-! # Real symmetry of the actual physical action Hamiltonians

The actual real action differential commutes with physical conjugation.
Applying the weak Hamiltonian identity to the verified unit-wave tests
therefore proves conjugate symmetry of every even Fourier coefficient.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

/-- Every actual weak action Hamiltonian vector is a real physical
potential direction, at arbitrary closed-gap sources. -/
theorem IsHillHamiltonianDirection.isReal_of_action_matching
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 n 0:ℂ))
    (v : Coeff 2) (hv : IsHillHamiltonianDirection (SpectralWeight.one.toCoeff q) A v) :
    IsRealHillPotential v := by
  let J : ℤ → Coeff 2 := fun k => Coeff.periodDouble
    (unitCurveCoefficientsCLM ((I*(Real.pi:ℂ)*(2*k:ℤ)) • unitWaveCurve k))
  let D := fderiv ℂ A (SpectralWeight.one.toCoeff q)
  have hJ (k : ℤ) : J (-k)=star (Coeff.reflection (J k)) := by
    dsimp only [J]
    rw [← periodDouble_unitCurveCoefficientsCLM_star,star_unitWaveCurve_derivative]
  have hD (k : ℤ) : D (J (-k))=conj (D (J k)) := by
    rw [hJ]
    exact fderiv_hillRealAction_conjugate_direction q hq hr n A hA hmatch (J k) (Coeff.periodDouble_mem _)
  have hmode (k : ℤ) : v (2*k)= -D (J (-k)) := by
    have h := hv.2.2 (unitWaveCurve (-k)) ((I*(Real.pi:ℂ)*(2*(-k):ℤ)) • unitWaveCurve (-k))
      (absolutelyContinuousOnInterval_unitWaveCurve (-k)) (ae_deriv_extend_unitWaveCurve (-k))
      (unitWaveCurve_endpoints (-k)) (unitWaveCurve_derivative_endpoints (-k))
    rw [hillPhysicalCurvePairing_unitWaveCurve_even v hv.1 k] at h
    exact h
  intro k
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,show -(2*(k/2))=2*(-(k/2)) by ring,hmode,hmode,neg_neg]
    have hc := hD (-(k/2))
    rw [neg_neg] at hc
    rw [hc,map_neg]
  · have hn : (-k)%2≠0 := by omega
    rw [(Coeff.mem_paritySubspace 0 v).mp hv.1 (-k) (by simpa using hn),
      (Coeff.mem_paritySubspace 0 v).mp hv.1 k (by simpa using hk),map_zero]

/-- The literal normalized action contour tangent preserves the real
physical source space, with no gap-opening assumption. -/
theorem hillL2TracePeriodDirection_isReal
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (m : ℕ) (hm : 1≤m) : IsRealHillPotential (hillL2TracePeriodDirection q hq hr m) := by
  exact IsHillHamiltonianDirection.isReal_of_action_matching q hq hr m
    (hillLocalContourAction q hq hr m) (analyticAt_hillLocalContourAction q hq hr m hm).differentiableAt
    (hillLocalContourAction_eventually_eq_physical q hq hr m hm) _
    (hillL2TracePeriodDirection_is_action_hamiltonian q hq hr m hm _
      (analyticAt_hillLocalContourAction q hq hr m hm).differentiableAt
      (hillLocalContourAction_eventually_eq_physical q hq hr m hm))

end NLS.KdV
