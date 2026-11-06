import NLS.KdV.HillL2QuarticCircleAsymptotics
import NLS.KdV.HillL2EnergySquareCircleAsymptotics
import NLS.ComplexAnalysis.UpperReflectionCircleIntegrability
import NLS.ComplexAnalysis.RawQuarticContourCoefficient

/-! # The physical KdV Hamiltonian in the actual quartic Hill contour

The shared actual full-circle squared-primitive expansion supplies the
physical H0 and H1 coefficients. Even powers of its upper/lower normalized
sheets are circle integrable by reflection. The quartic remainder gives an
explicit inverse-frequency contour error, a limit of -H1/4, and recovery
of the physical Hamiltonian after multiplication by -4.

This proves the smooth physical coefficient input in the argument for
source formula (69). Finite-gap contour independence, angle Poisson brackets
and identification of Hamiltonian frequencies remain separate obligations.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis

/-- Even powers are integrable on every positive-radius centered circle; no gap or real crossing is excluded. -/
theorem circleIntegrable_hillL2RealCutPrimitive_even
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (r : ℝ) (hrp : 0 < r) (m : ℕ) :
    CircleIntegrable (fun z => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z ^ (2*m)) 0 r := by
  apply circleIntegrable_of_continuous_upper_reflection _
    ((continuousOn_hillL2RealCutPrimitive_upper q hq hr).pow (2*m)) ?_ r hrp
  intro z hz
  have hs := hillL2RealCutPrimitive_sq_conj q hq hr z hz.ne
  have he := congrArg conj hs
  simp only [map_pow,conj_conj] at he
  have hp := congrArg (fun v : ℂ => v^m) he.symm
  simpa only [Pi.pow_apply,pow_mul,map_pow] using! hp

/-- Counterclockwise quartic contour with the literal source factor 1/(2*pi*i). -/
def hillL2QuarticPeriod (q : Coeff 2) (N : ℕ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ z in C((0 : ℂ),(hillFreeBandFrequency N)^2), hillL2RealCutPrimitive q z ^ 4

/-- Explicit contour error for the physical coefficient -H1/4. -/
theorem exists_hillL2QuarticPeriod_energy_error
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
      ‖hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N +
        classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4‖ ≤ C / hillFreeBandFrequency N := by
  obtain ⟨C,hC,K,hbound⟩ := exists_hillL2Quartic_circle_energy_remainder Q hq hr hreal hf hp hmean
  refine ⟨C,hC,K,?_⟩
  intro N hN
  apply norm_raw_quartic_circle_coefficient_sub_le _ _ _ _ C (hillFreeBandFrequency_pos N) ?_ (hbound N hN)
  simpa only [show 2*2 = (4 : ℕ) by norm_num] using
    circleIntegrable_hillL2RealCutPrimitive_even (hillContinuousCoefficients Q) hq hr
      ((hillFreeBandFrequency N)^2) (sq_pos_of_pos (hillFreeBandFrequency_pos N)) 2

theorem tendsto_hillL2QuarticPeriod_energy_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))) atTop
      (𝓝 (-classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4)) := by
  obtain ⟨C,_,K,hbound⟩ := exists_hillL2QuarticPeriod_energy_error Q hq hr hreal hf hp hmean
  have hlim : Tendsto (fun N => C/hillFreeBandFrequency N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using! tendsto_hillFreeBandFrequency.inv_tendsto_atTop.const_mul C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop K,hlim.eventually (gt_mem_nhds hε)] with N hN hsmall
  rw [dist_eq_norm,neg_div,sub_neg_eq_add]
  exact (hbound N hN).trans_lt hsmall

theorem tendsto_hillL2QuarticPeriod_physicalHamiltonian_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N => (-4 : ℂ)*hillL2QuarticPeriod (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) N) atTop
      (𝓝 (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  have h := (tendsto_hillL2QuarticPeriod_energy_smooth Q hq hr hreal hf hp hmean).const_mul (-4 : ℂ)
  have he : (-4 : ℂ)*(-classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) / 4) =
      classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) := by ring
  simpa only [he] using h

end NLS.KdV
