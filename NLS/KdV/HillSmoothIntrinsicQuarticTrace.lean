import NLS.KdV.HillSmoothQuarticTraceLimit
import NLS.KdV.HillL2CubicPhysicalPeriods

/-! # Physical KdV energy as the actual intrinsic Arnold and cubic trace -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff
namespace NLS.KdV

/-- The original smooth physical energy is the limit of the partial
intrinsic Arnold and cubic-moment trace, with exact article constants.
There is no finite-gap assumption and no input contour or energy identity. -/
theorem tendsto_intrinsic_Arnold_cubic_trace_Hamiltonian_smooth
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      (((8*((k+1 : ℕ) : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*
        hillHminusRealGapContourMoment (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) ⟨k+1,by omega⟩ 0+
      ((8*((k+1 : ℕ) : ℝ)*Real.pi : ℝ) : ℂ)*
        hillHminusRealGapCubicContourMoment (hillOriginalHminusSource (hillContinuousCoefficients Q))
          (hillOriginalHminusSource_real _ hr) ⟨k+1,by omega⟩)) atTop
      (nhds (classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))) := by
  let p : RealPeriodOneHillPotential := ⟨hillContinuousCoefficients Q,hq,hr⟩
  have hact (k : ℕ) :
      hillHminusRealGapContourMoment (hillOriginalHminusSource p.val)
        (hillOriginalHminusSource_real p.val p.property.2) ⟨k+1,by omega⟩ 0 =
      hillL2RealContourMoment p.val p.property.1 p.property.2 (k+1) 0 := by
    exact (hillHminusRealGapContourMoment_original_source p ⟨k+1,by omega⟩ 0).trans
      (hillL2RealContourMoment_eq_gapIntegral p.val p.property.1 p.property.2 (k+1) (by omega) 0).symm
  have hcubic (k : ℕ) :
      hillHminusRealGapCubicContourMoment (hillOriginalHminusSource p.val)
        (hillOriginalHminusSource_real p.val p.property.2) ⟨k+1,by omega⟩ =
      hillL2RealCubicContourMoment p.val p.property.1 p.property.2 (k+1) :=
    hillHminusRealGapCubicContourMoment_original_source p ⟨k+1,by omega⟩
  apply (tendsto_partial_hillL2Actions_and_cubic_Hamiltonian_smooth Q hq hr hreal hf hp hmean).congr'
  apply Eventually.of_forall
  intro N
  symm
  change (∑ k ∈ Finset.range N,
    (((8*((k+1 : ℕ) : ℝ)^3*Real.pi^3 : ℝ) : ℂ)*
      hillHminusRealGapContourMoment (hillOriginalHminusSource p.val)
        (hillOriginalHminusSource_real p.val p.property.2) ⟨k+1,by omega⟩ 0+
    ((8*((k+1 : ℕ) : ℝ)*Real.pi : ℝ) : ℂ)*
      hillHminusRealGapCubicContourMoment (hillOriginalHminusSource p.val)
        (hillOriginalHminusSource_real p.val p.property.2) ⟨k+1,by omega⟩)) = _
  simp_rw [hact,hcubic]
  apply Finset.sum_bij (fun k _ => k+1)
  · intro k hk
    simp only [Finset.mem_range] at hk
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro k _ l _ heq
    omega
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact ⟨n-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro k _
    rfl

end NLS.KdV
