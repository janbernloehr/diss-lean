import NLS.KdV.HillGlobalRegularAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem continuous_hillRegularAbelianCorrection (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    Continuous (fun p : RealPeriodOneHillPotential => hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C,hC,hmatch⟩ := exists_hillRegularAbelianCorrection_analytic_extension p.val p.property.1 p.property.2 h0q h0r n k hn hk
  let P : RealPeriodOneHillPotential → Coeff 2 := fun q => SpectralWeight.one.toCoeff q.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hc : ContinuousAt (fun q : RealPeriodOneHillPotential => C (P q)) p :=
    ContinuousAt.comp (f := P) hC.continuousAt hP.continuousAt
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)

end NLS.KdV
