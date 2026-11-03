import NLS.KdV.HillRootPeriodAffineFormula
import NLS.KdV.HillRootSlopeNonvanishing
import NLS.KdV.HillAbelianComplexPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillAbelianComplexUpdatedPeriod (n m : ℕ) (s : ℂ) (t : Coeff 2 × Coeff 2) : ℂ :=
  hillAbelianComplexPeriod q hq hr n m (hillAbelianRootUpdate m (t.1,s),t.2)

theorem analyticAt_hillAbelianComplexUpdatedPeriod
    (n m : ℕ) (hm : 1 ≤ m) (s : ℂ) (a : Coeff 2) :
    AnalyticAt ℂ (hillAbelianComplexUpdatedPeriod q hq hr n m s) (a,SpectralWeight.one.toCoeff q) := by
  obtain ⟨U,_,hqU,hP⟩ := exists_hillAbelianComplexPeriod_analytic_neighborhood q hq hr n m hm
  have hJ : AnalyticAt ℂ (fun t : Coeff 2 × Coeff 2 => (hillAbelianRootUpdate m (t.1,s),t.2))
      (a,SpectralWeight.one.toCoeff q) := by
    have hR : AnalyticAt ℂ (fun t : Coeff 2 × Coeff 2 => hillAbelianRootUpdate m (t.1,s))
        (a,SpectralWeight.one.toCoeff q) := by
      have hPair : AnalyticAt ℂ (fun t : Coeff 2 × Coeff 2 => (t.1,s)) (a,SpectralWeight.one.toCoeff q) :=
        analyticAt_fst.prod analyticAt_const
      convert! (analyticOnNhd_hillAbelianRootUpdate m (a,s) (mem_univ _)).comp
        (f := fun t : Coeff 2 × Coeff 2 => (t.1,s)) hPair using 1
    exact hR.prod analyticAt_snd
  exact (hP (hillAbelianRootUpdate m (a,s),SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
    (f := fun t : Coeff 2 × Coeff 2 => (hillAbelianRootUpdate m (t.1,s),t.2)) hJ

theorem hillAbelianComplexUpdatedPeriod_at_base
    (n m : ℕ) (hm : 1 ≤ m) (s : ℂ) (a : Coeff 2) :
    hillAbelianComplexUpdatedPeriod q hq hr n m s (a,SpectralWeight.one.toCoeff q) =
      hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s))) := by
  rw [hillAbelianComplexUpdatedPeriod,hillAbelianComplexPeriod_at_base q hq hr n m hm]
  rfl

end NLS.KdV
