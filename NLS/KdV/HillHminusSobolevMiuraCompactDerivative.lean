import NLS.KdV.HillHminusNativeSobolevMiuraLift
import NLS.SequenceSpaces.PeriodOneMiuraInverseCompact

/-! # Compact derivatives of the SAME actual Hill Miura lift

For ANY actual Hill chart, every genuine native analytic lift germ has
free mass inverse principal part and compact derivative remainder. At
EVERY real rough base the existing chart supplies such germs for ALL
orders and eligible complex points, with its original Hill labels intact.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

/-- Compactness of the actual derivative of ANY native analytic germ of
the SAME supplied Hill chart, including the exact energy translation. -/
theorem HillHminusMiuraChart.isCompactOperator_native_lift_derivative_sub_free
    (C : HillHminusMiuraChart) (t : ℝ) (ht : 0≤t)
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2)
    (hga : AnalyticOnNhd ℂ g V)
    (hdata : ∀ p∈V, periodOneSobolevImageInclusion t ht p∈C.domain ∧
      WeightedCoeff.sobolevToL2 ht (g p)=C.lift (periodOneSobolevImageInclusion t ht p))
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (hq : q∈V) :
    IsCompactOperator (fderiv ℂ g q-
      (periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap) := by
  let k : WeightedCoeff (Weight.sobolev (t-1)) 2 :=
    WeightedCoeff.ofFinsupp (Weight.sobolev (t-1)) 2 (Finsupp.single 0 C.energyShift)
  have hsolve (p : WeightedCoeff (Weight.sobolev (t-1)) 2) (hp : p∈V) :
      periodOneSobolevMiura t ht (g p)=p+k := by
    have H := C.image _ (hdata p hp).1
    rw [←(hdata p hp).2] at H
    apply Subtype.ext
    funext n
    have Hn := congrArg (fun a : PeriodOneHminusOne => a.val n) H
    simpa only [periodOneSobolevMiura_apply_toL2,WeightedCoeff.add_val,
      periodOneSobolevImageInclusion_apply,periodOneL2Inclusion_apply,k,
      WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply,
      show (0 : ℤ)=n ↔ n=0 from eq_comm] using Hn
  exact isCompactOperator_fderiv_unshiftedMiura_rightInverse_sub_free t ht g q k
    (hga q hq).differentiableAt (Filter.eventuallyEq_of_mem (hV.mem_nhds hq) hsolve)

/-- At EVERY real rough base, ONE ACTUAL chart and energy shift precede
ALL Sobolev orders and complex native sources. The SAME lift germs now
retain compact derivative remainders at EVERY point of their open domains. -/
theorem exists_hillHminus_real_all_sobolev_compact_Miura_derivatives
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ C : HillHminusMiuraChart, ∃ c : ℝ,
      0<c ∧ C.energyShift=(c : ℂ)^2 ∧ q0∈C.domain ∧
      (∀ q∈C.domain, IsRealPeriodOneHminusOne q → periodOneL2Conjugation (C.lift q)=C.lift q) ∧
      (∀ q∈C.domain, hillHminusRadicand q (-C.energyShift)≠0) ∧
      (∀ q∈C.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (C.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (C.lift q) n).re^2-c^2) ∧
      ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        periodOneSobolevImageInclusion t ht q∈C.domain →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
            AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈C.domain ∧
              WeightedCoeff.sobolevToL2 ht (g p)=C.lift (periodOneSobolevImageInclusion t ht p) ∧
              IsCompactOperator (fderiv ℂ g p-
                (periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap) := by
  obtain ⟨C,c,hc,hshift,hq0,hreal,houtside,hlabels,hstrong⟩ :=
    exists_hillHminus_real_Miura_all_strong_sobolev_chart q0 hr0
  refine ⟨C,c,hc,hshift,hq0,hreal,houtside,hlabels,?_⟩
  intro t ht q hq
  obtain ⟨V,hV,hqV,g,hga,hdata⟩ := hstrong t ht q hq
  exact ⟨V,hV,hqV,g,hga,fun p hp => ⟨(hdata p hp).1,(hdata p hp).2,
    C.isCompactOperator_native_lift_derivative_sub_free t ht V hV g hga hdata p hp⟩⟩

end NLS.KdV
