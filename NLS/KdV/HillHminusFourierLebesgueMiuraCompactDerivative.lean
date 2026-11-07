import NLS.KdV.HillHminusRetainedFourierLebesgueMiuraGerms
import NLS.SequenceSpaces.PeriodOneFourierLebesgueMiuraInverseCompact

/-! # The actual retained Hill lift has a compact native free derivative remainder

Every genuine native analytic germ of the SAME supplied chart has the
exact free mass inverse principal. The original energy shift remains
literal, and no new inverse or Jacobian bijectivity premise is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem HillHminusMiuraChart.isCompactOperator_fourierLebesgue_lift_derivative_sub_free
    (C : HillHminusMiuraChart) (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))) (hV : IsOpen V)
    (g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
      WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p))
    (hga : AnalyticOnNhd ℂ g V)
    (hdata : ∀ x∈V, periodOneFourierLebesgueImageInclusion s p hs hp x∈C.domain ∧
      ∀ n : ℤ, (g x).val n=C.lift (periodOneFourierLebesgueImageInclusion s p hs hp x) n)
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (hq : q∈V) :
    IsCompactOperator (fderiv ℂ g q-
      (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).symm.toContinuousLinearMap) := by
  let k : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) :=
    WeightedCoeff.ofFinsupp _ _ (Finsupp.single 0 C.energyShift)
  have hsolve (x : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (hx : x∈V) :
      periodOneFourierLebesgueMiura s p hs hp (g x)=x+k := by
    have H := C.image _ (hdata x hx).1
    apply Subtype.ext
    funext n
    have Hn := congrArg (fun a : PeriodOneHminusOne => a.val n) H
    simp only [periodOneMiura_apply,WeightedCoeff.add_val,periodOneL2Inclusion_apply,
      periodOneFourierLebesgueImageInclusion_apply] at Hn
    simpa only [periodOneFourierLebesgueMiura_apply,WeightedCoeff.add_val,(hdata x hx).2,
      k,WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply,
      show (0 : ℤ)=n ↔ n=0 from eq_comm,mul_assoc] using Hn
  exact isCompactOperator_fderiv_fourierLebesgueMiura_rightInverse_sub_free s p hs hp g q k
    (hga q hq).differentiableAt (Filter.eventuallyEq_of_mem (hV.mem_nhds hq) hsolve)

/-- The actual chosen chart retains native analytic lift germs with
compact free derivative remainder at EVERY point of their open domains. -/
theorem HillHminusPsiChart.exists_native_fourierLebesgue_compact_Miura_lift
    (P : HillHminusPsiChart) (hstrong : HasAllNativeMiuraGerms P)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hq : periodOneFourierLebesgueImageInclusion s p hs hp q∈P.miura.domain) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
        WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
        AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
          (periodOneFourierLebesgueImageInclusion s p hs hp x∈P.miura.domain ∧
            ∀ n : ℤ, (g x).val n=P.miura.lift (periodOneFourierLebesgueImageInclusion s p hs hp x) n) ∧
          IsCompactOperator (fderiv ℂ g x-
            (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).symm.toContinuousLinearMap) := by
  obtain ⟨V,hV,hqV,g,hga,hdata⟩ := P.exists_fourierLebesgue_native_Miura_lift hstrong s p hs hp q hq
  exact ⟨V,hV,hqV,g,hga,fun x hx => ⟨hdata x hx,
    P.miura.isCompactOperator_fourierLebesgue_lift_derivative_sub_free s p hs hp V hV g hga hdata x hx⟩⟩

end NLS.KdV
