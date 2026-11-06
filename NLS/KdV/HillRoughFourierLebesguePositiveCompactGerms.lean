import NLS.KdV.HillHminusFourierLebesgueEtaCompactGerms
import NLS.SequenceSpaces.AnalyticSymbolCompactGerm
import NLS.Articles.KdVKdV2Frequencies.PhysicallyOrientedRoughPackets

/-! # Native analytic positive packets of the fixed physical rough map

The complex germ has a uniform native norm bound and strictly positive
support. On the entire real slice it is the original physically oriented
packet with the exact Fourier-Lebesgue weight.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
variable {q0 : PeriodOneHminusOne}

theorem PhysicallyOrientedRoughPacketAt.exists_fourierLebesgue_positive_compact_germ
    (D : PhysicallyOrientedRoughPacketAt q0) (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)]
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hq : periodOneFourierLebesgueImageInclusion s p hs hp q∈ball q0 D.data.radius)
    (hqr : IsRealPeriodOneHminusOne (periodOneFourierLebesgueImageInclusion s p hs hp q)) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ C : ℝ, ∃ G : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) → Coeff (ENNReal.ofReal p),
        0≤C ∧ AnalyticOnNhd ℂ G V ∧
        (∃ σ ν : Coeff ⊤, (∀ n : ℤ, σ n*ν n=1) ∧
          IsCompactOperator (fderiv ℂ G q-
            (Coeff.signChange D.signs).comp
              ((Coeff.holderProduct (q := ENNReal.ofReal p) (D.data.symbol (periodOneFourierLebesgueImageInclusion s p hs hp q))).comp
                (((Coeff.holderProduct (q := ENNReal.ofReal p) σ).comp
                  ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev (s+1))
                    (ENNReal.ofReal p)).toContinuousLinearEquiv.toContinuousLinearMap)).comp
                      (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).symm.toContinuousLinearMap)))) ∧
        ∀ a∈V,
          periodOneFourierLebesgueImageInclusion s p hs hp a∈ball q0 D.data.radius ∧ ‖G a‖≤C ∧
          (∀ j : ℤ, j≤0 → G a j=0) ∧
          (IsRealPeriodOneHminusOne (periodOneFourierLebesgueImageInclusion s p hs hp a) →
            ∀ j : ℤ, G a j=(Weight.sobolev (s+1) j : ℂ)*
              D.positive (periodOneFourierLebesgueImageInclusion s p hs hp a) j) := by
  let L := periodOneFourierLebesgueImageInclusion s p hs hp
  obtain ⟨U,hU,hqU,M,E,hM,hEa,⟨σ,ν,hσν,hEc⟩,hE⟩ := D.data.chart.exists_native_fourierLebesgue_eta_compact_germ
    D.data.roots D.data.native_lifts D.data.real_lift s p hs hp q (D.data.source_domain hq) hqr
  let C := D.data.symbol_upper*M
  have hC : 0≤C := mul_nonneg D.data.upper_pos.le hM
  obtain ⟨V,hV,hqV,G,hGa,hGc,hG⟩ := Coeff.analytic_symbol_packet_compact_germ_properties ENNReal.ofReal_ne_top
    L (ball q0 D.data.radius) isOpen_ball q hq U hU hqU D.data.symbol D.data.symbol_analytic E hEa
    (((Coeff.holderProduct (q := ENNReal.ofReal p) σ).comp
      ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev (s+1))
        (ENNReal.ofReal p)).toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).symm.toContinuousLinearMap) hEc
    (Coeff.signChange D.signs)
    (fun a g => L a∈ball q0 D.data.radius ∧ ‖g‖≤C ∧ (∀ j : ℤ, j≤0 → g j=0) ∧
      (IsRealPeriodOneHminusOne (L a) → ∀ j : ℤ,
        g j=(Weight.sobolev (s+1) j : ℂ)*D.positive (L a) j)) (by
      intro a ha haB
      refine ⟨haB,?_,?_,?_⟩
      · rw [Coeff.norm_signChange]
        exact (Coeff.norm_holderProduct_le _ _).trans
          (mul_le_mul (D.data.symbol_data (L a) haB).1 (hE a ha).2.1
            (norm_nonneg _) D.data.upper_pos.le)
      · intro j hj
        simp only [Coeff.signChange_apply,Coeff.holderProduct_apply,
          ((D.data.symbol_data (L a) haB).2.2.1 j hj).1,zero_mul,neg_zero,ite_self]
      · intro har j
        have hpacket : D.data.packet (L a) j=D.data.symbol (L a) j*D.data.chart.sourceEtaSequence (L a) j := by
          rw [(D.data.packet_data (L a) haB).1]
          rfl
        change Coeff.signChange D.signs (Coeff.holderProduct (q := ENNReal.ofReal p)
          (D.data.symbol (L a)) (E a)) j=(Weight.sobolev (s+1) j : ℂ)*
            Coeff.signChange D.signs (D.data.packet (L a)) j
        rw [Coeff.signChange_apply,Coeff.signChange_apply,Coeff.holderProduct_apply,
          (hE a ha).2.2 har j,hpacket]
        cases D.signs j <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring)
  exact ⟨V,hV,hqV,C,G,hC,hGa,⟨σ,ν,hσν,hGc⟩,hG⟩

end NLS.Articles.KdVKdV2Frequencies
