import NLS.KdV.HillHminusSobolevAbelianSymbols
import NLS.SequenceSpaces.WeightedAnalyticPacketCompact

/-! # The actual full Abelian symbol contributes only a compact derivative

The leading derivative retains the exact weighted own-index eta germ,
multiplied by the SAME full amplitude, midpoint and phase symbol. The
remaining symbol derivative is compact at EVERY complex point of the
native Sobolev neighborhood, for every nonnegative order.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

/-- Actual native weighted eta and full Abelian packets have compact
symbol derivative difference, on ONE open complex neighborhood. -/
theorem exists_sobolev_abelian_symbol_packet_compact_germ (P : HillHminusPsiChart)
    (σ : PeriodOneHminusOne → Coeff ⊤) (U : Set PeriodOneHminusOne) (hU : IsOpen U)
    (hσ : AnalyticOnNhd ℂ σ U) (K : ℝ) (hK : 0≤K) (hσbound : ∀ p∈U, ‖σ p‖≤K)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqU : periodOneSobolevImageInclusion t ht q∈U)
    (heta : ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ F V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧ ‖F p‖≤M ∧
          ∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*
            P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ F E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain∩U ∧ ‖E p‖≤M ∧
          (∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*
            P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) ∧
          (∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*
            P.sourceAbelianSymbolPacket σ (periodOneSobolevImageInclusion t ht p) n) ∧
          IsCompactOperator (fderiv ℂ E p-
            (Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht p))).comp (fderiv ℂ F p)) := by
  obtain ⟨V,hV,hqV,M,F,hM,hF,hdata⟩ := heta
  obtain ⟨W,hW,hqW,hWV,C,E,hC,hE,hEd⟩ := Coeff.exists_analytic_weighted_symbol_packet_compact
    (periodOneSobolevImageInclusion t ht) U hU σ hσ K hK hσbound
    V hV q hqV hqU F hF M hM (fun p hp => (hdata p hp).2.1)
    P.sourceEtaSequence (fun n => (Weight.sobolev t n : ℂ)) (fun p hp => (hdata p hp).2.2)
  refine ⟨W,hW,hqW,C,F,E,hC,hF.mono hWV,hE,?_⟩
  intro p hp
  exact ⟨⟨(hdata p (hWV hp)).1,(hEd p hp).1⟩,(hEd p hp).2.1,
    (hdata p (hWV hp)).2.2,(hEd p hp).2.2⟩

end NLS.KdV.HillHminusPsiChart
