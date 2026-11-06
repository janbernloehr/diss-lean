import NLS.KdV.HillHminusSobolevEtaGerms
import NLS.SequenceSpaces.WeightedAnalyticPacket

/-! # Actual Abelian symbol packets in stronger Sobolev norms

Native bounded analytic symbols multiply the SAME actual own-index eta
sequence. Exact stronger coefficient realizations retain every phase
factor contained in the supplied actual symbol; no amplitude-only
replacement of the Abelian coordinate is made.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

/-- The actual eta sequence multiplied by its native Abelian symbol. -/
def sourceAbelianSymbolPacket (P : HillHminusPsiChart)
    (σ : PeriodOneHminusOne → Coeff ⊤) (q : PeriodOneHminusOne) : Coeff 2 :=
  Coeff.holderProduct (q := 2) (σ q) (P.sourceEtaSequence q)

@[simp] theorem sourceAbelianSymbolPacket_apply (P : HillHminusPsiChart)
    (σ : PeriodOneHminusOne → Coeff ⊤) (q : PeriodOneHminusOne) (n : ℤ) :
    P.sourceAbelianSymbolPacket σ q n=σ q n*P.sourceEtaSequence q n := rfl

/-- The actual rough packet is analytic with its full native symbol. -/
theorem analyticOnNhd_sourceAbelianSymbolPacket (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (σ : PeriodOneHminusOne → Coeff ⊤) (U : Set PeriodOneHminusOne)
    (hσ : AnalyticOnNhd ℂ σ U) :
    AnalyticOnNhd ℂ (P.sourceAbelianSymbolPacket σ) (P.sourceBetaDomain∩U) := by
  intro q hq
  exact ((Coeff.holderProduct (p := ⊤) (r := 2) (q := 2)).analyticAt_bilinear _).comp₂
    (hσ q hq.2) (P.analytic_sourceEtaSequence H q hq.1)

/-- Exact weighted eta germs give genuine stronger analytic germs of the
SAME full Abelian symbol packet, with one bound before every index. -/
theorem exists_sobolev_abelian_symbol_packet_germ (P : HillHminusPsiChart)
    (σ : PeriodOneHminusOne → Coeff ⊤) (U : Set PeriodOneHminusOne) (hU : IsOpen U)
    (hσ : AnalyticOnNhd ℂ σ U) (K : ℝ) (hK : 0≤K) (hσbound : ∀ p∈U, ‖σ p‖≤K)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqU : periodOneSobolevImageInclusion t ht q∈U)
    (heta : ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧ ‖E p‖≤M ∧
          ∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*
            P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain∩U ∧ ‖E p‖≤M ∧
          ∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*
            P.sourceAbelianSymbolPacket σ (periodOneSobolevImageInclusion t ht p) n := by
  obtain ⟨V,hV,hqV,M,F,hM,hF,hdata⟩ := heta
  obtain ⟨W,hW,hqW,hWV,C,G,hC,hG,hGdata⟩ :=
    Coeff.exists_analytic_weighted_symbol_packet (periodOneSobolevImageInclusion t ht)
      U hU σ hσ K hK hσbound V hV q hqV hqU F hF M hM
      (fun p hp => (hdata p hp).2.1) P.sourceEtaSequence (fun n => (Weight.sobolev t n : ℂ))
      (fun p hp => (hdata p hp).2.2)
  refine ⟨W,hW,hqW,C,G,hC,hG,?_⟩
  intro p hp
  exact ⟨⟨(hdata p (hWV hp)).1,(hGdata p hp).1⟩,(hGdata p hp).2⟩

end NLS.KdV.HillHminusPsiChart
