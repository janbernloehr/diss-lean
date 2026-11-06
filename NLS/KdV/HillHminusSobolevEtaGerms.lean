import NLS.KdV.HillMiuraSobolevEtaSequence
import NLS.KdV.HillHminusNativeSourceFactors
import NLS.SequenceSpaces.PeriodOneSobolevMiuraInverse

/-! # Stronger analytic germs of the SAME actual rough Hill eta sequence

A genuine stronger analytic Miura germ transfers the canonical weighted
eta theorem to the actual original rough Hill chart. Exact raw agreement
retains the SAME root family, ordinary Dirichlet phase and own-index eta.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

private theorem analytic_sequence_pullback
    {E F P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (D : Set P) (hD : IsOpen D) (q : E) (hqD : L q∈D)
    (U : Set E) (hU : IsOpen U) (hqU : q∈U) (g : E → F) (hga : AnalyticOnNhd ℂ g U)
    (A : Set F) (hA : IsOpen A) (hgqA : g q∈A)
    (B : F → Coeff 2) (hBa : AnalyticOnNhd ℂ B A) (M : ℝ) (hM : 0≤M)
    (hbound : ∀ a∈A, ‖B a‖≤M) (R : P → ℤ → ℂ) (w : ℤ → ℂ)
    (he : ∀ p∈U, g p∈A → L p∈D → ∀ n, B (g p) n=w n*R (L p) n) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ ∃ M : ℝ, ∃ E0 : E → Coeff 2,
      0≤M ∧ AnalyticOnNhd ℂ E0 V ∧ ∀ p∈V, L p∈D ∧ ‖E0 p‖≤M ∧
        ∀ n : ℤ, E0 p n=w n*R (L p) n := by
  let V := (U∩g ⁻¹' A)∩L ⁻¹' D
  have hV : IsOpen V := (hga.continuousOn.isOpen_inter_preimage hU hA).inter
    (hD.preimage L.continuous)
  refine ⟨V,hV,⟨⟨hqU,hgqA⟩,hqD⟩,M,(fun p => B (g p)),hM,?_,?_⟩
  · intro p hp
    exact (hBa (g p) hp.1.2).comp (hga p hp.1.1)
  · intro p hp
    exact ⟨hp.2,hbound (g p) hp.1.2,he p hp.1.1 hp.1.2 hp.2⟩

/-- Actual stronger Miura germs give native weighted eta germs at every
eligible real source. All complex points of the new open neighborhood
retain the original source beta domain and exact own-index coefficients. -/
theorem exists_native_sobolev_eta_germ (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hq : periodOneSobolevImageInclusion t ht q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion t ht q))=
      P.miura.lift (periodOneSobolevImageInclusion t ht q))
    (hlift : ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
        AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.miura.domain ∧
          WeightedCoeff.sobolevToL2 ht (g p)=P.miura.lift (periodOneSobolevImageInclusion t ht p)) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2,
        0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧ ‖E p‖≤M ∧
          ∀ n : ℤ, E p n=(Weight.sobolev t n : ℂ)*
            P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n := by
  obtain ⟨U,hU,hqU,g,hga,hg⟩ := hlift
  have hreal : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht (g q))=
      WeightedCoeff.sobolevToL2 ht (g q) := by
    rw [(hg q hqU).2]
    exact hr
  obtain ⟨A,hA,hgqA,M,hM,hEta⟩ := exists_hillMiuraSobolevEtaSequence_analytic H t ht (g q) hreal
  apply analytic_sequence_pullback (periodOneSobolevImageInclusion t ht)
    P.sourceBetaDomain P.sourceBetaDomain_open q hq U hU hqU g hga A hA hgqA
    (hillMiuraSobolevEtaSequence P.family.roots t ht 1) (hEta 1 (Or.inl rfl)).1 M hM
    (fun a ha => ((hEta 1 (Or.inl rfl)).2 a ha).1)
    (fun p n => P.sourceEtaSequence p n) (fun n => (Weight.sobolev t n : ℂ))
  intro p hp hpA hpD n
  have he := ((hEta 1 (Or.inl rfl)).2 (g p) hpA).2 n
  rw [(hg p hp).2] at he
  rw [P.sourceEtaSequence_apply H (periodOneSobolevImageInclusion t ht p) hpD n]
  exact he

end NLS.KdV.HillHminusPsiChart
