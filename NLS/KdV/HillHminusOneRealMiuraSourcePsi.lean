import NLS.KdV.HillHminusOneRealMiuraCharts
import NLS.ZakharovShabat.SourcePsiLemma12_11

/-! # Actual normalized NLS psi data on real rough Hill charts

Real-preserving Miura lifts prove the real-type hypothesis of the verified
global NLS theorem. Its common complex source domain pulls back to one
rough-open neighborhood before every deleted index, with actual spectral
placement and exact raw frequency periods retained. Energy descent and
identification with a normalized Hill differential are separate steps.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV
open NLS.ZakharovShabat

theorem exists_hillHminus_real_sourcePsi_data (q0 : PeriodOneHminusOne)
    (hq0 : periodOneHminusConjugation q0 = q0) :
    ∃ C : HillHminusMiuraChart, ∃ V : Set PeriodOneHminusOne, ∃ A W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
        q0 ∈ C.domain ∧ 0 < C.energyShift.re ∧ C.energyShift.im = 0 ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q →
          periodOneL2Conjugation (C.lift q) = C.lift q ∧
            IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) ∧
        IsOpen V ∧ q0 ∈ V ∧ V ⊆ C.domain ∧
        (∀ q ∈ C.domain, periodOneHminusConjugation q = q → q ∈ V) ∧
        SourceSpectralIsolationNeighborhood (by simp) (by norm_num) A ∧
        IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus 2 ⊆ W ∧ W ⊆ A ∧
        SourcePsiNormalizedComplexExtension (by simp) (by norm_num) W s ∧
        (∀ q ∈ V, C.criticalSource q ∈ W) ∧
        (∀ n : ℤ, AnalyticOnNhd ℂ (fun q => s n (C.criticalSource q)) V) ∧
        ∀ q ∈ V, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
          sourcePsiRealCenteredContourFamily (by simp) (by norm_num) (C.criticalSource q) c R ∧
          ∀ n m : ℤ, (∮ z in C(c m,R m),
            sourcePsiContourIntegrandJoint (by simp) (by norm_num) n
              (z,((s n (C.criticalSource q) : Coeff 2),C.criticalSource q))) =
                (2*Real.pi : ℂ)*(if m = n then 1 else 0) := by
  obtain ⟨C,hqC,hshift,hshiftim,hreal⟩ := exists_real_hillHminusMiuraChart q0 hq0
  obtain ⟨A,W,hA,hW,hWconn,hrealW,hWA,s,S⟩ := exists_sourcePsi_lemma12_11
    (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num : 1 < (2 : ENNReal))
  let V := C.domain ∩ C.criticalSource ⁻¹' W
  have hV : IsOpen V := C.analyticOnNhd_criticalSource.continuousOn.isOpen_inter_preimage C.domain_open hW
  have hrealV (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
      (hqr : periodOneHminusConjugation q = q) : q ∈ V :=
    ⟨hq,hrealW (hreal q hq hqr).2⟩
  refine ⟨C,V,A,W,s,hqC,hshift,hshiftim,hreal,hV,hrealV q0 hqC hq0,
    inter_subset_left,hrealV,hA,hW,hWconn,hrealW,hWA,S,fun _ hq => hq.2,?_,?_⟩
  · intro n q hq
    exact (S.analytic n (C.criticalSource q) hq.2).comp
      (C.analyticOnNhd_criticalSource q hq.1)
  · intro q hq
    exact S.raw_contour_orthogonality (C.criticalSource q) hq.2

end NLS.KdV
