import NLS.KdV.HillHminusEtaGapRegularity
import NLS.KdV.HillHminusMiuraFourierLebesgueRegularity

/-! # Exact Fourier-Lebesgue regularity of the fixed physical eta sequence -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- The literal positive eta sequence detects ALL source Sobolev orders
at EVERY real rough source, including non-L2 centers and collapsed gaps. -/
theorem fourierLebesgue_iff_positive_eta_mem (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q) = P.miura.lift q)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)] :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) p ↔
      Memℓp (fun j : ℤ => if 0 < j then
        (Weight.sobolev (s+1) j : ℂ)*P.sourceEtaSequence q j else 0) p := by
  let gap := fun j : ℤ => hillMiuraDiracRight (P.miura.lift q) j-hillMiuraDiracLeft (P.miura.lift q) j
  have hreal := (periodOneL2Conjugation_fixed_iff _).mp hr
  have hsource := P.miura.fourierLebesgue_iff_real_Dirac_gap_mem q hq.1.1 hreal s hs p hp h2p
  have hnorm (j : ℤ) : ‖(Weight.sobolev (s+1) (-j) : ℂ)*gap (-j)‖ =
      ‖(Weight.sobolev (s+1) j : ℂ)*gap j‖ := by
    obtain ⟨hl,hu⟩ := hillMiuraCanonicalEndpoints_neg (P.miura.lift q) j
    have hg : gap (-j) = gap j := by
      change canonicalPeriodicRight _ _ _ _ (-j)-canonicalPeriodicLeft _ _ _ _ (-j) = _
      rw [hl,hu]
      change -hillMiuraDiracLeft (P.miura.lift q) j- -hillMiuraDiracRight (P.miura.lift q) j = _
      ring
    rw [Weight.sobolev_neg,hg]
  have hpos := memlp_iff_positive_half_of_norm_neg_eq
    (p := p) (fun j => (Weight.sobolev (s+1) j : ℂ)*gap j) hnorm
  apply hsource.trans (hpos.trans ?_)
  have he (j : ℤ) : ‖(if 0 < j then (Weight.sobolev (s+1) j : ℂ)*gap j else 0)‖ =
      ‖(if 0 < j then (Weight.sobolev (s+1) j : ℂ)*P.sourceEtaSequence q j else 0)‖ := by
    split_ifs
    · rw [norm_mul,norm_mul,P.norm_sourceEtaSequence_eq_miura_gap H q hq hr j]
    · rfl
  exact ⟨fun h => h.mono' (fun j => (he j).symm.le),fun h => h.mono' (fun j => (he j).le)⟩

end NLS.KdV.HillHminusPsiChart
