import NLS.KdV.HillHminusNativeSourceFactors
import NLS.KdV.HillHminusMiuraSobolevRegularity
import NLS.KdV.HillHminusOneMiuraRootSymmetry
import NLS.ZakharovShabat.SourceGapWeightedEtaRealNorm
import NLS.ZakharovShabat.SourcePhaseCanonicalRoots
import NLS.SequenceSpaces.PositiveHalfMembership

/-! # Exact eta-gap regularity at arbitrary real rough sources

The original root family and ordinary Dirichlet phase are retained.
No initial strong membership of the rough source is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

theorem norm_sourceEtaSequence_eq_miura_gap (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q) = P.miura.lift q) (j : ℤ) :
    ‖P.sourceEtaSequence q j‖ =
      ‖hillMiuraDiracRight (P.miura.lift q) j-hillMiuraDiracLeft (P.miura.lift q) j‖ := by
  have hreal : IsRealType (CoeffPair.toMax 2 (P.dirichletSource q)) :=
    isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal
      ⟨P.miura.lift q,(periodOneL2Conjugation_fixed_iff _).mp hr⟩)
  rw [P.sourceEtaSequence_apply H q hq]
  have he := H.norm_gapWeightedEta_original_eq_gap (P.dirichletSource q) hq.2 hreal j
  rw [sourcePeriodicGapDisplacement_apply] at he
  change ‖sourceGapWeightedEtaCoordinate (by norm_num) (by norm_num) j P.family.roots 1
    (P.dirichletSource q)‖ = _ at he
  rw [canonicalPeriodicGap] at he
  simp only [dirichletSource] at he
  rw [congrFun (canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) _).1 j,
    congrFun (canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) _).2 j] at he
  exact he

/-- The literal positive eta sequence detects ALL source Sobolev orders
at EVERY real rough source, including non-L2 centers and collapsed gaps. -/
theorem sobolev_iff_positive_eta_mem (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q) = P.miura.lift q)
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
      Memℓp (fun j : ℤ => if 0 < j then
        (Weight.sobolev (s+1) j : ℂ)*P.sourceEtaSequence q j else 0) 2 := by
  let gap := fun j : ℤ => hillMiuraDiracRight (P.miura.lift q) j-hillMiuraDiracLeft (P.miura.lift q) j
  have hreal := (periodOneL2Conjugation_fixed_iff _).mp hr
  have hsource := P.miura.sobolev_iff_real_Dirac_gap_mem q hq.1.1 hreal s hs
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
    (p := 2) (fun j => (Weight.sobolev (s+1) j : ℂ)*gap j) hnorm
  apply hsource.trans (hpos.trans ?_)
  have he (j : ℤ) : ‖(if 0 < j then (Weight.sobolev (s+1) j : ℂ)*gap j else 0)‖ =
      ‖(if 0 < j then (Weight.sobolev (s+1) j : ℂ)*P.sourceEtaSequence q j else 0)‖ := by
    split_ifs
    · rw [norm_mul,norm_mul,P.norm_sourceEtaSequence_eq_miura_gap H q hq hr j]
    · rfl
  exact ⟨fun h => h.mono' (fun j => (he j).symm.le),fun h => h.mono' (fun j => (he j).le)⟩

end NLS.KdV.HillHminusPsiChart
