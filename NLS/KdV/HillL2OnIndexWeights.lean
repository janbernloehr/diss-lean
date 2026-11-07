import NLS.KdV.HillRotatedDiracL2Regularity
import NLS.KdV.HillDiracSpectralTerminal
import NLS.KdV.HillOnIndexCorrectionZeroTail
import NLS.ZakharovShabat.SourceH1DirichletGapWeights

/-! The ACTUAL weights in the Hill on-index correction estimate gain
one index order locally on complex L2 neighborhoods of every real
source. The original auxiliary divisor and periodic gap are retained. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

theorem physicalAbelianMidpointDisplacement_eq_rotated (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (k : ℤ) :
    P.physicalAbelianMidpointDisplacement q k =
      sourceDirichletMidpointDisplacement (by simp) (by norm_num) (P.rotatedDiracSource q) k := by
  rw [P.physicalAbelianMidpointDisplacement_apply,P.physicalDirichletFrequency_eq_rotatedDirichlet]
  simp only [rotatedDiracSource,sourceDirichletMidpointDisplacement_apply,sourceStandardRootMidpoint,
    canonicalPeriodicMidpoint_sourcePhase]

theorem sourcePeriodicGapDisplacement_rotated (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (k : ℤ) :
    sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.rotatedDiracSource q) k =
      sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi q) k := by
  simp only [rotatedDiracSource,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap_sourcePhase]

private theorem real_rotated_H1 (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (P.rotatedDiracL2Lift q))) := by
  rw [P.sobolevSourceInclusion_rotatedDiracL2Lift q hq]
  exact P.isRealType_rotatedDiracSource _ hq hr

private theorem weights_of_H1 (P : HillProductEquationPatch) (r : Coeff 2)
    (hrP : periodOneL2Inclusion r ∈ P.source) (M : ℝ)
    (h : ∀ n : ℕ+, Weight.sobolev 1 ((n : ℕ) : ℤ) *
      (‖sourceDirichletMidpointDisplacement (by simp) (by norm_num)
          (sobolevSourceInclusion (P.rotatedDiracL2Lift r)) ((n : ℕ) : ℤ)‖ +
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
          (sobolevSourceInclusion (P.rotatedDiracL2Lift r)) ((n : ℕ) : ℤ)‖) ≤ M)
    (n : ℕ+) :
    Weight.sobolev 1 ((n : ℕ) : ℤ) *
      (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
          (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖) ≤ M := by
  have hn := h n
  rw [P.sobolevSourceInclusion_rotatedDiracL2Lift r hrP,
    ← P.physicalAbelianMidpointDisplacement_eq_rotated (periodOneL2Inclusion r),
    P.sourcePeriodicGapDisplacement_rotated] at hn
  exact hn

private theorem eventually_phys_source (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.physicalDirichletSource :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (P.physicalDirichletSource_open.mem_nhds hq)

private theorem eventually_rotated_in (P : HillProductEquationPatch) (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ P.source) (V : Set (ScalarDomain 2 × ScalarDomain 2))
    (hV : IsOpen V) (hqV : P.rotatedDiracL2Lift q ∈ V) :
    ∀ᶠ r in 𝓝 q, P.rotatedDiracL2Lift r ∈ V :=
  (P.analytic_rotatedDiracL2Lift q hq).continuousAt.tendsto.eventually (hV.mem_nhds hqV)

theorem exists_local_l2OnIndex_weight_bound (P : HillProductEquationPatch)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ M : ℝ, 0 < M ∧ ∀ r ∈ U, ∀ n : ℕ+,
        Weight.sobolev 1 ((n : ℕ) : ℤ) *
          (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
              (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖) ≤ M := by
  obtain ⟨V,hV,hqV,M,hM,hB⟩ := exists_local_sourceH1Dirichlet_gap_weight_bound
    ⟨P.rotatedDiracL2Lift q,P.real_rotated_H1 q hq.1 hr⟩
  have hall : ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ P.physicalDirichletSource ∧
      ∀ n : ℕ+, Weight.sobolev 1 ((n : ℕ) : ℤ) *
        (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
            (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖) ≤ M :=
    ((P.eventually_phys_source q hq).and (P.eventually_rotated_in q hq.1 V hV hqV)).mono
      (fun r h => ⟨h.1,P.weights_of_H1 r h.1.1 M (hB _ h.2)⟩)
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hall
  exact ⟨U,hU,hqU,fun r hrU => (hUsub hrU).1,M,hM,fun r hrU => (hUsub hrU).2⟩

end NLS.KdV.HillProductEquationPatch
