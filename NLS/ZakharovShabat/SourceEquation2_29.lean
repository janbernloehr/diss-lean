import NLS.ZakharovShabat.SourceProposition12_9
import NLS.ZakharovShabat.SourcePsiOriginalLimitDiagonal
import NLS.ZakharovShabat.SourcePsiOriginalLimitContinuity
import NLS.SequenceSpaces.CompactOperatorTail
import NLS.FunctionalAnalysis.CompactDecomposition

/-!
# Equation (2.29) on the original real domain

The intrinsic Q* has nonzero diagonal entries, an lp diagonal correction
to 2, and one lp reciprocal-distance off-diagonal majorant. These actual
matrix estimates make Q* a compact perturbation of 2I. Full-domain norm
convergence and injectivity are separate remaining steps of Lemma 12.10.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal diagonal and off-diagonal assertions in (2.29). -/
structure SourceEquation2_29Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) : Prop where
  diagonal_nonzero : ∀ m : ℤ,
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m ≠ 0
  diagonal : ∃ S : Coeff p, ∀ m : ℤ,
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m = 2+S m
  offDiagonal : ∃ B : Coeff p, ∀ m k : ℤ, m ≠ k →
    ‖(sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m‖ ≤ ‖B m‖/‖((m-k:ℤ):ℂ)‖

/-- Equation (2.29) for every full original real root input. -/
theorem SourceLemma12_4Data.equation2_29
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0) : SourceEquation2_29Data hp hp1 a φ := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ := H.originalLimitOperator_diagonal_lp hW hD hV φ hφW hφV a
  obtain ⟨S,_,hS⟩ := hb (a,φ) hbase hφ ha haReal
  exact ⟨H.originalLimitOperator_diagonal_ne_zero hD φ hφW hφV hφ a ha haReal,
    ⟨S,hS⟩,H.originalLimitOperator_offDiagonal_majorant hW hD φ hφW hφV hφ a ha⟩

/-- The actual diagonal tends to 2 at both ends of the integer lattice. -/
theorem SourceEquation2_29Data.diagonal_tail
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {φ : CoeffPair p}
    (H : SourceEquation2_29Data hp hp1 a φ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m : ℤ, N ≤ m.natAbs →
      ‖(sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p m 1)) m-2‖ < ε := by
  obtain ⟨S,hS⟩ := H.diagonal
  obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt hp S hε
  refine ⟨N,?_⟩
  intro m hm
  rw [hS m,add_sub_cancel_left]
  exact hN m hm

/-- The original-domain Q* differs from twice the identity by a compact operator. -/
theorem SourceEquation2_29Data.compact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {φ : CoeffPair p}
    (H : SourceEquation2_29Data hp hp1 a φ) :
    IsCompactOperator (sourcePsiOriginalLimitOperator hp hp1 a φ -
      (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) := by
  let Q := sourcePsiOriginalLimitOperator hp hp1 a φ
  have hdiag : IsCompactOperator (Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol Q) -
      (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) := by
    apply Coeff.isCompactOperator_multiplier_sub_smul_id_of_constantTail _ 2
    intro ε hε
    obtain ⟨N,hN⟩ := H.diagonal_tail ε hε
    exact ⟨N,fun m hm => (hN m hm).le⟩
  obtain ⟨B,hB⟩ := H.offDiagonal
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hoff : IsCompactOperator (Coeff.operatorOffDiagonal Q) := by
    apply Coeff.isCompactOperator_offDiagonal_of_tailReciprocalEntries p.conjExponent hp Q B 0 0
    intro m k _ _ hkm
    have he : ‖((m-k:ℤ):ℂ)‖ = |((k-m:ℤ):ℝ)| := by
      rw [Complex.norm_intCast]
      simp only [Int.cast_sub,abs_sub_comm]
    simpa only [he] using hB m k hkm.symm
  have he : Q-(2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p) =
      (Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol Q) -
        (2:ℂ) • ContinuousLinearMap.id ℂ (Coeff p)) + Coeff.operatorOffDiagonal Q := by
    unfold Coeff.operatorOffDiagonal
    abel_nf
  rw [show sourcePsiOriginalLimitOperator hp hp1 a φ = Q from rfl,he]
  exact hdiag.add hoff

/-- Fredholm reduction for the actual full-domain operator; injectivity remains a separate premise. -/
theorem SourceEquation2_29Data.bijective_of_injective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {φ : CoeffPair p}
    (H : SourceEquation2_29Data hp hp1 a φ)
    (hinj : Function.Injective (sourcePsiOriginalLimitOperator hp hp1 a φ)) :
    Function.Bijective (sourcePsiOriginalLimitOperator hp hp1 a φ) :=
  NLS.CompactSpectrum.bijective_of_injective_compact_sub_smul _ (by norm_num : (2:ℂ) ≠ 0) H.compact hinj

/-- The preceding proposition yields (2.29) on every original real Omega. -/
theorem SourceProposition12_9Data.equation2_29
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W)
    (hW : IsOpen W) (hR : realTypeSourceLocus p ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (ht : t ∈ sourcePsiOriginalOmega V D) :
    SourceEquation2_29Data hp hp1 (RealCoeff.complexCLM p t.2) t.1 :=
  H.previous.previous.previous.previous.previous.equation2_29 hW hD hV t.1 (hR t.1.property)
    ht.1 t.1.property (RealCoeff.complexCLM p t.2) ht.2 (fun k => by simp)

/-- Keep the same original W and all preceding data while obtaining (2.29). -/
theorem sourceEquation2_29 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceProposition12_9Data hp hp1 W ∧
      ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
        SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
        ∀ t : realTypeSourceSubmodule p × RealCoeff p, t ∈ sourcePsiOriginalOmega V D →
          SourceEquation2_29Data hp hp1 (RealCoeff.complexCLM p t.2) t.1 := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceProposition12_9 hp hp1
  exact ⟨W,ho,hc,hr,H,fun hD hV t ht => H.equation2_29 ho hr hD hV t ht⟩

end NLS.ZakharovShabat
