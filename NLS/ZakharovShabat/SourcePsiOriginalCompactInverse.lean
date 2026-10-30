import NLS.ZakharovShabat.SourcePsiOriginalLimitCanonical
import NLS.ZakharovShabat.SourcePsiOriginalLimitRealInverse
import NLS.SequenceSpaces.RealCoeffNorm

/-!
# Uniform original inverse bounds on the compact gap product

The intrinsic limit and every full original Jacobian have two-sided
inverses with a bound uniform over the entire gap product. The real
limit inverse has the same bound under isometric complex inclusion.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One bound controls actual two-sided inverses of the intrinsic original
limit at every root in the full compact gap product. -/
theorem SourceLemma12_4Data.originalLimitOperator_gapUniform_inverse
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ∃ S : Coeff p →L[ℂ] Coeff p,
        (sourcePsiOriginalLimitOperator hp hp1 a.val φ).comp S =
          ContinuousLinearMap.id ℂ (Coeff p) ∧
        S.comp (sourcePsiOriginalLimitOperator hp hp1 a.val φ) =
          ContinuousLinearMap.id ℂ (Coeff p) ∧ ‖S‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := exists_uniform_sourcePsiGapLimitInverse_norm hp hp1 φ hφ
  refine ⟨M,hM,?_⟩
  intro a
  rw [H.originalLimitOperator_eq_gapLimit φ hφW hφ a]
  exact ⟨sourcePsiGapLimitInverse hp hp1 φ hφ a,
    sourcePsiGapLimitOperator_comp_inverse hp hp1 φ hφ a,
    sourcePsiGapLimitInverse_comp_operator hp hp1 φ hφ a,hb a⟩

/-- One bound controls every original full Jacobian inverse, uniformly in
the signed omitted index and the entire compact gap-root product. -/
theorem SourceLemma12_4Data.originalFullRootJacobian_gapUniform_inverse
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφW : φ ∈ W)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ a : sourcePeriodicGapRootSet hp hp1 φ,
      ∃ S : Coeff p →L[ℂ] Coeff p,
        (sourcePsiOriginalFullRootJacobian hp hp1 n a.val φ).comp S =
          ContinuousLinearMap.id ℂ (Coeff p) ∧
        S.comp (sourcePsiOriginalFullRootJacobian hp hp1 n a.val φ) =
          ContinuousLinearMap.id ℂ (Coeff p) ∧ ‖S‖ ≤ M := by
  obtain ⟨K,V,_,hφV,c,R,hc,_,hgeom⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  have hf : sourcePsiRealCenteredContourFamily hp hp1 φ c R := ⟨hc,hgeom φ hφV⟩
  obtain ⟨M,hM,hb⟩ := exists_uniform_sourcePsiGapJacobianInverse_norm hp hp1 φ hφ c R hf
  refine ⟨M,hM,?_⟩
  intro n a
  rw [H.originalFullRootJacobian_eq_selected φ hφW hφ c R hf]
  exact ⟨sourcePsiGapJacobianInverse hp hp1 φ hφ c R hf n a,
    sourcePsiFullRootJacobian_comp_gapInverse hp hp1 φ hφ c R hf n a,
    sourcePsiGapJacobianInverse_comp_fullRootJacobian hp hp1 φ hφ c R hf n a,hb n a⟩

end NLS.ZakharovShabat



namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual real limit inverses share one bound on the whole real
gap product. Complex inclusion preserves the bound with factor one. -/
theorem SourceLemma12_4Data.originalLimitRealOperator_gapUniform_inverse
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W)
    (hφV : (φ:CoeffPair p) ∈ V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : RealCoeff p,
      RealCoeff.complexCLM p a ∈ sourcePeriodicGapRootSet hp hp1 φ →
      ∃ S : RealCoeff p →L[ℝ] RealCoeff p,
        (sourcePsiOriginalLimitRealOperator hp hp1 a φ).comp S =
          ContinuousLinearMap.id ℝ (RealCoeff p) ∧
        S.comp (sourcePsiOriginalLimitRealOperator hp hp1 a φ) =
          ContinuousLinearMap.id ℝ (RealCoeff p) ∧ ‖S‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := H.originalLimitOperator_gapUniform_inverse φ hφW φ.property
  refine ⟨M,hM,?_⟩
  intro a ha
  have hplace : RealCoeff.complexCLM p a ∈ sourcePsiOriginalRootPlacement D :=
    fun m => hD.gap φ hφV m (ha m)
  obtain ⟨S,hQS,_,hS⟩ := hb ⟨RealCoeff.complexCLM p a,ha⟩
  obtain ⟨e,he⟩ := H.exists_originalLimitRealEquiv hW hD hV φ hφW hφV a hplace
  let Q := sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p a) φ
  have hQinj := (H.originalLimitOperator_bijective hW hD hV φ hφW hφV φ.property
    (RealCoeff.complexCLM p a) hplace (fun k => by simp)).1
  have hinc (x : RealCoeff p) : RealCoeff.complexCLM p (e.symm x) = S (RealCoeff.complexCLM p x) := by
    apply hQinj
    calc
      Q (RealCoeff.complexCLM p (e.symm x)) =
          RealCoeff.complexCLM p (sourcePsiOriginalLimitRealOperator hp hp1 a φ (e.symm x)) :=
        (H.originalLimitRealOperator_complex hD φ hφW hφV a hplace (e.symm x)).symm
      _ = RealCoeff.complexCLM p x := by rw [← he]; simp
      _ = Q (S (RealCoeff.complexCLM p x)) := by
        have h := congrArg (fun T : Coeff p →L[ℂ] Coeff p => T (RealCoeff.complexCLM p x)) hQS
        exact h.symm
  refine ⟨e.symm.toContinuousLinearMap,?_,?_,?_⟩
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  · rw [← he]
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  · apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro x
    change ‖e.symm x‖ ≤ M*‖x‖
    rw [← RealCoeff.norm_complexCLM (e.symm x),hinc x]
    exact (S.le_opNorm (RealCoeff.complexCLM p x)).trans
      (by rw [RealCoeff.norm_complexCLM]; exact mul_le_mul_of_nonneg_right hS (norm_nonneg _))

end NLS.ZakharovShabat
