import NLS.ZakharovShabat.SourcePsiOriginalLimitInjectivity
import NLS.ZakharovShabat.SourcePsiOriginalNormLimit
import NLS.SequenceSpaces.NearbyInverse

/-!
# Convergence and bounds of original Jacobian inverses

At every original real-domain point, the full inverses converge in norm
to the inverse of Q*. A tail bound and finitely many remaining indices
give one bound for all signed indices. The same bound controls the
genuine deleted-space inverse from Corollary 12.8.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceProposition12_9Data.originalFullRootJacobian_bijective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    Function.Bijective (sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1) :=
  (Coeff.deletedJacobianExtension_bijective_iff n _).mpr
    (H.previous.previous.originalJacobian_bijective hD hV t htW ht n)

theorem SourceProposition12_9Data.originalFullRootJacobian_inverse_tendsto
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    Tendsto (fun n : ℤ => Ring.inverse
      (sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1))
      (Filter.comap Int.natAbs atTop)
      (𝓝 (Ring.inverse (sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1))) := by
  let H4 := H.previous.previous.previous.previous.previous
  have hu := ContinuousLinearMap.isUnit_iff_bijective.mpr
    (H4.originalLimitOperator_bijective hW hD hV t.1 htW ht.1 t.1.property
      (RealCoeff.complexCLM p t.2) ht.2 (fun k => by simp))
  have hc : ContinuousAt Ring.inverse (sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1) := by
    simpa only [hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  exact hc.tendsto.comp (H4.originalFullRootJacobian_tendsto hW hD hV t.1 htW ht.1 t.1.property
    (RealCoeff.complexCLM p t.2) ht.2 (fun k => by simp))

theorem SourceProposition12_9Data.originalFullRootJacobian_inverse_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ,
      ‖Ring.inverse (sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)‖ ≤ M := by
  classical
  let R (n : ℤ) := Ring.inverse (sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1)
  let S := Ring.inverse (sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1)
  obtain ⟨K,hK⟩ := (Coeff.tendsto_operator_natAbs_iff R S).mp
    (H.originalFullRootJacobian_inverse_tendsto hW hD hV t htW ht) 1 zero_lt_one
  let head : Finset ℤ := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let B : ℝ := ∑ n ∈ head, ‖R n‖
  refine ⟨max B (‖S‖+1),le_max_of_le_right (by positivity),?_⟩
  intro n
  by_cases hn : K ≤ n.natAbs
  · have hb : ‖R n‖ ≤ ‖S‖+1 := by
      have htri := norm_le_norm_sub_add (R n) S
      linarith [hK n hn]
    exact hb.trans (le_max_right _ _)
  · have hnhead : n ∈ head := by
      simp only [head,Finset.mem_Icc]
      omega
    exact (Finset.single_le_sum (fun k _ => norm_nonneg (R k)) hnhead).trans (le_max_left _ _)


theorem SourceProposition12_9Data.originalFullRootJacobian_inverse_identities
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) (n : ℤ) :
    let Q := sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1
    Q.comp (Ring.inverse Q) = ContinuousLinearMap.id ℂ (Coeff p) ∧
      (Ring.inverse Q).comp Q = ContinuousLinearMap.id ℂ (Coeff p) := by
  dsimp only
  have hu := ContinuousLinearMap.isUnit_iff_bijective.mpr
    (H.originalFullRootJacobian_bijective hD hV t htW ht n)
  exact ⟨Ring.mul_inverse_cancel _ hu,Ring.inverse_mul_cancel _ hu⟩

theorem SourceProposition12_9Data.originalRootJacobian_inverse_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ,
      ‖(H.previous.previous.originalJacobianEquiv hD hV t htW ht n).symm.toContinuousLinearMap‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := H.originalFullRootJacobian_inverse_bound hW hD hV t htW ht
  refine ⟨M,hM,?_⟩
  intro n
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1
  let e := H.previous.previous.originalJacobianEquiv hD hV t htW ht n
  let S := e.symm.toContinuousLinearMap
  have hQS : Q.comp S = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have heq : Coeff.deletedOperatorExtension n (1/2:ℂ) S =
      Ring.inverse (sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1) := by
    apply ContinuousLinearMap.ext
    intro x
    apply (H.originalFullRootJacobian_bijective hD hV t htW ht n).1
    have hleft := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x)
      (Coeff.deletedJacobianExtension_inverse_comp n Q S hQS)
    have hright := congrArg (fun A : Coeff p →L[ℂ] Coeff p => A x)
      (H.originalFullRootJacobian_inverse_identities hD hV t htW ht n).1
    exact hleft.trans hright.symm
  calc
    ‖S‖ ≤ ‖Coeff.deletedOperatorExtension n (1/2:ℂ) S‖ := Coeff.norm_deletedOperator_le_norm_extension n _ S
    _ ≤ M := by rw [heq]; exact hbound n

end NLS.ZakharovShabat
