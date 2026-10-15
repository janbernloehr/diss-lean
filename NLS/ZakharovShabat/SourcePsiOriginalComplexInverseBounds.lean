import NLS.ZakharovShabat.SourcePsiOriginalInverseLimit
import NLS.ZakharovShabat.SourcePsiOriginalComplexJacobianCharts

/-!
# Common complex inverse bounds near the original real domain

The all-index inverse bound at a real point and the common complex
Lipschitz estimate give actual two-sided inverses on one joint complex
ball, with radius and norm bound independent of the deleted index.
This proves the inverse-bound step of Lemma 12.10, before construction
of a common analytic solution extension.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceProposition12_9Data.originalFullRootJacobian_local_inverse_bound_complex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ n : ℤ,
      ∀ u ∈ ball (RealCoeff.complexCLM p t.2,(t.1:CoeffPair p)) δ,
        ∃ R : Coeff p →L[ℂ] Coeff p,
          (sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2).comp R = ContinuousLinearMap.id ℂ (Coeff p) ∧
          R.comp (sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2) = ContinuousLinearMap.id ℂ (Coeff p) ∧
          ‖R‖ ≤ M := by
  let H4 := H.previous.previous.previous.previous.previous
  obtain ⟨M₀,hM₀,hbound⟩ := H.originalFullRootJacobian_inverse_bound hW hD hV t htW ht
  obtain ⟨r,L,hr,hL,hLip⟩ := H4.originalFullRootJacobian_complex_local_Lipschitz
    t.1 htW (RealCoeff.complexCLM p t.2)
  let ε : ℝ := 1/(2*(M₀+1)*(L+1))
  let δ := min r ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := lt_min hr hε
  refine ⟨δ,2*M₀,hδ,by positivity,?_⟩
  intro n u hu
  let Q := sourcePsiOriginalFullRootJacobian hp hp1 n (RealCoeff.complexCLM p t.2) t.1
  let T := sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2
  have hdiff : ‖Q-T‖ ≤ L*δ := by
    have h := hLip n u (ball_subset_ball (min_le_left _ _) hu)
      (RealCoeff.complexCLM p t.2,t.1) (mem_ball_self hr)
    rw [norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hu)) hL)
  have hnear : ‖Ring.inverse Q‖*‖Q-T‖ ≤ (1/2:ℝ) := by
    calc
      _ ≤ M₀*(L*δ) := mul_le_mul (hbound n) hdiff (norm_nonneg _) hM₀
      _ ≤ (M₀+1)*((L+1)*ε) := by
        gcongr
        · linarith
        · linarith
        · exact min_le_right _ _
      _ = 1/2 := by
        dsimp [ε]
        have hneM : M₀+1 ≠ 0 := by positivity
        have hneL : L+1 ≠ 0 := by positivity
        field_simp [hneM,hneL]
  obtain ⟨R,hTR,hRT,hR⟩ := NLS.exists_inverse_norm_le_two_mul_of_near T Q (Ring.inverse Q)
    (H.originalFullRootJacobian_inverse_identities hD hV t htW ht n).1
    (H.originalFullRootJacobian_inverse_identities hD hV t htW ht n).2 hnear
  exact ⟨R,hTR,hRT,hR.trans (mul_le_mul_of_nonneg_left (hbound n) (by norm_num))⟩


/-- One radius and bound for inverses on the actual deleted complex Banach spaces. -/
theorem SourceProposition12_9Data.originalRootJacobian_local_inverse_bound_complex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ n : ℤ,
      ∀ u ∈ ball (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2),(t.1:CoeffPair p)) δ,
        ∃ R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
          (sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2).comp R = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
          R.comp (sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2) = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
          ‖R‖ ≤ M := by
  let H4 := H.previous.previous.previous.previous.previous
  obtain ⟨M₀,hM₀,hbound⟩ := H.originalRootJacobian_inverse_bound hW hD hV t htW ht
  obtain ⟨r,L,hr,hL,hLip⟩ := H4.originalRootJacobian_allIndex_complex_local_Lipschitz
    t.1 htW (RealCoeff.complexCLM p t.2)
  let ε : ℝ := 1/(2*(M₀+1)*(L+1))
  let δ := min r ε
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hδ : 0 < δ := lt_min hr hε
  refine ⟨δ,2*M₀,hδ,by positivity,?_⟩
  intro n u hu
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)) t.1
  let e := H.previous.previous.originalJacobianEquiv hD hV t htW ht n
  let R₀ := e.symm.toContinuousLinearMap
  have hQR : Q.comp R₀ = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.apply_symm_apply x
  have hRQ : R₀.comp Q = ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    exact e.symm_apply_apply x
  let T := sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2
  have hdiff : ‖Q-T‖ ≤ L*δ := by
    have h : ‖T-Q‖ ≤ L*‖u-(Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2),(t.1:CoeffPair p))‖ := hLip n u (ball_subset_ball (min_le_left _ _) hu)
      (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2),t.1) (mem_ball_self hr)
    rw [norm_sub_rev Q T]
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hu)) hL)
  have hnear : ‖R₀‖*‖Q-T‖ ≤ (1/2:ℝ) := by
    calc
      _ ≤ M₀*(L*δ) := mul_le_mul (hbound n) hdiff (norm_nonneg (Q-T)) hM₀
      _ ≤ (M₀+1)*((L+1)*ε) := by
        gcongr
        · linarith
        · linarith
        · exact min_le_right _ _
      _ = 1/2 := by
        dsimp [ε]
        have hneM : M₀+1 ≠ 0 := by positivity
        have hneL : L+1 ≠ 0 := by positivity
        field_simp [hneM,hneL]
  obtain ⟨R,hTR,hRT,hR⟩ := NLS.exists_inverse_norm_le_two_mul_of_near T Q (R₀)
    hQR hRQ hnear
  exact ⟨R,hTR,hRT,hR.trans (mul_le_mul_of_nonneg_left (hbound n) (by norm_num))⟩


/-- Keep the original source neighborhoods and every original isolating disk
while obtaining one common complex neighborhood of invertibility. -/
theorem SourceProposition12_9Data.original_isolating_neighborhood_inverseBound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceProposition12_9Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (ht : t ∈ sourcePsiOriginalOmega V D) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (RealCoeff.complexCLM p t.2,(t.1:CoeffPair p)) ∈ U ∧
      U ⊆ sourcePsiOriginalRootPlacement D ×ˢ (W ∩ V) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ∀ u ∈ U,
        ∃ R : Coeff p →L[ℂ] Coeff p,
          (sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2).comp R = ContinuousLinearMap.id ℂ (Coeff p) ∧
          R.comp (sourcePsiOriginalFullRootJacobian hp hp1 n u.1 u.2) = ContinuousLinearMap.id ℂ (Coeff p) ∧
          ‖R‖ ≤ M := by
  obtain ⟨δ,M,hδ,hM,hb⟩ := H.originalFullRootJacobian_local_inverse_bound_complex hW hD hV t htW ht
  refine ⟨ball (RealCoeff.complexCLM p t.2,(t.1:CoeffPair p)) δ ∩
    (sourcePsiOriginalRootPlacement D ×ˢ (W ∩ V)),
    isOpen_ball.inter (hD.isOpen_originalRootPlacement.prod (hW.inter hV)),
    ⟨mem_ball_self hδ,ht.2,htW,ht.1⟩,(fun _ hu => hu.2),M,hM,?_⟩
  exact fun n u hu => hb n u hu.1

end NLS.ZakharovShabat
