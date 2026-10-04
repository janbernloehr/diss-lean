import NLS.ZakharovShabat.SourcePsiCentralGapBound
import NLS.ZakharovShabat.SourcePsiRefinedActualGapTail
import NLS.SequenceSpaces.FiniteModification

/-! # Refined psi row majorants on every actual complex gap

A finite central correction patches the uniform central bounds to the
refined tail estimates. One source neighborhood works for every finite
exponent above one and at least p/2, and every deleted index. The resulting
row controls both the quotient and off-diagonal chi errors at all selected
indices, including collapsed gaps.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual quotient and chi errors have refined row majorants on
all gaps. The source neighborhood precedes the exponent and both indices;
the sequence norm bound is uniform in the deleted index. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_refined_actualGap_majorants
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r,
          ‖B‖ ≤ M ∧
          (∀ k : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceSingleRootQuotientJointProduct hp hp1 k
              (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B k‖) ∧
          (∀ k : ℤ, k ≠ n → ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ ‖B k‖) := by
  classical
  obtain ⟨Tt,hTt,hφt,htV,K,htail⟩ := hs.exists_local_refined_actualGap_tail_majorants φ hφ
  let F := Finset.Icc (-(K:ℤ)) (K:ℤ)
  obtain ⟨Tc,hTc,hφc,_,C,hC,hcentral⟩ := hs.toSourcePsiIsolatingComplexExtension.exists_local_finiteGap_bounds φ F
  refine ⟨Tt ∩ Tc,hTt.inter hTc,⟨hφt,hφc⟩,fun _ h => htV h.1,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  let H : Coeff r := ⟨fun k => if k ∈ F then (C:ℂ) else 0,
    memℓp_of_eq_outside_finset (lp.memℓp (0 : Coeff r)) F (by intro k hk; simp [hk])⟩
  obtain ⟨M,hM,hrows⟩ := htail r hr hr1 hpr
  refine ⟨2*M+‖H‖,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨Bq,Bc,hBq,hBc,hquot,hchi⟩ := hrows ψ hψ.1 n
  let B := Coeff.magnitude Bq+Coeff.magnitude Bc+Coeff.magnitude H
  have hBpoint (k : ℤ) : ‖B k‖ = ‖Bq k‖+‖Bc k‖+‖H k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,
      Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ ‖Bq k‖+‖Bc k‖+‖H k‖)]
  have hBnorm : ‖B‖ ≤ ‖Bq‖+‖Bc‖+‖H‖ := by
    calc
      ‖B‖ ≤ ‖Coeff.magnitude Bq+Coeff.magnitude Bc‖+‖Coeff.magnitude H‖ := norm_add_le _ _
      _ ≤ ‖Coeff.magnitude Bq‖+‖Coeff.magnitude Bc‖+‖Coeff.magnitude H‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp only [Coeff.norm_magnitude]
  have hhead (k : ℤ) (hk : ¬ K ≤ k.natAbs) : k ∈ F := by
    simp only [F,Finset.mem_Icc]
    omega
  have hHpoint (k : ℤ) (hk : k ∈ F) : ‖H k‖ = C := by
    simp only [H,if_pos hk,Complex.norm_real,Real.norm_of_nonneg hC]
  refine ⟨B,by linarith,?_,?_⟩
  · intro k z hz
    rw [hBpoint]
    by_cases hk : K ≤ k.natAbs
    · exact (hquot k hk z hz).trans (by linarith [norm_nonneg (Bq k),norm_nonneg (Bc k),norm_nonneg (H k)])
    · have hkF := hhead k hk
      rw [hHpoint k hkF]
      exact ((hcentral ψ hψ.2 n k hkF z hz).1).trans (by linarith [norm_nonneg (Bq k),norm_nonneg (Bc k),norm_nonneg (H k)])
  · intro k hkn z hz
    rw [hBpoint]
    by_cases hk : K ≤ k.natAbs
    · exact (hchi k hk hkn z hz).trans (by linarith [norm_nonneg (Bq k),norm_nonneg (Bc k),norm_nonneg (H k)])
    · have hkF := hhead k hk
      rw [hHpoint k hkF]
      exact ((hcentral ψ hψ.2 n k hkF z hz).2 hkn).trans (by linarith [norm_nonneg (Bq k),norm_nonneg (Bc k),norm_nonneg (H k)])

end NLS.ZakharovShabat
