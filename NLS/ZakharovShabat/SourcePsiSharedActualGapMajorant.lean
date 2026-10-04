import NLS.ZakharovShabat.SourcePsiSharedQuotientTail
import NLS.ZakharovShabat.SourcePsiCentralGapBound
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.SequenceSpaces.FiniteModification

/-! # A common quotient majorant on every actual complex gap

A finite central correction patches the shared tail sequence. The resulting
sequence is chosen before every deleted and selected index, so it directly
controls the diagonal as well as arbitrary rows.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual quotient errors on all gaps admit one shared refined
majorant, locally uniformly and on a neighborhood preceding the exponent. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_shared_actualGap_quotient_majorant
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∃ B : Coeff r, ‖B‖ ≤ M ∧
          ∀ n k : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceSingleRootQuotientJointProduct hp hp1 k
              (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B k‖ := by
  classical
  obtain ⟨N,ε,_,Tt,hTt,hφt,htV,Kt,hNKt,htail⟩ := hs.exists_local_shared_quotient_tail_majorant φ hφ
  obtain ⟨Kg,Tg,hTg,hφg,hgap⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ.val
  let K := max Kt Kg
  let F := Finset.Icc (-(K:ℤ)) (K:ℤ)
  obtain ⟨Tc,hTc,hφc,_,C,hC,hcentral⟩ := hs.toSourcePsiIsolatingComplexExtension.exists_local_finiteGap_bounds φ F
  refine ⟨(Tt ∩ Tg) ∩ Tc,(hTt.inter hTg).inter hTc,⟨⟨hφt,hφg⟩,hφc⟩,
    fun _ h => htV h.1.1,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  let H : Coeff r := ⟨fun k => if k ∈ F then (C:ℂ) else 0,
    memℓp_of_eq_outside_finset (lp.memℓp (0 : Coeff r)) F (by intro k hk; simp [hk])⟩
  obtain ⟨M,hM,hrows⟩ := htail r hr hr1 hpr
  refine ⟨M+‖H‖,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨Bt,hBt,hquot⟩ := hrows ψ hψ.1.1
  let B := Coeff.magnitude Bt+Coeff.magnitude H
  have hBpoint (k : ℤ) : ‖B k‖ = ‖Bt k‖+‖H k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  refine ⟨B,(norm_add_le _ _).trans (by simpa only [Coeff.norm_magnitude] using add_le_add hBt (le_refl ‖H‖)),?_⟩
  intro n k z hz
  rw [hBpoint]
  by_cases hk : K ≤ k.natAbs
  · have hkt : Kt ≤ k.natAbs := (le_max_left _ _).trans hk
    have hkg : Kg ≤ k.natAbs := (le_max_right _ _).trans hk
    have hkN : ¬k.natAbs ≤ N := by omega
    obtain ⟨hm,hg⟩ := hgap ψ hψ.1.2 k hkg
    have hzball := sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ k hm hg hz
    have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ.val N ε k := by
      simp only [sourceIsolatingDisc,if_neg hkN]
      exact (mem_ball.mp hzball).trans (by linarith [Real.pi_pos])
    exact (hquot n k hkt z hzdisc).trans (by linarith [norm_nonneg (H k)])
  · have hkF : k ∈ F := by simp only [F,Finset.mem_Icc]; dsimp only [K] at hk ⊢; omega
    have hHk : ‖H k‖ = C := by simp only [H,if_pos hkF,Complex.norm_real,Real.norm_of_nonneg hC]
    rw [hHk]
    exact ((hcentral ψ hψ.2 n k hkF z hz).1).trans (by linarith [norm_nonneg (Bt k)])

end NLS.ZakharovShabat
