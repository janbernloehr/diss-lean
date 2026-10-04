import NLS.ZakharovShabat.SourcePsiRefinedChiTail
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles

/-! # Refined actual psi errors on the moving complex gaps

Uniform midpoint and gap tails place every distant actual segment inside
its free-centered eighth-pi disc. Quotient and chi errors therefore have
their refined sequence bounds on the very segments used by the moment
formulas, with one source neighborhood and one exponent-independent cutoff.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual gap quotient and chi errors have common locally uniform
refined row majorants. The same source domain and cutoff precede every
finite exponent above one and at least p/2. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_refined_actualGap_tail_majorants
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧ ∃ K : ℕ,
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ Bq Bc : Coeff r,
          ‖Bq‖ ≤ M ∧ ‖Bc‖ ≤ M ∧
          (∀ k : ℤ, K ≤ k.natAbs → ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceSingleRootQuotientJointProduct hp hp1 k
              (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖Bq k‖) ∧
          (∀ k : ℤ, K ≤ k.natAbs → k ≠ n → ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ ‖Bc k‖) := by
  obtain ⟨N,ε,_,Tq,hTq,hφq,hqV,Kq,hNKq,hquot⟩ := hs.exists_local_refined_quotient_tail_majorants φ hφ
  obtain ⟨Tc,hTc,hφc,hcV,Kc,hchi⟩ := hs.exists_local_refined_chi_tail_majorants φ hφ
  obtain ⟨Kg,Tg,hTg,hφg,hgap⟩ := exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ.val
  let K := max Kq (max Kc Kg)
  refine ⟨(Tq ∩ Tc) ∩ Tg,(hTq.inter hTc).inter hTg,⟨⟨hφq,hφc⟩,hφg⟩,fun _ h => hqV h.1.1,K,?_⟩
  intro r hr hr1 hpr
  obtain ⟨Mq,hMq,hq⟩ := hquot r hr hr1 hpr
  obtain ⟨Mc,_,hc⟩ := hchi r hr hr1 hpr
  refine ⟨max Mq Mc,hMq.trans (le_max_left _ _),?_⟩
  intro ψ hψ n
  obtain ⟨Bq,hBq,hqpoint⟩ := hq ψ hψ.1.1 n
  obtain ⟨Bc,hBc,hcpoint⟩ := hc ψ hψ.1.2 n
  have hseg (k : ℤ) (hk : K ≤ k.natAbs) :
      sourcePeriodicSegment hp hp1 ψ k ⊆ ball ((Real.pi:ℂ)*k) (Real.pi/8) := by
    have hkg : Kg ≤ k.natAbs := by dsimp only [K] at hk; omega
    obtain ⟨hm,hg⟩ := hgap ψ hψ.2 k hkg
    exact sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ k hm hg
  refine ⟨Bq,Bc,hBq.trans (le_max_left _ _),hBc.trans (le_max_right _ _),?_,?_⟩
  · intro k hk z hz
    have hkq : Kq ≤ k.natAbs := (le_max_left Kq (max Kc Kg)).trans hk
    have hkN : ¬k.natAbs ≤ N := by omega
    apply hqpoint k hkq z
    simp only [sourceIsolatingDisc,if_neg hkN]
    exact (mem_ball.mp (hseg k hk hz)).trans (by linarith [Real.pi_pos])
  · intro k hk hkn z hz
    have hkc : Kc ≤ k.natAbs := by dsimp only [K] at hk; omega
    exact hcpoint k hkc hkn z (ball_subset_closedBall (hseg k hk hz))

end NLS.ZakharovShabat
