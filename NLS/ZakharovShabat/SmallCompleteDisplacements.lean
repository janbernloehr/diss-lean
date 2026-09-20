import NLS.ZakharovShabat.SmallDisplacementBudgets
import NLS.ZakharovShabat.CompleteParityDisplacementBounds

/-!
# Small tails of complete actual spectral displacements

For each tolerance, actual counted high pairs and actual central parity labels
can be chosen on one open convex potential neighborhood. Their full displacement
norms are bounded and both tails are small at every larger cutoff. No continuity
of the chosen eigenvalue labels is assumed.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞}

/-- Agreement outside a finite set gives exactly the same remaining coefficient tail. -/
theorem Coeff.sub_truncate_eq_of_eq_outside (a b : Coeff p) (s : Finset ℤ)
    (h : ∀ n ∉ s, a n = b n) : a-Coeff.truncate s a = b-Coeff.truncate s b := by
  ext n
  by_cases hn : n ∈ s <;> simp [Coeff.truncate_apply, hn, h]

namespace ZakharovShabat
variable [Fact (1 ≤ p)]

/-- Complete actual parity pairs have bounded full displacements and arbitrarily small local tails. -/
theorem exists_uniform_small_completeDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∃ ξ η : ℤ → ℂ, ∃ h : CompletePeriodicParityPairs hp w ψ N₀ ξ η,
          ‖(⟨_,h.left_displacement⟩ : Coeff p)‖ ≤ R ∧
          ‖(⟨_,h.right_displacement⟩ : Coeff p)‖ ≤ R ∧
          ∀ M : ℕ, N₀ ≤ M →
            ‖(⟨_,h.left_displacement⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) ⟨_,h.left_displacement⟩‖ ≤ ε ∧
            ‖(⟨_,h.right_displacement⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) ⟨_,h.right_displacement⟩‖ ≤ ε := by
  obtain ⟨Nr, hNr, Ur, hor, hcr, hφr, h0r, hroots⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  obtain ⟨Nb, _, Ub, hob, hcb, hφb, h0b, hbudget⟩ := exists_uniform_small_rootDisplacementBudget hp hp1 w φ
    (Real.rpow_pos_of_pos hε p.toReal)
  obtain ⟨Nc, Uc, _, hoc, hcc, hφc, h0c, _, _, hcount⟩ :=
    exists_uniform_periodicCountingData hp (weightedBaseToPair w φ)
  let N := max Nr (max Nb Nc)
  let V := (weightedBaseToPair (p := p) w) ⁻¹' Uc
  have hoV : IsOpen V := hoc.preimage (weightedBaseToPair w).continuous
  have hcV : Convex ℝ V := hcc.linear_preimage ((weightedBaseToPair (p := p) w).restrictScalars ℝ).toLinearMap
  obtain ⟨B, hB, hb⟩ := exists_bound_centralParityLabel_displacements (p := p) hp N
  let s := Finset.Icc (-(N : ℤ)) N
  refine ⟨N, by dsimp [N]; omega, (Ur ∩ Ub) ∩ V, (hor.inter hob).inter hoV,
    (hcr.inter hcb).inter hcV, ⟨⟨hφr, hφb⟩, hφc⟩,
    ⟨⟨h0r, h0b⟩, by simpa [V] using h0c⟩, s.card*B+ε, by positivity, ?_⟩
  intro ψ hψ heven
  obtain ⟨ξ, η, hr, ht⟩ := hroots ψ hψ.1.1
  obtain ⟨hξ, hη⟩ := memℓp_pair_displacements_of_summable_tail hp Nr ξ η (ht Nr le_rfl).1
  obtain ⟨α, β, h, hagree⟩ := exists_completePeriodicParityPairs hp w ψ heven N
    (hcount _ hψ.2 N (by dsimp [N]; omega)) ξ η hξ hη (fun n hn => hr n (by dsimp [N] at hn; omega))
  have htail (M : ℕ) (hM : N ≤ M) :
      ‖(⟨_,h.left_displacement⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) ⟨_,h.left_displacement⟩‖ ≤ ε ∧
      ‖(⟨_,h.right_displacement⟩ : Coeff p)-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) ⟨_,h.right_displacement⟩‖ ≤ ε := by
    have htM := ht M (by dsimp [N] at hM; omega)
    have hm := norm_displacement_tails_le_of_power_sum hp M ξ η hξ hη htM.1 hε.le
      (htM.2.1.trans (hbudget ψ hψ.1.2 M (by dsimp [N] at hM; omega)).le)
    have he (a b : Coeff p) (ha : ∀ n, N < n.natAbs → a n = b n) :
        a-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) a = b-Coeff.truncate (Finset.Icc (-(M : ℤ)) M) b := by
      apply Coeff.sub_truncate_eq_of_eq_outside
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact ha n (by omega)
    rw [he (⟨_,h.left_displacement⟩ : Coeff p) (⟨_,hξ⟩ : Coeff p) (fun n hn => by change α n-_ = ξ n-_; rw [(hagree n hn).1]),
      he (⟨_,h.right_displacement⟩ : Coeff p) (⟨_,hη⟩ : Coeff p) (fun n hn => by change β n-_ = η n-_; rw [(hagree n hn).2])]
    exact hm
  have hlow (n : ℤ) (hn : n ∈ s) := hb _ α β h.central n (by simp only [s, Finset.mem_Icc] at hn; omega)
  refine ⟨α, β, h, ?_, ?_, htail⟩
  · apply (Coeff.norm_le_of_eq_outside_finset (⟨_,h.left_displacement⟩ : Coeff p)
      (⟨_,h.left_displacement⟩-Coeff.truncate s ⟨_,h.left_displacement⟩) s B
      (fun n hn => (hlow n hn).1) (fun n hn => by simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hn, sub_zero])).trans
    exact add_le_add le_rfl (htail N le_rfl).1
  · apply (Coeff.norm_le_of_eq_outside_finset (⟨_,h.right_displacement⟩ : Coeff p)
      (⟨_,h.right_displacement⟩-Coeff.truncate s ⟨_,h.right_displacement⟩) s B
      (fun n hn => (hlow n hn).2) (fun n hn => by simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hn, sub_zero])).trans
    exact add_le_add le_rfl (htail N le_rfl).2

end ZakharovShabat
end NLS
