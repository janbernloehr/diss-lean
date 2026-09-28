import NLS.ZakharovShabat.SourcePsiQuotientDiscMajorant
import NLS.SequenceSpaces.FiniteExponentTail

/-!
# Eventual nonvanishing of the psi regular quotient

The regular quotient differs from one by an `ℓᵖ` disc majorant.
Every fixed `ℓᵖ` majorant has vanishing two-sided coordinate tails,
so the quotient has no zeros on sufficiently distant selected discs.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On a common source neighborhood, the regular quotient is nonzero
throughout every sufficiently distant selected disc. The final cutoff
may depend on the fixed source and root input. -/
theorem exists_local_sourcePsiQuotient_eventually_nonzero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ a : Coeff p,
          ∃ K : ℕ, ∀ m : ℤ, K ≤ m.natAbs →
            ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
              sourceSingleRootQuotientJointProduct hp hp1 m
                (z,(a,ψ)) ≠ 0 := by
  obtain ⟨N,ε,hε,V,hVopen,hφV,K₀,hNK,hmajor⟩ :=
    exists_local_sourcePsiQuotient_lpDiscMajorant hp hp1 φ hφ
  refine ⟨N,ε,hε,V,hVopen,hφV,?_⟩
  intro ψ hψ a
  obtain ⟨B,hB⟩ := hmajor ψ hψ a
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨K₁,hK₁⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr B (by norm_num : (0:ℝ)<1)
  refine ⟨max K₀ K₁,?_⟩
  intro m hm z hz hzero
  have hm₀ : K₀ ≤ m.natAbs := (le_max_left _ _).trans hm
  have hm₁ : K₁ ≤ m.natAbs := (le_max_right _ _).trans hm
  have hdist :
      ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))-1‖ < 1 :=
    (hB m hm₀ z hz).trans_lt (hK₁ m hm₁)
  rw [hzero] at hdist
  norm_num at hdist

end NLS.ZakharovShabat
