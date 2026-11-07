import NLS.Articles.KdVPseudomeasures.WeightedComplexMidpoints

/-! Literal positive-index target of source Theorem2.1(ii), with EXACT
weighted infinity norm equality to the proved even, zero-central extension. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Original positive indices, with the exact source weight inside the
ordinary infinity coefficient norm. No finite block is omitted. -/
theorem sourceWeightedDirichletMidpointPositive_mem (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    Memℓp (fun n : ℕ+ => (w.negativeSobolev r (n:ℤ):ℂ)*
      sourceComplexDirichletMidpoint r hr (sourceForgetWeight w r q)
        (by rw [sourceForgetWeight_val];exact hp) n) ⊤ := by
  apply memℓp_infty
  refine ⟨‖sourceWeightedDirichletMidpoints w r hr q hp‖,?_⟩
  rintro _ ⟨n,rfl⟩
  have hc := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (WeightedCoeff.weightEquiv (w.negativeSobolev r) ⊤ (sourceWeightedDirichletMidpoints w r hr q hp)) (n:ℤ)
  change ‖(w.negativeSobolev r (n:ℤ):ℂ)*(sourceWeightedDirichletMidpoints w r hr q hp).val (n:ℤ)‖ ≤ _ at hc
  rw [sourceWeightedDirichletMidpoints_nat_apply] at hc
  exact hc

/-- The ACTUAL source sequence indexed by positive n in its exact weighted infinity norm. -/
def sourceWeightedDirichletMidpointPositive (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) : lp (fun _ : ℕ+ => ℂ) ⊤ :=
  ⟨fun n => (w.negativeSobolev r (n:ℤ):ℂ)*sourceComplexDirichletMidpoint r hr (sourceForgetWeight w r q)
    (by rw [sourceForgetWeight_val];exact hp) n,sourceWeightedDirichletMidpointPositive_mem w r hr q hp⟩

/-- Even extension with zero at zero preserves the genuine source
weighted infinity norm EXACTLY, rather than only an equivalent norm. -/
theorem norm_sourceWeightedDirichletMidpointPositive (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    ‖sourceWeightedDirichletMidpointPositive w r hr q hp‖ = ‖sourceWeightedDirichletMidpoints w r hr q hp‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro n
    have hc := lp.norm_apply_le_norm ENNReal.top_ne_zero
      (WeightedCoeff.weightEquiv (w.negativeSobolev r) ⊤ (sourceWeightedDirichletMidpoints w r hr q hp)) (n:ℤ)
    change ‖(w.negativeSobolev r (n:ℤ):ℂ)*(sourceWeightedDirichletMidpoints w r hr q hp).val (n:ℤ)‖ ≤ _ at hc
    rw [sourceWeightedDirichletMidpoints_nat_apply] at hc
    exact hc
  · change ‖WeightedCoeff.weightEquiv (w.negativeSobolev r) ⊤ _‖ ≤ _
    apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro k
    change ‖(w.negativeSobolev r k:ℂ)*sourceWeightedDirichletMidpointValues w r hr q hp k‖ ≤ _
    by_cases hk : k = 0
    · subst k
      simp [sourceWeightedDirichletMidpointValues]
    · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩
      have hw : w.negativeSobolev r k = w.negativeSobolev r (n:ℤ) := by
        change w.negativeSobolev r k = w.negativeSobolev r (k.natAbs:ℤ)
        simp only [Int.natCast_natAbs,SpectralWeight.negativeSobolev_apply,
          SpectralWeight.apply_abs,Weight.sobolev_apply,Int.cast_abs,abs_abs]
      rw [sourceWeightedDirichletMidpointValues,dif_neg hk,hw]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (sourceWeightedDirichletMidpointPositive w r hr q hp) n

/-- FULL source Theorem2.1(ii) in its LITERAL original positive-index
target, with the original weight and exact original infinity norm. -/
theorem sourceTheorem2_1_ii_positive (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
      Memℓp (fun n : ℕ+ => (w.negativeSobolev r (n:ℤ):ℂ)*sourceComplexDirichletMidpoint r hr
        (sourceForgetWeight w r q) (by rw [sourceForgetWeight_val];exact hp) n) ⊤) ∧
    ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
        ‖sourceWeightedDirichletMidpointPositive w r hr q hp‖ ≤ C := by
  refine ⟨sourceWeightedDirichletMidpointPositive_mem w r hr,?_⟩
  intro R
  obtain ⟨C,hC,hb⟩ := (sourceTheorem2_1_ii w r hr).2 R
  refine ⟨C,hC,?_⟩
  intro q hq hp
  rw [norm_sourceWeightedDirichletMidpointPositive]
  exact hb q hq hp

/-- Literal locally bounded source map, in the full ORIGINAL weighted
source topology and the EXACT original positive-index weighted infinity norm. -/
theorem sourceWeightedDirichletMidpointPositive_locallyBounded (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : {q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ |
      IsPeriodicDistribution 1 q.val.toTempered}) :
    ∃ U ∈ 𝓝 q, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ U,
      ‖sourceWeightedDirichletMidpointPositive w r hr p.val p.property‖ ≤ C := by
  obtain ⟨U,hU,C,hC,hb⟩ := sourceWeightedDirichletMidpoints_locallyBounded w r hr q
  exact ⟨U,hU,C,hC,fun p hp => by rw [norm_sourceWeightedDirichletMidpointPositive];exact hb p hp⟩

end NLS.Articles.KdVPseudomeasures
