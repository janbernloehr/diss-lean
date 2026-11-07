import NLS.Articles.KdVPseudomeasures.SourceWienerSpectralL1Bound
import NLS.Articles.KdVPseudomeasures.SourceWienerSobolevSpectralModels
import NLS.SequenceSpaces.PositiveWeightedL1Bound

/-! Theorem 5.2 in the literal original complex Sobolev Wiener source:
both COMPLETE spectral sequences, exact positive indices, and uniform
bounds on EVERY norm ball, with no reality or local-neighborhood premise. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.Articles.KdVPseudomeasures

theorem sourceTheorem5_2_uniform_realizations (N : ℕ) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
        ∃ G M : WeightedCoeff (Weight.sobolev (N:ℝ)) 1,
          (∀ k, G.val k=sourceWienerSobolevGapValues N q k) ∧
          (∀ k, M.val k=sourceWienerSobolevMidpointValues N q hp k) ∧ ‖G‖ ≤ B ∧ ‖M‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := sourceWienerSpectralSequences_uniform_l1 (sourceWienerSobolevWeight N) R
  refine ⟨B,hB,?_⟩
  intro q hq hp
  let Q := sourceWienerSobolevInput N q
  have hQ : ‖Q‖ ≤ R := ((sourceWienerSobolevInput N).norm_map q).le.trans hq
  have hpQ : IsPeriodicDistribution 1 Q.val.toTempered := by rw [sourceWienerSobolevInput_val]; exact hp
  obtain ⟨G,M,hG,hM,hGn,hMn⟩ := hbound Q hQ hpQ
  let e := WeightedCoeff.equalWeightIsometry 1 (sourceWienerSobolevWeight N).toWeight
    (Weight.sobolev (N:ℝ)) (sourceWienerSobolevWeight_eq N)
  refine ⟨e G,e M,?_,?_,(e.norm_map G).le.trans hGn,(e.norm_map M).le.trans hMn⟩
  · intro k
    exact (WeightedCoeff.equalWeightIsometry_apply 1 _ _ _ G k).trans (hG k)
  · intro k
    exact (WeightedCoeff.equalWeightIsometry_apply 1 _ _ _ M k).trans (hM k)

/-- BOTH literal positive-index spectral maps are uniformly bounded in
ell^(N,1) on every bounded subset of the full original complex Wiener source. -/
theorem sourceTheorem5_2 (N : ℕ) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
        Summable (fun n : ℕ+ => Weight.sobolev (N:ℝ) (n:ℤ)*‖sourceWienerSobolevGapValues N q (n:ℤ)‖) ∧
        Summable (fun n : ℕ+ => Weight.sobolev (N:ℝ) (n:ℤ)*‖sourceWienerSobolevMidpointValues N q hp (n:ℤ)‖) ∧
        (∑' n : ℕ+, Weight.sobolev (N:ℝ) (n:ℤ)*‖sourceWienerSobolevGapValues N q (n:ℤ)‖) ≤ B ∧
        (∑' n : ℕ+, Weight.sobolev (N:ℝ) (n:ℤ)*‖sourceWienerSobolevMidpointValues N q hp (n:ℤ)‖) ≤ B := by
  obtain ⟨B,hB,hbound⟩ := sourceTheorem5_2_uniform_realizations N R
  refine ⟨B,hB,?_⟩
  intro q hq hp
  obtain ⟨G,M,hG,hM,hGn,hMn⟩ := hbound q hq hp
  have hg := WeightedCoeff.positive_weighted_l1_bound (Weight.sobolev (N:ℝ)) G
  have hm := WeightedCoeff.positive_weighted_l1_bound (Weight.sobolev (N:ℝ)) M
  have hg' := hg.2.trans hGn
  have hm' := hm.2.trans hMn
  exact ⟨by simpa only [hG] using hg.1,by simpa only [hM] using hm.1,
    by simpa only [hG] using hg',by simpa only [hM] using hm'⟩

/-- In fact the complete signed even extensions belong to the actual
ordinary Sobolev-weighted ell-one target at each original complex potential. -/
theorem sourceTheorem5_2_membership (N : ℕ) (q : FourierLebesgueSpace (2:ℝ) (N:ℝ) 1)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    Memℓp (fun k => (Weight.sobolev (N:ℝ) k:ℂ)*sourceWienerSobolevGapValues N q k) 1 ∧
      Memℓp (fun k => (Weight.sobolev (N:ℝ) k:ℂ)*sourceWienerSobolevMidpointValues N q hp k) 1 := by
  obtain ⟨_,_,hbound⟩ := sourceTheorem5_2_uniform_realizations N ‖q‖
  obtain ⟨G,M,hG,hM,_,_⟩ := hbound q le_rfl hp
  have hg := G.property
  have hm := M.property
  change Memℓp (fun k => (Weight.sobolev (N:ℝ) k:ℂ)*G.val k) 1 at hg
  change Memℓp (fun k => (Weight.sobolev (N:ℝ) k:ℂ)*M.val k) 1 at hm
  exact ⟨by simpa only [hG] using hg,by simpa only [hM] using hm⟩

end NLS.Articles.KdVPseudomeasures
