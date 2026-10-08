import NLS.ZakharovShabat.M1GapGlobalBudget

/-! # The global weighted gap estimate for real potentials

This proves the second inequality of Proposition 25.5 on the real potential
space. Extending the central estimate to an open complex neighborhood remains
a separate geometric step; the conditional combination theorem exposes it.
-/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- A summable signed tail gives a summable full sequence and an exact finite/tail split. -/
theorem sum_eq_central_add_tail (f : ℤ → ℝ) (N : ℕ)
    (ht : Summable (fun n : ℤ => if N ≤ n.natAbs then f n else 0)) :
    Summable f ∧ (∑' n, f n) = (∑ n ∈ Finset.Ioo (-(N:ℤ)) N, f n)+
      (∑' n : ℤ, if N ≤ n.natAbs then f n else 0) := by
  let s := Finset.Ioo (-(N:ℤ)) N
  let g : ℤ → ℝ := fun n => if n ∈ s then f n else 0
  have hg : HasSum g (∑ n ∈ s, f n) := by
    convert hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℤ) (s := s) (f := g)
      (fun n hn => by simp [g,hn]) using 1
    exact Finset.sum_congr rfl (fun n hn => by simp [g,hn])
  have he : f = fun n => g n+(if N ≤ n.natAbs then f n else 0) := by
    funext n
    have hm : n ∈ s ↔ n.natAbs < N := by simp only [s,Finset.mem_Ioo]; omega
    by_cases hn : N ≤ n.natAbs <;> simp [g,hm,hn,show (n.natAbs < N ↔ ¬N ≤ n.natAbs) by omega]
  have hs := hg.add ht.hasSum
  rw [← he] at hs
  exact ⟨hs.summable,hs.tsum_eq⟩

/-- Combining any proved central budget with the tail yields the printed global constant.
The central budget is an explicit premise, to be discharged by the spectral geometry. -/
theorem M1_canonicalGap_global_le_of_central_bound (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ))
    (hc : (∑ n ∈ Finset.Ioo (-(N:ℤ)) N,
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
        256*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*‖φ‖^4) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 := by
  obtain ⟨hs,he⟩ := sum_eq_central_add_tail _ N
    (M1_canonicalGap_tail_summable_and_le w hw φ heven N hN).1
  refine ⟨hs,?_⟩
  rw [he]
  have ht := M1_canonicalGap_tail_quartic_le w hw φ heven N hN
  have hb := gap_global_265_budget (‖φ‖^2) (w.realExtension (16*‖φ‖^2))
    (sq_nonneg _) (w.one_le_realExtension _)
  have hp : (‖φ‖^2)^2 = ‖φ‖^4 := by ring
  rw [hp] at hb
  exact (add_le_add hc ht).trans hb

/-- Proposition 25.5's global bound on the real potential space, with exact real interpolation. -/
theorem M1_real_canonicalGap_global_summable_and_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (φ : WeightedCoeffPair w.toWeight 2) (heven : weightedBaseToPair w φ ∈ pairParitySubspace 0)
    (hreal : IsRealType (weightedBaseToPair w φ)) :
    Summable (fun n : ℤ =>
      (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ∧
    (∑' n : ℤ, (w (2*n)*‖canonicalPeriodicGap (by simp) (by norm_num) (weightedBaseToPair w φ) heven n‖)^2) ≤
      265*Real.pi^2*(w.realExtension (16*‖φ‖^2))^2*(1+‖φ‖^2)*‖φ‖^2 := by
  let N := ⌊8*‖φ‖^2⌋₊
  have hfloor : (N:ℝ) ≤ 8*‖φ‖^2 := Nat.floor_le (by positivity)
  have hN : 8*‖φ‖^2 ≤ 1+(N:ℝ) := by have h := Nat.lt_floor_add_one (8*‖φ‖^2); dsimp [N]; linarith
  apply M1_canonicalGap_global_le_of_central_bound w hw φ heven N hN
  by_cases hpos : 0 < N
  · have hc := M1_real_canonicalGap_weighted_central_sq_le w hw φ heven hreal N hpos hN
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hpos
    have hw' : w (2*(N:ℤ)-2) ≤ w.realExtension (16*‖φ‖^2) := by
      apply w.le_realExtension
      push_cast
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hwidth : (2*(N:ℝ)-1)*Real.pi ≤ 16*‖φ‖^2*Real.pi := by
      apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
      linarith
    calc
      _ ≤ w (2*(N:ℤ)-2)^2*((2*(N:ℝ)-1)*Real.pi)^2 := hc
      _ ≤ (w.realExtension (16*‖φ‖^2))^2*(16*‖φ‖^2*Real.pi)^2 := by
        exact mul_le_mul (pow_le_pow_left₀ (w.positive _).le hw' 2)
          (pow_le_pow_left₀ (mul_nonneg (by linarith) Real.pi_pos.le) hwidth 2)
          (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  · have he : N = 0 := by omega
    simp only [he,Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.sum_empty]
    positivity

end NLS.ZakharovShabat
