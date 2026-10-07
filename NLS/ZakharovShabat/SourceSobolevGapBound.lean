import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.ZakharovShabat.CanonicalWeightedGapSummability
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.SequenceSpaces.FunctionOrZero

/-! # Locally bounded weighted squared gaps on the full H¹ source

The weighted spectral estimate controls the infinite tail. A bounded canonical
gap sequence controls the finite central block. Together they construct the
actual weighted squared gaps in ℓ¹, uniformly on an H¹ neighborhood.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The squared gap with the physical Sobolev weight at its resonant index. -/
def sourceSobolevWeightedSquaredGap (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) : ℂ :=
  ((SpectralWeight.sobolev 1 (by norm_num)) (2*n) : ℂ)^2 *
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a) n)^2

private theorem continuous_hilbert_rootGapBudget (w : SpectralWeight) (N : ℕ) :
    Continuous (fun ψ : WeightedCoeffPair w.toWeight 2 => rootGapBudget w ψ N) := by
  simp only [rootGapBudget, ENNReal.toReal_ofNat]
  norm_num only [show (2 : ℝ)*2 = 4 by norm_num, show (2 : ℝ)-1 = 1 by norm_num,
    min_self, Real.rpow_one, Real.rpow_two, Real.rpow_ofNat]
  have ht := (weightedPairFourierTail (p := 2) w.toWeight (N/2)).continuous.norm
  exact continuous_const.mul ((ht.pow 2).add
    ((continuous_const.mul (continuous_norm.pow 2)).mul
      ((continuous_norm.pow 4).div_const (N : ℝ) |>.add
        (ht.pow 4))))

/-- Every H¹ source has a neighborhood on which the actual weighted squared gaps
have uniformly bounded ℓ¹ norm. No finite-gap or real-type hypothesis is required. -/
theorem exists_local_sourceSobolevWeightedSquaredGap_bound (a : ScalarDomain 2 × ScalarDomain 2) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∃ g : Coeff 1,
        (∀ n : ℤ, g n = sourceSobolevWeightedSquaredGap b n) ∧ ‖g‖ ≤ C := by
  classical
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let S := sobolevSourceWeightedPeriodOne
  let L := sobolevSourceInclusion
  obtain ⟨N,hN,V,hV,haV,htail⟩ :=
    exists_uniform_canonicalWeightedGapSummability (by simp) (by norm_num) w (S a)
  obtain ⟨_,_,W,hW,haW,R,hR,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement (by simp) (by norm_num) (L a)
      (by norm_num : (0 : ℝ) < 1)
  let B := rootGapBudget w (S a) N + 1
  let T := {b : ScalarDomain 2 × ScalarDomain 2 | rootGapBudget w (S b) N < B}
  have hT : IsOpen T := isOpen_lt ((continuous_hilbert_rootGapBudget w N).comp S.continuous)
    continuous_const
  let U := (S ⁻¹' V ∩ L ⁻¹' W) ∩ T
  let s := Finset.Icc (-(N : ℤ)) N
  let H := fun n : ℤ => if n ∈ s then (w (2*n))^2 * R^2 else 0
  have hHs : Summable H := summable_of_ne_finset_zero (s := s) (by intro n hn; simp [H,hn])
  refine ⟨U,((hV.preimage S.continuous).inter (hW.preimage L.continuous)).inter hT,
    ⟨⟨haV,haW⟩,by dsimp [T,B]; linarith⟩, (∑' n, H n) + B, ?_⟩
  intro b hb
  have he : weightedBaseToPair w (S b) = periodOnePotential (L b) :=
    weightedBaseToPair_sobolevSourceWeightedPeriodOne b
  have heven : weightedBaseToPair w (S b) ∈ pairParitySubspace 0 := by
    rw [he]; exact periodOnePotential_mem _
  obtain ⟨hts,htb⟩ := htail (S b) hb.1.1 heven N le_rfl
  let F := sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b)
  let Q := fun n : ℤ => if N ≤ n.natAbs then (w (2*n))^2 * ‖F n‖^2 else 0
  have hQs : Summable Q := by
    simpa only [Q,F,he,sourcePeriodicGapDisplacement_apply,ENNReal.toReal_ofNat,
      Real.rpow_two] using hts
  have hQb : (∑' n, Q n) ≤ B := by
    have ht : (∑' n, Q n) ≤ rootGapBudget w (S b) N := by
      simpa only [Q,F,he,sourcePeriodicGapDisplacement_apply,ENNReal.toReal_ofNat,
        Real.rpow_two] using htb
    exact ht.trans (le_of_lt hb.2)
  have hF : ‖F‖ ≤ R := (hgap (L b) hb.1.2).1
  have hpoint (n : ℤ) : ‖sourceSobolevWeightedSquaredGap b n‖ ≤ H n + Q n := by
    have hf : ‖F n‖ ≤ R := (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) F n).trans hF
    change ‖((w (2*n) : ℂ)^2 * (F n)^2)‖ ≤ _
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (w.toWeight.positive _)]
    by_cases hn : N ≤ n.natAbs
    · simp only [Q,if_pos hn]
      have hh : 0 ≤ H n := by dsimp [H]; split_ifs <;> positivity
      linarith
    · have hns : n ∈ s := by simp only [s,Finset.mem_Icc]; omega
      simp only [Q,if_neg hn,H,if_pos hns,add_zero]
      gcongr
  let g : Coeff 1 := Coeff.ofFunctionOrZero 1 (sourceSobolevWeightedSquaredGap b)
  have hm : Memℓp (sourceSobolevWeightedSquaredGap b) 1 :=
    Coeff.memℓp_of_power_dominated _ _ (hHs.add hQs) (by simpa using hpoint)
  refine ⟨g,fun n => Coeff.ofFunctionOrZero_apply_of_mem _ _ hm n,?_⟩
  have hn := Coeff.norm_ofFunctionOrZero_rpow_le (p := 1) (by simp)
    (sourceSobolevWeightedSquaredGap b) (fun n => H n + Q n) (hHs.add hQs)
    (by simpa using hpoint)
  have hg : ‖g‖ ≤ (∑' n, H n) + ∑' n, Q n := by
    simpa only [g, ENNReal.toReal_one, Real.rpow_one, hHs.tsum_add hQs] using hn
  exact hg.trans (add_le_add le_rfl hQb)

end NLS.ZakharovShabat
