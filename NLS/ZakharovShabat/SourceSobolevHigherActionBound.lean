import NLS.ZakharovShabat.SourceHigherActionPolynomialBound
import NLS.ZakharovShabat.SourceSobolevGapBound

/-! # Absolute convergence of the first three higher-action levels on H¹

The weighted squared-gap estimate dominates the actual complex higher
actions. One complex H¹ neighborhood and one ℓ¹ bound work for levels
one through three, without a finite-gap assumption.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem higherAction_sobolev_weight_bound (n : ℤ) (k : ℕ) (hk : k ≤ 2) :
    (1+|(n:ℝ)|)^k ≤ ((SpectralWeight.sobolev 1 (by norm_num)) (2*n))^2 := by
  calc
    _ ≤ (1+|(n:ℝ)|)^2 := pow_le_pow_right₀ (by linarith [abs_nonneg (n:ℝ)]) hk
    _ ≤ _ := by
      apply pow_le_pow_left₀ (by positivity)
      simp only [SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
        Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith [abs_nonneg (n:ℝ)]

/-- Actual higher-action sequences have uniformly bounded ℓ¹ realizations
near every real H¹ source, simultaneously through the physical energy level. -/
theorem exists_local_sourceSobolevHigherAction_bound
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∀ k : ℕ, k ≤ 2 → ∃ J : Coeff 1,
        (∀ n : ℤ, J n = sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) ∧
        ‖J‖ ≤ C := by
  let L := sobolevSourceInclusion
  let A := sourceHigherActionAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,hV,haV,G,hg⟩ := exists_local_sourceSobolevWeightedSquaredGap_bound a
  obtain ⟨W,hW,haW,_,B,D,hB,hD,hb⟩ := A.exists_local_all_actions_polynomial_bound ⟨L a,ha⟩
  let U := V ∩ L ⁻¹' W
  let K := B*(max 1 D)^2
  have hK : 0 ≤ K := mul_nonneg hB.le (sq_nonneg _)
  refine ⟨U,hV.inter (hW.preimage L.continuous),⟨haV,haW⟩,K*G,?_⟩
  intro b hbU k hk
  obtain ⟨g,hgcoord,hgnorm⟩ := hg b hbU.1
  let f : ℤ → ℂ := fun n => sourceComplexHigherAction (by simp) (by norm_num) n k (L b)
  have hDpow : D^k ≤ (max 1 D)^2 :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hbound (n : ℤ) : ‖f n‖ ≤ K*‖g n‖ := by
    let w := SpectralWeight.sobolev 1 (by norm_num)
    let d := sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n
    have hgabs : ‖g n‖ = (w (2*n))^2*‖d‖^2 := by
      rw [hgcoord n]
      change ‖((w (2*n) : ℂ)^2*d^2)‖ = _
      rw [norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (w.toWeight.positive _)]
    calc
      _ ≤ B*D^k*(1+|(n:ℝ)|)^k*‖d‖^2 := hb (L b) hbU.2 n k
      _ ≤ B*(max 1 D)^2*(w (2*n))^2*‖d‖^2 := by
        gcongr
        exact higherAction_sobolev_weight_bound n k hk
      _ = K*‖g n‖ := by rw [hgabs]; dsimp [K]; ring
  have hs := (g.property.norm.summable_of_one).mul_left K
  have hm : Memℓp f 1 := Coeff.memℓp_of_power_dominated _ _ hs (by simpa using hbound)
  let J := Coeff.ofFunctionOrZero 1 f
  refine ⟨J,fun n => Coeff.ofFunctionOrZero_apply_of_mem _ _ hm n,?_⟩
  have hn := Coeff.norm_ofFunctionOrZero_rpow_le (p := 1) (by simp) f (fun n => K*‖g n‖) hs
    (by simpa using hbound)
  have he : (∑' n : ℤ, ‖g n‖) = ‖g‖ := by
    simpa using (lp.norm_rpow_eq_tsum (p := 1) (by simp) g).symm
  have hJ : ‖J‖ ≤ K*‖g‖ := by
    simpa only [J,ENNReal.toReal_one,Real.rpow_one,tsum_mul_left,he] using hn
  exact hJ.trans (mul_le_mul_of_nonneg_left hgnorm hK)

/-- On a common complex H¹ neighborhood, the first three defining
higher-action series are absolutely convergent. -/
theorem exists_local_sourceSobolevHigherAction_summable
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) :
    ∃ U : Set (ScalarDomain 2 × ScalarDomain 2), IsOpen U ∧ a ∈ U ∧
      ∀ b ∈ U, ∀ k : ℕ, k ≤ 2 → Summable (fun n : ℤ =>
        sourceComplexHigherAction (by simp) (by norm_num) n k (sobolevSourceInclusion b)) := by
  obtain ⟨U,hU,haU,C,hbound⟩ := exists_local_sourceSobolevHigherAction_bound a ha
  refine ⟨U,hU,haU,?_⟩
  intro b hb k hk
  obtain ⟨J,hJ,_⟩ := hbound b hb k hk
  exact J.property.summable_of_one.congr hJ

end NLS.ZakharovShabat
