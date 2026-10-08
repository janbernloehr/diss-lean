import NLS.ZakharovShabat.SourceHigherActionPolynomialBound
import NLS.ZakharovShabat.SourceWeightedGapBound

/-! # Higher-action bounds from weighted Hilbert source maps

A weight dominating a finite range of polynomial powers controls that whole
range of higher-action sequences on one complex neighborhood.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- All levels whose polynomial factors are dominated by the squared weight
have one locally uniform ℓ¹ bound in the original source topology. -/
theorem exists_local_sourceWeightedHigherAction_bound
    (w : SpectralWeight) (L : E →L[ℂ] CoeffPair 2)
    (S : E →L[ℂ] WeightedCoeffPair w.toWeight 2)
    (hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b))
    (m : ℕ) (hm : ∀ n : ℤ, ∀ k : ℕ, k ≤ m → (1+|(n:ℝ)|)^k ≤ (w (2*n))^2)
    (a : E) (ha : IsRealType (CoeffPair.toMax 2 (L a))) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧
      ∃ C : ℝ, ∀ b ∈ U, ∀ k : ℕ, k ≤ m → ∃ J : Coeff 1,
        (∀ n : ℤ, J n = sourceComplexHigherAction (by simp) (by norm_num) n k (L b)) ∧
        ‖J‖ ≤ C := by
  let A := sourceHigherActionAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,hV,haV,G,hg⟩ := exists_local_sourceWeightedSquaredGap_bound w L S hSL a
  obtain ⟨W,hW,haW,_,B,D,hB,hD,hb⟩ := A.exists_local_all_actions_polynomial_bound ⟨L a,ha⟩
  let U := V ∩ L ⁻¹' W
  let K := B*(max 1 D)^m
  have hK : 0 ≤ K := mul_nonneg hB.le (pow_nonneg (le_trans zero_le_one (le_max_left 1 D)) _)
  refine ⟨U,hV.inter (hW.preimage L.continuous),⟨haV,haW⟩,K*G,?_⟩
  intro b hbU k hk
  obtain ⟨g,hgcoord,hgnorm⟩ := hg b hbU.1
  let f : ℤ → ℂ := fun n => sourceComplexHigherAction (by simp) (by norm_num) n k (L b)
  have hDpow : D^k ≤ (max 1 D)^m :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hbound (n : ℤ) : ‖f n‖ ≤ K*‖g n‖ := by
    let d := sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n
    have hgabs : ‖g n‖ = (w (2*n))^2*‖d‖^2 := by
      rw [hgcoord n]
      change ‖((w (2*n) : ℂ)^2*d^2)‖ = _
      rw [norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos (w.toWeight.positive _)]
    calc
      _ ≤ B*D^k*(1+|(n:ℝ)|)^k*‖d‖^2 := hb (L b) hbU.2 n k
      _ ≤ B*(max 1 D)^m*(w (2*n))^2*‖d‖^2 := by
        gcongr
        exact hm n k hk
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

end NLS.ZakharovShabat
