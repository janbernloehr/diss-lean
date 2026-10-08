import NLS.ZakharovShabat.SourceHigherActionComplexBound
import NLS.ZakharovShabat.SourcePsiGlobalTailSequenceBound

/-! # Locally uniform polynomial bounds for the higher actions -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral size of a gap is controlled by the actual displacement norms. -/
theorem sourceGapSpectralRadius_le (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceGapSpectralRadius hp hp1 ψ n ≤ Real.pi*|(n:ℝ)| +
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ + ‖sourcePeriodicGapDisplacement hp hp1 ψ‖/2 := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hm := lp.norm_apply_le_norm hp0 (sourcePeriodicMidpointDisplacement hp hp1 ψ) n
  have hg := lp.norm_apply_le_norm hp0 (sourcePeriodicGapDisplacement hp hp1 ψ) n
  have he : sourceStandardRootMidpoint hp hp1 ψ n =
      sourcePeriodicMidpointDisplacement hp hp1 ψ n+(Real.pi:ℂ)*n := by
    rw [sourcePeriodicMidpointDisplacement_apply]
    unfold sourceStandardRootMidpoint
    ring
  have hmid := norm_add_le (sourcePeriodicMidpointDisplacement hp hp1 ψ n) ((Real.pi:ℂ)*n)
  rw [← he] at hmid
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast] at hmid
  have hhalf : ‖sourceStandardRootHalfGap hp hp1 ψ n‖ = ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2 := by
    simp only [sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat]
  unfold sourceGapSpectralRadius
  rw [hhalf]
  linarith

/-- Locally, every gap has spectral size at most a constant times `1+|n|`. -/
theorem exists_local_sourceGapSpectralRadius_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ ∃ D : ℝ, 0 < D ∧
      ∀ ψ ∈ V, ∀ n : ℤ, sourceGapSpectralRadius hp hp1 ψ n ≤ D*(1+|(n:ℝ)|) := by
  obtain ⟨V,hV,hφ,hb⟩ := exists_local_sourcePeriodicDisplacement_normBounds hp hp1 φ.val φ.property
  let M := ‖sourcePeriodicMidpointDisplacement hp hp1 φ.val‖+1
  let G := ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖+1
  let D := Real.pi+M+G
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  refine ⟨V,hV,hφ,D,by dsimp [D]; positivity,?_⟩
  intro ψ hψ n
  have h := sourceGapSpectralRadius_le hp hp1 ψ n
  have hb' := hb ψ hψ
  change _ ≤ M ∧ _ ≤ G at hb'
  dsimp [D]
  nlinarith [Real.pi_pos,mul_nonneg hM (abs_nonneg (n:ℝ)),mul_nonneg hG (abs_nonneg (n:ℝ))]

namespace SourceHigherActionAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceHigherActionAtlas hp hp1)

/-- One complex neighborhood and two positive constants work for all levels
and indices. The weight is explicit; no endpoint-localization hypothesis is supplied. -/
theorem exists_local_all_actions_polynomial_bound (φ : realTypeSourceSubmodule p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧ U ⊆ A.domain ∧
      ∃ B D : ℝ, 0 < B ∧ 0 < D ∧ ∀ ψ ∈ U, ∀ (n : ℤ) (k : ℕ),
        ‖A.action n k ψ‖ ≤ B*D^k*(1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  obtain ⟨V,hV,hφV,hVA,B,hB,hb⟩ := A.exists_local_all_actions_gap_bound φ
  obtain ⟨G,hG,hφG,D,hD,hd⟩ := exists_local_sourceGapSpectralRadius_bound hp hp1 φ
  refine ⟨V ∩ G,hV.inter hG,⟨hφV,hφG⟩,fun ψ hψ => hVA hψ.1,B,D,hB,hD,?_⟩
  intro ψ hψ n k
  calc
    _ ≤ B*sourceGapSpectralRadius hp hp1 ψ n ^ k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := hb ψ hψ.1 n k
    _ ≤ B*(D*(1+|(n:ℝ)|))^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
      gcongr
      · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact hd ψ hψ.2 n
    _ = _ := by rw [mul_pow]; ring

/-- A summable weighted squared-gap majorant gives absolute convergence
of the higher-action series and an explicit bound on its norm sum. -/
theorem summable_action_of_polynomial_bound (ψ : CoeffPair p) (k : ℕ) (B D : ℝ)
    (hb : ∀ n : ℤ, ‖A.action n k ψ‖ ≤ B*D^k*(1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2)
    (hs : Summable (fun n : ℤ => (1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2)) :
    Summable (fun n => A.action n k ψ) ∧
      (∑' n, ‖A.action n k ψ‖) ≤ B*D^k*(∑' n : ℤ, (1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2) := by
  have hdom := hs.mul_left (B*D^k)
  have hle (n : ℤ) : ‖A.action n k ψ‖ ≤ B*D^k*((1+|(n:ℝ)|)^k*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2) := by
    simpa only [mul_assoc] using hb n
  have hn := Summable.of_nonneg_of_le (fun n => norm_nonneg (A.action n k ψ)) hle hdom
  exact ⟨hn.of_norm,(hn.tsum_le_tsum hle hdom).trans_eq (tsum_mul_left)⟩

end SourceHigherActionAtlas
end NLS.ZakharovShabat
