import NLS.ZakharovShabat.SourceCriticalSobolevDisplacement
import NLS.ZakharovShabat.SourceBoundaryWeightedDisplacement
import NLS.ZakharovShabat.SourceCriticalDisplacementContinuity

/-! # Weighted canonical critical displacement on Sobolev neighborhoods

The actual critical displacement has one local inverse-bracket bound at every index near a real original Hs source, with no smooth representative assumption.
-/

noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual critical displacements have one local inverse-bracket
budget, including the central block, on the original complex Hs space
near each real source. No smooth physical representative is needed. -/
theorem exists_local_higherSobolev_critical_weighted_displacement_bounds
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ R D M : ℝ, 0 ≤ R ∧ 0 ≤ D ∧ 0 ≤ M ∧ ∀ ab ∈ U,
        ‖ab‖ ≤ R ∧
        ‖sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab)‖ ≤ D ∧
        ∀ n : ℤ, (1+|(n:ℝ)|)*
          ‖sourceCriticalDisplacement (by norm_num) (by norm_num) (higherSobolevSourceInclusion s ab) n‖ ≤ M := by
  let F := higherSobolevSourceInclusion s
  let δ (ab : SobolevSource s) := sourceCriticalDisplacement (by norm_num) (by norm_num) (F ab)
  have hδ : ContinuousAt δ a₀.val :=
    (continuousAt_sourceCriticalDisplacement_of_realType (by norm_num) (by norm_num)
      (F a₀.val) a₀.property).comp F.continuous.continuousAt
  let R := ‖a₀.val‖+1
  let D := ‖δ a₀.val‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr : ∀ᶠ ab in 𝓝 a₀.val, ‖ab‖ < R := continuousAt_id.norm.eventually
    (gt_mem_nhds (by dsimp [R]; linarith))
  have hd : ∀ᶠ ab in 𝓝 a₀.val, ‖δ ab‖ < D := hδ.norm.eventually
    (gt_mem_nhds (by dsimp [D]; linarith))
  obtain ⟨V,hsub,hV,haV⟩ := _root_.mem_nhds_iff.mp (hr.and hd)
  obtain ⟨W₁,hW₁,haW₁,K,hK,B,hB,hbound⟩ :=
    exists_local_source_critical_sobolev_inverse_index_bound (F a₀.val) (2*R) (by positivity)
  let U := V ∩ F ⁻¹' W₁
  let M := (1+(K:ℝ))*D+2*B
  refine ⟨U,hV.inter (hW₁.preimage F.continuous),⟨haV,haW₁⟩,
    R,D,M,hR,hD,by dsimp [M]; positivity,?_⟩
  intro ab hab
  have habR := (hsub hab.1).1.le
  have habD := (hsub hab.1).2.le
  refine ⟨habR,habD,?_⟩
  intro n
  have hnabs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
  rw [hnabs]
  by_cases hn : K ≤ n.natAbs
  · have hn1 : 1 ≤ (n.natAbs:ℝ) := by exact_mod_cast hK.trans_le hn
    have hphys : ‖higherSobolevOperatorDomain s hs ab‖ ≤ 2*R :=
      (norm_higherSobolevOperatorDomain_le s hs ab).trans (by gcongr)
    have hh := hbound (F ab) hab.2
      (higherSobolevOperatorDomain s hs ab) hphys (higherSobolevOperatorDomain_compatibility s hs ab) n hn
    have htail : ‖δ ab n‖ ≤ B/(n.natAbs:ℝ) := by
      simpa only [δ,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] using hh
    have hm := (le_div_iff₀ (by linarith : (0:ℝ) < n.natAbs)).mp htail
    have hdB : ‖δ ab n‖ ≤ B := htail.trans (div_le_self hB hn1)
    change (1+(n.natAbs:ℝ))*‖δ ab n‖ ≤ M
    dsimp [M]
    nlinarith
  · have hnK : (n.natAbs:ℝ) ≤ K := by exact_mod_cast (show n.natAbs ≤ K by omega)
    have hnD : ‖δ ab n‖ ≤ D := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (δ ab) n).trans habD
    change (1+(n.natAbs:ℝ))*‖δ ab n‖ ≤ M
    have hh := mul_le_mul (by linarith : 1+(n.natAbs:ℝ) ≤ 1+(K:ℝ)) hnD
      (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1+(K:ℝ))
    exact hh.trans (by dsimp [M]; linarith)

end NLS.ZakharovShabat
