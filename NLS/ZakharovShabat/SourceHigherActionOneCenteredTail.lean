import NLS.ZakharovShabat.SourceHigherActionOneUniformCircle
import NLS.ZakharovShabat.SourceCenteredActionCircleBound
import NLS.ZakharovShabat.SourceNormalizedActionFactorDiscMajorants
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform

/-! The actual filled first higher-action quotient minus periodic
midpoint times the actual ordinary normalized action is uniformly
bounded BEFORE ALL distant signed labels on ONE complex neighborhood.
The spectral weight remains the original one, also at collapse. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_local_sourceHigherActionOneNormalized_centered_tail_bound
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ψ ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ‖sourceHigherActionOneNormalized (by simp) (by norm_num) n ψ -
          sourceStandardRootMidpoint (by simp) (by norm_num) ψ n*
            sourceNormalizedActionComplexExtension (by simp) (by norm_num) n ψ‖ ≤ C := by
  obtain ⟨Kh,Vh,hVh,hφVh,hhigher⟩ :=
    exists_local_sourceHigherActionOneNormalized_uniform_circle (by simp) (by norm_num) φ hφ
  obtain ⟨Ka,ra,hra,hagree⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_complex_agreement (by simp) (by norm_num) φ hφ
  obtain ⟨Kg,Vg,hVg,hφVg,hgeom⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data (by simp) (by norm_num) φ hφ
  obtain ⟨Vb,hVb,hφVb,M,hM,hB⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient (by simp) (by norm_num) φ hφ
  obtain ⟨Ve,hVe,hφVe,Ke,Le,hEbound⟩ :=
    exists_local_sourceNormalizedAction_factor_circle_uniform_bound (q := 2)
      (by simp) (by norm_num) (by norm_num) (by simp) (by norm_num) φ hφ
  obtain ⟨W,hW,_,hrealW,hoffset⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact (p := 2) (by simp) (by norm_num)
  let V := ((Vh ∩ ball φ ra) ∩ (Vg ∩ Vb)) ∩ (Ve ∩ W)
  let N := max Kh (max Ka (max Kg Ke))
  let a : ℝ := Real.pi/16
  let R : ℝ := Real.pi/8
  let L : ℝ := max 0 Le
  let T : ℝ := 1/(8*a)+2*M+a^2*(2/a^3+M/a^2+2*M^2/a)
  let C : ℝ := R*((2*R+a^2*M)*(T*L))
  have ha : 0 < a := by dsimp [a]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hL : 0 ≤ L := le_max_left _ _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨V,((hVh.inter isOpen_ball).inter (hVg.inter hVb)).inter (hVe.inter hW),
    ⟨⟨⟨hφVh,mem_ball_self hra⟩,hφVg,hφVb⟩,hφVe,hrealW hφ⟩,
    N,C,by dsimp [C]; positivity,?_⟩
  intro ψ hψ n hn
  have hKh : Kh ≤ n.natAbs := (le_max_left _ _).trans hn
  have hKa : Ka ≤ n.natAbs := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hKg : Kg ≤ n.natAbs :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  have hKe : Ke ≤ n.natAbs :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hn
  obtain ⟨hseg,_,hE,hsep,hq⟩ := hgeom ψ hψ.1.2.1 n hKg
  let c : ℂ := (Real.pi:ℂ)*n
  let τ := sourceStandardRootMidpoint (by simp) (by norm_num) ψ n
  let g := (sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ n)^2
  let B := canonicalCriticalGapQuotient (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) n
  let b := canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ) (periodOnePotential_mem _) n
  let E := sourceCriticalRootRatioExtension (by simp) (by norm_num) n ψ
  let f : ℂ → ℂ := fun z => normalizedActionCircleKernel τ g B z*E z
  have hτ : τ ∈ ball c R := hseg (sourcePeriodicMidpoint_mem_segment (by simp) (by norm_num) ψ n)
  have hBp : ‖B‖ ≤ M := by
    have h := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (sourceCriticalGapQuotient (by simp) (by norm_num) ψ) n
    exact (show ‖B‖ ≤ ‖sourceCriticalGapQuotient (by simp) (by norm_num) ψ‖ by
      simpa only [B,sourceCriticalGapQuotient_apply] using h).trans (hB ψ hψ.1.2.2).1
  have hEp : ∀ z ∈ sphere c R, ‖E z‖ ≤ L :=
    fun z hz => (hEbound ψ hψ.2.1 n hKe z hz).trans (le_max_right _ _)
  have hrootEq : ∀ z, normalizedStandardRoot τ g z =
      sourceStandardRoot (by simp) (by norm_num) ψ n z := by
    intro z
    simp only [sourceStandardRoot,τ,g,sourceStandardRootMidpoint,sourcePeriodicGapDisplacement_apply]
  have hcont : ContinuousOn f (sphere c R) := by
    intro z hz
    have hd : τ ≠ z := sub_ne_zero.mp (norm_pos_iff.mp (ha.trans_le (hsep z hz)))
    have hnot : z ∉ sourcePeriodicSegment (by simp) (by norm_num) ψ n := by
      intro hzs
      exact (ne_of_lt (mem_ball.mp (hseg hzs))) (mem_sphere.mp hz)
    have hroot : AnalyticAt ℂ (normalizedStandardRoot τ g) z := by
      have he : normalizedStandardRoot τ g = sourceStandardRoot (by simp) (by norm_num) ψ n := funext hrootEq
      rw [he]
      exact sourceStandardRoot_analyticAt (by simp) (by norm_num) ψ n z hnot
    have hw : normalizedStandardRoot τ g z ≠ 0 := by
      rw [hrootEq]
      exact sourceStandardRoot_ne_zero_off_segment (by simp) (by norm_num) ψ n z hnot
    exact ((normalizedActionCircleKernel_analyticAt τ g B z hroot hw
      (normalizedStandardRoot_add_ne_zero τ g z hd)).mul
        (hE z (sphere_subset_closedBall hz))).continuousAt.continuousWithinAt
  have hfb : ∀ z ∈ sphere c R, ‖f z‖ ≤ T*L := by
    intro z hz
    rw [show f z = normalizedActionCircleKernel τ g B z*E z from rfl,norm_mul]
    exact mul_le_mul (norm_normalizedActionCircleKernel_le_of_separation τ g B z a M ha
      (hsep z hz) hq hBp) (hEp z hz) (norm_nonneg _) hT
  have hbo : ‖b-τ‖ ≤ a^2*M := by
    have he : b-τ = g*B := (hoffset ψ hψ.2.2 n).2
    rw [he,norm_mul]
    exact mul_le_mul hq hBp (norm_nonneg _) (sq_nonneg _)
  have hb : ∀ z ∈ sphere c R, ‖z+b-2*τ‖ ≤ 2*R+a^2*M := by
    intro z hz
    have hzτ : ‖z-τ‖ ≤ 2*R := by
      have h := dist_triangle z c τ
      rw [mem_sphere.mp hz,dist_comm c τ] at h
      have hm := mem_ball.mp hτ
      rw [dist_eq_norm] at h
      linarith
    have he : z+b-2*τ = (z-τ)+(b-τ) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hzτ hbo)
  rw [(hhigher ψ hψ.1.1.1 n hKh).1,← (hagree ψ hψ.1.1.2 n hKa).1]
  change ‖-(2*(Real.pi:ℂ))⁻¹*(∮ z in C(c,R), (z+b)*f z) -
    τ*(-(Real.pi:ℂ)⁻¹*(∮ z in C(c,R), f z))‖ ≤ C
  exact norm_centeredActionCircle_le c τ b R (T*L) (2*R+a^2*M) f hR.le
    hcont hb hfb

end NLS.ZakharovShabat
