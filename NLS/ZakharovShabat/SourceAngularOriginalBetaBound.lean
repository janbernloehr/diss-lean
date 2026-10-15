import NLS.ZakharovShabat.SourceAngularOriginalAnnulusTail
import NLS.ZakharovShabat.SourceAngularOriginalBetaSelectedBound

/-!
# The uniform beta estimate throughout the original domain

Fixed tail annuli give one bound for all distant selected indices and
all deleted indices. A finite intersection with the original selected
chart bounds yields one local constant for every off-diagonal pair at
every complex source in the unchanged W.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The distant selected gaps have one bound uniform in both indices. -/
theorem beta_original_uniform_tail_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, K < m.natAbs → m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  obtain ⟨Vt,hVt,hφt,hVtW,Kt,c,T,hcharts⟩ :=
    H.angular_original_annulus_tail φ hφ
  obtain ⟨Vr,hVr,hφr,_,A,hApos,hroots⟩ :=
    H.angular_extension.exists_local_uniform_retainedRoot_displacement_bound φ hφ
  obtain ⟨Vχ,hVχ,hφχ,_,Kχ,M,hM,hfactor⟩ :=
    H.angular_extension.toSourcePsiFactorMajorantComplexExtension.exists_local_uniform_midpointFilledRegularFactor_tail_bound
      φ hφ
  let U := (Vt ∩ Vr) ∩ Vχ
  let K := max Kt Kχ
  let ρ := 3*Real.pi/32
  let C := ρ^2*(A+ρ)*M/(ρ-Real.pi/16)^3
  have hrρ : Real.pi/16 < ρ := by dsimp only [ρ]; nlinarith [Real.pi_pos]
  have hρR : ρ < Real.pi/8 := by dsimp only [ρ]; nlinarith [Real.pi_pos]
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hC : 0 < C := by
    have hd := sub_pos.mpr hrρ
    dsimp only [C]
    positivity
  refine ⟨U,(hVt.inter hVr).inter hVχ,⟨⟨hφt,hφr⟩,hφχ⟩,
    (fun ψ hψ => hVtW hψ.1.1),K,C,hC,?_⟩
  intro ψ hψ n m hm hmn
  have hmKt : Kt < m.natAbs := (le_max_left _ _).trans_lt hm
  have hmKχ : Kχ ≤ m.natAbs := ((le_max_right _ _).trans_lt hm).le
  obtain ⟨hc,_,D⟩ := hcharts m hmKt
  have hχ (w : ℂ) (hw : w ∈ sphere (c m) ρ) :
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ w‖ ≤ M := by
    apply hfactor ψ hψ.2 n m hmKχ hmn w
    rw [← hc]
    exact mem_closedBall.mpr ((mem_sphere.mp hw).le.trans hρR.le)
  have hroot : ‖displacedRoots (s n ψ : Coeff p) m-c m‖ ≤ A := by
    rw [hc]
    exact hroots ψ hψ.1.2 n m hmn
  have h := D.norm_beta_le_of_midpointFilledRegularFactor_bound ψ hψ.1.1 n hmn ρ M hrρ hρR hM.le hχ
  have hcoeff : ρ^2*(‖displacedRoots (s n ψ : Coeff p) m-c m‖+ρ)*M/(ρ-Real.pi/16)^3 ≤ C := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl ρ)) (sq_nonneg _)) hM.le
  exact h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (abs_nonneg _))

/-- Theorem 13.1(i)'s bound is locally uniform on all of the retained complex W. -/
theorem beta_original_uniform_bound (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  classical
  obtain ⟨Ut,hUt,hφt,hUtW,K,Ct,hCt,htail⟩ := H.beta_original_uniform_tail_bound φ hφ
  have hlocal (m : ℤ) := H.beta_original_uniform_selected_bound φ hφ m
  choose Um hUm hφUm _ Cm hCm hbound using hlocal
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ m ∈ S, ψ ∈ Um m := by
    rw [Finset.eventually_all]
    intro m _
    exact (hUm m).mem_nhds (hφUm m)
  obtain ⟨H,hHsub,hH,hφH⟩ := _root_.mem_nhds_iff.mp hevent
  let B := ∑ m ∈ S, Cm m
  have hB : 0 ≤ B := Finset.sum_nonneg (fun m _ => (hCm m).le)
  let C := Ct+B
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨Ut ∩ H,hUt.inter hH,⟨hφt,hφH⟩,inter_subset_left.trans hUtW,C,hC,?_⟩
  intro ψ hψ n m hmn
  by_cases hm : K < m.natAbs
  · exact (htail ψ hψ.1 n m hm hmn).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB : Ct ≤ C) (by positivity)) (abs_nonneg _))
  · have hmS : m ∈ S := by simp only [S,Finset.mem_Icc]; omega
    have hmB : Cm m ≤ B := Finset.single_le_sum (fun k _ => (hCm k).le) hmS
    have hmC : Cm m ≤ C := by dsimp only [C]; linarith
    exact (hbound m ψ (hHsub hψ.2 m hmS) n hmn).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmC (by positivity)) (abs_nonneg _))

end SourceLemma12_12Data
end NLS.ZakharovShabat
