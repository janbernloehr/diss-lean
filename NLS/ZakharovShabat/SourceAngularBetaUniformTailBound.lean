import NLS.ZakharovShabat.SourceAngularBetaRegularFactorBound
import NLS.ZakharovShabat.SourceAngularUniformAnnulusPrimitive
import NLS.ZakharovShabat.SourcePsiUniformRetainedRootBounds

/-!
# Uniform beta estimates for every sufficiently distant selected gap

Fixed annuli inside the free eighth-pi discs carry the actual chi tail
bounds. One retained-root displacement bound and one chi bound give a
single beta constant for all deleted indices and all selected indices
beyond one cutoff, on a common complex source neighborhood. The finite
selected head is not covered by this theorem.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The quantitative assertion of Theorem 13.1(i) for every deleted
index and all sufficiently distant selected gaps, with one local
constant and cutoff independent of both indices. -/
theorem exists_local_uniform_sourceAngularBeta_tail_bound
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W₀ s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWW₀ : W ⊆ W₀)
    (hA : ∀ ψ ∈ W, ∀ k : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p => (canonicalPeriodicGap hp hp1
        (periodOnePotential χ) (periodOnePotential_mem χ) k)^2) ψ)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U, ∀ n m : ℤ, K < m.natAbs → m ≠ n →
        ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
            ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m-
              sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)| := by
  obtain ⟨Vt,hVt,hφt,hVtW,Kt,c,T,hcharts⟩ :=
    hs.toSourcePsiIsolatingComplexExtension.exists_local_joint_angular_annulus_primitives_tail
      W hW hWW₀ hA φ hφ hreal
  obtain ⟨Vr,hVr,hφr,_,A,hApos,hroots⟩ :=
    hs.exists_local_uniform_retainedRoot_displacement_bound φ (hWW₀ hφ)
  obtain ⟨Vχ,hVχ,hφχ,_,Kχ,M,hM,hfactor⟩ :=
    hs.toSourcePsiFactorMajorantComplexExtension.exists_local_uniform_midpointFilledRegularFactor_tail_bound
      φ (hWW₀ hφ)
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

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
