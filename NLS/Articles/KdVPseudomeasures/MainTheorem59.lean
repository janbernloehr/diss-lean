import NLS.Articles.KdVPseudomeasures.OriginalHillWienerAnalyticTrajectories
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalClassicalRoughSolution

/-! Original Theorem5.9: global C-omega wellposedness on EVERY original
physical real mean-zero period-one FL^(N,1) space. For EVERY T>0 the
initial-data map is real analytic in the actual UNIFORM strong norm on
C([-T,T],FL^(N,1)). The ENTIRE original physical flow and the unique
classical-approximation KdV solution are retained. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem originalWienerCanonicalFlow_is_solutionByClassicalApproximation
    (N : ℕ) (q : OriginalWienerPotential N) :
    OriginalKdVSolutionByClassicalApproximation (originalWienerOriginalPotential N q)
      (fun t => originalWienerOriginalPotential N (originalWienerCanonicalKdVFlow N q t)) := by
  have he : (fun t => originalWienerOriginalPotential N (originalWienerCanonicalKdVFlow N q t)) =
      hillOriginalCanonicalKdVFlow (originalWienerOriginalPotential N q) :=
    funext (originalWienerCanonicalKdVFlow_original N q)
  rw [he]
  exact hillOriginalCanonicalFlow_is_solutionByClassicalApproximation _

theorem originalWienerKdVSolutionByClassicalApproximation_unique (N : ℕ) (q : OriginalWienerPotential N)
    (γ : ℝ → OriginalWienerPotential N)
    (hγ : OriginalKdVSolutionByClassicalApproximation (originalWienerOriginalPotential N q)
      (fun t => originalWienerOriginalPotential N (γ t))) :
    γ=originalWienerCanonicalKdVFlow N q := by
  have he := originalKdVSolutionByClassicalApproximation_unique (originalWienerOriginalPotential N q)
    (fun t => originalWienerOriginalPotential N (γ t)) hγ
  funext t
  apply originalWienerOriginalPotential_injective N
  exact (congrFun he t).trans (originalWienerCanonicalKdVFlow_original N q t).symm

def originalWienerKdVCompactTrajectory (N : ℕ) (T : ℝ) (q : OriginalWienerPotential N) :
    C(Icc (-T) T,OriginalWienerPotential N) :=
  originalWienerKdVTrajectory N (⟨Subtype.val,continuous_subtype_val⟩ : C(Icc (-T) T,ℝ)) q

theorem analyticAt_originalWienerKdVCompactTrajectory (N : ℕ) (T : ℝ) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalWienerKdVCompactTrajectory N T) q :=
  analyticAt_originalWienerKdVTrajectory N _ q

def sourceTheorem5_9Statement : Prop :=
  ∀ N : ℕ, ∃ S : OriginalWienerPotential N → ℝ → OriginalWienerPotential N,
    (∀ q, S q 0=q) ∧
    (∀ q t s, S (S q s) t=S q (t+s)) ∧
    (∀ q, OriginalKdVSolutionByClassicalApproximation (originalWienerOriginalPotential N q)
      (fun t => originalWienerOriginalPotential N (S q t))) ∧
    (∀ q γ, OriginalKdVSolutionByClassicalApproximation (originalWienerOriginalPotential N q)
      (fun t => originalWienerOriginalPotential N (γ t)) → γ=S q) ∧
    (∀ q t, originalWienerOriginalPotential N (S q t) =
      hillOriginalCanonicalKdVFlow (originalWienerOriginalPotential N q) t) ∧
    ∀ T : ℝ, 0<T → ∃ Γ : OriginalWienerPotential N → C(Icc (-T) T,OriginalWienerPotential N),
      (∀ q t, Γ q t=S q (t:ℝ)) ∧ ∀ q, AnalyticAt ℝ Γ q

theorem sourceTheorem5_9 : sourceTheorem5_9Statement := by
  intro N
  refine ⟨originalWienerCanonicalKdVFlow N,originalWienerCanonicalKdVFlow_zero N,
    originalWienerCanonicalKdVFlow_add N,originalWienerCanonicalFlow_is_solutionByClassicalApproximation N,
      originalWienerKdVSolutionByClassicalApproximation_unique N,originalWienerCanonicalKdVFlow_original N,?_⟩
  intro T _
  refine ⟨originalWienerKdVCompactTrajectory N T,?_,analyticAt_originalWienerKdVCompactTrajectory N T⟩
  intro q t
  exact originalWienerKdVTrajectory_apply N _ q t

end NLS.Articles.KdVPseudomeasures
