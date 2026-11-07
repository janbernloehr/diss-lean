import NLS.ZakharovShabat.SourceReciprocalScaling
import NLS.ZakharovShabat.SourceMidpointSpectralData

/-! # All real phases, reflected labels, and the full canonical-root symmetry

Theorem 6's actual spectral functions are compared on the original complex
source domain. The root identity includes its sign, not merely its square.
The spatial-gradient ODE and invariant-neighborhood assertions remain separate.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePhaseRotation (α : ℝ) : CoeffPair p →L[ℂ] CoeffPair p :=
  sourceReciprocalScaling (exp ((α:ℂ)*I))

@[simp] theorem sourcePhaseRotation_fst (α : ℝ) (φ : CoeffPair p) :
    (sourcePhaseRotation α φ).fst = exp ((α:ℂ)*I) • φ.fst := rfl

@[simp] theorem sourcePhaseRotation_snd (α : ℝ) (φ : CoeffPair p) :
    (sourcePhaseRotation α φ).snd = exp (-((α:ℂ)*I)) • φ.snd := by
  simp only [sourcePhaseRotation,sourceReciprocalScaling_snd,exp_neg]

theorem theorem6_i_phase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (α : ℝ) (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential (sourcePhaseRotation α φ)) z :=
  (sourceDiscriminant_reciprocalScaling hp hp1 _ (exp_ne_zero _) φ z).symm

theorem theorem6_ii_phase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (α : ℝ) (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
      deriv (canonicalDiscriminant hp (periodOnePotential (sourcePhaseRotation α φ))) z :=
  (sourceDiscriminant_deriv_reciprocalScaling hp hp1 _ (exp_ne_zero _) φ z).symm

theorem theorem6_iii_phase_covectors (hp : p ≠ ⊤) (hp1 : 1 < p)
    (α : ℝ) (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp z (sourcePhaseRotation α φ)).comp (sourcePhaseRotation α) :=
  sourceDiscriminantCotangent_reciprocalScaling hp hp1 _ (exp_ne_zero _) φ z

theorem theorem6_i_endpoint_labels (hp : p ≠ ⊤) (hp1 : 1 < p)
    (α : ℝ) (φ : CoeffPair p) (n : ℤ) :
    (canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n =
        -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential (sourceComponentSwap φ)) (periodOnePotential_mem _) n =
        -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n)) ∧
    (canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceMidpointReflection φ)) (periodOnePotential_mem _) n =
        -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential (sourceMidpointReflection φ)) (periodOnePotential_mem _) n =
        -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n)) ∧
    (canonicalPeriodicLeft hp hp1 (periodOnePotential (sourcePhaseRotation α φ)) (periodOnePotential_mem _) n =
        canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential (sourcePhaseRotation α φ)) (periodOnePotential_mem _) n =
        canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) n) := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling hp hp1
    (exp ((α:ℂ)*I)) (exp_ne_zero _) φ
  exact ⟨sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 φ n,
    sourceCanonicalPeriodicEndpoints_midpointReflection hp hp1 φ n,
    congrFun hl n,congrFun hr n⟩

/-- All three original root identities, with the exact normalization.
They hold on the cut complement and even at the root's total cut values. -/
theorem theorem6_iv (hp : p ≠ ⊤) (hp1 : 1 < p)
    (α : ℝ) (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 φ z = -sourceCanonicalRoot hp hp1 (sourceComponentSwap φ) (-z) ∧
    sourceCanonicalRoot hp hp1 φ z = -sourceCanonicalRoot hp hp1 (sourceMidpointReflection φ) (-z) ∧
    sourceCanonicalRoot hp hp1 φ z = sourceCanonicalRoot hp hp1 (sourcePhaseRotation α φ) z := by
  refine ⟨?_,?_,?_⟩
  · rw [sourceCanonicalRoot_componentSwap hp hp1,neg_neg]
  · rw [sourceCanonicalRoot_midpointReflection hp hp1,neg_neg]
  · exact (sourceCanonicalRoot_reciprocalScaling hp hp1
      (exp ((α:ℂ)*I)) (exp_ne_zero _) φ z).symm

end NLS.Articles.MKdVNLSHierarchies
