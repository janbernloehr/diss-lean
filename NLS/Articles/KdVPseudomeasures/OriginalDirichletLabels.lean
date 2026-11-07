import NLS.Articles.KdVPseudomeasures.OriginalHillLabels
import NLS.KdV.HminusOneDirichletLabelAsymptotics

/-! Complete ordered Dirichlet characteristic labels on the article's
ENTIRE original real, mean-zero, physically period-one H-minus-one domain.
The raw unit-period extraction represents the same entire distribution.
Identification with the native H_dir^1 to H_dir^(-1) pencil remains separate. -/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- The normalized full Dirichlet characteristic of the original potential. -/
def originalDirichletCharacteristic (q : OriginalHminusOnePotential) (lambda : ℂ) : ℂ :=
  hillHminusDirichlet (originalPeriodOneCoefficients q) lambda

/-- All positive original Dirichlet characteristic labels, including low energies. -/
def originalDirichletLabels (q : OriginalHminusOnePotential) : ℕ+ → ℝ :=
  hillHminusDirichletLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)

theorem strictMono_originalDirichletLabels (q : OriginalHminusOnePotential) :
    StrictMono (originalDirichletLabels q) :=
  strictMono_hillHminusDirichletLabels _ _

/-- The full scalar characteristic zero set is exhausted in the original
strictly increasing positive indexing, with no endpoint regularity premise. -/
theorem originalDirichletLabels_roots_iff (q : OriginalHminusOnePotential) (lambda : ℂ) :
    originalDirichletCharacteristic q lambda = 0 ↔
      ∃ n : ℕ+, lambda = (originalDirichletLabels q n:ℂ) :=
  hillHminusDirichletLabels_roots_iff _ _ lambda

theorem originalDirichletLabels_is_root (q : OriginalHminusOnePotential) (n : ℕ+) :
    originalDirichletCharacteristic q (originalDirichletLabels q n) = 0 :=
  (originalDirichletLabels_roots_iff q _).mpr ⟨n,rfl⟩

/-- Every original Dirichlet analytic multiplicity is counted exactly. -/
theorem originalDirichletLabels_global_multiplicity
    (q : OriginalHminusOnePotential) (lambda : ℂ) :
    (∑ᶠ n : ℕ+, if (originalDirichletLabels q n:ℂ) = lambda then (1:ℕ) else 0) =
      analyticOrderNatAt (originalDirichletCharacteristic q) lambda :=
  hillHminusDirichletLabels_global_multiplicity _ _ lambda

/-- The source's literal n-times-L2 asymptotic holds for the ENTIRE
original real scalar Dirichlet characteristic sequence. -/
theorem memlp_originalDirichletLabels_inverseIndex_error (q : OriginalHminusOnePotential) :
    Memℓp (fun n : ℕ+ =>
      ((originalDirichletLabels q n:ℂ)-((Real.pi:ℂ)*(n:ℕ))^2)/(n:ℕ)) 2 :=
  memlp_hillHminusDirichletLabels_inverseIndex_error _ _

/-- The actual same-index original Dirichlet labels lie in their original
high periodic gaps; exact midpoint deviation is at most half the gap. -/
theorem exists_originalDirichletLabels_in_high_gap (q : OriginalHminusOnePotential) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n:ℕ) →
      originalHillLabels q (2*(n:ℕ)-1) ≤ originalDirichletLabels q n ∧
      originalDirichletLabels q n ≤ originalHillLabels q (2*(n:ℕ)) ∧
      ‖(((originalHillLabels q (2*(n:ℕ)-1)+originalHillLabels q (2*(n:ℕ)))/2:ℝ):ℂ)-
          (originalDirichletLabels q n:ℂ)‖ ≤
        ‖((originalHillLabels q (2*(n:ℕ))-originalHillLabels q (2*(n:ℕ)-1):ℝ):ℂ)‖/2 :=
  exists_hillHminusDirichletLabels_in_high_gap _ _

end NLS.Articles.KdVPseudomeasures
