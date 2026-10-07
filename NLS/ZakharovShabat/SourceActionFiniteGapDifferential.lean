import NLS.ZakharovShabat.SourceBirkhoffActionHamiltonian
import NLS.ZakharovShabat.SourceActionSequenceExponent
import NLS.ZakharovShabat.SourceFiniteGap

/-! # Finite support of the full action differential

At a real collapsed gap the full complex action differential vanishes,
including directions that open that gap. Consequently the Banach action
sequence differential at a finite-gap source has a single finite support
for every direction. This gives a finite chain rule for any differentiable
function of the actions.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A collapsed real gap has zero full complex action differential. -/
theorem sourceComplexAction_fderiv_eq_zero_of_closed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hn : sourcePeriodicGapDisplacement hp hp1 φ n = 0) :
    fderiv ℂ (sourceComplexAction hp hp1 n) φ = 0 := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨hx,hy⟩ := D.real_closed_gap_zero φ (D.real_subset hφ) hφ n hn
  rw [D.actionDifferential_eq_map_rectangular n φ (D.real_subset hφ),hx,hy]
  ext h
  simp only [add_apply,smul_apply,smul_eq_mul,zero_mul,add_zero]
  rfl

/-- A finite-gap source has one finite cutoff supporting all its action cotangents. -/
theorem exists_sourceComplexAction_fderiv_support
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ S : Finset ℤ, ∀ n ∉ S, fderiv ℂ (sourceComplexAction hp hp1 n) φ.val = 0 := by
  classical
  refine ⟨hf.toFinset,fun n hn => ?_⟩
  apply sourceComplexAction_fderiv_eq_zero_of_closed_gap hp hp1 φ.val φ.property n
  rw [sourcePeriodicGapDisplacement_apply]
  by_contra h
  exact hn (hf.mem_toFinset.mpr h)

namespace SourceBirkhoffMapComplexData
variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full sequence derivative is a finite sum, on arbitrary source directions. -/
theorem actionSequence_fderiv_eq_finite_sum
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction hp hp1 n) φ.val = 0)
    (h : CoeffPair p) :
    fderiv ℂ (sourceActionSequence (q := q) hp hp1 s) φ.val h =
      ∑ n ∈ S, lp.single q n ((fderiv ℂ (sourceComplexAction hp hp1 n) φ.val) h) := by
  classical
  ext n
  rw [D.actionSequence_fderiv_apply φ.val (D.real_subset φ.property)]
  change _ = (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n) _
  rw [map_sum]
  by_cases hn : n ∈ S
  · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn]
  · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,hn,hS n hn]

/-- Differentiating any differentiable action Hamiltonian reduces to the active actions. -/
theorem fderiv_comp_actionSequence_eq_finite_sum
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : realTypeSourceSubmodule p) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction hp hp1 n) φ.val = 0)
    (H : Coeff q → ℂ)
    (hH : DifferentiableAt ℂ H (sourceActionSequence hp hp1 s φ.val)) (h : CoeffPair p) :
    fderiv ℂ (fun ψ => H (sourceActionSequence (q := q) hp hp1 s ψ)) φ.val h =
      ∑ n ∈ S, (fderiv ℂ H (sourceActionSequence hp hp1 s φ.val) (lp.single q n 1)) *
        ((fderiv ℂ (sourceComplexAction hp hp1 n) φ.val) h) := by
  change fderiv ℂ (H ∘ sourceActionSequence (q := q) hp hp1 s) φ.val h = _
  rw [fderiv_comp φ.val hH (D.actionSequence_analytic φ.val (D.real_subset φ.property)).differentiableAt]
  change (fderiv ℂ H _) (fderiv ℂ (sourceActionSequence hp hp1 s) φ.val h) = _
  rw [D.actionSequence_fderiv_eq_finite_sum φ S hS h,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he (c : ℂ) : (lp.single q n c : Coeff q) = c • lp.single q n (1 : ℂ) := by
    ext k
    simp [lp.single_apply,Pi.single_apply]
  rw [he,map_smul,smul_eq_mul,mul_comm]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
