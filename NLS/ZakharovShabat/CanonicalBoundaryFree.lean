import NLS.ZakharovShabat.CanonicalBoundaryRoots
import NLS.ZakharovShabat.FreeBoundaryCharacteristic

/-! # Free values of the canonical boundary coordinates
Both ordered sequences reduce to the signed free lattice, with zero displacement.
-/

noncomputable section
open Set
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The free central root multiset has exactly one copy of each central lattice point. -/
theorem centralRoots_zero (hp : p ≠ ⊤) (N : ℕ) :
    b.centralRoots hp (0 : PairSpace p) (by simp) N =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({(Real.pi : ℂ)*n} : Multiset ℂ) := by
  unfold centralRoots
  rw [b.centralSpectrum_zero,Finset.sum_image]
  · simp only [b.algebraicMultiplicity_zero,Multiset.replicate_one]
  · intro n _ m _ hnm
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact_mod_cast mul_left_cancel₀ hpi hnm

/-- The free lattice is a complete boundary labeling at any admissible cutoff. -/
theorem rootLabeling_free (hp : p ≠ ⊤) (N : ℕ)
    (hc : BoundaryCountingData hp (0 : PairSpace p) (by simp) N) :
    BoundaryRootLabeling b hp (0 : PairSpace p) (by simp) N (fun n => (Real.pi : ℂ)*n) := by
  refine ⟨hc,(b.centralRoots_zero hp N).symm,?_,?_⟩
  · intro n _
    exact (b.eigenvalue_zero hp n).symm
  · simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := p))

/-- Every canonical free Dirichlet or Neumann root has its signed free index. -/
@[simp] theorem canonicalRoots_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    b.canonicalRoots hp hp1 (0 : PairSpace p) (by simp) n = (Real.pi : ℂ)*n := by
  have h := b.rootLabeling_free hp _ (b.canonicalRoots_spec hp hp1 0 (by simp)).1.counting
  have hs : Monotone (fun n : ℤ => complexLexKey ((Real.pi : ℂ)*n)) := by
    intro i j hij
    change complexLexLE ((Real.pi : ℂ)*i) ((Real.pi : ℂ)*j)
    have hi : (Real.pi : ℂ)*i = ((Real.pi*(i : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    have hj : (Real.pi : ℂ)*j = ((Real.pi*(j : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hi,hj,complexLexLE_ofReal_iff]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) Real.pi_pos.le
  exact (congrFun (BoundaryRootLabeling.eq_canonicalRoots hp1 h hs) n).symm

/-- Both canonical free displacements vanish in the original coefficient space. -/
@[simp] theorem canonicalDisplacement_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    b.canonicalDisplacement hp hp1 (0 : PairSpace p) (by simp) = 0 := by
  ext n
  simp only [canonicalDisplacement_apply,canonicalRoots_zero,sub_self]
  rfl

end NLS.ZakharovShabat.BoundaryCondition
