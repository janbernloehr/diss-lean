import NLS.ZakharovShabat.UniformCanonicalPeriodicEndpoints

/-!
# Canonical periodic endpoints at zero potential

The free central multiset has two copies of each lattice center. Comparing
ordered central enumerations at an enlarged cutoff identifies every signed
canonical coordinate, without making any choice of distant roots.
-/

noncomputable section
open Complex
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free central roots are exactly two copies of every central lattice point. -/
theorem centralPeriodicRoots_zero (hp : p ≠ ⊤) (N : ℕ) :
    centralPeriodicRoots hp 0 N =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({(Real.pi : ℂ)*n,(Real.pi : ℂ)*n} : Multiset ℂ) := by
  unfold centralPeriodicRoots
  rw [centralPeriodicSpectrum_zero, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n _
    simp [periodicAlgebraicMultiplicity_zero, Multiset.replicate_succ, Multiset.insert_eq_cons]
  · intro a _ b _ h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact_mod_cast mul_left_cancel₀ hπ h

/-- The repeated free lattice centers give a central endpoint labeling at every cutoff. -/
theorem centralPeriodicLabeling_free (hp : p ≠ ⊤) (N : ℕ) :
    CentralPeriodicLabeling hp 0 N (fun n => (Real.pi : ℂ)*n) (fun n => (Real.pi : ℂ)*n) :=
  ⟨(centralPeriodicRoots_zero hp N).symm⟩

/-- Both canonical periodic endpoints collapse to the free lattice center at zero potential. -/
theorem canonicalPeriodicEndpoints_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalPeriodicLeft hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n ∧
    canonicalPeriodicRight hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n := by
  obtain ⟨hl,hw,hc⟩ := canonicalPeriodicEndpoints_spec hp hp1 0 (pairParitySubspace 0).zero_mem
  let K := max (canonicalPeriodicCutoff hp hp1 0 (pairParitySubspace 0).zero_mem) n.natAbs
  have hs (i j : ℤ) (hij : i < j) : complexLexLE ((Real.pi : ℂ)*i) ((Real.pi : ℂ)*j) := by
    have he (k : ℤ) : (Real.pi : ℂ)*k = ((Real.pi*(k : ℝ) : ℝ) : ℂ) := by simp
    rw [he i,he j,complexLexLE_ofReal_iff]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij.le) Real.pi_pos.le
  exact (hl.central_at_larger_cutoff K (le_max_left _ _)).ordered_unique
    (centralPeriodicLabeling_free hp K) hw hc (fun _ => le_refl _) hs n (le_max_right _ _)

@[simp] theorem canonicalPeriodicLeft_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalPeriodicLeft hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n :=
  (canonicalPeriodicEndpoints_zero hp hp1 n).1

@[simp] theorem canonicalPeriodicRight_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalPeriodicRight hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n :=
  (canonicalPeriodicEndpoints_zero hp hp1 n).2

/-- The left canonical displacement vanishes identically at the free potential. -/
@[simp] theorem canonicalPeriodicLeftDisplacement_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    canonicalPeriodicLeftDisplacement hp hp1 0 (pairParitySubspace 0).zero_mem = 0 := by
  ext n
  simp only [canonicalPeriodicLeftDisplacement_apply, canonicalPeriodicLeft_zero, sub_self,
    lp.coeFn_zero, Pi.zero_apply]

/-- The right canonical displacement vanishes identically at the free potential. -/
@[simp] theorem canonicalPeriodicRightDisplacement_zero (hp : p ≠ ⊤) (hp1 : 1 < p) :
    canonicalPeriodicRightDisplacement hp hp1 0 (pairParitySubspace 0).zero_mem = 0 := by
  ext n
  simp only [canonicalPeriodicRightDisplacement_apply, canonicalPeriodicRight_zero, sub_self,
    lp.coeFn_zero, Pi.zero_apply]

end NLS.ZakharovShabat
