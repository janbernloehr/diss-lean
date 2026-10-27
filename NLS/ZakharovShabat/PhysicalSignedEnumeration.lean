import NLS.ZakharovShabat.ClassicalSignedPairCounts

/-! # Independent ordered physical periodic and antiperiodic eigenvalue lists -/
noncomputable section
set_option autoImplicit false
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A signed physical list is specified by lexicographic order, its free lattice,
and the actual classical operator's full Jordan-chain multiplicities. -/
structure PhysicalSignedPairData (u : IntervalPairL2) (r : ℤ) (ξ η : ℤ → ℂ) : Prop where
  left_displacement : Memℓp (fun n => ξ n-(Real.pi : ℂ)*(2*n+r : ℤ)) 2
  right_displacement : Memℓp (fun n => η n-(Real.pi : ℂ)*(2*n+r : ℤ)) 2
  within : ∀ n, complexLexLE (ξ n) (η n)
  between : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)
  multiplicity : ∀ z, (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
    classicalSignedAlgebraicMultiplicity u r z
  exhaustive : ∀ z, z ∈ classicalSignedSpectrum u r ↔ ∃ n : ℤ, ξ n = z ∨ η n = z

/-- The two actual classical signed operators admit separately sorted physical lists
with their exact algebraic multiplicities for every complex L2 potential. -/
theorem exists_physicalSignedPairData (u : IntervalPairL2) (r : ℤ) (hr : r = 0 ∨ r = 1) :
    ∃ ξ η : ℤ → ℂ, PhysicalSignedPairData u r ξ η := by
  have he : weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) =
      periodOnePotential (sourcePhysicalL2Equiv.symm u) := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨N,ξ,η,h,hw,ho⟩ := exists_ordered_completePeriodicParityPairs (by simp) (by norm_num)
    SpectralWeight.one (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u)))
    (by rw [he]; exact periodOnePotential_mem _)
  have hi : Function.Injective (fun n : ℤ => 2*n+r) := by intro a b hab; dsimp at hab; omega
  refine ⟨fun n => ξ (2*n+r),fun n => η (2*n+r),⟨?_,?_,fun n => hw (2*n+r),?_,?_,?_⟩⟩
  · rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact (h.left_displacement.summable (by norm_num)).comp_injective hi
  · rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact (h.right_displacement.summable (by norm_num)).comp_injective hi
  · intro i j hij
    exact ho (2*i+r) (2*j+r) (by omega) (by omega)
  · exact h.classicalSigned_multiplicity u r hr
  · exact h.classicalSigned_exhaustive u r hr

/-- The first member of each pair in the independently specified physical signed list. -/
def physicalSignedLeft (u : IntervalPairL2) (r : Fin 2) : ℤ → ℂ :=
  (exists_physicalSignedPairData u (r.val : ℤ) (by have := r.isLt; omega)).choose

/-- The second member of each pair in the same physical signed list. -/
def physicalSignedRight (u : IntervalPairL2) (r : Fin 2) : ℤ → ℂ :=
  (exists_physicalSignedPairData u (r.val : ℤ) (by have := r.isLt; omega)).choose_spec.choose

/-- The selected physical lists have the actual operator multiplicities, order and l2 asymptotics. -/
theorem physicalSignedPairs_spec (u : IntervalPairL2) (r : Fin 2) :
    PhysicalSignedPairData u (r.val : ℤ) (physicalSignedLeft u r) (physicalSignedRight u r) :=
  (exists_physicalSignedPairData u (r.val : ℤ) (by have := r.isLt; omega)).choose_spec.choose_spec

/-- The physical signed pair count is exactly the full actual classical algebraic multiplicity. -/
theorem physicalSignedPairs_count_multiplicity (u : IntervalPairL2) (r : Fin 2) (z : ℂ) :
    (∑ᶠ n : ℤ, ({physicalSignedLeft u r n,physicalSignedRight u r n} : Multiset ℂ).count z) =
      classicalSignedAlgebraicMultiplicity u (r.val : ℤ) z :=
  (physicalSignedPairs_spec u r).multiplicity z

/-- The separate physical lists exhaust the actual classical signed bounded-inverse spectra. -/
theorem physicalSignedPairs_exhaustive (u : IntervalPairL2) (r : Fin 2) (z : ℂ) :
    z ∈ classicalSignedSpectrum u (r.val : ℤ) ↔
      ∃ n : ℤ, physicalSignedLeft u r n = z ∨ physicalSignedRight u r n = z :=
  (physicalSignedPairs_spec u r).exhaustive z

end NLS.ZakharovShabat
