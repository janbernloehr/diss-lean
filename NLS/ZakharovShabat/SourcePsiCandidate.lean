import NLS.ZakharovShabat.SourcePsiFree

/-!
# The entire psi numerator family in equation (2.23)

The unknown roots in Section 12 are represented by an `ℓᵖ` sequence
of displacements from the free lattice. Removing the index `n` from
the normalized product produces an entire numerator. Its value does
not depend on the unused `n`th displacement, and each other displaced
root is a zero. This is the function family entering the contour map
of Lemma 12.4, before solving its implicit equations.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.23), jointly in the spectral parameter and an `ℓᵖ`
sequence of root displacements. The deleted index's coordinate is unused. -/
def sourcePsiCandidate (n : ℤ) : ℂ × Coeff p → ℂ :=
  fun t => -2 * jointDeletedSingleSpectralProduct n t

/-- The candidate is the limit of the literal symmetric products in
(2.23), with the exceptional zero-mode denominator included. -/
theorem tendsto_sourcePsiCandidate_partialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (t : ℂ × Coeff p) :
    Tendsto (fun N => -2 * jointDeletedSingleSpectralPartialProduct n N t)
      atTop (𝓝 (sourcePsiCandidate n t)) := by
  exact (tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n t).const_mul (-2)

/-- The psi numerator is jointly analytic in its spectral parameter
and all root displacements. -/
theorem analyticOnNhd_sourcePsiCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourcePsiCandidate (p := p) n) univ := by
  intro t _
  exact analyticAt_const.mul
    (analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 n t (mem_univ _))

/-- For any fixed root sequence, the candidate is entire in the
spectral parameter. -/
theorem differentiable_sourcePsiCandidate
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) :
    Differentiable ℂ (fun z => sourcePsiCandidate n (z,a)) := by
  intro z
  exact ((analyticOnNhd_sourcePsiCandidate hp hp1 n (z,a) (mem_univ _)).comp
    (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- The candidate specializes to the normalized free psi-function. -/
theorem sourcePsiCandidate_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (z : ℂ) :
    sourcePsiCandidate n (z,(0 : Coeff p)) = sourcePsiFree n z := by
  rw [sourcePsiCandidate,
    (congrFun (jointDeletedSingleSpectralProduct_zero_eq_freeSineQuotient hp hp1 n) z)]
  rfl

omit [Fact (1 ≤ p)] in
/-- Each root at an index other than `n` annihilates all sufficiently
large literal cutoffs of the deleted product. -/
theorem eventually_jointDeletedSingleSpectralPartialProduct_other_root
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p) :
    ∀ᶠ N : ℕ in atTop,
      jointDeletedSingleSpectralPartialProduct n N
        (displacedRoots a m,a) = 0 := by
  filter_upwards [eventually_ge_atTop m.natAbs] with N hN
  unfold jointDeletedSingleSpectralPartialProduct
  have hmem : m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n :=
    Finset.mem_erase.mpr ⟨hmn, by
      simp only [Finset.mem_Icc]
      constructor <;> omega⟩
  have hprod : (∏ k ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      singleSpectralFactor (displacedRoots a) (displacedRoots a m) k) = 0 := by
    apply Finset.prod_eq_zero hmem
    simp [singleSpectralFactor]
  rw [hprod]
  simp

/-- Every displaced root except the deleted one is a zero of the
entire candidate, even if roots collide. -/
theorem sourcePsiCandidate_other_root
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hmn : m ≠ n) (a : Coeff p) :
    sourcePsiCandidate n (displacedRoots a m,a) = 0 := by
  have hlim := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n
    (displacedRoots a m,a)
  have hzero : jointDeletedSingleSpectralProduct n
      (displacedRoots a m,a) = 0 := by
    exact tendsto_nhds_unique hlim
      (tendsto_const_nhds.congr' ((eventually_jointDeletedSingleSpectralPartialProduct_other_root
        n m hmn a).mono (fun _ h => h.symm)))
  simp [sourcePsiCandidate, hzero]

omit [Fact (1 ≤ p)] in
/-- The finite deleted numerator ignores its deleted coordinate. -/
theorem jointDeletedSingleSpectralPartialProduct_eq_of_off_index
    (n : ℤ) (N : ℕ) (z : ℂ) (a b : Coeff p)
    (hab : ∀ m : ℤ, m ≠ n → a m = b m) :
    jointDeletedSingleSpectralPartialProduct n N (z,a) =
      jointDeletedSingleSpectralPartialProduct n N (z,b) := by
  unfold jointDeletedSingleSpectralPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  simp only [singleSpectralFactor, displacedRoots]
  rw [hab m (Finset.mem_erase.mp hm).1]

/-- The full candidate depends only on the `ℓᵖ` coordinates outside
its deleted index. -/
theorem sourcePsiCandidate_eq_of_off_index
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ) (a b : Coeff p)
    (hab : ∀ m : ℤ, m ≠ n → a m = b m) :
    sourcePsiCandidate n (z,a) = sourcePsiCandidate n (z,b) := by
  have hlimA := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n (z,a)
  have hlimB := tendsto_jointDeletedSingleSpectralPartialProduct hp hp1 n (z,b)
  have heq : (fun N => jointDeletedSingleSpectralPartialProduct n N (z,a)) =
      (fun N => jointDeletedSingleSpectralPartialProduct n N (z,b)) := by
    funext N
    exact jointDeletedSingleSpectralPartialProduct_eq_of_off_index n N z a b hab
  rw [heq] at hlimA
  have h := tendsto_nhds_unique hlimA hlimB
  exact congrArg ((-2 : ℂ) * ·) h

end NLS.ZakharovShabat
