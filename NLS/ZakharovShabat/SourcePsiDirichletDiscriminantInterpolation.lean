import NLS.ZakharovShabat.SourceDirichletDiscriminantKernel
import NLS.ZakharovShabat.SourcePsiDirichletInterpolation

/-! # Filled actual discriminant interpolation at every spectral parameter

The weighted Dirichlet interpolation identifies the symmetric kernel sum
away from characteristic zeros. At an actual Dirichlet zero only its own
filled kernel survives. This proves the same limit at every parameter.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At any actual Dirichlet root, every other filled kernel vanishes. -/
theorem sourceDirichletDiscriminantKernel_at_other_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (m j : ℤ) (hmj : m ≠ j) :
    sourceDirichletDiscriminantKernel hp hp1 m φ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val j) = 0 := by
  rw [sourceDirichletDiscriminantKernel_eq hp hp1 m φ.val _
    ((injective_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property).ne hmj),
    periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero,zero_div]

/-- The actual filled discriminant kernel sums converge to minus
one half the numerator at every parameter, for every finite `p > 1`. -/
theorem tendsto_sourcePsiDirichlet_discriminantKernelSums
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : realTypeSourceLocus p) (w : ℂ) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,a)*
        sourceDirichletDiscriminantKernel hp hp1 m φ.val w) atTop
      (𝓝 (-sourcePsiCandidate n (w,a)/2)) := by
  by_cases hw : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ.val w = 0
  · obtain ⟨j,hj⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 .dirichlet φ.val w).mp
      ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 .dirichlet φ.val w).mp hw)
    have hterm (m : ℤ) :
        sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m,a)*
          sourceDirichletDiscriminantKernel hp hp1 m φ.val w =
        if m = j then -sourcePsiCandidate n (w,a)/2 else 0 := by
      by_cases hm : m = j
      · subst m
        rw [if_pos rfl,← hj,sourceDirichletDiscriminantKernel_at_root hp hp1 j φ.val φ.property]
        ring
      · rw [if_neg hm,← hj,sourceDirichletDiscriminantKernel_at_other_root hp hp1 φ m j hm,mul_zero]
    apply (tendsto_const_nhds (x := -sourcePsiCandidate n (w,a)/2)).congr'
    filter_upwards [eventually_ge_atTop j.natAbs] with N hN
    have hmem : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by simp only [Finset.mem_Icc]; omega
    symm
    calc
      _ = ∑ m ∈ Finset.Icc (-(N : ℤ)) N, if m = j then -sourcePsiCandidate n (w,a)/2 else 0 :=
        Finset.sum_congr rfl (fun m _ => hterm m)
      _ = -sourcePsiCandidate n (w,a)/2 := by simp [hmem]
  · have hi := (tendsto_sourcePsiDirichlet_weightedInterpolation hp hp1 n a φ w hw).const_mul (1/2 : ℂ)
    have hlimit : (1/2 : ℂ)*(-sourcePsiCandidate n (w,a)) = -sourcePsiCandidate n (w,a)/2 := by ring
    rw [hlimit] at hi
    apply hi.congr'
    apply Eventually.of_forall
    intro N
    dsimp only
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    have hmw : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m ≠ w := by
      intro he
      exact hw (he ▸ periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet φ.val m)
    rw [sourceDirichletDiscriminantKernel_eq hp hp1 m φ.val w hmw]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

end NLS.ZakharovShabat
