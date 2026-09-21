import NLS.ZakharovShabat.DeletedPairErrorLp
import NLS.ZakharovShabat.CanonicalPeriodicDisplacementBounds
import NLS.ZakharovShabat.DiscriminantPairFactorization

/-!
# Locally uniform lp errors for the canonical remaining product

The canonical endpoint displacement bounds transfer the generic deleted-pair
estimates to the actual discriminant factors. One neighborhood supplies
bounded lp majorants for values on half-pi discs and derivatives on quarter-pi
discs, including all free centers and possible endpoint collisions.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual remaining-product error relative to the filled squared free quotient. -/
def canonicalDeletedPairError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (z : ℂ) : ℂ :=
  canonicalDeletedPeriodicProduct hp hp1 φ heven n z-(freeSineQuotient n z)^2

/-- Canonical endpoint displacements recover the generic remaining-product error exactly. -/
theorem canonicalDeletedPairError_eq (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) :
    canonicalDeletedPairError hp hp1 φ heven =
      deletedPairError (canonicalPeriodicLeftDisplacement hp hp1 φ heven)
        (canonicalPeriodicRightDisplacement hp hp1 φ heven) := by
  have hl : displacedRoots (canonicalPeriodicLeftDisplacement hp hp1 φ heven) =
      canonicalPeriodicLeft hp hp1 φ heven := by
    funext n
    simp [displacedRoots,canonicalPeriodicLeftDisplacement_apply]
  have hr : displacedRoots (canonicalPeriodicRightDisplacement hp hp1 φ heven) =
      canonicalPeriodicRight hp hp1 φ heven := by
    funext n
    simp [displacedRoots,canonicalPeriodicRightDisplacement_apply]
  funext n z
  simp only [canonicalDeletedPairError,canonicalDeletedPeriodicProduct,deletedPairError,hl,hr]

/-- The derivative error is the difference of the two actual derivatives. -/
theorem deriv_canonicalDeletedPairError (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ) (z : ℂ) :
    deriv (canonicalDeletedPairError hp hp1 φ heven n) z =
      deriv (canonicalDeletedPeriodicProduct hp hp1 φ heven n) z-
        deriv (fun w => (freeSineQuotient n w)^2) z :=
  deriv_sub ((analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 φ heven n z (mem_univ _)).differentiableAt)
    (((differentiable_freeSineQuotient n).pow 2) z)

/-- A common open convex potential neighborhood supplies bounded value and derivative error majorants. -/
theorem exists_uniform_canonicalDeletedPairError_majorants (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∃ A : Coeff p, ‖A‖ ≤ K ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
          ‖canonicalDeletedPairError hp hp1 ψ heven n z‖ ≤ ‖A n‖) ∧
        (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
          ‖deriv (canonicalDeletedPairError hp hp1 ψ heven n) z‖ ≤ (4/Real.pi)*‖A n‖) := by
  obtain ⟨U,ho,hc,hφ,h0,R,hR,hbound⟩ := exists_uniform_bounded_canonicalPeriodicDisplacements hp hp1 φ
  obtain ⟨K,hK,hmajorant⟩ := exists_uniform_deletedPairError_majorants hp1 hp hR
  refine ⟨U,ho,hc,hφ,h0,K,hK,fun ψ hψ heven => ?_⟩
  obtain ⟨A,hA,hv,hd⟩ := hmajorant (canonicalPeriodicLeftDisplacement hp hp1 ψ heven)
    (canonicalPeriodicRightDisplacement hp hp1 ψ heven) (hbound ψ hψ heven).1 (hbound ψ hψ heven).2
  refine ⟨A,hA,?_,?_⟩
  · rw [canonicalDeletedPairError_eq]; exact hv
  · rw [canonicalDeletedPairError_eq]; exact hd

/-- Actual sampled remaining-product and derivative errors have locally uniform lp norms. -/
theorem exists_uniform_sampled_canonicalDeletedPairErrors (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ z : ℤ → ℂ,
        (∀ n, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) →
        ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ (4/Real.pi)*K ∧
          (∀ n, a n = canonicalDeletedPairError hp hp1 ψ heven n (z n)) ∧
          ∀ n, b n = deriv (canonicalDeletedPairError hp hp1 ψ heven n) (z n) := by
  obtain ⟨U,ho,hc,hφ,h0,K,hK,h⟩ := exists_uniform_canonicalDeletedPairError_majorants hp hp1 φ
  refine ⟨U,ho,hc,hφ,h0,K,hK,fun ψ hψ heven z hz => ?_⟩
  obtain ⟨A,hA,hv,hd⟩ := h ψ hψ heven
  have hval (n : ℤ) : ‖canonicalDeletedPairError hp hp1 ψ heven n (z n)‖ ≤ ‖A n‖ :=
    hv n (z n) (by linarith [hz n,Real.pi_pos])
  let B : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
  have hder (n : ℤ) : ‖deriv (canonicalDeletedPairError hp hp1 ψ heven n) (z n)‖ ≤ ‖B n‖ := by
    simpa only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd n (z n) (hz n)
  let a : Coeff p := ⟨_,(lp.memℓp A).mono' hval⟩
  let b : Coeff p := ⟨_,(lp.memℓp B).mono' hder⟩
  refine ⟨a,b,(lp.norm_mono (zero_lt_one.trans hp1).ne' hval).trans hA,
    (lp.norm_mono (zero_lt_one.trans hp1).ne' hder).trans ?_,fun _ => rfl,fun _ => rfl⟩
  change ‖((4/Real.pi : ℝ) : ℂ) • A‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)]
  exact mul_le_mul_of_nonneg_left hA (by positivity)

/-- At any fixed even potential the sampled value and derivative errors both belong to lp. -/
theorem memℓp_sampled_canonicalDeletedPairErrors (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (z : ℤ → ℂ)
    (hz : ∀ n, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/4) :
    Memℓp (fun n => canonicalDeletedPairError hp hp1 φ heven n (z n)) p ∧
      Memℓp (fun n => deriv (canonicalDeletedPairError hp hp1 φ heven n) (z n)) p := by
  rw [canonicalDeletedPairError_eq]
  exact ⟨memℓp_deletedPairError hp1 hp _ _ z (fun n => by linarith [hz n,Real.pi_pos]),
    memℓp_deriv_deletedPairError hp1 hp _ _ z hz⟩

end NLS.ZakharovShabat
