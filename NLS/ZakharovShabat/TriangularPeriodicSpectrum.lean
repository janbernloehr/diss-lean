import NLS.ZakharovShabat.PeriodicSpectrum
import NLS.ZakharovShabat.SourceFiniteGapClosingCriterion

/-! # The actual periodic spectrum of complex triangular sources

A triangular potential (u,0) has free periodic spectrum at every finite
Banach exponent. The perturbation of the free inverse is square-zero,
so the inverse is a finite expression without a smallness assumption.
This applies to arbitrary coefficient potentials, including rough sources.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The second row of a triangular potential operator vanishes. -/
theorem potentialOperator_triangular (hp : p ≠ ⊤) (u : Coeff p) (f : Domain p) :
    potentialOperator hp (u,0) f = (potentialMul hp u f.2,0) := by
  apply Prod.ext
  · rfl
  · ext n
    simp [potentialOperator_apply,potentialMul_apply]

/-- The free-resolvent perturbation of a triangular potential is square-zero. -/
theorem potentialFreeResolvent_triangular_square (hp : p ≠ ⊤) (u : Coeff p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    potentialFreeResolvent hp (u,0) z hz (potentialFreeResolvent hp (u,0) z hz a) = 0 := by
  have hR (b : PairSpace p) : (freeResolventToDomain z hz b).2 = scalarFreeResolvent z hz b.2 := rfl
  simp only [potentialFreeResolvent,ContinuousLinearMap.comp_apply,potentialOperator_triangular,hR,
    map_zero,Prod.mk_zero_zero]

/-- The exact triangular inverse maps into the original one-derivative domain. -/
def triangularResolventToDomain (hp : p ≠ ⊤) (u : Coeff p) (z : ℂ) (hz : z ∉ freeLattice) :
    PairSpace p →L[ℂ] Domain p :=
  (freeResolventToDomain z hz).comp (1+potentialFreeResolvent hp (u,0) z hz)

/-- Right inverse identity, with no norm restriction on the potential. -/
theorem spectralPencil_triangularResolvent (hp : p ≠ ⊤) (u : Coeff p)
    (z : ℂ) (hz : z ∉ freeLattice) (a : PairSpace p) :
    spectralPencil hp (u,0) z (triangularResolventToDomain hp u z hz a) = a := by
  rw [spectralPencil_factorization hp (u,0) z hz]
  simp only [triangularResolventToDomain,ContinuousLinearMap.comp_apply,add_apply,
    one_apply_eq_self,freePencil_freeResolventToDomain,map_add,
    potentialFreeResolvent_triangular_square,add_zero,add_sub_cancel_right]

/-- Left inverse identity on the full original domain. -/
theorem triangularResolvent_spectralPencil (hp : p ≠ ⊤) (u : Coeff p)
    (z : ℂ) (hz : z ∉ freeLattice) (f : Domain p) :
    triangularResolventToDomain hp u z hz (spectralPencil hp (u,0) z f) = f := by
  rw [spectralPencil_factorization hp (u,0) z hz]
  simp only [triangularResolventToDomain,ContinuousLinearMap.comp_apply,add_apply,
    one_apply_eq_self,map_sub,map_add,potentialFreeResolvent_triangular_square,add_zero,
    add_sub_cancel_right,freeResolventToDomain_freePencil]

/-- Every point off the free lattice is in the actual triangular resolvent set. -/
theorem mem_resolventSet_triangular (hp : p ≠ ⊤) (u : Coeff p) {z : ℂ} (hz : z ∉ freeLattice) :
    z ∈ resolventSet hp (u,0) :=
  ⟨Function.LeftInverse.injective (triangularResolvent_spectralPencil hp u z hz),
    Function.RightInverse.surjective (spectralPencil_triangularResolvent hp u z hz)⟩

/-- Every free frequency remains an actual triangular eigenvalue. -/
theorem freeLattice_subset_periodicSpectrum_triangular (hp : p ≠ ⊤) (u : Coeff p) :
    freeLattice ⊆ periodicSpectrum hp (u,0) := by
  rintro z ⟨n,rfl⟩
  apply (mem_periodicSpectrum_iff_exists_eigenvector hp (u,0) _).mpr
  refine ⟨negativeMode n,?_,?_⟩
  · intro h
    apply domainInclusion_negativeMode_ne_zero (p := p) n
    rw [h,map_zero]
  · change freeOperator (negativeMode n) + potentialOperator hp (u,0) (negativeMode n) = _
    rw [potentialOperator_triangular]
    simp only [negativeMode,map_zero,Prod.mk_zero_zero,add_zero]
    exact freeOperator_negativeMode n

/-- The whole periodic spectrum, not just distant roots, is exactly the free lattice. -/
theorem periodicSpectrum_triangular (hp : p ≠ ⊤) (u : Coeff p) :
    periodicSpectrum hp (u,0) = freeLattice := by
  apply Set.Subset.antisymm _ (freeLattice_subset_periodicSpectrum_triangular hp u)
  intro z hz
  by_contra h
  exact hz (mem_resolventSet_triangular hp u h)

/-- The original period-one source embedding preserves triangularity and the free spectrum. -/
theorem sourcePeriodicSpectrum_triangular (hp : p ≠ ⊤) (u : Coeff p) :
    periodicSpectrum hp (periodOnePotential (WithLp.toLp p (u,0))) = freeLattice := by
  simpa only [periodOnePotential_apply,WithLp.toLp_fst,WithLp.toLp_snd,map_zero] using
    periodicSpectrum_triangular hp (Coeff.periodDouble u)

/-- A free-lattice point in a resonant strip is its center. -/
theorem mem_freeLattice_iff_eq_center_of_mem_resonantStrip (n : ℤ) {z : ℂ}
    (hz : z ∈ resonantStrip n) : z ∈ freeLattice ↔ z = (Real.pi : ℂ)*n := by
  constructor
  · rintro ⟨m,rfl⟩
    have h : |(m : ℝ)-(n : ℝ)| ≤ 1/2 := by
      change |((Real.pi : ℂ)*m).re-Real.pi*n| ≤ Real.pi/2 at hz
      simp only [mul_re,ofReal_re,ofReal_im,intCast_re,intCast_im,mul_zero,sub_zero] at hz
      rw [← mul_sub,abs_mul,abs_of_pos Real.pi_pos] at hz
      nlinarith [Real.pi_pos]
    have hm : m = n := by
      rw [abs_le] at h
      have hl : (n : ℝ)-1 < m := by linarith
      have hu : (m : ℝ) < n+1 := by linarith
      have hl' : n-1 < m := by exact_mod_cast hl
      have hu' : m < n+1 := by exact_mod_cast hu
      omega
    rw [hm]
  · rintro rfl
    exact ⟨n,rfl⟩

/-- Every complex triangular source is spectrally finite-gap in the source's
literal sense: only finitely many canonical indexed gaps can be nonzero. -/
theorem finite_canonicalPeriodicGap_triangular (hp : p ≠ ⊤) (hp1 : 1 < p) (u : Coeff p) :
    {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential (WithLp.toLp p (u,0)))
      (periodOnePotential_mem (WithLp.toLp p (u,0))) n ≠ 0}.Finite := by
  apply finite_canonicalPeriodicGap_of_singleton_strips hp hp1 _ 0 (fun n => (Real.pi : ℂ)*n)
  intro n _ z hz
  rw [sourcePeriodicSpectrum_triangular]
  exact mem_freeLattice_iff_eq_center_of_mem_resonantStrip n hz

end NLS.ZakharovShabat
