import NLS.KdV.SingularHillRealSpectrum
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-!
# The free singular Hill eigenspaces on the full original domain

The zero potential is treated on the original period-two H1/H-minus-one
spaces. Its constant eigenspace has dimension one and every positive Fourier
shell has dimension two. These statements do not transport a regular-potential
operator to a singular domain.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- Equality of free values detects exactly the two signed resonant modes. -/
theorem freeHillValue_eq_iff (k j : ℤ) :
    freeHillValue k = freeHillValue j ↔ k = j ∨ k = -j := by
  constructor
  · intro h
    have hs : (k:ℝ)^2 = (j:ℝ)^2 := mul_left_cancel₀
      (pow_ne_zero 2 Real.pi_ne_zero) h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  · rintro (rfl | rfl) <;> simp

/-- The full original zero-potential equation is diagonal at every Fourier mode. -/
theorem singularHill_zero_eigen_iff (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator 0 f = z • singularHillDomainInclusion f ↔
      ∀ k : ℤ, (z-(freeHillValue k:ℂ))*f.val (mode (-k)) = 0 := by
  rw [singularHillOperator_eigen_iff]
  change (∀ k : ℤ, (z-(freeHillValue k:ℂ))*f.val (mode (-k)) =
    ∑' j : ℤ, 0*f.val (mode (-j))) ↔ _
  simp only [zero_mul,tsum_zero]

/-- At a free Fourier value, an original eigenvector is supported exactly on its shell. -/
theorem singularHill_zero_eigen_iff_support (j : ℤ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator 0 f = (freeHillValue j:ℂ) • singularHillDomainInclusion f ↔
      ∀ k : ℤ, k ≠ j → k ≠ -j → f.val (mode (-k)) = 0 := by
  rw [singularHill_zero_eigen_iff]
  constructor
  · intro h k hkj hkn
    apply (mul_eq_zero.mp (h k)).resolve_left
    apply sub_ne_zero.mpr
    intro he
    have he' : freeHillValue k = freeHillValue j := Complex.ofReal_injective he.symm
    exact ((freeHillValue_eq_iff k j).mp he').elim hkj hkn
  · intro h k
    by_cases hp : k = j
    · simp [hp]
    by_cases hm : k = -j
    · simp [hm]
    rw [h k hp hm, mul_zero]

/-- A genuine physical unit Fourier mode on the full original H1 domain. -/
def singularHillFreeMode (k : ℤ) : FourierLebesgueSpace (2:ℝ) 1 2 :=
  ofSmooth 1 2 (mode k)

@[simp] theorem singularHillFreeMode_coefficient (k j : ℤ) :
    (singularHillFreeMode k).val (mode (-j)) = if j = k then 1 else 0 :=
  ofSmooth_h1_mode_coefficient k j

@[simp] theorem singularHillFreeMode_apply (k j : ℤ) :
    (singularHillFreeMode k).val (mode j) = if j = -k then 1 else 0 := by
  simpa only [neg_neg,neg_eq_iff_eq_neg] using singularHillFreeMode_coefficient k (-j)

/-- Every physical unit Fourier mode is nonzero. -/
theorem singularHillFreeMode_ne_zero (k : ℤ) : singularHillFreeMode k ≠ 0 := by
  intro h
  have he := congrArg (fun f : FourierLebesgueSpace (2:ℝ) 1 2 => f.val (mode (-k))) h
  change (singularHillFreeMode k).val (mode (-k)) = 0 at he
  simp at he

/-- Every physical unit mode solves the actual free operator equation. -/
theorem singularHillFreeMode_eigen (k : ℤ) :
    singularHillOperator 0 (singularHillFreeMode k) =
      (freeHillValue k:ℂ) • singularHillDomainInclusion (singularHillFreeMode k) := by
  apply (singularHill_zero_eigen_iff_support k _).mpr
  intro j hj _
  simp [hj]

/-- A nonzero free eigenvector has one of the genuine free Fourier values. -/
theorem singularHill_zero_eigenvalue_iff (z : ℂ) :
    (∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator 0 f = z • singularHillDomainInclusion f) ↔
      ∃ n : ℕ, z = (freeHillValue n:ℂ) := by
  constructor
  · rintro ⟨f,hf,he⟩
    have hex : ∃ k : ℤ, f.val (mode (-k)) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply Subtype.ext
      apply Distribution.ext_coefficients
      exact h
    obtain ⟨k,hk⟩ := hex
    have hv := (mul_eq_zero.mp ((singularHill_zero_eigen_iff z f).mp he k)).resolve_right hk
    refine ⟨k.natAbs,(sub_eq_zero.mp hv).trans ?_⟩
    congr 1
    exact (freeHillValue_eq_iff k (k.natAbs:ℤ)).mpr (by omega)
  · rintro ⟨n,rfl⟩
    exact ⟨singularHillFreeMode n,singularHillFreeMode_ne_zero n,singularHillFreeMode_eigen n⟩

/-- The constant Fourier amplitude parametrizes the entire zero eigenspace. -/
def singularHillFreeConstantMap : ℂ →ₗ[ℂ] singularHillEigenspace 0 0 where
  toFun c := ⟨c • singularHillFreeMode 0, by
    apply (mem_singularHillEigenspace_iff 0 0 _).mpr
    have h := singularHillFreeMode_eigen 0
    simpa [freeHillValue, map_smul] using congrArg (fun f => c • f) h⟩
  map_add' _ _ := Subtype.ext (add_smul _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul _ _ _)

/-- The actual zero eigenspace has no extra H1 solutions. -/
theorem singularHillFreeConstantMap_bijective : Function.Bijective singularHillFreeConstantMap := by
  constructor
  · intro c d h
    have he := congrArg (fun f : singularHillEigenspace 0 0 => f.val.val (mode 0)) h
    change c*(singularHillFreeMode 0).val (mode 0) = d*(singularHillFreeMode 0).val (mode 0) at he
    simpa using he
  · intro f
    refine ⟨f.val.val (mode 0),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    have hs := (singularHill_zero_eigen_iff_support 0 f.val).mp (by
      simpa [freeHillValue] using (mem_singularHillEigenspace_iff 0 0 f.val).mp f.property)
    change f.val.val (mode 0) * (singularHillFreeMode 0).val (mode (-k)) = _
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk,hs k hk (by simpa using hk)]

/-- The full original constant eigenspace has complex dimension one. -/
theorem finrank_singularHillEigenspace_zero : Module.finrank ℂ (singularHillEigenspace 0 0) = 1 := by
  rw [← (LinearEquiv.ofBijective singularHillFreeConstantMap
    singularHillFreeConstantMap_bijective).finrank_eq]
  exact Module.finrank_self ℂ

/-- Both signed amplitudes parametrize the genuine positive free shell. -/
def singularHillFreePairMap (n : ℕ) : (ℂ × ℂ) →ₗ[ℂ]
    singularHillEigenspace 0 (freeHillValue n:ℂ) where
  toFun c := ⟨c.1 • singularHillFreeMode n+c.2 • singularHillFreeMode (-(n:ℤ)), by
    apply (mem_singularHillEigenspace_iff 0 _ _).mpr
    rw [map_add,map_smul,map_smul,singularHillFreeMode_eigen,singularHillFreeMode_eigen,
      freeHillValue_neg,map_add,map_smul,map_smul,smul_add]
    module⟩
  map_add' c d := by
    apply Subtype.ext
    change (c.1+d.1) • singularHillFreeMode n+(c.2+d.2) • singularHillFreeMode (-(n:ℤ)) = _
    simp only [add_smul]
    change _ = (c.1 • singularHillFreeMode n+c.2 • singularHillFreeMode (-(n:ℤ)))+
      (d.1 • singularHillFreeMode n+d.2 • singularHillFreeMode (-(n:ℤ)))
    abel
  map_smul' c d := by
    apply Subtype.ext
    change (c*d.1) • singularHillFreeMode n+(c*d.2) • singularHillFreeMode (-(n:ℤ)) =
      c • (d.1 • singularHillFreeMode n+d.2 • singularHillFreeMode (-(n:ℤ)))
    simp only [mul_smul,smul_add]

/-- Reading the signed resonant coefficients inverts the full positive free eigenspace map. -/
theorem singularHillFreePairMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (singularHillFreePairMap n) := by
  have hpm : (n:ℤ) ≠ -(n:ℤ) := by omega
  have hmp : -(n:ℤ) ≠ (n:ℤ) := Ne.symm hpm
  constructor
  · intro c d h
    apply Prod.ext
    · have he := congrArg (fun f : singularHillEigenspace 0 (freeHillValue n:ℂ) =>
        f.val.val (mode (-(n:ℤ)))) h
      change c.1*(singularHillFreeMode n).val (mode (-(n:ℤ)))+
        c.2*(singularHillFreeMode (-(n:ℤ))).val (mode (-(n:ℤ))) =
        d.1*(singularHillFreeMode n).val (mode (-(n:ℤ)))+
        d.2*(singularHillFreeMode (-(n:ℤ))).val (mode (-(n:ℤ))) at he
      simpa only [singularHillFreeMode_coefficient,ite_true,if_neg hpm,mul_one,mul_zero,add_zero] using he
    · have he := congrArg (fun f : singularHillEigenspace 0 (freeHillValue n:ℂ) =>
        f.val.val (mode (n:ℤ))) h
      change c.1*(singularHillFreeMode n).val (mode (n:ℤ))+
        c.2*(singularHillFreeMode (-(n:ℤ))).val (mode (n:ℤ)) =
        d.1*(singularHillFreeMode n).val (mode (n:ℤ))+
        d.2*(singularHillFreeMode (-(n:ℤ))).val (mode (n:ℤ)) at he
      simpa only [singularHillFreeMode_apply,neg_neg,if_neg hpm,ite_true,mul_one,mul_zero,zero_add] using he
  · intro f
    refine ⟨(f.val.val (mode (-(n:ℤ))),f.val.val (mode (n:ℤ))),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    have hs := (singularHill_zero_eigen_iff_support (n:ℤ) f.val).mp
      ((mem_singularHillEigenspace_iff 0 _ _).mp f.property)
    change f.val.val (mode (-(n:ℤ))) * (singularHillFreeMode n).val (mode (-k)) +
      f.val.val (mode (n:ℤ)) * (singularHillFreeMode (-(n:ℤ))).val (mode (-k)) = _
    by_cases hp : k = (n:ℤ)
    · subst k
      simp only [singularHillFreeMode_coefficient,ite_true,if_neg hpm,mul_one,mul_zero,add_zero]
    by_cases hm : k = -(n:ℤ)
    · subst k
      simp only [singularHillFreeMode_apply,neg_neg,if_neg hpm,ite_true,mul_zero,mul_one,zero_add]
    · simp only [singularHillFreeMode_coefficient,if_neg hp,if_neg hm,mul_zero,zero_add,hs k hp hm]

/-- Every positive free eigenspace has dimension two on the full original H1 domain. -/
theorem finrank_singularHillEigenspace_free (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℂ (singularHillEigenspace 0 (freeHillValue n:ℂ)) = 2 := by
  rw [← (LinearEquiv.ofBijective (singularHillFreePairMap n)
    (singularHillFreePairMap_bijective n hn)).finrank_eq]
  simp

/-- The genuine free Fourier values increase strictly with the unsigned mode. -/
theorem strictMono_freeHillValues : StrictMono (fun n : ℕ => freeHillValue n) := by
  intro m n hmn
  have hm : (0:ℝ) ≤ m := by positivity
  have hmn' : (m:ℝ) < n := by exact_mod_cast hmn
  unfold freeHillValue
  simp only [Int.cast_natCast]
  exact mul_lt_mul_of_pos_left (by nlinarith) (sq_pos_of_pos Real.pi_pos)

end NLS.KdV
