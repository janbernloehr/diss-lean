import NLS.SequenceSpaces.ConjugateCotangent

/-! # Full scalar duality at every finite Banach exponent

The representing conjugate sequence includes the (1,infinity) endpoint and
has exactly the functional's operator norm. The inverse maps form a complex
linear isometry equivalence with the full continuous dual.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

theorem exists_full_cotangent (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    ∃ a : Coeff q, (∀ n : ℤ, a n = L (lp.single p n 1)) ∧ ‖a‖ ≤ ‖L‖ := by
  by_cases hq : q = ⊤
  · subst q
    have hb (n : ℤ) : ‖L (lp.single p n 1)‖ ≤ ‖L‖ := by
      simpa [lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))] using
        L.le_opNorm (lp.single p n (1 : ℂ))
    let a : Coeff ⊤ := ⟨fun n => L (lp.single p n 1), memℓp_infty ⟨‖L‖,by
      rintro x ⟨n,rfl⟩
      exact hb n⟩⟩
    exact ⟨a,fun _ => rfl,lp.norm_le_of_forall_le (norm_nonneg L) hb⟩
  · exact exists_conjugate_cotangent hp hq L

def fullCotangent (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) : Coeff q :=
  (exists_full_cotangent hp L).choose

@[simp] theorem fullCotangent_apply (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) (n : ℤ) :
    fullCotangent (q := q) hp L n = L (lp.single p n 1) :=
  (exists_full_cotangent hp L).choose_spec.1 n

theorem dualPairing_fullCotangent (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    Coeff.dualPairing (fullCotangent (q := q) hp L) = L :=
  (Coeff.eq_dualPairing_of_single hp L _ (fun n => (fullCotangent_apply hp L n).symm)).symm

theorem norm_fullCotangent (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    ‖fullCotangent (q := q) hp L‖ = ‖L‖ := by
  apply le_antisymm ((exists_full_cotangent hp L).choose_spec.2)
  calc
    ‖L‖ = ‖Coeff.dualPairing (fullCotangent (q := q) hp L)‖ :=
      congrArg norm (dualPairing_fullCotangent hp L).symm
    _ ≤ ‖fullCotangent (q := q) hp L‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      exact Coeff.norm_dualPairing_le (p := q) (q := p) _


/-- Pairing with a unit mode reads the corresponding coefficient. -/
@[simp] theorem dualPairing_single (a : Coeff q) (n : ℤ) :
    dualPairing a (lp.single p n 1) = a n := by
  simp [dualPairing_apply,lp.single_apply,Pi.single_apply]

/-- The representation is unique, even when the representing exponent is infinity. -/
theorem dualPairing_injective : Function.Injective (dualPairing (p := q) (q := p)) := by
  intro a b h
  ext n
  simpa only [dualPairing_single] using congrArg (fun L : Coeff p →L[ℂ] ℂ => L (lp.single p n 1)) h

@[simp] theorem fullCotangent_dualPairing (hp : p ≠ ⊤) (a : Coeff q) :
    fullCotangent hp (dualPairing a) = a := by
  ext n
  simp

/-- Every conjugate sequence has its exact norm as a functional on the finite-p space. -/
theorem norm_dualPairing_eq (hp : p ≠ ⊤) (a : Coeff q) : ‖dualPairing (p := q) (q := p) a‖ = ‖a‖ := by
  simpa only [fullCotangent_dualPairing] using (norm_fullCotangent (q := q) hp (dualPairing a)).symm

/-- The entire continuous dual, including the dual of l1, is linearly isometric to lq. -/
def dualityIsometry (hp : p ≠ ⊤) : Coeff q ≃ₗᵢ[ℂ] (Coeff p →L[ℂ] ℂ) where
  toLinearEquiv := LinearEquiv.ofBijective (dualPairing (p := q) (q := p)).toLinearMap
    ⟨dualPairing_injective,fun L => ⟨fullCotangent hp L,dualPairing_fullCotangent hp L⟩⟩
  norm_map' := norm_dualPairing_eq hp

@[simp] theorem dualityIsometry_apply (hp : p ≠ ⊤) (a : Coeff q) :
    dualityIsometry hp a = dualPairing a := rfl

@[simp] theorem dualityIsometry_symm_apply (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] ℂ) :
    (dualityIsometry (q := q) hp).symm L = fullCotangent hp L := by
  apply (dualityIsometry hp).injective
  simp only [LinearIsometryEquiv.apply_symm_apply,dualityIsometry_apply,dualPairing_fullCotangent]

end NLS.Coeff
