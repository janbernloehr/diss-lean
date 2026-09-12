import NLS.SequenceSpaces.PairNorm
import NLS.SequenceSpaces.Reflection

/-!
# The source's infinity-exponent Fourier pair norm

The source uses the supremum of the sum at each signed pair frequency, not
`WithLp ∞ (Coeff ∞ × Coeff ∞)` and not the sum of the two scalar suprema.
The first signed coefficient at `n` represents scalar frequency `-n` in (1.2).
`toMax` keeps signed coefficients; `toScalarMax` makes that reflection explicit.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Bounded sequences of pairs carrying the sum norm at each signed frequency. -/
abbrev CoeffPairInfty := lp (fun _ : ℤ => WithLp 1 (ℂ × ℂ)) ⊤

namespace CoeffPairInfty

/-- The exact source norm at regularity zero, in signed pair coefficients. -/
theorem norm_eq_ciSup (u : CoeffPairInfty) :
    ‖u‖ = ⨆ n : ℤ, (‖(u n).fst‖ + ‖(u n).snd‖) := by
  rw [lp.norm_eq_ciSup]
  simp only [WithLp.prod_norm_eq_of_L1]

/-- The first signed coefficient sequence. -/
def fst (u : CoeffPairInfty) : Coeff ⊤ :=
  ⟨fun n => (u n).fst, (lp.memℓp u).norm.mono (fun n => WithLp.norm_fst_le ℂ (u n))⟩

/-- The second signed coefficient sequence. -/
def snd (u : CoeffPairInfty) : Coeff ⊤ :=
  ⟨fun n => (u n).snd, (lp.memℓp u).norm.mono (fun n => WithLp.norm_snd_le ℂ (u n))⟩

@[simp] theorem fst_apply (u : CoeffPairInfty) (n : ℤ) : fst u n = (u n).fst := rfl
@[simp] theorem snd_apply (u : CoeffPairInfty) (n : ℤ) : snd u n = (u n).snd := rfl

/-- Combine two bounded signed sequences using the frequencywise sum norm. -/
def ofPair (a b : Coeff ⊤) : CoeffPairInfty :=
  ⟨fun n => WithLp.toLp 1 (a n, b n), by
    apply memℓp_infty
    refine ⟨‖a‖ + ‖b‖, ?_⟩
    rintro y ⟨n, rfl⟩
    exact (WithLp.prod_norm_eq_of_L1 (WithLp.toLp 1 (a n, b n))).trans_le
      (add_le_add (lp.norm_apply_le_norm (by simp) a n)
        (lp.norm_apply_le_norm (by simp) b n))⟩

@[simp] theorem ofPair_apply (a b : Coeff ⊤) (n : ℤ) :
    ofPair a b n = WithLp.toLp 1 (a n, b n) := rfl

/-- Splitting and recombining signed coefficients is a linear equivalence. -/
def pairEquiv : CoeffPairInfty ≃ₗ[ℂ] Coeff ⊤ × Coeff ⊤ where
  toFun u := (fst u, snd u)
  invFun u := ofPair u.1 u.2
  left_inv u := by ext n; rfl
  right_inv u := by rfl
  map_add' u v := by rfl
  map_smul' c u := by rfl

@[simp] theorem pairEquiv_apply (u : CoeffPairInfty) : pairEquiv u = (fst u, snd u) := rfl
@[simp] theorem pairEquiv_symm_apply (a b : Coeff ⊤) : pairEquiv.symm (a, b) = ofPair a b := rfl

/-- The frequencywise sum dominates the maximum of the component suprema. -/
theorem norm_pairEquiv_le (u : CoeffPairInfty) : ‖pairEquiv u‖ ≤ ‖u‖ := by
  apply max_le
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro n
    exact (WithLp.norm_fst_le ℂ (u n)).trans (lp.norm_apply_le_norm (by simp) u n)
  · apply lp.norm_le_of_forall_le (norm_nonneg _)
    intro n
    exact (WithLp.norm_snd_le ℂ (u n)).trans (lp.norm_apply_le_norm (by simp) u n)

/-- The reverse comparison has factor two. -/
theorem norm_ofPair_le (a b : Coeff ⊤) : ‖ofPair a b‖ ≤ 2 * ‖(a, b)‖ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro n
  rw [ofPair_apply, WithLp.prod_norm_eq_of_L1]
  change ‖a n‖ + ‖b n‖ ≤ _
  have ha := (lp.norm_apply_le_norm (by simp) a n).trans (norm_fst_le (a, b))
  have hb := (lp.norm_apply_le_norm (by simp) b n).trans (norm_snd_le (a, b))
  linarith

/-- The same signed coefficients in the existing maximum product norm. -/
def toMax : CoeffPairInfty ≃L[ℂ] Coeff ⊤ × Coeff ⊤ :=
  pairEquiv.toContinuousLinearEquivOfBounds 1 2
    (by intro u; simpa only [one_mul] using norm_pairEquiv_le u)
    (fun u => norm_ofPair_le u.1 u.2)

@[simp] theorem toMax_apply (u : CoeffPairInfty) : toMax u = (fst u, snd u) := rfl
@[simp] theorem toMax_symm_apply (a b : Coeff ⊤) : toMax.symm (a, b) = ofPair a b := rfl

theorem norm_toMax_le (u : CoeffPairInfty) : ‖toMax u‖ ≤ ‖u‖ := norm_pairEquiv_le u

theorem norm_toMax_symm_le (u : Coeff ⊤ × Coeff ⊤) : ‖toMax.symm u‖ ≤ 2 * ‖u‖ :=
  norm_ofPair_le u.1 u.2

/-- Equal signed sequences attain factor two, including nondecaying endpoint data. -/
theorem norm_diagonal (a : Coeff ⊤) : ‖ofPair a a‖ = 2 * ‖a‖ := by
  apply le_antisymm
  · simpa only [Prod.norm_def, max_self] using norm_ofPair_le a a
  · have h : ‖a‖ ≤ ‖ofPair a a‖ / 2 := by
      apply lp.norm_le_of_forall_le (by positivity)
      intro n
      have hn := lp.norm_apply_le_norm (by simp) (ofPair a a) n
      rw [ofPair_apply, WithLp.prod_norm_eq_of_L1] at hn
      change ‖a n‖ + ‖a n‖ ≤ _ at hn
      linarith
    linarith

/-- Convert signed pair coefficients to scalar Fourier coefficients as in (1.2). -/
def toScalarMax : CoeffPairInfty ≃L[ℂ] Coeff ⊤ × Coeff ⊤ :=
  toMax.trans (Coeff.reflection.toContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℂ (Coeff ⊤)))

@[simp] theorem toScalarMax_apply (u : CoeffPairInfty) :
    toScalarMax u = (Coeff.reflection (fst u), snd u) := rfl

/-- In scalar coordinates the first component must be sampled at the opposite frequency. -/
theorem norm_eq_ciSup_scalar (u : CoeffPairInfty) :
    ‖u‖ = ⨆ n : ℤ, (‖(toScalarMax u).1 (-n)‖ + ‖(toScalarMax u).2 n‖) := by
  simp only [toScalarMax_apply, Coeff.reflection_apply, neg_neg, fst_apply, snd_apply]
  exact norm_eq_ciSup u

theorem norm_toScalarMax_le (u : CoeffPairInfty) : ‖toScalarMax u‖ ≤ ‖u‖ := by
  simpa only [toScalarMax_apply, toMax_apply, Prod.norm_def, LinearIsometryEquiv.norm_map] using norm_toMax_le u

theorem norm_toScalarMax_symm_le (u : Coeff ⊤ × Coeff ⊤) :
    ‖toScalarMax.symm u‖ ≤ 2 * ‖u‖ := by
  have h := norm_toMax_symm_le (Coeff.reflection.symm u.1, u.2)
  simpa only [Prod.norm_def, LinearIsometryEquiv.norm_map] using! h

end CoeffPairInfty
end NLS
