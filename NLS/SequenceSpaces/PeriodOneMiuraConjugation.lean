import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.ConjugateReflection

/-! # Physical conjugation and the actual rough Miura maps

Physical realness is conjugate Fourier reflection. The period-one mass
inverse and the distributional convolution product commute with it.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS

def periodOneL2Conjugation (a : Coeff 2) : Coeff 2 := star (Coeff.reflection a)

@[simp] theorem periodOneL2Conjugation_apply (a : Coeff 2) (k : ℤ) :
    periodOneL2Conjugation a k = conj (a (-k)) := by
  simp only [periodOneL2Conjugation,lp.star_apply,Coeff.reflection_apply,starRingEnd_apply]

@[simp] theorem norm_periodOneL2Conjugation (a : Coeff 2) : ‖periodOneL2Conjugation a‖ = ‖a‖ := by
  rw [periodOneL2Conjugation,norm_star,Coeff.reflection.norm_map]

@[simp] theorem periodOneL2Conjugation_involutive (a : Coeff 2) :
    periodOneL2Conjugation (periodOneL2Conjugation a) = a := by ext k;simp

theorem periodOneL2Conjugation_add (a b : Coeff 2) :
    periodOneL2Conjugation (a+b) = periodOneL2Conjugation a+periodOneL2Conjugation b := by
  ext k
  simp only [periodOneL2Conjugation_apply,lp.coeFn_add,Pi.add_apply,map_add]

def periodOneHminusConjugation (q : PeriodOneHminusOne) : PeriodOneHminusOne :=
  WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) q

@[simp] theorem periodOneHminusConjugation_apply (q : PeriodOneHminusOne) (k : ℤ) :
    (periodOneHminusConjugation q).val k = conj (q.val (-k)) := by
  exact WeightedCoeff.conjugateReflection_apply _ _ q k

@[simp] theorem norm_periodOneHminusConjugation (q : PeriodOneHminusOne) :
    ‖periodOneHminusConjugation q‖ = ‖q‖ := WeightedCoeff.norm_conjugateReflection _ _ q

@[simp] theorem periodOneHminusConjugation_involutive (q : PeriodOneHminusOne) :
    periodOneHminusConjugation (periodOneHminusConjugation q) = q := by
  apply Subtype.ext
  funext k
  simp only [periodOneHminusConjugation_apply,neg_neg,starRingEnd_self_apply]

theorem periodOneMassSymbol_conjugation (m : ℕ) (k : ℤ) :
    conj (periodOneMassSymbol m (-k)) = periodOneMassSymbol m k := by
  simp [periodOneMassSymbol,Complex.conj_ofNat]

theorem periodOneMassInverse_conjugation (m : ℕ) (q : PeriodOneHminusOne) :
    periodOneL2Conjugation (periodOneMassInverse m q) =
      periodOneMassInverse m (periodOneHminusConjugation q) := by
  ext k
  simp only [periodOneL2Conjugation_apply,periodOneMassInverse_apply,
    periodOneHminusConjugation_apply,map_mul,map_inv₀,periodOneMassSymbol_conjugation]

theorem periodOneMiuraProduct_conjugation (a b : Coeff 2) :
    periodOneHminusConjugation (periodOneMiuraProduct a b) =
      periodOneMiuraProduct (periodOneL2Conjugation a) (periodOneL2Conjugation b) := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply,periodOneMiuraProduct_apply,
    WeightedCoeff.conj_tsum_convolution,periodOneMiuraProduct_apply]
  simp only [periodOneL2Conjugation_apply]

theorem periodOneResolvedProduct_conjugation (m : ℕ) (a b : Coeff 2) :
    periodOneL2Conjugation (periodOneResolvedProduct m a b) =
      periodOneResolvedProduct m (periodOneL2Conjugation a) (periodOneL2Conjugation b) := by
  change periodOneL2Conjugation (periodOneMassInverse m (periodOneMiuraProduct a b)) = _
  rw [periodOneMassInverse_conjugation,periodOneMiuraProduct_conjugation]
  rfl

theorem periodOneResolvedQuadratic_conjugation (m : ℕ) (a : Coeff 2) :
    periodOneL2Conjugation (a+periodOneResolvedProduct m a a) =
      periodOneL2Conjugation a+
        periodOneResolvedProduct m (periodOneL2Conjugation a) (periodOneL2Conjugation a) := by
  rw [periodOneL2Conjugation_add,periodOneResolvedProduct_conjugation]

theorem periodOneShiftedMiura_conjugation (m : ℕ) (a : Coeff 2) :
    periodOneHminusConjugation (periodOneShiftedMiura m a) =
      periodOneShiftedMiura m (periodOneL2Conjugation a) := by
  apply (periodOneMassInverse_injective m)
  rw [← periodOneMassInverse_conjugation,periodOneMassInverse_shiftedMiura,
    periodOneMassInverse_shiftedMiura,periodOneResolvedQuadratic_conjugation]

theorem periodOneL2Conjugation_fixed_iff (a : Coeff 2) :
    periodOneL2Conjugation a = a ↔ ∀ k : ℤ, a (-k) = conj (a k) := by
  constructor
  · intro h k
    have he := congrArg (fun b : Coeff 2 => b (-k)) h
    simpa only [periodOneL2Conjugation_apply,neg_neg] using he.symm
  · intro h
    ext k
    exact (h (-k)).symm.trans (by rw [neg_neg])

theorem periodOneHminusConjugation_fixed_iff (q : PeriodOneHminusOne) :
    periodOneHminusConjugation q = q ↔ ∀ k : ℤ, q.val (-k) = conj (q.val k) := by
  constructor
  · intro h k
    have he := congrArg (fun r : PeriodOneHminusOne => r.val (-k)) h
    simpa only [periodOneHminusConjugation_apply,neg_neg] using he.symm
  · intro h
    apply Subtype.ext
    funext k
    simpa only [periodOneHminusConjugation_apply,neg_neg] using! (h (-k)).symm

theorem periodOneL2Conjugation_single_real (c : ℝ) :
    periodOneL2Conjugation (lp.single 2 0 (c : ℂ)) = lp.single 2 0 (c : ℂ) := by
  ext k
  by_cases hk : k = 0 <;> simp [periodOneL2Conjugation_apply,lp.single_apply,hk]

end NLS
