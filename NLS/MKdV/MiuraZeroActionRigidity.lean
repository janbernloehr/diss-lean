import NLS.MKdV.MiuraMassActionTrace

/-! # Rigidity of the physical zero-action fiber

The exact mass trace and the original scalar Fourier norm imply that
vanishing of every positive physical action forces a constant profile.
Thus on each fixed-mean leaf the zero-action fiber contains one point.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Every real H¹ profile with all positive physical actions zero is its literal mean. -/
theorem eq_scalarMode_mean_of_miuraActions_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (hz : ∀ n : ℕ, 1 ≤ n → miuraMKdVAction a ha n = 0) :
    a = scalarMode 0 (a.val 0) := by
  have hs := hasSum_miuraH1ActionMoment_physical a ha
  have hterm : (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*miuraMKdVAction a ha (n+1)) =
      (fun _ => 0) := by
    funext n
    rw [hz (n+1) (by omega),mul_zero]
  rw [hterm] at hs
  have hG : miuraH1ActionMoment a = 0 := hs.unique hasSum_zero
  have hnorm := miuraL2_norm_sq_eq_actions_mean a ha
  rw [hG,Complex.zero_re,mul_zero,add_zero] at hnorm
  have him : (a.val 0).im = 0 := by
    have h := congrArg Complex.im (ha 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have hreal : a.val 0 = ((a.val 0).re : ℂ) := Complex.ext rfl him
  have hnorm0 : ‖a.val 0‖^2 = (a.val 0).re^2 := by
    conv_lhs => rw [hreal]
    rw [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hsum : HasSum (fun n : ℤ => ‖scalarInclusion a n‖^2) (‖scalarInclusion a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) (scalarInclusion a)
  have hcoeff (k : ℤ) (hk : k ≠ 0) : a.val k = 0 := by
    have hle := hsum.summable.sum_le_tsum ({0,k} : Finset ℤ) (fun _ _ => sq_nonneg _)
    rw [hsum.tsum_eq] at hle
    have hmem : (0 : ℤ) ∉ ({k} : Finset ℤ) := by simpa only [Finset.mem_singleton] using hk.symm
    rw [Finset.sum_insert hmem,Finset.sum_singleton] at hle
    simp only [scalarInclusion_apply] at hle
    rw [hnorm,hnorm0] at hle
    have hn : ‖a.val k‖^2 = 0 := by nlinarith [sq_nonneg ‖a.val k‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  apply Subtype.ext
  funext k
  rw [scalarMode_apply]
  by_cases hk : k = 0
  · simp only [hk,ite_true]
  · simp only [hk,ite_false,hcoeff k hk]

/-- Zero positive physical actions characterize spatially constant real profiles. -/
theorem miuraActions_zero_iff_derivative_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (∀ n : ℕ, 1 ≤ n → miuraMKdVAction a ha n = 0) ↔ periodOneDerivative a = 0 := by
  constructor
  · intro hz
    have he := eq_scalarMode_mean_of_miuraActions_zero a ha hz
    rw [he]
    ext k
    rw [periodOneDerivative_apply,scalarMode_apply]
    by_cases hk : k = 0 <;> simp [hk]
  · intro hd n hn
    exact miuraMKdVAction_eq_zero_of_derivative_zero a ha hd n hn

end NLS.MKdV
