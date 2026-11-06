import NLS.KdV.NativeMiuraSpectralInvariance
import NLS.SequenceSpaces.PeriodOneMiuraSobolevEquivalence

/-! # Normalized ground factors on every original native Sobolev domain

The already constructed rough ground factor has exactly one additional
Sobolev derivative. This upgrades that same factor, retaining every
original coefficient, its mean, and its actual ground energy.
-/
noncomputable section
set_option autoImplicit false
open NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

/-- Every real mean-zero H^s source has an actual normalized H^(s+1)
ground factor, for every nonnegative integer s. No factor regularity is assumed. -/
theorem exists_nativeMiura_ground_factor (s : ℕ) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0)
    (hq : Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*q.val n) 2) :
    ∃ u : ScalarSobolev (s+1), ∃ hu : ∀ n : ℤ, u.val (-n) = conj (u.val n),
      u.val 0 = 0 ∧
      periodOneMiura (nativeRealMiuraFactor (s+1) u hu).val =
        q+periodOneL2Inclusion (lp.single 2 0 (-hillHminusLowestRealRoot q hr : ℝ)) ∧
      ‖(nativeRealMiuraFactor (s+1) u hu).val‖^2 = -hillHminusLowestRealRoot q hr := by
  obtain ⟨v,hv,hi,hn,_⟩ := exists_periodOneMiura_ground_factor q hr hm
  have hs : -1 ≤ (s : ℝ) := by have h : 0 ≤ (s : ℝ) := Nat.cast_nonneg s; linarith
  have hreg := (periodOneMiura_sobolev_iff q v.val
    ((-hillHminusLowestRealRoot q hr : ℝ) : ℂ) hi (s : ℝ) hs).mp hq
  let u : ScalarSobolev (s+1) := ⟨v.val,by
    change Memℓp (fun n => (Weight.sobolev ((s+1 : ℕ) : ℝ) n : ℂ)*v.val n) 2
    simpa only [Nat.cast_add,Nat.cast_one] using hreg⟩
  have hu : ∀ n : ℤ, u.val (-n) = conj (u.val n) := v.property
  have he : nativeRealMiuraFactor (s+1) u hu = v := by
    apply Subtype.ext
    ext n
    exact nativeRealMiuraFactor_apply (s+1) u hu n
  refine ⟨u,hu,hv,?_,?_⟩
  · rw [he]
    exact hi
  · rw [he]
    exact hn

end NLS.KdV
