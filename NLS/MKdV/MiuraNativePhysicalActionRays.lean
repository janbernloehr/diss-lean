import NLS.MKdV.MiuraNativeActionMeanParameters
import NLS.MKdV.MiuraSobolevActionRealization
import NLS.SequenceSpaces.WeightedSingle

/-! # Positive physical action rays remain attained at every native order

Increasing one positive action preserves nonnegativity, support and the
signed mean, including when the selected action is initially closed.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevActionSequence_nonnegative (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℤ) :
    ((miuraSobolevActionSequence s a.val).val n).im = 0 ∧
      0 ≤ ((miuraSobolevActionSequence s a.val).val n).re := by
  have hr := congrArg (fun J : WeightedCoeff (miuraSpectralActionWeight s) 1 => J.val n)
    (miuraSobolevCartesianActions_sequence_eq s a.val a.property).symm
  rw [miuraSobolevCartesianActions_apply] at hr
  obtain ⟨hx,hy⟩ := miuraSobolevCartesianSequence_real s a.val a.property n
  have he (z : ℂ) (hz : z.im = 0) : z = (z.re : ℂ) := Complex.ext rfl (by simp [hz])
  rw [hr,he _ hx,he _ hy]
  have hp : (1/2 : ℂ)*
      ((((miuraSobolevCartesianSequence s a.val).1.val n).re : ℂ)^2+
       (((miuraSobolevCartesianSequence s a.val).2.val n).re : ℂ)^2) =
      (((1/2 : ℝ)*(((miuraSobolevCartesianSequence s a.val).1.val n).re^2+
        ((miuraSobolevCartesianSequence s a.val).2.val n).re^2) : ℝ) : ℂ) := by push_cast; rfl
  rw [hp]
  exact ⟨rfl,mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))⟩

/-- Every nonnegative one-sided increment of any positive physical
action is realized by another real H^s profile with the same mean. -/
theorem exists_native_profile_on_positive_action_ray (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℤ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    ∃ b : MiuraRealSobolevSource s,
      miuraNativeActionMeanMap s b.val = miuraNativeActionMeanMap s a.val+
        (t : ℂ) • (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1,0) := by
  let J := miuraSobolevActionSequence s a.val+
    (t : ℂ) • WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1
  have hJpos (k : ℤ) : (J.val k).im = 0 ∧ 0 ≤ (J.val k).re := by
    have hbase := miuraSobolevActionSequence_nonnegative s a k
    change ((miuraSobolevActionSequence s a.val).val k+(t : ℂ)*
      (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1).val k).im = 0 ∧
      0 ≤ ((miuraSobolevActionSequence s a.val).val k+(t : ℂ)*
        (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1).val k).re
    rw [WeightedCoeff.single_val]
    by_cases hk : k = n
    · subst k
      simpa only [Pi.single_eq_same,mul_one,Complex.add_im,Complex.ofReal_im,add_zero,
        Complex.add_re,Complex.ofReal_re] using ⟨hbase.1,add_nonneg hbase.2 ht⟩
    · simpa only [Pi.single_eq_of_ne hk,mul_zero,add_zero] using hbase
  have hJzero (k : ℤ) (hk : ¬0 < k) : J.val k = 0 := by
    have hkn : k ≠ n := by omega
    change (miuraSobolevActionSequence s a.val).val k+(t : ℂ)*
      (WeightedCoeff.single (p := 1) (miuraSpectralActionWeight s) n 1).val k = 0
    rw [miuraSobolevActionSequence_nonpositive s a.val k hk,WeightedCoeff.single_val,Pi.single_eq_of_ne hkn]
    simp
  have hmean : a.val.val 0 = ((a.val.val 0).re : ℂ) := by
    have h := congrArg Complex.im (a.property 0)
    simp only [neg_zero,Complex.conj_im] at h
    apply Complex.ext
    · rfl
    · change (a.val.val 0).im = 0
      linarith
  obtain ⟨b,hact,hc⟩ := exists_miuraSobolev_profile_of_nonnegative_actions s hs J hJpos hJzero (a.val.val 0).re
  refine ⟨b,?_⟩
  apply Prod.ext
  · exact hact
  · change b.val.val 0 = a.val.val 0+(t : ℂ)*0
    rw [hc,mul_zero,add_zero]
    exact hmean.symm

end NLS.MKdV
