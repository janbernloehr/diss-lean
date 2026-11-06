import NLS.KdV.NativeHillHierarchyConstantVariation
import NLS.KdV.HillHierarchyMiuraRestriction
import NLS.KdV.NativeHamiltonianIsospectral
import Mathlib.Analysis.Calculus.MeanValue

/-! # Spectral invariance of every original native KdV Hamiltonian

A common actual ground energy fixes the Miura hierarchy values. The
all-order constant-shift derivative makes the difference constant by
induction, so no list of assumed shift formulas is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
open scoped ComplexConjugate
namespace NLS.KdV

/-- Equal entire original Hill discriminants give equal native hierarchy
values at EVERY common complex constant shift, on the sharp H^m domains. -/
theorem nativeHillHierarchyHamiltonian_shift_eq_of_discriminant_eq (m : ℕ) :
    ∀ q r : ScalarSobolev m,
      (∀ n : ℤ, q.val (-n) = conj (q.val n)) → (∀ n : ℤ, r.val (-n) = conj (r.val n)) →
      q.val 0 = 0 → r.val 0 = 0 →
      hillHminusDiscriminant (nativeHillSource m q) = hillHminusDiscriminant (nativeHillSource m r) →
      ∀ c : ℂ, nativeHillHierarchyHamiltonian m (q+c • nativeScalarConstant m 1) =
        nativeHillHierarchyHamiltonian m (r+c • nativeScalarConstant m 1) := by
  induction m with
  | zero =>
    intro q r hq hr hqm hrm hΔ c
    have hM := nativeMiuraMass_eq_of_discriminant_eq 0 0 q r hq hr hqm hrm hΔ
    simp only [nativeHillHierarchyHamiltonian_zero,smul_nativeScalarConstant,mul_one,
      nativeMiuraMass_add_constant,hqm,hrm,mul_zero,add_zero,hM]
  | succ m ih =>
    intro q r hq hr hqm hrm hΔ c
    obtain ⟨u,hu,hmu,hi,_⟩ := exists_nativeMiura_ground_factor (m+1) (nativeHillSource (m+1) q)
      (nativeHillSource_real (m+1) q hq)
      (by simpa only [nativeHillSource_apply] using hqm) (nativeHillSource_regular (m+1) q)
    obtain ⟨v,hv,hmv,hj,_⟩ := exists_nativeMiura_ground_factor (m+1) (nativeHillSource (m+1) r)
      (nativeHillSource_real (m+1) r hr)
      (by simpa only [nativeHillSource_apply] using hrm) (nativeHillSource_regular (m+1) r)
    have he := miura_ground_energy_eq_of_discriminant_eq _ _
      (nativeRealMiuraFactor (m+2) u hu) (nativeRealMiuraFactor (m+2) v hv) _ _
      (by simpa only [nativeRealMiuraFactor_apply] using hmu)
      (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ
    have hK := nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq (m+2) (by omega)
      _ _ u v _ _ hu hv hmu hmv hi hj hΔ
    rw [←nativeHillHierarchyHamiltonian_miura (m+1) v,←nativeHillHierarchyHamiltonian_miura (m+1) u,
      nativeMiuraPotential_eq_add_constant (m+1) r v hv _ hj,
      nativeMiuraPotential_eq_add_constant (m+1) q u hu _ hi,←he] at hK
    let e : ℂ := (-hillHminusLowestRealRoot (nativeHillSource (m+1) q) (nativeHillSource_real (m+1) q hq) : ℝ)
    let F : ℂ → ℂ := fun d => nativeHillHierarchyHamiltonian (m+1) (q+d • nativeScalarConstant (m+1) 1)-
      nativeHillHierarchyHamiltonian (m+1) (r+d • nativeScalarConstant (m+1) 1)
    have hd (d : ℂ) : HasDerivAt F 0 d := by
      have h := (hasDerivAt_nativeHillHierarchyHamiltonian_shift m q d).sub
        (hasDerivAt_nativeHillHierarchyHamiltonian_shift m r d)
      have hlow := ih (hierarchySobolevInclusion (m+1) m (by omega) q)
        (hierarchySobolevInclusion (m+1) m (by omega) r)
        (by simpa only [hierarchySobolevInclusion_apply] using hq)
        (by simpa only [hierarchySobolevInclusion_apply] using hr)
        (by simpa only [hierarchySobolevInclusion_apply] using hqm)
        (by simpa only [hierarchySobolevInclusion_apply] using hrm)
        (by simpa only [nativeHillSource_inclusion] using hΔ) d
      rw [hlow,sub_self] at h
      exact h
    have hzero : F e = 0 := by
      dsimp only [F]
      rw [smul_nativeScalarConstant,mul_one]
      exact sub_eq_zero.mpr hK.symm
    have hconst := is_const_of_deriv_eq_zero (fun d => (hd d).differentiableAt) (fun d => (hd d).deriv) c e
    exact sub_eq_zero.mp (hconst.trans hzero)

/-- Every original physical hierarchy member is a genuine spectral invariant
on its full native real mean-zero H^m domain, including nonsmooth sources. -/
theorem nativeHillHierarchyHamiltonian_eq_of_discriminant_eq (m : ℕ) (q r : ScalarSobolev m)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n))
    (hr : ∀ n : ℤ, r.val (-n) = conj (r.val n)) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hΔ : hillHminusDiscriminant (nativeHillSource m q) = hillHminusDiscriminant (nativeHillSource m r)) :
    nativeHillHierarchyHamiltonian m q = nativeHillHierarchyHamiltonian m r := by
  simpa only [zero_smul,add_zero] using
    nativeHillHierarchyHamiltonian_shift_eq_of_discriminant_eq m q r hq hr hqm hrm hΔ 0

end NLS.KdV
