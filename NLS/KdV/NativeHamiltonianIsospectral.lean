import NLS.KdV.NativeHamiltonianShifts
import NLS.KdV.NativeMiuraPhysicalHamiltonians
import NLS.KdV.NativeMiuraGroundFactors

/-! # Spectral invariance of the original native KdV and KdV2 Hamiltonians

Actual normalized ground factors, the independent scalar hierarchy and
exact constant-shift identities prove invariance on the full original
real mean-zero endpoint domains. No smoothness or finite-gap premise remains.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.MKdV
open scoped ComplexConjugate
namespace NLS.KdV

/-- The original distributional coefficients of a native source. -/
def nativeHillSource (s : ℕ) : ScalarSobolev s →L[ℂ] PeriodOneHminusOne :=
  WeightedCoeff.sobolevInclusion (by have := Nat.cast_nonneg (α := ℝ) s; linarith : (-1 : ℝ) ≤ s)

@[simp] theorem nativeHillSource_apply (s : ℕ) (q : ScalarSobolev s) (n : ℤ) :
    (nativeHillSource s q).val n = q.val n := WeightedCoeff.sobolevInclusion_apply _ _ _

theorem nativeHillSource_inclusion (s t : ℕ) (ht : t ≤ s) (q : ScalarSobolev s) :
    nativeHillSource t (hierarchySobolevInclusion s t ht q) = nativeHillSource s q := by
  apply Subtype.ext
  funext n
  simp only [nativeHillSource_apply,hierarchySobolevInclusion_apply]

theorem nativeHillSource_real (s : ℕ) (q : ScalarSobolev s)
    (hr : ∀ n : ℤ, q.val (-n) = conj (q.val n)) : IsRealPeriodOneHminusOne (nativeHillSource s q) := by
  intro n
  simpa only [nativeHillSource_apply] using hr n

theorem nativeHillSource_regular (s : ℕ) (q : ScalarSobolev s) :
    Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*(nativeHillSource s q).val n) 2 := by
  simpa only [nativeHillSource_apply] using
    (show Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*q.val n) 2 from q.property)

/-- An actual rough shifted factor equation is the same original native equation. -/
theorem nativeMiuraPotential_eq_add_constant (s : ℕ) (q : ScalarSobolev s)
    (u : ScalarSobolev (s+1)) (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n)) (c : ℂ)
    (hi : periodOneMiura (nativeRealMiuraFactor (s+1) u hu).val =
      nativeHillSource s q+periodOneL2Inclusion (lp.single 2 0 c)) :
    nativeMiuraPotential s u = q+nativeScalarConstant s c := by
  apply Subtype.ext
  funext n
  have he := congrArg (fun a : PeriodOneHminusOne => a.val n) hi
  simpa only [nativeMiuraPotential_apply,WeightedCoeff.add_val,nativeScalarConstant,
    WeightedCoeff.ofFinsupp_apply,periodOneMiura_apply,nativeRealMiuraFactor_apply,
    nativeHillSource_apply,periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,
    Finsupp.single_apply,show 0=n ↔ n=0 from eq_comm] using he

/-- Quadratic physical mass is invariant already at the original real L2 endpoint. -/
theorem nativeMiuraMass_zero_eq_of_discriminant_eq (q r : ScalarSobolev 0)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n))
    (hr : ∀ n : ℤ, r.val (-n) = conj (r.val n)) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hΔ : hillHminusDiscriminant (nativeHillSource 0 q) =
      hillHminusDiscriminant (nativeHillSource 0 r)) : nativeMiuraMass 0 q = nativeMiuraMass 0 r := by
  obtain ⟨u,hu,hmu,hi,_⟩ := exists_nativeMiura_ground_factor 0 (nativeHillSource 0 q)
    (nativeHillSource_real 0 q hq)
    (by simpa only [nativeHillSource_apply] using hqm) (nativeHillSource_regular 0 q)
  obtain ⟨v,hv,hmv,hj,_⟩ := exists_nativeMiura_ground_factor 0 (nativeHillSource 0 r)
    (nativeHillSource_real 0 r hr)
    (by simpa only [nativeHillSource_apply] using hrm) (nativeHillSource_regular 0 r)
  have he := miura_ground_energy_eq_of_discriminant_eq _ _
    (nativeRealMiuraFactor 1 u hu) (nativeRealMiuraFactor 1 v hv) _ _
    (by simpa only [nativeRealMiuraFactor_apply] using hmu)
    (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ
  have hH := nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq 1 (by omega)
    _ _ u v _ _ hu hv hmu hmv hi hj hΔ
  rw [←nativeMiuraMass_miura v,←nativeMiuraMass_miura u,
    nativeMiuraPotential_eq_add_constant 0 r v hv _ hj,
    nativeMiuraPotential_eq_add_constant 0 q u hu _ hi,
    nativeMiuraMass_add_constant,nativeMiuraMass_add_constant,hqm,hrm,←he] at hH
  linear_combination -hH

/-- The same physical mass is spectrally invariant at every native order. -/
theorem nativeMiuraMass_eq_of_discriminant_eq (s t : ℕ) (q : ScalarSobolev s) (r : ScalarSobolev t)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n))
    (hr : ∀ n : ℤ, r.val (-n) = conj (r.val n)) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hΔ : hillHminusDiscriminant (nativeHillSource s q) =
      hillHminusDiscriminant (nativeHillSource t r)) : nativeMiuraMass s q = nativeMiuraMass t r := by
  let q₀ := hierarchySobolevInclusion s 0 (by omega) q
  let r₀ := hierarchySobolevInclusion t 0 (by omega) r
  have hq₀ (n : ℤ) : q₀.val n = q.val n := hierarchySobolevInclusion_apply _ _ _ _ _
  have hr₀ (n : ℤ) : r₀.val n = r.val n := hierarchySobolevInclusion_apply _ _ _ _ _
  have h := nativeMiuraMass_zero_eq_of_discriminant_eq q₀ r₀
    (by simpa only [hq₀] using hq) (by simpa only [hr₀] using hr)
    (by simpa only [hq₀] using hqm) (by simpa only [hr₀] using hrm) (by
      simpa only [q₀,r₀,nativeHillSource_inclusion] using hΔ)
  exact (nativeMiuraMass_eq_of_coefficients s 0 q q₀ (fun n => (hq₀ n).symm)).trans
    (h.trans (nativeMiuraMass_eq_of_coefficients 0 t r₀ r hr₀))

/-- The printed physical H1 is an actual spectral invariant on ALL real mean-zero H1. -/
theorem nativeKdVHamiltonian_eq_of_discriminant_eq (q r : ScalarSobolev 1)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n))
    (hr : ∀ n : ℤ, r.val (-n) = conj (r.val n)) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hΔ : hillHminusDiscriminant (nativeHillSource 1 q) =
      hillHminusDiscriminant (nativeHillSource 1 r)) : nativeKdVHamiltonian q = nativeKdVHamiltonian r := by
  obtain ⟨u,hu,hmu,hi,_⟩ := exists_nativeMiura_ground_factor 1 (nativeHillSource 1 q)
    (nativeHillSource_real 1 q hq)
    (by simpa only [nativeHillSource_apply] using hqm) (nativeHillSource_regular 1 q)
  obtain ⟨v,hv,hmv,hj,_⟩ := exists_nativeMiura_ground_factor 1 (nativeHillSource 1 r)
    (nativeHillSource_real 1 r hr)
    (by simpa only [nativeHillSource_apply] using hrm) (nativeHillSource_regular 1 r)
  have he := miura_ground_energy_eq_of_discriminant_eq _ _
    (nativeRealMiuraFactor 2 u hu) (nativeRealMiuraFactor 2 v hv) _ _
    (by simpa only [nativeRealMiuraFactor_apply] using hmu)
    (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ
  have hH := nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq 2 (by omega)
    _ _ u v _ _ hu hv hmu hmv hi hj hΔ
  rw [←nativeKdVHamiltonian_miura v,←nativeKdVHamiltonian_miura u,
    nativeMiuraPotential_eq_add_constant 1 r v hv _ hj,
    nativeMiuraPotential_eq_add_constant 1 q u hu _ hi,
    nativeKdVHamiltonian_add_constant,nativeKdVHamiltonian_add_constant,hqm,hrm,←he,
    nativeMiuraMass_eq_of_discriminant_eq 1 1 q r hq hr hqm hrm hΔ] at hH
  linear_combination -hH

/-- The printed physical H2 is an actual spectral invariant on ALL real mean-zero H2. -/
theorem nativeKdV2Hamiltonian_eq_of_discriminant_eq (q r : ScalarSobolev 2)
    (hq : ∀ n : ℤ, q.val (-n) = conj (q.val n))
    (hr : ∀ n : ℤ, r.val (-n) = conj (r.val n)) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hΔ : hillHminusDiscriminant (nativeHillSource 2 q) =
      hillHminusDiscriminant (nativeHillSource 2 r)) : nativeKdV2Hamiltonian q = nativeKdV2Hamiltonian r := by
  obtain ⟨u,hu,hmu,hi,_⟩ := exists_nativeMiura_ground_factor 2 (nativeHillSource 2 q)
    (nativeHillSource_real 2 q hq)
    (by simpa only [nativeHillSource_apply] using hqm) (nativeHillSource_regular 2 q)
  obtain ⟨v,hv,hmv,hj,_⟩ := exists_nativeMiura_ground_factor 2 (nativeHillSource 2 r)
    (nativeHillSource_real 2 r hr)
    (by simpa only [nativeHillSource_apply] using hrm) (nativeHillSource_regular 2 r)
  have he := miura_ground_energy_eq_of_discriminant_eq _ _
    (nativeRealMiuraFactor 3 u hu) (nativeRealMiuraFactor 3 v hv) _ _
    (by simpa only [nativeRealMiuraFactor_apply] using hmu)
    (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ
  have hH := nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq 3 (by omega)
    _ _ u v _ _ hu hv hmu hmv hi hj hΔ
  have hL := nativeKdVHamiltonian_eq_of_discriminant_eq
    (hierarchySobolevInclusion 2 1 (by omega) q) (hierarchySobolevInclusion 2 1 (by omega) r)
    (by simpa only [hierarchySobolevInclusion_apply] using hq)
    (by simpa only [hierarchySobolevInclusion_apply] using hr)
    (by simpa only [hierarchySobolevInclusion_apply] using hqm)
    (by simpa only [hierarchySobolevInclusion_apply] using hrm) (by
      simpa only [nativeHillSource_inclusion] using hΔ)
  rw [←nativeKdV2Hamiltonian_miura v,←nativeKdV2Hamiltonian_miura u,
    nativeMiuraPotential_eq_add_constant 2 r v hv _ hj,
    nativeMiuraPotential_eq_add_constant 2 q u hu _ hi,
    nativeKdV2Hamiltonian_add_constant,nativeKdV2Hamiltonian_add_constant,hqm,hrm,←he,hL,
    nativeMiuraMass_eq_of_discriminant_eq 2 2 q r hq hr hqm hrm hΔ] at hH
  linear_combination -hH

end NLS.KdV
