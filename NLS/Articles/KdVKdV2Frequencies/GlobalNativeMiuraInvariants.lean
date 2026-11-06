import NLS.Articles.KdVKdV2Frequencies.GlobalRoughActionIsospectral
import NLS.KdV.NativeMiuraGroundFactors

/-! # Complete actual actions determine the normalized native Miura hierarchy

The same global rough Birkhoff map determines the actual ground-factor
energy and every independently defined native scalar hierarchy value.
The factors exist with exactly the regularity supplied by the original
source. Identifying the printed KdV Hamiltonians and analytic descent
through actions remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open NLS.KdV NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Every positive-order native scalar hierarchy value of actual normalized
ground factors is fixed by the COMPLETE original signed actions. -/
theorem nativeMiuraHillHamiltonian_eq_of_signed_actions_eq
    (D : GlobalRoughAbelianForwardData) (s : ℕ) (hs : 1 ≤ s)
    (q r : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hr : IsRealPeriodOneHminusOne r) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (u v : ScalarSobolev s) (e f : ℝ)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n))
    (hv : ∀ n : ℤ, v.val (-n) = conj (v.val n))
    (hmu : u.val 0 = 0) (hmv : v.val 0 = 0)
    (hi : periodOneMiura (nativeRealMiuraFactor s u hu).val =
      q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hj : periodOneMiura (nativeRealMiuraFactor s v hv).val =
      r+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)))
    (h : ∀ n : ℕ+, (D.signed q).val (n : ℤ)*(D.signed q).val (-(n : ℤ)) =
      (D.signed r).val (n : ℤ)*(D.signed r).val (-(n : ℤ))) :
    nativeMiuraHillHamiltonian s v = nativeMiuraHillHamiltonian s u := by
  exact NLS.KdV.nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq
    s hs q r u v e f hu hv hmu hmv hi hj
    (funext (D.discriminant_eq_of_signed_actions_eq q r hq hr hqm hrm h))

/-- On EVERY original real mean-zero H^s action fiber, actual normalized
H^(s+1) factors exist with a COMMON ground energy and equal native hierarchy
values. All orders, all amplitudes and all collapsed gaps are included. -/
theorem exists_native_ground_factors_eq_of_signed_actions_eq
    (D : GlobalRoughAbelianForwardData) (s : ℕ)
    (q r : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (hr : IsRealPeriodOneHminusOne r) (hqm : q.val 0 = 0) (hrm : r.val 0 = 0)
    (hqs : Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*q.val n) 2)
    (hrs : Memℓp (fun n => (Weight.sobolev (s : ℝ) n : ℂ)*r.val n) 2)
    (h : ∀ n : ℕ+, (D.signed q).val (n : ℤ)*(D.signed q).val (-(n : ℤ)) =
      (D.signed r).val (n : ℤ)*(D.signed r).val (-(n : ℤ))) :
    ∃ u v : ScalarSobolev (s+1),
      ∃ hu : ∀ n : ℤ, u.val (-n) = conj (u.val n),
      ∃ hv : ∀ n : ℤ, v.val (-n) = conj (v.val n), ∃ e : ℝ,
      u.val 0 = 0 ∧ v.val 0 = 0 ∧
      periodOneMiura (nativeRealMiuraFactor (s+1) u hu).val =
        q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∧
      periodOneMiura (nativeRealMiuraFactor (s+1) v hv).val =
        r+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)) ∧
      ‖(nativeRealMiuraFactor (s+1) u hu).val‖^2 = e ∧
      ‖(nativeRealMiuraFactor (s+1) v hv).val‖^2 = e ∧
      nativeMiuraHillHamiltonian (s+1) v = nativeMiuraHillHamiltonian (s+1) u := by
  obtain ⟨u,hu,hmu,hi,hnu⟩ := exists_nativeMiura_ground_factor s q hq hqm hqs
  obtain ⟨v,hv,hmv,hj,hnv⟩ := exists_nativeMiura_ground_factor s r hr hrm hrs
  have hΔ := funext (D.discriminant_eq_of_signed_actions_eq q r hq hr hqm hrm h)
  have he := miura_ground_energy_eq_of_discriminant_eq q r
    (nativeRealMiuraFactor (s+1) u hu) (nativeRealMiuraFactor (s+1) v hv)
    (-hillHminusLowestRealRoot q hq) (-hillHminusLowestRealRoot r hr)
    (by simpa only [nativeRealMiuraFactor_apply] using hmu)
    (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ
  refine ⟨u,v,hu,hv,-hillHminusLowestRealRoot q hq,hmu,hmv,hi,?_,hnu,?_,?_⟩
  · rw [he]
    exact hj
  · exact hnv.trans he.symm
  · exact NLS.KdV.nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq
      (s+1) (by omega) q r u v _ _ hu hv hmu hmv hi hj hΔ

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
