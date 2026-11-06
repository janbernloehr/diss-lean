import NLS.KdV.HillMiuraGroundIsospectral
import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.ZakharovShabat.SobolevOddHamiltonianIsospectral

/-! # The native Miura hierarchy is determined by the rough Hill spectrum

The scalar Hamiltonians retain their independent physical definitions.
The full native odd trace and the actual global ground-factor spectral
identity prove invariance at every positive integer Sobolev order.
-/
noncomputable section
set_option autoImplicit false
open NLS.ZakharovShabat NLS.MKdV
open scoped ComplexConjugate
namespace NLS.KdV

/-- The original L2 coefficients of a physically real native scalar factor. -/
def nativeRealMiuraFactor (s : ℕ) (u : ScalarSobolev s)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n)) : PeriodOneRealL2 :=
  ⟨hierarchySobolevJetL2 s 0 (by omega) u,by
    intro n
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using hu n⟩

@[simp] theorem nativeRealMiuraFactor_apply (s : ℕ) (u : ScalarSobolev s)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n)) (n : ℤ) :
    (nativeRealMiuraFactor s u hu).val n = u.val n := by
  simp only [nativeRealMiuraFactor,hierarchySobolevJetL2_apply,pow_zero,one_mul]

/-- The native diagonal has exactly the original Dirac source of its L2 factor. -/
theorem higherSobolevSourceInclusion_diagonal_eq (s : ℕ) (u : ScalarSobolev s)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n)) :
    higherSobolevSourceInclusion s (u,u) =
      (hillMiuraRealSource (nativeRealMiuraFactor s u hu)).val := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · ext n
    change (higherSobolevSourceInclusion s (u,u)).fst n =
      (hillMiuraDiagonal (nativeRealMiuraFactor s u hu).val).fst n
    simp only [higherSobolevSourceInclusion_fst,hillMiuraDiagonal_fst,nativeRealMiuraFactor_apply]
  · ext n
    change (higherSobolevSourceInclusion s (u,u)).snd n =
      (hillMiuraDiagonal (nativeRealMiuraFactor s u hu).val).snd n
    simp only [higherSobolevSourceInclusion_snd,hillMiuraDiagonal_snd,nativeRealMiuraFactor_apply]

/-- The independent scalar native hierarchy is invariant under the actual
periodic Dirac isospectral relation, with no extra regularity premise. -/
theorem nativeMiuraHillHamiltonian_eq_of_isospectral (s : ℕ) (hs : 1 ≤ s)
    (u v : ScalarSobolev s)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n))
    (hv : ∀ n : ℤ, v.val (-n) = conj (v.val n))
    (h : hillMiuraRealSource (nativeRealMiuraFactor s v hv) ∈
      sourceIsospectralSet (by simp) (hillMiuraRealSource (nativeRealMiuraFactor s u hu))) :
    nativeMiuraHillHamiltonian s v = nativeMiuraHillHamiltonian s u := by
  let a : realTypeHigherSobolevSourceLocus s := ⟨(u,u),by
    rw [higherSobolevSourceInclusion_diagonal_eq s u hu]
    exact (hillMiuraRealSource (nativeRealMiuraFactor s u hu)).property⟩
  let b : realTypeHigherSobolevSourceLocus s := ⟨(v,v),by
    rw [higherSobolevSourceInclusion_diagonal_eq s v hv]
    exact (hillMiuraRealSource (nativeRealMiuraFactor s v hv)).property⟩
  have he : sobolevOddHamiltonian s hs (v,v) = sobolevOddHamiltonian s hs (u,u) := by
    apply sobolevOddHamiltonian_eq_of_discriminant_eq s hs a b
    change canonicalDiscriminant (by simp) (periodOnePotential (higherSobolevSourceInclusion s (v,v))) =
      canonicalDiscriminant (by simp) (periodOnePotential (higherSobolevSourceInclusion s (u,u)))
    rw [higherSobolevSourceInclusion_diagonal_eq s v hv,
      higherSobolevSourceInclusion_diagonal_eq s u hu]
    exact (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) _ _).mp h
  rw [nativeMiuraHillHamiltonian_odd_restriction,nativeMiuraHillHamiltonian_odd_restriction] at he
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) he

/-- Equal original rough Hill discriminants give equal independently defined
native hierarchy values on ANY normalized real ground factors. -/
theorem nativeMiuraHillHamiltonian_eq_of_hill_discriminant_eq
    (s : ℕ) (hs : 1 ≤ s) (q r : PeriodOneHminusOne)
    (u v : ScalarSobolev s) (e f : ℝ)
    (hu : ∀ n : ℤ, u.val (-n) = conj (u.val n))
    (hv : ∀ n : ℤ, v.val (-n) = conj (v.val n))
    (hmu : u.val 0 = 0) (hmv : v.val 0 = 0)
    (hi : periodOneMiura (nativeRealMiuraFactor s u hu).val =
      q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hj : periodOneMiura (nativeRealMiuraFactor s v hv).val =
      r+periodOneL2Inclusion (lp.single 2 0 (f : ℂ)))
    (hΔ : hillHminusDiscriminant q = hillHminusDiscriminant r) :
    nativeMiuraHillHamiltonian s v = nativeMiuraHillHamiltonian s u := by
  apply nativeMiuraHillHamiltonian_eq_of_isospectral s hs u v hu hv
  apply miura_ground_mem_isospectralSet_of_hill_discriminant_eq q r _ _ e f
    (by simpa only [nativeRealMiuraFactor_apply] using hmu)
    (by simpa only [nativeRealMiuraFactor_apply] using hmv) hi hj hΔ

end NLS.KdV
