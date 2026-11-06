import NLS.MKdV.SpectralMiuraHamiltonians
import NLS.MKdV.MiuraSobolevCartesianComplexCompatibility
import NLS.MKdV.MiuraSobolevCartesianActionFlow
import NLS.ZakharovShabat.SourceHigherActionIsospectral

/-! # Every native physical Hill Hamiltonian is conserved by the action flows

The sharp all-order NLS trace and the independently checked factor-two
restriction identify the invariant on the exact H^s source domain.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRealHigherSobolevDiagonal (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : realTypeHigherSobolevSourceLocus s :=
  ⟨(a,a),by
    change IsRealType (CoeffPair.toMax 2 (miuraSobolevActionSource s a))
    rw [miuraSobolevActionSource_eq_L2_diagonal]
    exact (scalarL2Diagonal_realDiagonal _ (miuraSobolevL2Inclusion_real s a ha)).1⟩

theorem miuraRealHigherSobolevDiagonal_source (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (⟨higherSobolevSourceInclusion s (miuraRealHigherSobolevDiagonal s a ha).val,
      (miuraRealHigherSobolevDiagonal s a ha).property⟩ : realTypeSourceSubmodule 2) =
      miuraActionInitialSource s a ha := by
  apply Subtype.ext
  change miuraSobolevActionSource s a = _
  rw [miuraSobolevActionSource_eq_L2_diagonal,miuraActionInitialSource_L2_diagonal]

theorem miuraRealHigherSobolevDiagonal_actionFlow_isospectral (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    (⟨higherSobolevSourceInclusion s
      (miuraRealHigherSobolevDiagonal s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t)).val,
      (miuraRealHigherSobolevDiagonal s (miuraActionFlow s a ha n t) (miuraActionFlow_real s a ha n t)).property⟩ :
      realTypeSourceSubmodule 2) ∈ sourceIsospectralSet (by simp)
        ⟨higherSobolevSourceInclusion s (miuraRealHigherSobolevDiagonal s a ha).val,
          (miuraRealHigherSobolevDiagonal s a ha).property⟩ := by
  rw [miuraRealHigherSobolevDiagonal_source,miuraRealHigherSobolevDiagonal_source]
  exact miuraActionFlow_isospectral s a ha n t

/-- Conservation of K_(s+1) along every complete physical action orbit,
at every s>=1, without requiring an open selected action or nonzero mean. -/
theorem miuraSpectralHillHamiltonian_miuraActionFlow (s : ℕ) (hs : 1 ≤ s) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraSpectralHillHamiltonian s (miuraActionFlow s a ha n t) = miuraSpectralHillHamiltonian s a := by
  let b := miuraActionFlow s a ha n t
  have hb := miuraActionFlow_real s a ha n t
  have hiso := miuraRealHigherSobolevDiagonal_actionFlow_isospectral s a ha n t
  have h := sobolevOddHamiltonian_eq_of_isospectral s hs
    (miuraRealHigherSobolevDiagonal s a ha) (miuraRealHigherSobolevDiagonal s b hb) hiso
  change sobolevOddHamiltonian s hs (b,b) = sobolevOddHamiltonian s hs (a,a) at h
  rw [nativeMiuraHillHamiltonian_odd_restriction s hs b,nativeMiuraHillHamiltonian_odd_restriction s hs a] at h
  rw [miuraSpectralHillHamiltonian_eq_native]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/-- K_1 conservation on the entire real H^0 domain uses the original
mass trace and the same independently normalized scalar mass. -/
theorem miuraSpectralHillHamiltonian_mass_miuraActionFlow (a : ScalarSobolev 0)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraSpectralHillHamiltonian 0 (miuraActionFlow 0 a ha n t) = miuraSpectralHillHamiltonian 0 a := by
  let b := miuraActionFlow 0 a ha n t
  have hb := miuraActionFlow_real 0 a ha n t
  have h := sobolevNLSHamiltonian_eq_of_isospectral 0 0 le_rfl
    (miuraRealHigherSobolevDiagonal 0 a ha) (miuraRealHigherSobolevDiagonal 0 b hb)
    (miuraRealHigherSobolevDiagonal_actionFlow_isospectral 0 a ha n t)
  change sobolevNLSHamiltonian 0 (b,b) 1 _ = sobolevNLSHamiltonian 0 (a,a) 1 _ at h
  rw [nativeMiuraHillHamiltonian_mass_restriction b,nativeMiuraHillHamiltonian_mass_restriction a] at h
  rw [miuraSpectralHillHamiltonian_eq_native]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/-- All independent physical Hill Hamiltonians are conserved on their
exact original real H^(m-1) domains, including m=1 and closed actions. -/
theorem miuraSpectralHillHamiltonian_allOrders_miuraActionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraSpectralHillHamiltonian s (miuraActionFlow s a ha n t) = miuraSpectralHillHamiltonian s a := by
  by_cases hs : 1 ≤ s
  · exact miuraSpectralHillHamiltonian_miuraActionFlow s hs a ha n t
  · have he : s = 0 := by omega
    subst s
    exact miuraSpectralHillHamiltonian_mass_miuraActionFlow a ha n t

end NLS.MKdV
