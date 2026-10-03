import NLS.SequenceSpaces.ConjugateCotangentLinear
import NLS.ZakharovShabat.SourceAngularThetaHamiltonian
import NLS.ZakharovShabat.SourceAngularThetaExponent

/-! # Stronger-exponent regularity of the Hilbert angle Hamiltonian

For conjugate exponents `p ≤ 2 ≤ q`, analyticity of the angle cotangent
on exponent `q` gives an exponent-`p` vector, analytic in the Hilbert
source. Its Hilbert inclusion is the actual angle Hamiltonian, including
when the Hilbert and exponent-`q` normalized families differ.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The stronger coefficient realization of the Hilbert angle vector. -/
def hilbertThetaVectorInExponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2q : 2 ≤ q) (k : ℤ) (u : (j : ℤ) → CoeffPair q → DeletedCoeff q j)
    (φ : CoeffPair 2) : CoeffPair p :=
  conjugateHamiltonianDirection hq hp
    (sourceAngularThetaDifferential hq hq1 k u (CoeffPair.exponentInclusion h2q φ))

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hq1 : 1 < q}
  {W₀ B W : Set (CoeffPair 2)} {V₀ C V : Set (CoeffPair q)}
  {s : (j : ℤ) → CoeffPair 2 → DeletedCoeff 2 j}
  {u : (j : ℤ) → CoeffPair q → DeletedCoeff q j}

/-- Analytic dependence in the stronger exponent at every real Hilbert
source whose selected gap is open. -/
theorem analyticAt_hilbertThetaVectorInExponent
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V u)
    (h2q : 2 ≤ q) (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    AnalyticAt ℂ (hilbertThetaVectorInExponent hp hq hq1 h2q k u) φ.val := by
  have hgap : canonicalPeriodicGap hq hq1
      (periodOnePotential (CoeffPair.exponentInclusion h2q φ.val)) (periodOnePotential_mem _) k ≠ 0 := by
    rw [← canonicalPeriodicGap_source_exponent (by simp) hq (by norm_num) hq1 h2q φ.val k]
    exact hk
  have ha := E.analyticOnNhd_thetaDifferential k (CoeffPair.exponentInclusion h2q φ.val)
    ⟨E.real_subset (realTypeSourceExponentInclusion h2q φ).property,hgap⟩
  exact ((conjugateHamiltonianDirection hq hp).analyticAt _).comp
    (ha.comp ((CoeffPair.exponentInclusion h2q).analyticAt _))

/-- The stronger vector represents the original Hilbert Hamiltonian,
with no equality assumption on the two normalized families. -/
theorem hilbertThetaVectorInExponent_inclusion
    (D : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V u)
    (hp2 : p ≤ 2) (h2q : 2 ≤ q) (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    CoeffPair.exponentInclusion hp2 (hilbertThetaVectorInExponent hp hq hq1 h2q k u φ.val) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k s φ.val := by
  rw [hilbertThetaVectorInExponent,conjugateHamiltonianDirection_hilbert_inclusion hq hp hp2 h2q]
  unfold sourceAngularThetaHamiltonianVector
  rw [D.thetaDifferential_exponent E h2q k φ hk]

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
