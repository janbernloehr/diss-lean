import NLS.ZakharovShabat.PeriodicParity
import NLS.SequenceSpaces.Truncation

/-!
# Finite Fourier approximation inside a fixed parity subspace

Truncations preserve parity and lift to the original one-derivative domain.
They converge within the parity subspace at every finite Banach exponent.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Retain the same finite set of frequencies in both potential components. -/
def pairTruncate (s : Finset ℤ) (φ : PairSpace p) : PairSpace p :=
  (Coeff.truncate s φ.1, Coeff.truncate s φ.2)

omit [Fact (1 ≤ p)] in
@[simp] theorem pairTruncate_apply (s : Finset ℤ) (φ : PairSpace p) :
    pairTruncate s φ = (Coeff.truncate s φ.1, Coeff.truncate s φ.2) := rfl

/-- Finite truncations preserve either Fourier parity, including negative residues. -/
theorem pairTruncate_mem_parity (s : Finset ℤ) (φ : PairSpace p) (r : ℤ)
    (hφ : φ ∈ pairParitySubspace r) : pairTruncate s φ ∈ pairParitySubspace r := by
  rw [mem_pairParitySubspace, Coeff.mem_paritySubspace, Coeff.mem_paritySubspace] at hφ ⊢
  constructor
  · intro n hn
    simp [pairTruncate, hφ.1 n hn]
  · intro n hn
    simp [pairTruncate, hφ.2 n hn]

/-- The pair truncations converge in the original potential norm. -/
theorem tendsto_pairTruncate (hp : p ≠ ⊤) (φ : PairSpace p) :
    Tendsto (fun s : Finset ℤ => pairTruncate s φ) atTop (𝓝 φ) :=
  (Coeff.tendsto_truncate hp φ.1).prodMk_nhds (Coeff.tendsto_truncate hp φ.2)

/-- The finite Fourier sum in the original one-derivative domain. -/
def pairTruncateDomain (s : Finset ℤ) (φ : PairSpace p) : Domain p :=
  (∑ n ∈ s, scalarMode n (φ.1 n), ∑ n ∈ s, scalarMode n (φ.2 n))

@[simp] theorem domainInclusion_pairTruncateDomain (s : Finset ℤ) (φ : PairSpace p) :
    domainInclusion (pairTruncateDomain s φ) = pairTruncate s φ := by
  simp only [pairTruncateDomain, domainInclusion_apply, map_sum,
    scalarInclusion_scalarMode, pairTruncate, Coeff.truncate]

/-- The domain lift has the same prescribed parity. -/
theorem pairTruncateDomain_mem_parity (s : Finset ℤ) (φ : PairSpace p) (r : ℤ)
    (hφ : φ ∈ pairParitySubspace r) : pairTruncateDomain s φ ∈ domainParitySubspace r := by
  rw [mem_domainParitySubspace, domainInclusion_pairTruncateDomain]
  exact pairTruncate_mem_parity s φ r hφ

/-- The finite projection regarded as a map within its parity subspace. -/
def parityTruncate (r : ℤ) (s : Finset ℤ) (φ : pairParitySubspace (p := p) r) :
    pairParitySubspace (p := p) r :=
  ⟨pairTruncate s φ.val, pairTruncate_mem_parity s φ.val r φ.property⟩

/-- Convergence holds in the subspace topology used by the analytic products. -/
theorem tendsto_parityTruncate (hp : p ≠ ⊤) (r : ℤ) (φ : pairParitySubspace (p := p) r) :
    Tendsto (fun s : Finset ℤ => parityTruncate r s φ) atTop (𝓝 φ) := by
  exact tendsto_subtype_rng.mpr (tendsto_pairTruncate hp φ.val)

/-- Domain-valued potentials are dense within each fixed Fourier parity. -/
theorem dense_domainInclusion_parity (hp : p ≠ ⊤) (r : ℤ) :
    Dense {φ : pairParitySubspace (p := p) r | ∃ a : Domain p, domainInclusion a = φ.val} := by
  intro φ
  apply mem_closure_of_tendsto (tendsto_parityTruncate hp r φ)
  exact Eventually.of_forall (fun s => ⟨pairTruncateDomain s φ.val, domainInclusion_pairTruncateDomain s φ.val⟩)

end NLS.ZakharovShabat
