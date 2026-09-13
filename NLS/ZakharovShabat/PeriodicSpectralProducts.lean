import NLS.ZakharovShabat.PerturbedSpectralProducts
import NLS.ZakharovShabat.PeriodicRootSequence
import NLS.ZakharovShabat.SpectralDisplacementTail
import NLS.ZakharovShabat.PeriodicCounting

/-!
# Products for actual periodic spectra off the free lattice

The finite central cluster uses the original algebraic multiplicities.
Only the distant spectral pairs enter the infinite relative product; no
arbitrary central root labels enter the construction.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complete a high spectral sequence by the free values at the finite central indices. -/
def centralFreeCompletion (N : ℕ) (ξ : ℤ → ℂ) (n : ℤ) : ℂ :=
  if N < n.natAbs then ξ n else (Real.pi : ℂ)*n

omit [Fact (1 ≤ p)] in
theorem memℓp_centralFreeCompletion (N : ℕ) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    Memℓp (fun n => centralFreeCompletion N ξ n-(Real.pi : ℂ)*n) p := by
  let a : Coeff p := ⟨_, hξ⟩
  have h := (Coeff.fourierTail (N+1) a).property
  change Memℓp (fun n => (Coeff.fourierTail (N+1) a) n) p at h
  convert h using 1
  funext n
  simp only [centralFreeCompletion, Coeff.fourierTail_apply]
  by_cases hn : N < n.natAbs
  · rw [if_pos hn, if_pos (by omega)]
  · rw [if_neg hn, if_neg (by omega), sub_self]

/-- Off the free lattice, central free completions contribute no zeros. -/
theorem centralFreeCompletion_root_iff (N : ℕ) (ξ η : ℤ → ℂ) (z : ℂ) (hz : z ∉ freeLattice) :
    (∃ n : ℤ, centralFreeCompletion N ξ n = z ∨ centralFreeCompletion N η n = z) ↔
      ∃ n : ℤ, N < n.natAbs ∧ (ξ n = z ∨ η n = z) := by
  constructor
  · rintro ⟨n, hn⟩
    by_cases hc : N < n.natAbs
    · exact ⟨n,hc,by simpa only [centralFreeCompletion, if_pos hc] using hn⟩
    · have he : (Real.pi : ℂ)*n = z := by simpa only [centralFreeCompletion, if_neg hc, or_self] using hn
      exact (hz ⟨n,he⟩).elim
  · rintro ⟨n, hn, hr⟩
    exact ⟨n,by simpa only [centralFreeCompletion, if_pos hn] using hr⟩

/-- The finite central polynomial counts each actual spectral value with its original algebraic multiplicity. -/
def centralPeriodicPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ ζ ∈ centralPeriodicSpectrum hp φ N, (ζ-z)^(periodicAlgebraicMultiplicity hp φ ζ)

theorem centralPeriodicPolynomial_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    centralPeriodicPolynomial hp φ N z = 0 ↔ z ∈ centralPeriodicSpectrum hp φ N := by
  classical
  constructor
  · intro h
    obtain ⟨ζ,hζ,hpow⟩ := Finset.prod_eq_zero_iff.mp h
    have he : ζ = z := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hpow)
    simpa only [he] using hζ
  · intro hz
    apply Finset.prod_eq_zero hz
    rw [sub_self]
    exact zero_pow (Nat.ne_of_gt ((periodicAlgebraicMultiplicity_pos_iff hp φ z).mpr
      ((mem_centralPeriodicSpectrum hp φ N z).mp hz).1))

/-- The central free polynomial removes precisely the artificial central values of the completion. -/
def centralFreePolynomial (N : ℕ) (z : ℂ) : ℂ :=
  ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ((Real.pi : ℂ)*n-z)^2

theorem centralFreePolynomial_ne_zero (N : ℕ) (z : ℂ) (hz : z ∉ freeLattice) :
    centralFreePolynomial N z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro n _
  apply pow_ne_zero
  simpa only [sub_ne_zero] using (sub_ne_zero.mp (free_denominator_ne_zero hz n)).symm

/-- Finite central multiplicities and the high spectral factors in a symmetric cutoff.
The removable free central factors are divided out only off the free lattice. -/
def periodicSpectralProductCutoff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) (M : ℕ) : ℂ :=
  (centralPeriodicPolynomial hp φ N z.val / centralFreePolynomial N z.val) *
    spectralPairPartialProduct (centralFreeCompletion N ξ) (centralFreeCompletion N η) z.val M

/-- The actual central cluster and high spectral tail define a product off the free lattice. -/
def periodicSpectralProductOffLattice (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) : ℂ :=
  (centralPeriodicPolynomial hp φ N z.val / centralFreePolynomial N z.val) *
    spectralPairProductOffLattice (centralFreeCompletion N ξ) (centralFreeCompletion N η) z

theorem tendsto_periodicSpectralProductCutoff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : {z : ℂ // z ∉ freeLattice}) :
    Tendsto (periodicSpectralProductCutoff hp φ N ξ η z) atTop
      (𝓝 (periodicSpectralProductOffLattice hp φ N ξ η z)) :=
  (tendsto_spectralPairPartialProduct hp _ _ (memℓp_centralFreeCompletion N ξ hξ)
    (memℓp_centralFreeCompletion N η hη) z.val z.property).const_mul _

/-- The completed product has exactly the original periodic spectral zeros off the free lattice. -/
theorem periodicSpectralProductOffLattice_eq_zero_iff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (z : {z : ℂ // z ∉ freeLattice}) :
    periodicSpectralProductOffLattice hp (weightedBaseToPair w φ) N ξ η z = 0 ↔
      z.val ∈ periodicSpectrum hp (weightedBaseToPair w φ) := by
  rw [periodicSpectralProductOffLattice, mul_eq_zero, div_eq_zero_iff]
  simp only [centralFreePolynomial_ne_zero N z.val z.property, or_false,
    centralPeriodicPolynomial_eq_zero_iff]
  rw [spectralPairProductOffLattice_eq_zero_iff hp _ _ (memℓp_centralFreeCompletion N ξ hξ)
    (memℓp_centralFreeCompletion N η hη), centralFreeCompletion_root_iff N ξ η z.val z.property]
  constructor
  · rintro (hz | ⟨n,hn,hz⟩)
    · exact ((mem_centralPeriodicSpectrum hp _ N z.val).mp hz).1
    · have hset := (hr n hn).enclosed_eq
      have hmem : z.val ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ)
          ((Real.pi : ℂ)*n) (Real.pi/4) := by
        rw [hset]
        simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using hz
      exact ((mem_enclosedPeriodicSpectrum hp _ _ z.val _).mp hmem).1
  · intro hz
    rcases (hc.mem_spectrum_iff_central_or_disk z.val).mp hz with hz | ⟨n,hn,_⟩
    · exact Or.inl hz
    · refine Or.inr ⟨n,hn.1,?_⟩
      have hmem := hn.2
      rw [(hr n hn.1).enclosed_eq] at hmem
      simpa only [Finset.mem_insert, Finset.mem_singleton, eq_comm] using hmem

/-- Arbitrary choices of high eigenvalue labels give the same product, even at double roots.
The finite central labels are discarded by construction. -/
theorem periodicSpectralProductOffLattice_eq_of_pairs {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} (N : ℕ) (ξ η α β : ℤ → ℂ)
    (h : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (k : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (α n) (β n))
    (z : {z : ℂ // z ∉ freeLattice}) :
    periodicSpectralProductOffLattice hp (weightedBaseToPair w φ) N ξ η z =
      periodicSpectralProductOffLattice hp (weightedBaseToPair w φ) N α β z := by
  unfold periodicSpectralProductOffLattice spectralPairProductOffLattice spectralRelativePairProduct
  congr 2
  apply tprod_congr
  intro n
  by_cases hn : N < n.natAbs
  · rcases (h n hn).eq_or_swap (k n hn) with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · simp only [spectralRelativeFactor, centralFreeCompletion, if_pos hn, hx, hy]
    · simp only [spectralRelativeFactor, centralFreeCompletion, if_pos hn, hx, hy, mul_comm]
  · simp only [spectralRelativeFactor, centralFreeCompletion, if_neg hn]

end NLS.ZakharovShabat
