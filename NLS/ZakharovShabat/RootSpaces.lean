import NLS.ZakharovShabat.PeriodicSpectrum
import NLS.FunctionalAnalysis.CompactGeneralized

/-!
# Periodic root spaces and algebraic multiplicity

Root spaces are defined recursively from the actual domain-to-base spectral
pencil. They therefore do not depend on a reference resolvent parameter.
A bounded compact-pencil representation proves stabilization, finite-dimensional
full root spaces, and finite algebraic multiplicities.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Vectors killed by `n` successive applications of `z - L`, requiring domain
membership at each application. The recursion is expressed on the base space. -/
def periodicRootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : ℕ → Submodule ℂ (PairSpace p)
  | 0 => ⊥
  | n + 1 => ((periodicRootSpace hp φ z n).comap (spectralPencil hp φ z).toLinearMap).map
      domainInclusion.toLinearMap

@[simp] theorem periodicRootSpace_zero (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpace hp φ z 0 = ⊥ := rfl

/-- The recursion records a domain representative and its image at the previous level. -/
theorem mem_periodicRootSpace_succ (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (n : ℕ) (x : PairSpace p) :
    x ∈ periodicRootSpace hp φ z (n + 1) ↔
      ∃ f : Domain p, domainInclusion f = x ∧ spectralPencil hp φ z f ∈ periodicRootSpace hp φ z n := by
  simp only [periodicRootSpace, Submodule.mem_map, Submodule.mem_comap]
  exact exists_congr fun _ => and_comm

/-- At level one the root space is exactly the included ordinary eigenspace. -/
theorem periodicRootSpace_one (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpace hp φ z 1 = (periodicEigenspace hp φ z).map domainInclusion.toLinearMap := rfl

/-- The finite root spaces form an increasing sequence. -/
theorem periodicRootSpace_mono (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    Monotone (periodicRootSpace hp φ z) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact Submodule.map_mono (Submodule.comap_mono ih)

/-- Every root vector lies in the one-derivative operator domain. -/
theorem exists_domain_of_mem_periodicRootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (n : ℕ) (x : PairSpace p) (hx : x ∈ periodicRootSpace hp φ z n) :
    ∃ f : Domain p, domainInclusion f = x := by
  cases n with
  | zero =>
    have hx0 : x = 0 := hx
    exact ⟨0, by simp [hx0]⟩
  | succ n =>
    obtain ⟨f, hf, _⟩ := (mem_periodicRootSpace_succ hp φ z n x).mp hx
    exact ⟨f, hf⟩

/-- The full root space is the increasing union of the finite root spaces. -/
def periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : Submodule ℂ (PairSpace p) :=
  ⨆ n : ℕ, periodicRootSpace hp φ z n

/-- Full root-space membership is witnessed by a finite chain length. -/
theorem mem_periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (x : PairSpace p) :
    x ∈ periodicRootSpaceTop hp φ z ↔ ∃ n, x ∈ periodicRootSpace hp φ z n :=
  Submodule.mem_iSup_of_directed _ (periodicRootSpace_mono hp φ z).directed_le

/-- A bounded pencil on the base space, obtained using a resolvent at `w`. -/
def boundedRootPencil (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ) :
    PairSpace p →L[ℂ] PairSpace p :=
  1 + (z - w) • resolvent hp φ w

/-- Recursive root spaces equal kernels of powers of the bounded pencil.
This equality proves that the construction is independent of `w`. -/
theorem periodicRootSpace_eq_ker (hp : p ≠ ⊤) (φ : PairSpace p) (w z : ℂ)
    (hw : w ∈ resolventSet hp φ) (n : ℕ) :
    periodicRootSpace hp φ z n = ((boundedRootPencil hp φ w z) ^ n).toLinearMap.ker := by
  let R := resolvent hp φ w
  let D := resolventToDomain hp φ w
  let B := boundedRootPencil hp φ w z
  have hRinj : Function.Injective R := by
    intro x y h
    apply Function.LeftInverse.injective (spectralPencil_resolventToDomain hp φ w hw)
    exact domainInclusion_injective h
  have hcomm (a : PairSpace p) : B (R a) = R (B a) := by
    change R a + (z - w) • R (R a) = R (a + (z - w) • R a)
    rw [map_add, map_smul]
  have hpowR (k : ℕ) (a : PairSpace p) : (B ^ k) (R a) = R ((B ^ k) a) := by
    induction k generalizing a with
    | zero => rfl
    | succ k ih => simp only [pow_succ, mul_apply_eq_comp, hcomm, ih]
  have hRker (k : ℕ) (a : PairSpace p) :
      R a ∈ (B ^ k).toLinearMap.ker ↔ a ∈ (B ^ k).toLinearMap.ker := by
    change (B ^ k) (R a) = 0 ↔ (B ^ k) a = 0
    rw [hpowR]
    constructor
    · intro h
      exact hRinj (h.trans (map_zero R).symm)
    · intro h
      rw [h, map_zero]
  have hRP (f : Domain p) : R (spectralPencil hp φ z f) = B (domainInclusion f) := by
    have hP : spectralPencil hp φ z f =
        spectralPencil hp φ w f + (z - w) • domainInclusion f := by
      simp only [spectralPencil_apply]
      module
    rw [hP, map_add, map_smul]
    change domainInclusion (D (spectralPencil hp φ w f)) +
      (z - w) • R (domainInclusion f) = _
    rw [resolventToDomain_spectralPencil hp φ w hw]
    rfl
  induction n with
  | zero => ext a; simp
  | succ n ih =>
    ext a
    rw [mem_periodicRootSpace_succ]
    constructor
    · rintro ⟨f, hf, hfn⟩
      rw [ih] at hfn
      have hBa : B a ∈ (B ^ n).toLinearMap.ker := by
        rw [← hf, ← hRP]
        exact (hRker n _).mpr hfn
      change (B ^ n) (B a) = 0 at hBa
      change (B ^ (n + 1)) a = 0
      simpa only [pow_succ, mul_apply_eq_comp] using hBa
    · intro ha
      have hBa : B a ∈ (B ^ n).toLinearMap.ker := by
        change (B ^ n) (B a) = 0
        change (B ^ (n + 1)) a = 0 at ha
        simpa only [pow_succ, mul_apply_eq_comp] using ha
      have hBan : B a ∈ periodicRootSpace hp φ z n := by rw [ih]; exact hBa
      obtain ⟨g, hg⟩ := exists_domain_of_mem_periodicRootSpace hp φ z n (B a) hBan
      let f : Domain p := g - (z - w) • D a
      have hf : domainInclusion f = a := by
        change domainInclusion (g - (z - w) • D a) = a
        rw [map_sub, map_smul, hg]
        change (a + (z - w) • R a) - (z - w) • R a = a
        abel
      refine ⟨f, hf, ?_⟩
      rw [ih]
      apply (hRker n _).mp
      rw [hRP, hf]
      exact hBa

/-- A finite root space is a nonzero generalized eigenspace of a compact
operator. The value `-1` avoids a reciprocal singularity when `z = w`. -/
theorem periodicRootSpace_eq_compact_genEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (n : ℕ) :
    periodicRootSpace hp φ z n =
      Module.End.genEigenspace (((z - w) • resolvent hp φ w).toLinearMap) (-1) n := by
  rw [periodicRootSpace_eq_ker hp φ w z hw,
    NLS.CompactSpectrum.genEigenspace_eq_ker_shift_pow]
  have heq : boundedRootPencil hp φ w z = (z - w) • resolvent hp φ w - (-1 : ℂ) • 1 := by
    unfold boundedRootPencil
    module
  rw [heq]

/-- The same representation holds for the full root space. -/
theorem periodicRootSpaceTop_eq_compact_genEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) :
    periodicRootSpaceTop hp φ z =
      Module.End.genEigenspace (((z - w) • resolvent hp φ w).toLinearMap) (-1) ⊤ := by
  rw [periodicRootSpaceTop, Module.End.genEigenspace_top]
  exact iSup_congr fun n => periodicRootSpace_eq_compact_genEigenspace hp φ w z hw n

/-- Every full periodic root space is finite dimensional. -/
theorem finiteDimensional_periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  rw [periodicRootSpaceTop_eq_compact_genEigenspace hp φ w z hw]
  exact NLS.CompactSpectrum.finiteDimensional_genEigenspace_top _
    ((isCompactOperator_resolvent hp φ w).smul (z - w)) (by norm_num)

/-- The full periodic root space is reached after finitely many iterations. -/
theorem exists_periodicRootSpace_eq_top (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    ∃ n : ℕ, periodicRootSpace hp φ z n = periodicRootSpaceTop hp φ z := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  obtain ⟨n, hn⟩ := NLS.CompactSpectrum.exists_genEigenspace_eq_top
    ((z - w) • resolvent hp φ w) ((isCompactOperator_resolvent hp φ w).smul (z - w))
    (show (-1 : ℂ) ≠ 0 by norm_num)
  exact ⟨n, by rw [periodicRootSpace_eq_compact_genEigenspace hp φ w z hw,
    periodicRootSpaceTop_eq_compact_genEigenspace hp φ w z hw, hn]⟩

/-- Algebraic multiplicity is the dimension of the full, finite-dimensional
root space of the unbounded coefficient-space operator. -/
def periodicAlgebraicMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : ℕ :=
  Module.finrank ℂ (periodicRootSpaceTop hp φ z)

/-- Every finite root space is finite dimensional as a subspace of the full root space. -/
theorem finiteDimensional_periodicRootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (n : ℕ) :
    FiniteDimensional ℂ (periodicRootSpace hp φ z n) := by
  let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) :=
    finiteDimensional_periodicRootSpaceTop hp φ z
  have hle : periodicRootSpace hp φ z n ≤ periodicRootSpaceTop hp φ z :=
    le_iSup (periodicRootSpace hp φ z) n
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective _)

/-- The full root space is closed in the base-space topology. -/
theorem isClosed_periodicRootSpaceTop (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    IsClosed (periodicRootSpaceTop hp φ z : Set (PairSpace p)) := by
  let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) :=
    finiteDimensional_periodicRootSpaceTop hp φ z
  exact (periodicRootSpaceTop hp φ z).closed_of_finiteDimensional

/-- At a resolvent parameter there are no nonzero root vectors. -/
theorem periodicRootSpaceTop_eq_bot_of_mem_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∈ resolventSet hp φ) : periodicRootSpaceTop hp φ z = ⊥ := by
  obtain ⟨n, hn⟩ := exists_periodicRootSpace_eq_top hp φ z
  rw [← hn, periodicRootSpace_eq_ker hp φ z z hz]
  simp only [boundedRootPencil, sub_self, zero_smul, add_zero, one_pow,
    ContinuousLinearMap.toLinearMap_one]
  ext x
  rfl

/-- Nontrivial full root spaces occur exactly at periodic spectral points. -/
theorem periodicRootSpaceTop_ne_bot_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicRootSpaceTop hp φ z ≠ ⊥ ↔ z ∈ periodicSpectrum hp φ := by
  constructor
  · intro h hz
    exact h (periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ z hz)
  · intro hz hbot
    obtain ⟨f, hf0, hf⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mp hz
    have hx : domainInclusion f ∈ periodicRootSpace hp φ z 1 := by
      apply (mem_periodicRootSpace_succ hp φ z 0 _).mpr
      refine ⟨f, rfl, ?_⟩
      change spectralPencil hp φ z f = 0
      simp only [spectralPencil_apply, hf, sub_self]
    have htop : domainInclusion f ∈ periodicRootSpaceTop hp φ z :=
      (le_iSup (periodicRootSpace hp φ z) 1) hx
    rw [hbot] at htop
    have hx0 : domainInclusion f = 0 := htop
    exact hf0 (domainInclusion_injective (hx0.trans (map_zero _).symm))

/-- Algebraic multiplicity is positive precisely on the periodic spectrum. -/
theorem periodicAlgebraicMultiplicity_pos_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    0 < periodicAlgebraicMultiplicity hp φ z ↔ z ∈ periodicSpectrum hp φ := by
  let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) :=
    finiteDimensional_periodicRootSpaceTop hp φ z
  rw [periodicAlgebraicMultiplicity, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  exact periodicRootSpaceTop_ne_bot_iff hp φ z

/-- Algebraic multiplicity vanishes precisely on the resolvent set. -/
theorem periodicAlgebraicMultiplicity_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ z = 0 ↔ z ∈ resolventSet hp φ := by
  have h := not_congr (periodicAlgebraicMultiplicity_pos_iff hp φ z)
  simpa only [Nat.not_lt, Nat.le_zero, periodicSpectrum, Set.mem_compl_iff, not_not] using h

end NLS.ZakharovShabat
