import NLS.ZakharovShabat.SourceFiniteGapMassDivergence
import NLS.ZakharovShabat.SourceOrdinaryPhaseTrajectory
import NLS.ZakharovShabat.SourceRenormalizedPhaseTrajectory
import NLS.ZakharovShabat.SourceSecondMomentFrequencyTheorem20_4

/-! # Ordinary finite-gap coordinate trajectories at every finite exponent

The mass is the original first physical Hamiltonian. Adding it back to
the renormalized frequency recovers the physical finite-gap frequency.
These scalar trajectories provide the dense domain for the obstruction
to continuous extension outside the Hilbert locus.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}

/-- The real finite-gap mass equals the complex physical Hamiltonian on the real form. -/
theorem sourceFiniteGapRealMass_complex (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (sourceFiniteGapRealMass hp hp1 φ hf : ℂ) = sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1 := by
  rw [← sourceFiniteGapHilbertModel_hamiltonian_one hp hp1 φ hf,
    sourceFiniteGapNLSHamiltonian_one_eq_mass]
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  change ((sourceHilbertMass ψ.val).re : ℂ) = sourceHilbertMass ψ.val
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType ψ.val ψ.property,Complex.ofReal_re]

/-- In the summable range this is exactly the mass used by the global ordinary flow. -/
theorem sourceFiniteGapRealMass_eq_ordinaryMass (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapRealMass hp hp1 φ hf = sourceOrdinaryMass hp2 φ := by
  have he := sourceFiniteGapHilbertModel_eq_of_coefficients hp hp1 φ hf
    (realTypeSourceExponentInclusion hp2 φ) (fun _ => ⟨rfl,rfl⟩)
  unfold sourceFiniteGapRealMass
  rw [he]
  rfl

namespace SourceAbelianMomentAtlas
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The ordinary physical frequency on the dense finite-gap domain. -/
def finiteGapOrdinaryFrequency (A : SourceAbelianMomentAtlas hp hp1 W s)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) : ℝ :=
  A.phaseFrequency φ n + 4*sourceFiniteGapRealMass hp hp1 φ hf

/-- The restored frequency is the original physical Hamiltonian frequency. -/
theorem finiteGapOrdinaryFrequency_physical (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    {V₀ C V : Set (CoeffPair 2)} {u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    (A.finiteGapOrdinaryFrequency φ hf n : ℂ) = E.finiteGapFrequencyAtExponent hp hp1 φ hf n := by
  simp only [finiteGapOrdinaryFrequency,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [A.phaseFrequency_complex hs,sourceFiniteGapRealMass_complex,
    A.renormalizedFrequency_eq_physical_finiteGap_all_exponents E hs φ hf n]
  ring

/-- On p ≤ 2 this is the frequency in the already constructed ordinary flow. -/
theorem finiteGapOrdinaryFrequency_eq_ordinary (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    A.finiteGapOrdinaryFrequency φ hf n = A.ordinaryPhaseFrequency hp2 φ n := by
  simp only [finiteGapOrdinaryFrequency,phaseFrequency,ordinaryPhaseFrequency,
    sourceFiniteGapRealMass_eq_ordinaryMass hp2]

/-- Every fixed ordinary finite-gap frequency diverges near a non-Hilbert source. -/
theorem tendsto_finiteGapOrdinaryFrequency_atTop (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P) (h2p : 2 ≤ p)
    {ι : Type*} {l : Filter ι} (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (ψ : ι → realTypeSourceSubmodule p) (hf : ∀ j, ψ j ∈ sourceFiniteGapLocus hp hp1)
    (hψ : Tendsto ψ l (𝓝 φ)) (n : ℤ) :
    Tendsto (fun j => A.finiteGapOrdinaryFrequency (ψ j) (hf j) n) l atTop :=
  ((A.continuous_phaseFrequency hs hP hr n).continuousAt.tendsto.comp hψ).add_atTop
    ((tendsto_sourceFiniteGapRealMass_atTop hp hp1 h2p φ hφ ψ hf hψ).const_mul_atTop (by norm_num))

/-- The first ordinary finite-gap coordinate as a continuous compact-time path. -/
def finiteGapOrdinaryCoordinate (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (T : ℝ)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    C(Icc (0 : ℝ) T,ℂ) where
  toFun τ := Complex.exp (((τ.val*A.finiteGapOrdinaryFrequency φ hf n : ℝ) : ℂ)*Complex.I)*
    (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n
  continuous_toFun := by fun_prop

/-- The second coordinate has the opposite physical phase sign. -/
def finiteGapOrdinaryCoordinateSnd (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (T : ℝ)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    C(Icc (0 : ℝ) T,ℂ) where
  toFun τ := Complex.exp (((-τ.val*A.finiteGapOrdinaryFrequency φ hf n : ℝ) : ℂ)*Complex.I)*
    (sourceComplexBirkhoffMap hp hp1 t φ.val).2 n
  continuous_toFun := by fun_prop

/-- Literal agreement with the previously constructed ordinary first coordinate. -/
theorem finiteGapOrdinaryCoordinate_eq_ordinary (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (hp2 : p ≤ 2) (T : ℝ)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ)
    (τ : Icc (0 : ℝ) T) :
    A.finiteGapOrdinaryCoordinate t T φ hf n τ = (A.ordinaryPhaseTrajectory t hp2 φ τ.val).1 n := by
  change Complex.exp _ * _ = _
  rw [A.finiteGapOrdinaryFrequency_eq_ordinary hp2,ordinaryPhaseTrajectory,Birkhoff.phaseFlow_fst]

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
