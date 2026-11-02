import NLS.Fourier.PeriodicFourierLebesgueEndpoints
import NLS.ZakharovShabat.SourceBirkhoffDenseRange
import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.Dynamics.ComplexBirkhoffCoordinates
import NLS.Dynamics.RealComplexBirkhoffCoordinates

/-! # Physical distribution input for the article's Birkhoff map

The input consists of original period-one distributions. Their Fourier
coefficients are evaluated on the negative physical mode, then fed to the
existing spectral Birkhoff construction. No sequence-flow identification
with mKdV is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance periodOnePositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev PhysicalFL (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  PeriodicFourierLebesgue (1 : ℝ) Weight.one p

/-- Actual Fourier coefficient transport from the physical distribution pair. -/
def physicalCoefficients : (PhysicalFL p × PhysicalFL p) ≃L[ℂ] CoeffPair p :=
  ((PeriodicFourierLebesgue.unweightedCoefficients p).toContinuousLinearEquiv.prodCongr
    (PeriodicFourierLebesgue.unweightedCoefficients p).toContinuousLinearEquiv).trans
      (CoeffPair.toMax p).symm

@[simp] theorem physicalCoefficients_apply (u : PhysicalFL p × PhysicalFL p) (n : ℤ) :
    (physicalCoefficients u).fst n = u.1.val (mode (-n)) ∧
    (physicalCoefficients u).snd n = u.2.val (mode (-n)) := by
  constructor <;> simp [physicalCoefficients, CoeffPair.toMax]

variable {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Complex Birkhoff coordinates of the physical distribution input. -/
def physicalBirkhoff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (u : PhysicalFL p × PhysicalFL p) : Coeff p × Coeff p :=
  Birkhoff.rectangularToComplex (sourceBirkhoffMap hp hp1 s (physicalCoefficients u))

/-- The spectral construction gives a holomorphic physical-input map on an open domain. -/
theorem physicalBirkhoff_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℂ (physicalBirkhoff hp hp1 s)
      (physicalCoefficients ⁻¹' W) := by
  intro u hu
  exact (Birkhoff.rectangularToComplex.analyticAt _).comp
    ((D.analytic _ hu).comp (physicalCoefficients.analyticAt u))

/-- The complex coordinate product is the actual spectral action of that input. -/
theorem physicalBirkhoff_action
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (u : PhysicalFL p × PhysicalFL p) (hu : physicalCoefficients u ∈ W) (n : ℤ) :
    (physicalBirkhoff hp hp1 s u).1 n * (physicalBirkhoff hp hp1 s u).2 n =
      sourceComplexAction hp hp1 n (physicalCoefficients u) := by
  rw [physicalBirkhoff, Birkhoff.rectangularToComplex_action, D.action_radius _ hu n]
  ring

/-- Physical complex-input analyticity is obtained from constructed data. -/
theorem exists_physicalBirkhoff (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      IsOpen (physicalCoefficients (p := p) ⁻¹' W) ∧
      AnalyticOnNhd ℂ (physicalBirkhoff hp hp1 s) (physicalCoefficients ⁻¹' W) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.source_open.preimage (physicalCoefficients (p := p)).continuous,
    physicalBirkhoff_analytic D⟩

/-- The physical real-type pair locus, expressed on the actual distribution inputs.
This is the NLS real form; the smaller real diagonal for mKdV is a further restriction. -/
abbrev PhysicalRealInput (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  {u : PhysicalFL p × PhysicalFL p // physicalCoefficients u ∈ realTypeSourceLocus p}

/-- Fourier transport is a homeomorphism on the physical real form as well. -/
def physicalRealCoefficients : PhysicalRealInput p ≃ₜ realTypeSourceSubmodule p :=
  (physicalCoefficients (p := p)).toHomeomorph.subtype (fun _ => Iff.rfl)

/-- The existing real rectangular coordinates, now on actual physical distributions. -/
def physicalRealBirkhoff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (u : PhysicalRealInput p) :
    RealCoeff p × RealCoeff p :=
  sourceRealBirkhoffMap hp hp1 s (physicalRealCoefficients u)

/-- Exact range identity lets the established open dense image transfer without assumptions. -/
theorem range_physicalRealBirkhoff :
    range (physicalRealBirkhoff hp hp1 s) = range (sourceRealBirkhoffMap hp hp1 s) := by
  ext z
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨physicalRealCoefficients u,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨physicalRealCoefficients.symm a,by
      simp only [physicalRealBirkhoff,Homeomorph.apply_symm_apply]⟩

/-- The physical real-input map is injective with open dense image. -/
theorem physicalRealBirkhoff_geometry
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    Function.Injective (physicalRealBirkhoff hp hp1 s) ∧
    IsOpen (range (physicalRealBirkhoff hp hp1 s)) ∧
    Dense (range (physicalRealBirkhoff hp hp1 s)) := by
  refine ⟨D.proposition17_2.comp physicalRealCoefficients.injective,?_⟩
  rw [range_physicalRealBirkhoff]
  exact D.real_map_open_dense_range

/-- On physical real inputs, the complex map lands in the article's conjugate pair locus. -/
theorem physicalBirkhoff_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (u : PhysicalRealInput p) :
    Birkhoff.IsConjugatePair (physicalBirkhoff hp hp1 s u.val) := by
  apply Birkhoff.rectangularToComplex_real
  exact D.coordinates_im_eq_zero_of_realType _ u.property

/-- Every physical real-input complex coordinate has the original spectral action. -/
theorem physicalBirkhoff_real_action
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (u : PhysicalRealInput p) (n : ℤ) :
    (physicalBirkhoff hp hp1 s u.val).1 n * (physicalBirkhoff hp hp1 s u.val).2 n =
      sourceComplexAction hp hp1 n (physicalCoefficients u.val) :=
  physicalBirkhoff_action D u.val (D.real_subset u.property) n

/-- At p=2 the physical real-form adapter is onto in rectangular coordinates. -/
theorem physicalRealBirkhoff_surjective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (hp2 : p ≤ 2) :
    Function.Surjective (physicalRealBirkhoff hp hp1 s) := by
  intro z
  obtain ⟨a,ha⟩ := D.proposition17_3 hp2 z
  exact ⟨physicalRealCoefficients.symm a, by
    simpa only [physicalRealBirkhoff,Homeomorph.apply_symm_apply] using ha⟩

/-- Local topological invertibility is transported through the actual Fourier map. -/
theorem physicalRealBirkhoff_isOpenEmbedding
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    IsOpenEmbedding (physicalRealBirkhoff hp hp1 s) :=
  D.real_map_isOpenEmbedding.comp physicalRealCoefficients.isOpenEmbedding

/-- The real-input geometry also has constructed data, rather than an assumed chart. -/
theorem exists_physicalRealBirkhoff_geometry (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      IsOpenEmbedding (physicalRealBirkhoff hp hp1 s) ∧
      Dense (range (physicalRealBirkhoff hp hp1 s)) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,physicalRealBirkhoff_isOpenEmbedding D,
    (physicalRealBirkhoff_geometry D).2.2⟩

end NLS.Articles.MKdVBelowL2
