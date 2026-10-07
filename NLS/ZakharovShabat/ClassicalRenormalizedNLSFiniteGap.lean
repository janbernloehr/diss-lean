import NLS.ZakharovShabat.SourceFiniteGapClassicalRenormalizedNLS
import NLS.ZakharovShabat.ClassicalNLSNonextension

/-! # The unique physical renormalized solution of every finite-gap source

Finite-gap sources at every finite exponent greater than one have a
smooth physical representative and a finite physical mass. Gauging the
unique ordinary classical trajectory constructs the unique renormalized
one. Its Fourier coefficients agree with the actual Hilbert spectral flow
of the same source, independently of all choices of spectral atlas.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original physical mass of a finite-gap source at any finite exponent. -/
def sourceFiniteGapPhysicalMass (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖(sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x‖^2

/-- The same physical mass is obtained from the Hilbert model's unchanged coefficients. -/
theorem sourceFiniteGapPhysicalMass_eq_hilbertMass (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapPhysicalMass hp hp1 φ hf =
      sourceOrdinaryMass le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) := by
  rw [sourceOrdinaryMass_eq_finiteGap_integral _ (sourceFiniteGapHilbertModel_mem hp hp1 φ hf),
    sourceFiniteGapHilbertModel_physicalPair]
  rfl

/-- The canonical renormalized classical trajectory is the physical mass
gauge of the unique ordinary trajectory of the same finite-gap source. -/
def sourceFiniteGapClassicalRenormalizedTrajectory (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  classicalNLSGauge (sourceFiniteGapPhysicalMass hp hp1 φ hf)
    (sourceFiniteGapClassicalTrajectory hp hp1 φ hf)

/-- The canonical trajectory obeys the renormalized PDE with its actual
physical mass and has the exact original physical initial value. -/
theorem sourceFiniteGapClassicalRenormalizedTrajectory_spec (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    IsClassicalRenormalizedNLSTrajectory (sourceFiniteGapPhysicalMass hp hp1 φ hf)
      (sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf) ∧
    ∀ x : ℝ, sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x := by
  have hu := sourceFiniteGapClassicalTrajectory_spec hp hp1 φ hf
  exact ⟨hu.1.gauge _,by simpa only [sourceFiniteGapClassicalRenormalizedTrajectory,
    classicalNLSGauge_zero_time] using hu.2⟩

/-- Every real finite-gap source at every finite p>1 has a unique classical
renormalized trajectory; the mass is its original physical integral. -/
theorem existsUnique_sourceFiniteGap_classicalRenormalizedNLS_trajectory_atExponent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      IsClassicalRenormalizedNLSTrajectory (sourceFiniteGapPhysicalMass hp hp1 φ hf) u ∧
        ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) = (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x := by
  have hc := sourceFiniteGapClassicalRenormalizedTrajectory_spec hp hp1 φ hf
  refine ⟨sourceFiniteGapClassicalRenormalizedTrajectory hp hp1 φ hf,hc,?_⟩
  intro u hu
  apply hu.1.eq_of_eq_at hc.1 0
  ext y
  induction y using QuotientAddGroup.induction_on with
  | H y => exact (hu.2 y).trans (hc.2 y).symm

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Every classical renormalized solution has exactly the Fourier coefficients
of the constructed Hilbert flow of the same finite-gap physical source. -/
theorem periodOneCoefficient_classicalRenormalizedNLS_eq_hamiltonianFlow
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (sourceFiniteGapPhysicalMass hp hp1 φ hf) u)
    (hinit : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) n =
      (H.hamiltonianRenormalizedSourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) time).val.fst n := by
  have hu₂ : IsClassicalRenormalizedNLSTrajectory
      (sourceOrdinaryMass le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf)) u := by
    rwa [sourceFiniteGapPhysicalMass_eq_hilbertMass] at hu
  have hinit₂ : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
        (sourceFiniteGapHilbertModel_mem hp hp1 φ hf)).1 x := by
    simpa only [sourceFiniteGapHilbertModel_physicalPair] using hinit
  have he : (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) =
      (H.hamiltonianRenormalizedPhysicalFlow E (sourceFiniteGapHilbertModel hp hp1 φ hf)
        (sourceFiniteGapHilbertModel_mem hp hp1 φ hf) time).1 :=
    funext (H.classicalRenormalizedNLS_eq_hamiltonianRenormalizedPhysicalFlow hs E _ _ u hu₂ hinit₂ time)
  rw [he]
  exact (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) _ _ n).1

end SourceAbelianMomentAtlas

/-- Any classical renormalized trajectory with finite-gap initial data
conserves the actual physical mass integral at all real times. -/
theorem classicalRenormalizedNLS_finiteGap_mass
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (u : ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hu : IsClassicalRenormalizedNLSTrajectory (sourceFiniteGapPhysicalMass hp hp1 φ hf) u)
    (hinit : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 x) (time : ℝ) :
    (∫ x in (0 : ℝ)..1, ‖u time (x : AddCircle (2 : ℝ))‖^2) =
      sourceFiniteGapPhysicalMass hp hp1 φ hf := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨H⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,B,X,t,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  rw [sourceFiniteGapPhysicalMass_eq_hilbertMass] at hu ⊢
  have hinit₂ : ∀ x : ℝ, u 0 (x : AddCircle (2 : ℝ)) =
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) (sourceFiniteGapHilbertModel hp hp1 φ hf)
        (sourceFiniteGapHilbertModel_mem hp hp1 φ hf)).1 x := by
    simpa only [sourceFiniteGapHilbertModel_physicalPair] using hinit
  have he := H.classicalRenormalizedNLS_eq_hamiltonianRenormalizedPhysicalFlow
    hs.toSourcePsiIsolatingComplexExtension E _ _ u hu hinit₂ time
  simp only [he]
  exact H.hamiltonianRenormalizedPhysicalFlow_mass E _ _ time

end NLS.ZakharovShabat
