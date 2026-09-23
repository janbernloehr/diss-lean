import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness
import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-! # Starred source boundary interlacing, Lemma 9.1(iii)

Phase conjugation preserves the intrinsic periodic spectrum and every
algebraic multiplicity. Ordered spectral-data uniqueness therefore keeps the
original signed periodic endpoint indices unchanged. The ordinary source
interlacing theorem then applies to the phase-rotated source, whose boundary
roots are exactly the actual auxiliary roots.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both signed original periodic endpoint sequences are invariant under the source phase. -/
theorem canonicalPeriodicEndpoints_sourcePhase (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourcePhase φ))
      (periodOnePotential_mem (sourcePhase φ)) =
        canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourcePhase φ))
      (periodOnePotential_mem (sourcePhase φ)) =
        canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) :=
  canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential (sourcePhase φ)) (periodOnePotential φ)
    (periodOnePotential_mem _) (periodOnePotential_mem _)
    (periodicSpectrum_periodOne_sourcePhase hp φ)
    (periodicAlgebraicMultiplicity_periodOne_sourcePhase hp φ)

/-- Lemma 9.1(iii): each actual starred root lies in its original signed periodic gap. -/
theorem canonicalAuxiliaryPeriodOneRoots_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n).re ∈
      Icc (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re := by
  have h := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b (sourcePhase φ)
    (isRealType_sourcePhase φ hφ) n
  rw [(canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).1,
    (canonicalPeriodicEndpoints_sourcePhase hp hp1 φ).2] at h
  rwa [canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]

/-- Both actual auxiliary boundary sequences interlace with the same original gaps. -/
theorem canonicalAuxiliaryPeriodOneRoots_interlacing (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let l := (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    let r := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (canonicalAuxiliaryPeriodOneRoots hp hp1 .dirichlet φ n).re ∈ Icc l r ∧
      (canonicalAuxiliaryPeriodOneRoots hp hp1 .neumann φ n).re ∈ Icc l r :=
  ⟨canonicalAuxiliaryPeriodOneRoots_mem_gap hp hp1 .dirichlet φ hφ n,
    canonicalAuxiliaryPeriodOneRoots_mem_gap hp hp1 .neumann φ hφ n⟩

/-- Starred roots are strictly separated from neighboring original gaps. -/
theorem canonicalAuxiliaryPeriodOneRoots_interlacing_chain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let μ := canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n
    (R (n-1)).re < (L n).re ∧ (L n).re ≤ μ.re ∧ μ.re ≤ (R n).re ∧ (R n).re < (L (n+1)).re := by
  have h := canonicalAuxiliaryPeriodOneRoots_mem_gap hp hp1 b φ hφ n
  exact ⟨canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) (by omega), h.1, h.2,
    canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) (by omega)⟩

/-- A collapsed original gap identifies either starred root with its endpoint. -/
theorem canonicalAuxiliaryPeriodOneRoots_eq_of_collapsed_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (he : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) :
    canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
  apply Complex.ext
  · have h := canonicalAuxiliaryPeriodOneRoots_mem_gap hp hp1 b φ hφ n
    rw [← he] at h
    exact le_antisymm h.2 h.1
  · exact (canonicalAuxiliaryPeriodOneRoots_im_eq_zero hp hp1 b φ hφ n).trans
      (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ)
        (isRealType_periodOnePotential φ hφ) n).1.symm

/-- The original discriminant has the signed gap level at every actual starred root. -/
theorem signed_discriminant_auxiliaryPeriodOneRoot_ge_two (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n)).re := by
  have h := signed_discriminant_ge_two_on_canonicalGap hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) n _
    (canonicalAuxiliaryPeriodOneRoots_mem_gap hp hp1 b φ hφ n)
  have he : (((canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n).re : ℝ) : ℂ) =
      canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n := by
    apply Complex.ext
    · rfl
    · simpa only [ofReal_im] using (canonicalAuxiliaryPeriodOneRoots_im_eq_zero hp hp1 b φ hφ n).symm
  rwa [he] at h

end NLS.ZakharovShabat
