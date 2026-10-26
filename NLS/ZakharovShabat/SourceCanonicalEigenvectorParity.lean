import NLS.ZakharovShabat.DiscriminantRootParity
import NLS.ZakharovShabat.SourcePeriodicCounting
import NLS.ZakharovShabat.FiniteSourceRealization

/-! # Periodicity of every canonical endpoint eigenfunction in the original source domain -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every original-domain eigenvector at either canonical real endpoint has
the index parity, with no restriction to large indices. -/
theorem sourceCanonicalEndpoint_eigenvector_parity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (z : ℂ)
    (hz : z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
      z = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp (periodOnePair φ) a = z • sourceDomainInclusion a) :
    a ∈ sourceDomainParitySubspace n := by
  change WeightedCoeffPair.toMax (Weight.sobolev 1) p a ∈ domainParitySubspace n
  have hpar := canonicalPeriodicEndpoints_rootSpace_parity hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n
  have hzpar : periodicRootSpaceTop hp (periodOnePotential φ) z ≤ pairParitySubspace n := by
    rcases hz with rfl | rfl
    · exact hpar.1
    · exact hpar.2
  apply eigenvector_mem_domainParitySubspace_of_root_le hp (periodOnePotential φ) z n hzpar
  have he := congrArg (CoeffPair.toMax p) ha
  change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
    (operator hp (periodOnePotential φ) (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) =
    (CoeffPair.toMax p) (z • (CoeffPair.toMax p).symm
      (domainInclusion (WeightedCoeffPair.toMax (Weight.sobolev 1) p a))) at he
  simpa only [map_smul,ContinuousLinearEquiv.apply_symm_apply] using he

/-- The actual continuous physical components have the precise one-period
Floquet sign at every canonical index, including central and collapsed gaps. -/
theorem sourceCanonicalEndpoint_eigenfunction_unit_translation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (z : ℂ)
    (hz : z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
      z = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp (periodOnePair φ) a = z • sourceDomainInclusion a) (x : ℝ) :
    Fourier.sobolevSynthesis hp a.fst ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.fst (x : AddCircle (2 : ℝ)) ∧
    Fourier.sobolevSynthesis hp a.snd ((x+1 : ℝ) : AddCircle (2 : ℝ)) =
      Fourier.wave n 1 * Fourier.sobolevSynthesis hp a.snd (x : AddCircle (2 : ℝ)) := by
  have hpar : WeightedCoeffPair.toMax (Weight.sobolev 1) p a ∈ domainParitySubspace n :=
    sourceCanonicalEndpoint_eigenvector_parity hp hp1 φ hφ n z hz a ha
  exact ⟨Fourier.sobolevSynthesis_add_one_of_parity hp a.fst n (fun k hk => (hpar k hk).1) x,
    Fourier.sobolevSynthesis_add_one_of_parity hp a.snd n (fun k hk => (hpar k hk).2) x⟩

/-- Every endpoint eigenfunction of an even canonical index is one-periodic. -/
theorem sourceCanonicalEndpoint_eigenfunction_periodic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (hn : n % 2 = 0) (z : ℂ)
    (hz : z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
      z = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp (periodOnePair φ) a = z • sourceDomainInclusion a) :
    Function.Periodic (fun x : ℝ => Fourier.sobolevSynthesis hp a.fst (x : AddCircle (2 : ℝ))) 1 ∧
    Function.Periodic (fun x : ℝ => Fourier.sobolevSynthesis hp a.snd (x : AddCircle (2 : ℝ))) 1 := by
  have hsign : Fourier.wave n 1 = 1 := by
    rw [show n = 2*(n/2) by omega,Fourier.wave_even_at_one]
  constructor
  · intro x
    simpa only [hsign,one_mul] using
      (sourceCanonicalEndpoint_eigenfunction_unit_translation hp hp1 φ hφ n z hz a ha x).1
  · intro x
    simpa only [hsign,one_mul] using
      (sourceCanonicalEndpoint_eigenfunction_unit_translation hp hp1 φ hφ n z hz a ha x).2

/-- Every endpoint eigenfunction of an odd canonical index is one-antiperiodic. -/
theorem sourceCanonicalEndpoint_eigenfunction_antiperiodic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (hn : n % 2 = 1) (z : ℂ)
    (hz : z = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∨
      z = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
    (a : WeightedCoeffPair (Weight.sobolev 1) p)
    (ha : sourceOperator hp (periodOnePair φ) a = z • sourceDomainInclusion a) :
    Function.Antiperiodic (fun x : ℝ => Fourier.sobolevSynthesis hp a.fst (x : AddCircle (2 : ℝ))) 1 ∧
    Function.Antiperiodic (fun x : ℝ => Fourier.sobolevSynthesis hp a.snd (x : AddCircle (2 : ℝ))) 1 := by
  have hsign : Fourier.wave n 1 = -1 := by
    rw [show n = 2*(n/2)+1 by omega,Fourier.wave_odd_at_one]
  constructor
  · intro x
    simpa only [hsign,neg_one_mul] using
      (sourceCanonicalEndpoint_eigenfunction_unit_translation hp hp1 φ hφ n z hz a ha x).1
  · intro x
    simpa only [hsign,neg_one_mul] using
      (sourceCanonicalEndpoint_eigenfunction_unit_translation hp hp1 φ hφ n z hz a ha x).2

end NLS.ZakharovShabat
