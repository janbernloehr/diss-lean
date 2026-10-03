import NLS.ZakharovShabat.SourceAntiDiscriminantGradientError
import NLS.ZakharovShabat.SourceBoundarySobolevDisplacement
import NLS.ZakharovShabat.ClassicalCharacteristicGradientSummability
import NLS.SequenceSpaces.SourceConjugateGradient

/-! # G.6 at the actual source boundary roots

The proved H¹ displacement of both canonical boundary sequences supplies
G.6's spectral hypothesis. Physical gradient comparison then gives the
actual source operator estimate and its conjugate Fourier pair version.
The sources may be complex, and the finite central block is included.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At the actual Dirichlet or Neumann roots, both physical Fourier remainder
components have outer summability above the finite-exponent threshold. -/
theorem memlp_source_antiDiscriminant_gradient_fourier_norms
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (s : ℝ) (hs : 1 < s) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/s) < q)
    (φ : CoeffPair 2) (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a)
    (b : BoundaryCondition) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (fun n : ℤ => ‖classicalAntiDiscriminantGradientFourierCoefficients
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
      (classicalSobolevPotential a)
      (canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n)
      ((Real.pi : ℂ)*n) P‖) (ENNReal.ofReal s) := by
  obtain ⟨U,_,hφ,N,_,B,hB,hbound⟩ := exists_local_source_boundary_sobolev_inverse_index_bound
    hp hp1 h2p (CoeffPair.exponentInclusion h2p φ) ‖a‖ (norm_nonneg a)
  have h := memlp_classicalAntiDiscriminantGradient_fourier_norms s hs q hq B hB N
    (fun n => canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n)
    (hbound φ hφ a le_rfl ha b) a P hP
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using h

/-- The genuine anti-discriminant derivative error at either actual boundary
sequence forms an outer ℓp sequence of bounded source operators. -/
theorem memlp_source_antiDiscriminantCotangent_boundary_error
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a)
    (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => sourceAntiDiscriminantCotangent hp hp1
      (canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n)
      (CoeffPair.exponentInclusion h2p φ)-sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let q := ENNReal.ofReal (p.toReal/(p.toReal-1))
  have hq : ENNReal.ofReal (1+1/p.toReal) < q :=
    conjugate_exponent_ennreal_gt_gradient_threshold p.toReal hs
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let : q.HolderConjugate p := by
    have hc := (Real.HolderConjugate.conjExponent hs).symm.ennrealOfReal
    simpa only [Real.conjExponent,q,ENNReal.ofReal_toReal hp] using hc
  have h₁ := memlp_source_antiDiscriminant_gradient_fourier_norms hp hp1 h2p p.toReal hs q hq φ a ha b
    (ContinuousLinearMap.fst ℝ ℂ ℂ) (ContinuousLinearMap.norm_fst_le ..)
  have h₂ := memlp_source_antiDiscriminant_gradient_fourier_norms hp hp1 h2p p.toReal hs q hq φ a ha b
    (ContinuousLinearMap.snd ℝ ℂ ℂ) (ContinuousLinearMap.norm_snd_le ..)
  have hm := (h₁.add h₂).mono (fun n => norm_sourceAntiDiscriminantCotangent_error_le hp hp1 h2p hq1
    φ (classicalSobolevPotential a) (physicalBase_source_sobolev_compatibility φ a ha)
    (canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n) ((Real.pi : ℂ)*n))
  simpa only [ENNReal.ofReal_toReal hp] using hm

/-- G.6 for the actual source derivative, in the literal conjugate Fourier
pair norm, at every canonical Dirichlet or Neumann root of a complex H¹ source. -/
theorem memlp_source_antiDiscriminant_conjugate_boundary_error
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (a : Domain 2) (ha : periodOnePotential φ = domainInclusion a)
    (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => CoeffPair.conjugateGradient hp
      ((ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne')
      (sourceAntiDiscriminantCotangent hp hp1
        (canonicalPeriodOneBoundaryRoots hp hp1 b (CoeffPair.exponentInclusion h2p φ) n)
        (CoeffPair.exponentInclusion h2p φ)-sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0)) p :=
  CoeffPair.memlp_conjugateGradient hp _ _
    (memlp_source_antiDiscriminantCotangent_boundary_error hp hp1 h2p φ a ha b)

end NLS.ZakharovShabat
