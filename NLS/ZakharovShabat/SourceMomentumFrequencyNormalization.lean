import NLS.ZakharovShabat.SourceSection20MomentumBracket
import NLS.ZakharovShabat.SobolevNLSHamiltonianHierarchy

/-! # The original NLS S_2 frequency and its physical momentum normalization

The actual constructed original angle family has {theta_n,S_2}=2πn
on every real H¹ source where the angle is defined. No mKdV object enters
this normalization. The constant source function is its entire candidate
frequency extension; uniqueness on the real L² domain is proved separately.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The original hierarchy's actual S₂ differential is represented by the
physical momentum cotangent used below to normalize its angle bracket. -/
theorem fderiv_originalS2_eq_sourceMomentumCotangent (a : ScalarDomain 2 × ScalarDomain 2) :
    fderiv ℂ (fun b => sobolevNLSHamiltonian 1 (higherSobolevSourceOneEquiv b) 2 (by norm_num)) a =
      (sourceSobolevMomentumCotangent a).comp sobolevSourceInclusion := by
  have he : (fun b => sobolevNLSHamiltonian 1 (higherSobolevSourceOneEquiv b) 2 (by norm_num)) =
      periodOneSobolevMomentum := funext sobolevNLSHamiltonian_two_eq_periodOneSobolevMomentum
  rw [he]
  exact fderiv_periodOneSobolevMomentum a

structure SourceMomentumFrequencyFamily where
  base : Set (CoeffPair 2)
  beta : Set (CoeffPair 2)
  domain : Set (CoeffPair 2)
  psi : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n
  angle : SourceAngularThetaCommonDomainData (by simp) (by norm_num) base beta domain psi
  normalization : ∀ a : realTypeSobolevSourceLocus, ∀ n : ℤ,
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0 → sourceSobolevThetaMomentumBracket n psi a.val = 2*(Real.pi : ℂ)*n

theorem nonempty_sourceMomentumFrequencyFamily : Nonempty SourceMomentumFrequencyFamily := by
  obtain ⟨W₀,W,V,s,D,Wa,A,B,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  exact ⟨⟨_,_,_,s,D.previous.original_theta_common_domain,Q.sobolev_momentum_bracket⟩⟩

/-- The NLS momentum frequency with the original period-one sign. -/
def sourceMomentumFrequency (n : ℤ) (_φ : CoeffPair 2) : ℂ := 2*(Real.pi : ℂ)*n

theorem analyticAt_sourceMomentumFrequency (n : ℤ) (φ : CoeffPair 2) :
    AnalyticAt ℂ (sourceMomentumFrequency n) φ := analyticAt_const

/-- This is an identification with the original physical S_2 bracket,
not a frequency prescribed by the mKdV restriction. -/
theorem SourceMomentumFrequencyFamily.frequency_eq_original_bracket (A : SourceMomentumFrequencyFamily)
    (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0) :
    sourceMomentumFrequency n (sobolevSourceInclusion a.val) = sourceSobolevThetaMomentumBracket n A.psi a.val :=
  (A.normalization a n hn).symm

end NLS.ZakharovShabat
