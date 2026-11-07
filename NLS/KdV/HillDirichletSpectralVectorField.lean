import NLS.KdV.HillIntrinsicAngleBrackets
import NLS.KdV.HillFilledMixedGardner
import NLS.KdV.HillDiscriminantRealForm

/-! Actual native indexed spectral vector fields. The energy is
held fixed when taking the discriminant cotangent and only then
set to the actual moving Dirichlet energy. The field is isospectral,
real on physical sources, and moves only its own divisor energy. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

def hillHminusDirichletSpectralVector (k : ℕ+) (q : PeriodOneHminusOne) : PeriodOneHminusOne :=
  NLS.Poisson.gardnerHamiltonianDirection
    (hillHminusDiscriminantCotangent (hillHminusCanonicalDirichlet k q) q)

theorem analyticOnNhd_hillHminusDirichletSpectralVector (k : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDirichletSpectralVector k) hillHminusCanonicalDirichletDomain := by
  intro q hq
  exact (NLS.Poisson.gardnerHamiltonianDirection.analyticAt _).comp
    ((analyticOnNhd_hillHminusDiscriminantCotangent_joint (hillHminusCanonicalDirichlet k q,q) (mem_univ _)).comp
      (f := fun p : PeriodOneHminusOne => (hillHminusCanonicalDirichlet k p,p))
      ((analyticOnNhd_hillHminusCanonicalDirichlet k q hq).prod analyticAt_id))

theorem hillHminusDirichletSpectralVector_real (k : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : IsRealPeriodOneHminusOne (hillHminusDirichletSpectralVector k q) := by
  dsimp only [hillHminusDirichletSpectralVector]
  rw [hillHminusCanonicalDirichlet_eq_real q hr k]
  exact hillHminusDiscriminant_Hamiltonian_real q hr (hillHminusDirichletLabels q hr k)

theorem hillHminusDirichletSpectralVector_zero_mode (k : ℕ+) (q : PeriodOneHminusOne) :
    (hillHminusDirichletSpectralVector k q).val 0=0 := by
  change (NLS.Poisson.gardnerDerivative (NLS.Poisson.hminusCotangentCLM
    (hillHminusDiscriminantCotangent (hillHminusCanonicalDirichlet k q) q))).val 0=0
  rw [NLS.Poisson.gardnerDerivative_apply]
  simp

theorem hillHminusDirichletSpectralVector_isospectral (k : ℕ+) (q : PeriodOneHminusOne) (E : ℂ) :
    hillHminusDiscriminantCotangent E q (hillHminusDirichletSpectralVector k q)=0 := by
  rw [hillHminusDirichletSpectralVector,NLS.Poisson.apply_gardnerHamiltonianDirection]
  exact hillHminusDiscriminantCotangents_Gardner_commute q E (hillHminusCanonicalDirichlet k q)

theorem fderiv_hillHminusDirichlet_spectralVector (j k : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    (fderiv ℂ (hillHminusCanonicalDirichlet j) q) (hillHminusDirichletSpectralVector k q)=
      if j=k then hillHminusDirichletSheet j q/2 else 0 := by
  change (fderiv ℂ (hillHminusCanonicalDirichlet j) q)
    (NLS.Poisson.gardnerHamiltonianVector (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet k q)) q)=_
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,NLS.Poisson.hminusGardnerBracket_antisymm,
    hillHminus_discriminant_at_Dirichlet_Gardner_matrix j k q hq]
  split_ifs <;> ring

theorem fderiv_hillHminusCompletePhasePair_spectralVector_eq_zero (n m k : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hn : hillHminusCanonicalGapSquare n q ≠ 0) (hm : hillHminusCanonicalGapSquare m q ≠ 0) :
    (fderiv ℂ (hillHminusCompletePhasePairBracket n m) q) (hillHminusDirichletSpectralVector k q)=0 := by
  change (fderiv ℂ (hillHminusCompletePhasePairBracket n m) q)
    (NLS.Poisson.gardnerHamiltonianVector (fun p => hillHminusDiscriminant p (hillHminusCanonicalDirichlet k q)) q)=0
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusCompletePhasePair_discriminant_Gardner_eq_zero_of_real n m
    (hillHminusCanonicalDirichlet k q) q hr hn hm

end NLS.KdV
