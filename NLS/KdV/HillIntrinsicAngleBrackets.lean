import NLS.KdV.HillCompletePhaseCotangent
import NLS.KdV.HillAnglePairDiscriminantStationarity

/-! Branch-independent native Gardner brackets of the actual
complete Abelian angle differentials. Local chart identities supply
the actual mixed brackets and isospectrality at every real source
in the natural original open-gap locus. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

def hillHminusCompletePhaseFunctionalBracket (n : ℕ+) (G : PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) : ℂ :=
  NLS.Poisson.gardnerCotangentBivector (hillHminusCompletePhaseCotangent n q) (fderiv ℂ G q)

def hillHminusCompletePhasePairBracket (n m : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  NLS.Poisson.gardnerCotangentBivector (hillHminusCompletePhaseCotangent n q) (hillHminusCompletePhaseCotangent m q)

theorem analyticOnNhd_hillHminusCompletePhasePairBracket (n m : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCompletePhasePairBracket n m)
      (hillHminusCompletePhaseDomain n ∩ hillHminusCompletePhaseDomain m) := by
  intro q hq
  exact (NLS.Poisson.gardnerCotangentBivector.analyticAt_bilinear _).comp₂
    (analyticOnNhd_hillHminusCompletePhaseCotangent n q hq.1)
    (analyticOnNhd_hillHminusCompletePhaseCotangent m q hq.2)

namespace HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem completePhaseFunctionalBracket_eq_local_of_real (C : HillPhysicalOnIndexPhaseChart P n)
    (G : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ C.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCompletePhaseFunctionalBracket n G q=NLS.Poisson.hminusGardnerBracket C.completePhase G q := by
  change NLS.Poisson.gardnerCotangentBivector (hillHminusCompletePhaseCotangent n q) (fderiv ℂ G q)=_
  rw [C.completePhaseCotangent_eq_fderiv_of_real q hq hr]
  rfl

theorem eventually_completePhasePairBracket_eq_local (C : HillPhysicalOnIndexPhaseChart P n)
    (D : HillPhysicalOnIndexPhaseChart Q m) (q : PeriodOneHminusOne)
    (hqC : q ∈ C.source) (hqD : q ∈ D.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCompletePhasePairBracket n m =ᶠ[𝓝 q] C.completePhasePairBracket D := by
  filter_upwards [C.eventually_completePhaseCotangent_eq_fderiv q hqC hr,
    D.eventually_completePhaseCotangent_eq_fderiv q hqD hr] with p hpC hpD
  change NLS.Poisson.gardnerCotangentBivector (hillHminusCompletePhaseCotangent n p)
    (hillHminusCompletePhaseCotangent m p)=_
  rw [hpC,hpD]
  rfl

end HillPhysicalOnIndexPhaseChart

theorem hillHminusCompletePhaseFunctionalBracket_action_of_real (n k : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusCompletePhaseFunctionalBracket n (hillHminusCanonicalAction k) q=-(if k=n then (1:ℂ) else 0) := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨C,_,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q (P.real_mem_physicalDirichletSource q hq hr) hr hg
  rw [C.completePhaseFunctionalBracket_eq_local_of_real _ q hCq hr]
  exact C.completePhase_action_Gardner_of_real k q hCq hr

theorem hillHminusCompletePhaseFunctionalBracket_discriminant_of_real (n : ℕ+) (E : ℂ)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusCompletePhaseFunctionalBracket n (fun p => hillHminusDiscriminant p E) q=
      (1/2:ℂ)*hillHminusCanonicalPsi n (E,q) := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨C,_,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q (P.real_mem_physicalDirichletSource q hq hr) hr hg
  rw [C.completePhaseFunctionalBracket_eq_local_of_real _ q hCq hr]
  exact C.completePhase_discriminant_Gardner_of_real E q hCq hr

theorem hillHminusCompletePhasePair_discriminant_Gardner_eq_zero_of_real (n m : ℕ+) (E : ℂ)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hn : hillHminusCanonicalGapSquare n q ≠ 0) (hm : hillHminusCanonicalGapSquare m q ≠ 0) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCompletePhasePairBracket n m)
      (fun p => hillHminusDiscriminant p E) q=0 := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨C,_,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q (P.real_mem_physicalDirichletSource q hq hr) hr hn
  obtain ⟨D,_,hDq⟩ := exists_hillPhysicalOnIndexPhaseChart P m q (P.real_mem_physicalDirichletSource q hq hr) hr hm
  have he := C.eventually_completePhasePairBracket_eq_local D q hCq hDq hr
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCompletePhasePairBracket n m) q)
    (fderiv ℂ (fun p => hillHminusDiscriminant p E) q)=0
  rw [he.fderiv_eq]
  exact C.completePhasePairDiscriminantBracket_eq_zero_of_real D q hCq hDq hr E

end NLS.KdV
