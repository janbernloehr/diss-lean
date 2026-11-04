import NLS.KdV.HillCanonicalActionGradient
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! The ACTUAL canonical Hill actions Poisson-commute on their whole
common complex action domain. The full source-dual contour formula
proves this at every real potential; analytic real-form uniqueness
then proves it at every complex point of the unchanged domain. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusCanonicalActions_Gardner_commute_of_real
    (q : PeriodOneHminusOne) (hreal : IsRealPeriodOneHminusOne q) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction n) (hillHminusCanonicalAction m) q=0 := by
  obtain ⟨u,c,_,a,R,_,hf,hF⟩ := exists_hillHminusCanonicalAction_cotangent_contour q hreal n
  obtain ⟨v,d,_,b,S,_,hg,hG⟩ := exists_hillHminusCanonicalAction_cotangent_contour q hreal m
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusCanonicalAction n) q)
    (fderiv ℂ (hillHminusCanonicalAction m) q)=0
  rw [hF,hG]
  simp only [map_smul,smul_apply,hillMiuraActionCotangentContours_Gardner_commute q u v c d a b R S hf hg,
    smul_zero]

theorem hillHminusCanonicalActions_Gardner_commute
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalActionDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction n) (hillHminusCanonicalAction m) q=0 := by
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have he := analytic_eqOn_of_real_periodOneHminus hillHminusCanonicalActionDomain
    isOpen_hillHminusCanonicalActionDomain isConnected_hillHminusCanonicalActionDomain.isPreconnected
    ⟨0,real_mem_hillHminusCanonicalActionDomain 0 hzero,hzero⟩
    (NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction n) (hillHminusCanonicalAction m))
    (fun _ => 0)
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      (analyticOnNhd_hillHminusCanonicalAction n) (analyticOnNhd_hillHminusCanonicalAction m))
    analyticOnNhd_const (fun p _ hp => hillHminusCanonicalActions_Gardner_commute_of_real p hp n m)
  exact he hq

end NLS.KdV
