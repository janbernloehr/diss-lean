import NLS.KdV.HillNativeGardnerCoordinates
import NLS.Poisson.GardnerHamiltonianDirection

/-! The literal zero coordinate is a constant, so both rows involving
its full source cotangent vanish at every complex source. -/
noncomputable section
namespace NLS.KdV

theorem hillHminusNativeCoordinate_zero_mode :
    hillHminusNativeCoordinate 0=(fun _ : PeriodOneHminusOne => (0:ℂ)) :=
  funext hillHminusNativeComplexMap_zero_mode

theorem hillHminusNativeGardnerBracket_zero_left (l : ℤ) (q : PeriodOneHminusOne) :
    hillHminusNativeGardnerBracket 0 l q=0 := by
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusNativeCoordinate 0) q)
    (fderiv ℂ (hillHminusNativeCoordinate l) q)=0
  rw [hillHminusNativeCoordinate_zero_mode,(hasFDerivAt_const (0:ℂ) q).fderiv]
  simp only [map_zero,zero_apply]

theorem hillHminusNativeGardnerBracket_zero_right (k : ℤ) (q : PeriodOneHminusOne) :
    hillHminusNativeGardnerBracket k 0 q=0 := by
  rw [hillHminusNativeGardnerBracket_antisymm,hillHminusNativeGardnerBracket_zero_left,neg_zero]

end NLS.KdV
