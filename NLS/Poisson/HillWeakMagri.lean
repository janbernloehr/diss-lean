import NLS.ZakharovShabat.PeriodOneSobolevProductIntegration

/-! # The weak physical Hill Magri bivector on L² potentials

For a general complex L² Hill potential q, H² test gradients f,g are
represented by H¹ pairs (f,f') and (g,g'). The formula is independent of
a Miura representative and involves no pointwise derivative of q.
Its exact normalization is -d³ + 4q*d + 2q' on smooth test fields.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Poisson

def hillWeakMagriBivector (q : Coeff 2) (f df g dg : ScalarDomain 2) : ℂ :=
  reflectedHilbertPairing (scalarInclusion df) (periodOneDerivative dg)+
    2*reflectedHilbertPairing q (scalarInclusion (periodOneSobolevProduct f dg-periodOneSobolevProduct df g))

theorem hillWeakMagriBivector_antisymm (q : Coeff 2) (f df g dg : ScalarDomain 2) :
    hillWeakMagriBivector q f df g dg = -hillWeakMagriBivector q g dg f df := by
  unfold hillWeakMagriBivector
  rw [reflectedHilbertPairing_periodOneDerivative df dg,reflectedHilbertPairing_comm (periodOneDerivative df),
    periodOneSobolevProduct_comm g df,periodOneSobolevProduct_comm dg f]
  simp only [map_sub]
  ring

end NLS.Poisson
