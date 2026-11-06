import NLS.Poisson.HminusGardnerBracket

noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal

namespace NLS.Poisson



def gardnerCotangentBivector :
    (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ]
      (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] ℂ :=
  gardnerBivector.bilinearComp hminusCotangentCLM hminusCotangentCLM

theorem gardnerCotangentBivector_antisymm (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerCotangentBivector L M= -gardnerCotangentBivector M L := gardnerBivector_antisymm _ _

def gardnerHamiltonianDirection :
    (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) 2 :=
  gardnerDerivative.comp hminusCotangentCLM

theorem apply_gardnerHamiltonianDirection (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    L (gardnerHamiltonianDirection M)=gardnerCotangentBivector L M :=
  hminusCotangentCLM_represents L (gardnerDerivative (hminusCotangentCLM M))

theorem norm_gardnerHamiltonianDirection_le (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    ‖gardnerHamiltonianDirection L‖ ≤ (2*Real.pi)*‖L‖ := by
  change ‖gardnerDerivative (hminusCotangentCLM L)‖ ≤ _
  simpa only [norm_hminusCotangentCLM] using norm_gardnerDerivative_le (hminusCotangentCLM L)

def gardnerHamiltonianVector (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : WeightedCoeff (Weight.sobolev (-1)) 2 :=
  gardnerHamiltonianDirection (fderiv ℂ F q)

theorem fderiv_apply_gardnerHamiltonianVector (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) :
    (fderiv ℂ F q) (gardnerHamiltonianVector G q)=hminusGardnerBracket F G q :=
  apply_gardnerHamiltonianDirection _ _

theorem gardnerHamiltonianVector_apply (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (k : ℤ) :
    (gardnerHamiltonianVector F q).val k=(2*Real.pi:ℂ)*I*k*(hminusScalarGradient F q).val k := rfl

theorem analyticOnNhd_gardnerHamiltonianVector (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    {U : Set (WeightedCoeff (Weight.sobolev (-1)) 2)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (gardnerHamiltonianVector F) U := by
  intro q hq
  exact (gardnerHamiltonianDirection.analyticAt _).comp (hF.fderiv q hq)

end NLS.Poisson
