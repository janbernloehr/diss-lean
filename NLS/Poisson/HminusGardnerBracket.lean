import NLS.Poisson.GardnerBivector
import NLS.Poisson.SobolevBivector
import NLS.SequenceSpaces.SobolevScalarGradient

noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal

namespace NLS.Poisson



def hminusCotangentCLM :
    (WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  (negNegIsometry (p := 2) 1).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (-1) (by norm_num))

theorem hminusCotangentCLM_apply (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) (k : ℤ) :
    (hminusCotangentCLM L).val k=
      L (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1)) := by
  change (negNegIsometry (p := 2) 1
    (WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (-1) (by norm_num) L)).val k=_
  rw [negNegIsometry_val,WeightedCoeff.sobolevCotangentCLM_apply,WeightedCoeff.sobolevCotangent_val]

theorem norm_hminusCotangentCLM (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    ‖hminusCotangentCLM L‖=‖L‖ := by
  change ‖negNegIsometry (p := 2) 1
    (WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (-1) (by norm_num) L)‖=_
  rw [LinearIsometryEquiv.norm_map,WeightedCoeff.sobolevCotangentCLM_apply,WeightedCoeff.norm_sobolevCotangent]

theorem hminusCotangentCLM_represents (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (h : WeightedCoeff (Weight.sobolev (-1)) 2) :
    L h=WeightedCoeff.sobolevBilinearPairing 1 (hminusCotangentCLM L) h := by
  have he := (WeightedCoeff.sobolevBilinearPairing_sobolevCotangent
    (p := 2) (q := 2) (-1) (by norm_num) L h).symm
  rw [WeightedCoeff.sobolevBilinearPairing_apply] at he ⊢
  rw [he,← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => (hminusCotangentCLM L).val k*h.val (-k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply,neg_neg,hminusCotangentCLM_apply,WeightedCoeff.sobolevCotangent_val]
  ring

def hminusScalarGradient (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : WeightedCoeff (Weight.sobolev 1) 2 :=
  hminusCotangentCLM (fderiv ℂ F q)

theorem hminusScalarGradient_apply (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (k : ℤ) :
    (hminusScalarGradient F q).val k=
      (fderiv ℂ F q) (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1)) :=
  hminusCotangentCLM_apply _ k

theorem hminusScalarGradient_represents (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q h : WeightedCoeff (Weight.sobolev (-1)) 2) :
    fderiv ℂ F q h=WeightedCoeff.sobolevBilinearPairing 1 (hminusScalarGradient F q) h := by
  exact hminusCotangentCLM_represents (fderiv ℂ F q) h

theorem norm_hminusScalarGradient (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : ‖hminusScalarGradient F q‖=‖fderiv ℂ F q‖ :=
  norm_hminusCotangentCLM _

theorem analyticOnNhd_hminusScalarGradient (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    {U : Set (WeightedCoeff (Weight.sobolev (-1)) 2)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (hminusScalarGradient F) U := by
  intro q hq
  exact (hminusCotangentCLM.analyticAt _).comp (hF.fderiv q hq)

def hminusGardnerBracket (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : ℂ :=
  gardnerBivector (hminusScalarGradient F q) (hminusScalarGradient G q)

theorem hminusGardnerBracket_antisymm (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : hminusGardnerBracket F G q= -hminusGardnerBracket G F q :=
  gardnerBivector_antisymm _ _

theorem hminusGardnerBracket_self (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) : hminusGardnerBracket F F q=0 := gardnerBivector_self _

theorem norm_hminusGardnerBracket_le (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) :
    ‖hminusGardnerBracket F G q‖ ≤ (2*Real.pi)*‖fderiv ℂ F q‖*‖fderiv ℂ G q‖ := by
  simpa only [hminusGardnerBracket,norm_hminusScalarGradient] using
    norm_gardnerBivector_le (hminusScalarGradient F q) (hminusScalarGradient G q)

theorem analyticOnNhd_hminusGardnerBracket (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    {U : Set (WeightedCoeff (Weight.sobolev (-1)) 2)} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U) :
    AnalyticOnNhd ℂ (hminusGardnerBracket F G) U :=
  analyticOnNhd_gardnerBivector _ _ (analyticOnNhd_hminusScalarGradient F hF) (analyticOnNhd_hminusScalarGradient G hG)

end NLS.Poisson
