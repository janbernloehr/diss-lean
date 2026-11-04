import NLS.Poisson.GardnerBracketJacobi

/-! Jacobi turns locally constant mixed Gardner brackets into
stationarity of the bracket of the two functionals. -/
noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Poisson

theorem hminusGardnerBracket_pair_stationary_of_constant_germs
    (F G H : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (a b : ℂ)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q)
    (hFH : hminusGardnerBracket F H =ᶠ[𝓝 q] (fun _ => a))
    (hGH : hminusGardnerBracket G H =ᶠ[𝓝 q] (fun _ => b)) :
    hminusGardnerBracket (hminusGardnerBracket F G) H q = 0 := by
  have hHF : hminusGardnerBracket H F =ᶠ[𝓝 q] (fun _ => -a) := by
    filter_upwards [hFH] with p hp
    rw [hminusGardnerBracket_antisymm,hp]
  have hdGH : fderiv ℂ (hminusGardnerBracket G H) q = 0 :=
    hGH.fderiv_eq.trans (hasFDerivAt_const b q).fderiv
  have hdHF : fderiv ℂ (hminusGardnerBracket H F) q = 0 :=
    hHF.fderiv_eq.trans (hasFDerivAt_const (-a) q).fderiv
  have h₂ : hminusGardnerBracket (hminusGardnerBracket G H) F q = 0 := by
    rw [← fderiv_apply_gardnerHamiltonianVector,hdGH,zero_apply]
  have h₃ : hminusGardnerBracket (hminusGardnerBracket H F) G q = 0 := by
    rw [← fderiv_apply_gardnerHamiltonianVector,hdHF,zero_apply]
  have hj := hminusGardnerBracket_jacobi F G H q hF hG hH
  simpa only [h₂,h₃,add_zero] using hj

theorem hminusGardnerBracket_pair_of_mixed_germs
    (F G H A B : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hF : AnalyticAt ℂ F q) (hG : AnalyticAt ℂ G q) (hH : AnalyticAt ℂ H q)
    (hFH : hminusGardnerBracket F H =ᶠ[𝓝 q] A)
    (hGH : hminusGardnerBracket G H =ᶠ[𝓝 q] B) :
    hminusGardnerBracket (hminusGardnerBracket F G) H q =
      hminusGardnerBracket F B q-hminusGardnerBracket G A q := by
  have hHF : hminusGardnerBracket H F =ᶠ[𝓝 q] (fun p => -A p) := by
    filter_upwards [hFH] with p hp
    rw [hminusGardnerBracket_antisymm,hp]
  have h₂ : hminusGardnerBracket (hminusGardnerBracket G H) F q = -hminusGardnerBracket F B q := by
    change gardnerCotangentBivector (fderiv ℂ (hminusGardnerBracket G H) q) (fderiv ℂ F q) = _
    rw [hGH.fderiv_eq]
    exact hminusGardnerBracket_antisymm B F q
  have h₃ : hminusGardnerBracket (hminusGardnerBracket H F) G q = hminusGardnerBracket G A q := by
    change gardnerCotangentBivector (fderiv ℂ (hminusGardnerBracket H F) q) (fderiv ℂ G q) = _
    rw [hHF.fderiv_eq]
    change gardnerCotangentBivector (fderiv ℂ (-A) q) (fderiv ℂ G q) = _
    rw [fderiv_neg,map_neg,neg_apply]
    change -hminusGardnerBracket A G q = _
    rw [hminusGardnerBracket_antisymm A G,neg_neg]
  have hj := hminusGardnerBracket_jacobi F G H q hF hG hH
  rw [h₂,h₃] at hj
  linear_combination hj

theorem hminusGardnerBracket_const_mul_right
    (F G : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2) (c : ℂ) (hG : AnalyticAt ℂ G q) :
    hminusGardnerBracket F (fun p => c*G p) q = c*hminusGardnerBracket F G q := by
  change gardnerCotangentBivector (fderiv ℂ F q) (fderiv ℂ (fun p => c*G p) q) = _
  rw [fderiv_const_mul hG.differentiableAt c,map_smul,smul_eq_mul]
  rfl

end NLS.Poisson
