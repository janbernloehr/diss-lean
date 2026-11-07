import NLS.KdV.HillCompletePhaseDiscriminant
import NLS.KdV.HillLiftedPrimitiveDifferential

/-! The actual complete Hill phase varies every normalization of the
actual lifted primitive by Psi/(2*root), with the physical Hill sign. -/
noncomputable section
open Set Metric Complex NLS.Poisson NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P : HillProductEquationPatch} {n : ℕ+} {W : Set (CoeffPair 2)}

theorem completePhase_liftedPrimitive_Gardner_of_real
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (j : ℤ) (z : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ A.source)
    (hC : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    hminusGardnerBracket A.completePhase (fun a => P.liftedAbelianPrimitive W j (z,a)) q =
      hillHminusCanonicalPsi n (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ),q)/
        (2*sourceCanonicalRoot (by simp) (by norm_num) (P.sourcePsi q) z) := by
  have hd := P.liftedAbelianPrimitive_source_hasFDerivAt_of_real C j z q hC hr hz
  have he := A.completePhase_discriminant_Gardner_of_real
    (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) q hq hr
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (hillHminusDiscriminantCotangent (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) q)=_ at he
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (fun a => P.liftedAbelianPrimitive W j (z,a)) q)=_
  rw [hd.fderiv,map_smul,smul_eq_mul,he]
  ring

theorem completePhase_weightedQuarticIntegrand_Gardner_of_real
    (A : HillPhysicalOnIndexPhaseChart P n)
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (z : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ A.source)
    (hC : q ∈ P.momentSource C) (hr : IsRealPeriodOneHminusOne q)
    (hz : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (P.sourcePsi q)) :
    hminusGardnerBracket A.completePhase (fun a => z*(P.liftedAbelianPrimitive W 0 (z,a))^4) q =
      (P.liftedAbelianPrimitive W 0 (z,q))^3*P.abelianFrequencyDifferential n (z,q) := by
  have hd := ((P.liftedAbelianPrimitive_source_hasFDerivAt_of_real C 0 z q hC hr hz).pow 4).const_mul z
  have he := A.completePhase_liftedPrimitive_Gardner_of_real C 0 z q hq hC hr hz
  have hbase := P.liftedAbelianPrimitive_source_hasFDerivAt_of_real C 0 z q hC hr hz
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (fun a => P.liftedAbelianPrimitive W 0 (z,a)) q)=_ at he
  rw [hbase.fderiv,map_smul,smul_eq_mul] at he
  change gardnerCotangentBivector (fderiv ℂ A.completePhase q)
    (fderiv ℂ (fun a => z*(P.liftedAbelianPrimitive W 0 (z,a))^4) q)=_
  rw [hd.fderiv]
  simp only [map_smul,smul_eq_mul]
  dsimp only [HillProductEquationPatch.abelianFrequencyDifferential,
    HillProductEquationPatch.abelianFrequencyNumerator]
  linear_combination 4*z*(P.liftedAbelianPrimitive W 0 (z,q))^3*he

end NLS.KdV.HillPhysicalOnIndexPhaseChart
