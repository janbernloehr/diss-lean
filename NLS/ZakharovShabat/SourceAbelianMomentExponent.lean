import NLS.ZakharovShabat.SourceAbelianPrimitiveExponent
import NLS.ZakharovShabat.SourceAbelianMomentAtlas
import NLS.ZakharovShabat.SourcePsiGapRootExponent

/-! # Exponent compatibility of the actual normalized moments

The literal integrands agree on a common circle. Contour homotopy then
compares independently chosen atlases. All moment orders, selected
indices, and collapsed gaps are included.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A real-source moment on a fixed admissible circle is unchanged by
exponent inclusion, including its primitive normalization. -/
theorem sourceAbelianMomentCircle_real_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (W : Set (CoeffPair p)) (V : Set (CoeffPair q)) (φ : realTypeSourceSubmodule p)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val)
    (E : SourceAbelianSpectralChart hq hq1 V (CoeffPair.exponentInclusion hpq φ.val))
    (n k : ℤ) (m : ℕ) (a : Coeff p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAbelianMomentCircle hp hp1 W n k m a φ.val c R =
      sourceAbelianMomentCircle hq hq1 V n k m (Coeff.exponentInclusion hpq a)
        (CoeffPair.exponentInclusion hpq φ.val) c R := by
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only [sourceAbelianMomentIntegrand,sourcePsiContourIntegrandJoint]
  rw [sourceFullAbelianPrimitive_real_exponent hp hq hp1 hq1 hpq W V φ D E k z (hcircle hz),
    sourcePsiCandidate_exponent hpq n a z, sourceCanonicalRoot_exponent hp hq hp1 hq1 hpq φ.val z]

/-- Actual moments from arbitrary compatible normalized extensions
and arbitrary local contour atlases agree after real-source inclusion. -/
theorem SourceAbelianMomentAtlas.moment_real_exponent
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W P : Set (CoeffPair p)} {V Q : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hq hq1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hq hq1 Q t)
    (hpq : p ≤ q) (φ : realTypeSourceSubmodule p) (n k : ℤ) (m : ℕ) :
    A.moment n k m φ.val = B.moment n k m (CoeffPair.exponentInclusion hpq φ.val) := by
  let ψ := realTypeSourceExponentInclusion hpq φ
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  have hψ : ψ.val ∈ B.sourceBall ψ := mem_ball_self (B.localChart ψ).radius_pos
  obtain ⟨D⟩ := (A.localChart φ).charts φ.val hφ
  obtain ⟨E⟩ := (B.localChart ψ).charts ψ.val hψ
  have hA := (A.localChart φ).family φ.val hφ
  have hB := (B.localChart ψ).family ψ.val hψ
  have ha : Coeff.exponentInclusion hpq (s n φ.val : Coeff p) = (t n ψ.val : Coeff q) :=
    congrArg (fun a : DeletedCoeff q n => (a : Coeff q)) (hs.real_exponent_agreement ht hpq n φ)
  change A.moment n k m φ.val = B.moment n k m ψ.val
  rw [A.moment_eq_local n k m φ hφ,B.moment_eq_local n k m ψ hψ]
  dsimp only [SourceAbelianMomentAtlas.localMoment]
  trans sourceAbelianMomentCircle hq hq1 V n k m (t n ψ.val : Coeff q) ψ.val
    ((A.localChart φ).center k) ((A.localChart φ).contourRadius k)
  · exact (sourceAbelianMomentCircle_real_exponent hp hq hp1 hq1 hpq W V φ D E n k m
      (s n φ.val : Coeff p) _ _ (hA.2 k).1.le (hA.2 k).2.2.2).trans
      (congrArg (fun a : Coeff q => sourceAbelianMomentCircle hq hq1 V n k m a ψ.val
        ((A.localChart φ).center k) ((A.localChart φ).contourRadius k)) ha)
  · apply sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hq hq1 V k m n k
      (t n ψ.val : Coeff q) ψ.val E ψ.property _ _ _ _
      (hA.1 k) (hB.1 k) (hA.2 k).1 (hB.2 k).1
      _ (hB.2 k).2.1 _ (hB.2 k).2.2.1
    · simpa only [ψ,realTypeSourceExponentInclusion,sourcePeriodicSegment_exponent hp hq hp1 hq1 hpq φ.val] using (hA.2 k).2.1
    · simpa only [ψ,realTypeSourceExponentInclusion,sourceStandardRootOmittedDomain_exponent hp hq hp1 hq1 hpq φ.val] using (hA.2 k).2.2.1

/-- Equal Fourier coefficients give equal real-source moments, even
when neither source exponent was fixed in advance. -/
theorem SourceAbelianMomentAtlas.moment_real_eq_of_coefficients
    {hp : p ≠ ⊤} {hq : q ≠ ⊤} {hp1 : 1 < p} {hq1 : 1 < q}
    {W P : Set (CoeffPair p)} {V Q : Set (CoeffPair q)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hq hq1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hq hq1 Q t)
    (φ : realTypeSourceSubmodule p) (ψ : realTypeSourceSubmodule q)
    (hcoeff : ∀ j : ℤ, ψ.val.fst j = φ.val.fst j ∧ ψ.val.snd j = φ.val.snd j)
    (n k : ℤ) (m : ℕ) : A.moment n k m φ.val = B.moment n k m ψ.val := by
  rcases le_total p q with hpq | hqp
  · have he : CoeffPair.exponentInclusion hpq φ.val = ψ.val := by
      apply (CoeffPair.toMax q).injective
      apply Prod.ext
      · ext j; exact (hcoeff j).1.symm
      · ext j; exact (hcoeff j).2.symm
    simpa only [he] using A.moment_real_exponent B hs ht hpq φ n k m
  · have he : CoeffPair.exponentInclusion hqp ψ.val = φ.val := by
      apply (CoeffPair.toMax p).injective
      apply Prod.ext
      · ext j; exact (hcoeff j).1
      · ext j; exact (hcoeff j).2
    simpa only [he] using (B.moment_real_exponent A ht hs hqp ψ n k m).symm

end NLS.ZakharovShabat
