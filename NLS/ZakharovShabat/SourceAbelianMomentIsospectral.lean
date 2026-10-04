import NLS.ZakharovShabat.SourceAbelianPrimitiveIsospectral
import NLS.ZakharovShabat.SourceAbelianMomentAtlas

/-! # Isospectral invariance of all normalized moments

The normalized psi roots and endpoint-normalized primitive agree on a
common contour. Homotopy then compares independently chosen local
atlases. Every moment order and both signed indices are retained.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Literal moment integrals agree on any common admissible circle. -/
theorem sourceAbelianMomentCircle_real_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W V : Set (CoeffPair p))
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (D : SourceAbelianSpectralChart hp hp1 W ψ.val)
    (E : SourceAbelianSpectralChart hp hp1 V φ.val)
    (n k : ℤ) (m : ℕ) (a : Coeff p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ.val) :
    sourceAbelianMomentCircle hp hp1 W n k m a ψ.val c R =
      sourceAbelianMomentCircle hp hp1 V n k m a φ.val c R := by
  apply circleIntegral.integral_congr hR
  intro z hz
  dsimp only [sourceAbelianMomentIntegrand,sourcePsiContourIntegrandJoint]
  rw [sourceFullAbelianPrimitive_real_eq_of_isospectral hp hp1 W V φ ψ h D E k z (hcircle hz),
    sourceCanonicalRoot_eq_of_isospectral hp hp1 φ ψ h z]

/-- Actual moments from independent compatible atlases agree at every
pair of isospectral real sources, including all collapsed gaps. -/
theorem SourceAbelianMomentAtlas.moment_real_eq_of_isospectral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W P V Q : Set (CoeffPair p)}
    {s t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 W s) (B : SourceAbelianMomentAtlas hp hp1 V t)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (ht : SourcePsiIsolatingComplexExtension hp hp1 Q t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (n k : ℤ) (m : ℕ) : A.moment n k m ψ.val = B.moment n k m φ.val := by
  have hψ : ψ.val ∈ A.sourceBall ψ := mem_ball_self (A.localChart ψ).radius_pos
  have hφ : φ.val ∈ B.sourceBall φ := mem_ball_self (B.localChart φ).radius_pos
  obtain ⟨D⟩ := (A.localChart ψ).charts ψ.val hψ
  obtain ⟨E⟩ := (B.localChart φ).charts φ.val hφ
  have hA := (A.localChart ψ).family ψ.val hψ
  have hB := (B.localChart φ).family φ.val hφ
  have ha : (s n ψ.val : Coeff p) = (t n φ.val : Coeff p) :=
    congrArg (fun a : DeletedCoeff p n => (a : Coeff p)) (hs.real_isospectral_agreement ht φ ψ h n)
  rw [A.moment_eq_local n k m ψ hψ,B.moment_eq_local n k m φ hφ]
  dsimp only [SourceAbelianMomentAtlas.localMoment]
  trans sourceAbelianMomentCircle hp hp1 V n k m (t n φ.val : Coeff p) φ.val
    ((A.localChart ψ).center k) ((A.localChart ψ).contourRadius k)
  · exact (sourceAbelianMomentCircle_real_eq_of_isospectral hp hp1 W V φ ψ h D E n k m
      (s n ψ.val : Coeff p) _ _ (hA.2 k).1.le (hA.2 k).2.2.2).trans
      (congrArg (fun a : Coeff p => sourceAbelianMomentCircle hp hp1 V n k m a φ.val
        ((A.localChart ψ).center k) ((A.localChart ψ).contourRadius k)) ha)
  · apply sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hp hp1 V k m n k
      (t n φ.val : Coeff p) φ.val E φ.property _ _ _ _
      (hA.1 k) (hB.1 k) (hA.2 k).1 (hB.2 k).1
      _ (hB.2 k).2.1 _ (hB.2 k).2.2.1
    · simpa only [sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h] using (hA.2 k).2.1
    · simpa only [sourceStandardRootOmittedDomain_eq_of_isospectral hp hp1 φ ψ h] using (hA.2 k).2.2.1

end NLS.ZakharovShabat
