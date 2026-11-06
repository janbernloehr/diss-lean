import NLS.ZakharovShabat.SourceAbelianMomentAtlas
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle

/-! # Evaluating the actual moment atlas on any physical isolating circle -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)] {hp : p≠⊤} {hp1 : 1<p}
    {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The glued moment equals its literal raw contour on EVERY original
real-centered isolating circle, retaining its actual normalized roots. -/
theorem SourceAbelianMomentAtlas.moment_eq_periodCircle
    (A : SourceAbelianMomentAtlas hp hp1 W s) (φ : realTypeSourceLocus p)
    (n k : ℤ) (m : ℕ) (D : SourceCriticalRootPeriodCircle hp hp1 φ.val k) :
    A.moment n k m φ.val = sourceAbelianMomentCircle hp hp1 W n k m
      (s n φ.val:Coeff p) φ.val (D.center:ℂ) D.radius := by
  have hφ : φ.val∈A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  rw [A.moment_eq_local n k m φ hφ]
  obtain ⟨E⟩ := (A.localChart φ).charts φ.val hφ
  have hf := (A.localChart φ).family φ.val hφ
  exact sourceAbelianMomentCircle_eq_of_realCentered_enclosingCircles hp hp1 W k m n k
    (s n φ.val:Coeff p) φ.val E φ.property _ _ _ _ (hf.1 k) (ofReal_im _) (hf.2 k).1 D.radius_pos
    (hf.2 k).2.1 D.gap (hf.2 k).2.2.1 D.closedBall_subset_omittedDomain

end NLS.ZakharovShabat
