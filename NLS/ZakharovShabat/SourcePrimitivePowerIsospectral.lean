import NLS.ZakharovShabat.SourceAbelianPrimitiveIsospectral
import NLS.ZakharovShabat.SourceActionIsospectralAllExponents
import NLS.ZakharovShabat.SourceRenormalizedHamiltonian

/-! # Primitive-power moments depend only on the actions

Isospectral primitives agree on common circles. Comparing independently
chosen isolating circles gives invariance of all moments and their sum.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Primitive-power integrals agree on a common circle for isospectral real sources. -/
theorem sourcePrimitivePowerCircle_real_eq_of_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W V : Set (CoeffPair p))
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (D : SourceAbelianSpectralChart hp hp1 W ψ.val) (E : SourceAbelianSpectralChart hp hp1 V φ.val)
    (n : ℤ) (m : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hc : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ.val) :
    sourcePrimitivePowerCircle hp hp1 W n m ψ.val c R =
      sourcePrimitivePowerCircle hp hp1 V n m φ.val c R := by
  unfold sourcePrimitivePowerCircle
  congr 1
  apply circleIntegral.integral_congr hR
  intro z hz
  exact congrArg (fun v : ℂ => v^m)
    (sourceFullAbelianPrimitive_real_eq_of_isospectral hp hp1 W V φ ψ h D E n z (hc hz))

namespace SourcePrimitivePowerAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}

/-- Isospectral real sources have identical actual primitive-power moments. -/
theorem moment_real_eq_of_isospectral
    (A : SourcePrimitivePowerAtlas hp hp1 W) (B : SourcePrimitivePowerAtlas hp hp1 V)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ) (m : ℕ) :
    A.moment n m ψ.val = B.moment n m φ.val := by
  have hψ : ψ.val ∈ A.sourceBall ψ := mem_ball_self (A.localChart ψ).radius_pos
  have hφ : φ.val ∈ B.sourceBall φ := mem_ball_self (B.localChart φ).radius_pos
  obtain ⟨D⟩ := (A.localChart ψ).charts ψ.val hψ
  obtain ⟨E⟩ := (B.localChart φ).charts φ.val hφ
  have hA := (A.localChart ψ).family ψ.val hψ
  have hB := (B.localChart φ).family φ.val hφ
  rw [A.moment_eq_local n m ψ hψ,B.moment_eq_local n m φ hφ]
  dsimp only [localMoment]
  trans sourcePrimitivePowerCircle hp hp1 V n m φ.val ((A.localChart ψ).center n) ((A.localChart ψ).contourRadius n)
  · exact sourcePrimitivePowerCircle_real_eq_of_isospectral hp hp1 W V φ ψ h D E n m _ _
      (hA.2 n).1.le (hA.2 n).2.2.2
  · apply sourcePrimitivePowerCircle_eq_of_realCentered_enclosingCircles hp hp1 V n m φ.val E φ.property
      _ _ _ _ (hA.1 n) (hB.1 n) (hA.2 n).1 (hB.2 n).1 _ (hB.2 n).2.1 _ (hB.2 n).2.2.1
    · simpa only [sourcePeriodicSegment_eq_of_isospectral hp hp1 φ ψ h] using (hA.2 n).2.1
    · simpa only [sourceStandardRootOmittedDomain_eq_of_isospectral hp hp1 φ ψ h] using (hA.2 n).2.2.1

/-- Equal original actions determine every moment at every finite exponent above one. -/
theorem moment_real_eq_of_actions
    (A : SourcePrimitivePowerAtlas hp hp1 W) (B : SourcePrimitivePowerAtlas hp hp1 V)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceRealActionLevelSet hp hp1 φ) (n : ℤ) (m : ℕ) :
    A.moment n m ψ.val = B.moment n m φ.val := by
  apply A.moment_real_eq_of_isospectral B φ ψ _ n m
  rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents hp hp1 φ]

end SourcePrimitivePowerAtlas

namespace SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {W V : Set (CoeffPair 4)}

/-- The actual FL⁴ Hamiltonian is constant on real action level sets. -/
theorem renormalizedHamiltonian_real_eq_of_actions
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (B : SourcePrimitivePowerAtlas (by simp) (by norm_num) V)
    (φ ψ : realTypeSourceSubmodule 4)
    (h : ψ ∈ sourceRealActionLevelSet (by simp) (by norm_num) φ) :
    A.renormalizedHamiltonian ψ.val = B.renormalizedHamiltonian φ.val := by
  unfold renormalizedHamiltonian
  congr 1
  exact tsum_congr (fun n => A.moment_real_eq_of_actions B φ ψ h n 3)

end SourcePrimitivePowerAtlas
end NLS.ZakharovShabat
