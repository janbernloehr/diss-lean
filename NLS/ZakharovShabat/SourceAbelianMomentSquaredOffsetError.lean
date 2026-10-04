import NLS.ZakharovShabat.SourceAbelianMomentSecondError
import NLS.ZakharovShabat.SourcePsiLemma12_12

/-! # Actual squared-gap root offsets in the cubic moment bound

Lemma 12.12 supplies the retained psi-root offset sequence. Substituting
it in the quantitative off-diagonal error gives a cubic-gap majorant,
with no separate root-to-gap-distance hypothesis and no division by gaps.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every complex segment lies within a half-gap of its midpoint. -/
theorem norm_sourceMidpoint_sub_le_halfGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
    ‖sourceStandardRootMidpoint hp hp1 ψ k-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖/2 := by
  rw [← sourceStandardRoot_gapSegment_eq_periodicSegment hp hp1 ψ k] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have he : sourceStandardRootMidpoint hp hp1 ψ k -
      (sourceStandardRootMidpoint hp hp1 ψ k+sourceStandardRootHalfGap hp hp1 ψ k*(t:ℂ)) =
        -sourceStandardRootHalfGap hp hp1 ψ k*(t:ℂ) := by ring
  rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
  have hb := mul_le_mul_of_nonneg_left (abs_le.mpr ht) (norm_nonneg (sourceStandardRootHalfGap hp hp1 ψ k))
  simpa only [mul_one,sourceStandardRootHalfGap,sourcePeriodicGapDisplacement_apply,norm_div,norm_ofNat] using hb

namespace SourceAbelianMomentErrorDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- A squared-gap root offset turns the exact leading term and the
remainder into one explicit cubic-gap bound, including zero gaps. -/
theorem offDiagonal_squaredOffset_bound
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (n k : ℤ) (hkn : k ≠ n) (α : ℂ)
    (hα : displacedRoots (s n ψ : Coeff p) k = sourceStandardRootMidpoint hp hp1 ψ k+
      (sourcePeriodicGapDisplacement hp hp1 ψ k)^2*α)
    (E F : ℝ) (hE : 0 ≤ E)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*E)
    (hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ F) :
    ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3 *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖α‖/4+
          2*(‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖α‖+1/2)*(E*(F+1)+F/4)) := by
  let G := ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖
  have hL : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖displacedRoots (s n ψ : Coeff p) k-z‖ ≤ G*(G*‖α‖+1/2) := by
    intro z hz
    rw [hα]
    calc
      _ = ‖(sourcePeriodicGapDisplacement hp hp1 ψ k)^2*α+(sourceStandardRootMidpoint hp hp1 ψ k-z)‖ := by congr 1; ring
      _ ≤ G^2*‖α‖+G/2 := (norm_add_le _ _).trans
        (add_le_add (by simp [G,norm_pow]) (norm_sourceMidpoint_sub_le_halfGap hp hp1 ψ k z hz))
      _ = _ := by ring
  have hb := D.offDiagonal_error_bound ψ hψ n k hkn E F (G*‖α‖+1/2) hE
    (by dsimp only [G]; positivity) hS hR hL
  let Q := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2 *
    (displacedRoots (s n ψ : Coeff p) k-sourceStandardRootMidpoint hp hp1 ψ k)/4
  have hQ : ‖Q‖ = G^4*‖α‖/4 := by
    dsimp only [Q]
    rw [hα]
    simp only [add_sub_cancel_left,norm_div,norm_mul,norm_pow,norm_ofNat,sourcePeriodicGapDisplacement_apply,G]
    ring
  calc
    _ ≤ ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ-Q‖+‖Q‖ := by
      simpa only [sub_add_cancel] using norm_add_le (((n-k:ℤ):ℂ)*A.moment n k 2 ψ-Q) Q
    _ ≤ 2*G^3*(G*‖α‖+1/2)*(E*(F+1)+F/4)+G^4*‖α‖/4 := add_le_add hb hQ.le
    _ = _ := by dsimp only [G]; ring

/-- The offset coefficients in the cubic estimate come from the actual
normalized psi branch, with one locally uniform lp bound for every row. -/
theorem locally_uniform_offDiagonal_squaredOffset_bound
    (D : SourceAbelianMomentErrorDomain A)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : CoeffPair p) (hφD : φ ∈ D.domain) (hφV : φ ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ ∈ T ∧ T ⊆ D.domain ∩ V ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧ ‖α‖ ≤ C ∧
        ∀ k : ℤ, k ≠ n → ∀ E F : ℝ, 0 ≤ E →
          (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
              ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*E) →
          (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ F) →
          ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ‖ ≤
            ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3 *
              (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖α k‖/4+
                2*(‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*‖α k‖+1/2)*(E*(F+1)+F/4)) := by
  obtain ⟨T,hT,hφT,hTV,C,hC,hbound⟩ := hs.locally_uniform_squared_gap_offsets φ hφV
  refine ⟨T ∩ D.domain,hT.inter D.isOpen_domain,⟨hφT,hφD⟩,fun _ h => ⟨h.2,hTV h.1⟩,C,hC,?_⟩
  intro ψ hψ n
  obtain ⟨α,hαn,hfactor,hαnorm⟩ := hbound ψ hψ.1 n
  exact ⟨α,hαn,hαnorm,fun k hkn E F hE hS hR =>
    D.offDiagonal_squaredOffset_bound ψ hψ.2 n k hkn (α k) (hfactor k hkn) E F hE hS hR⟩

end SourceAbelianMomentErrorDomain
end NLS.ZakharovShabat
