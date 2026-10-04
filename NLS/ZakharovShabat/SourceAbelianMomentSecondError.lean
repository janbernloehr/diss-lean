import NLS.ZakharovShabat.SourceAbelianMomentErrorDomain
import NLS.ZakharovShabat.SourceMomentRegularFactorization

/-! # Explicit second-moment errors for Lemma 20.3

The diagonal model is pi times the squared gap divided by four. Off the
diagonal, cancellation leaves the squared gap times the psi-root offset.
The remaining error retains respectively two and three gap factors.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceAngularSelectedPolynomial_eq_midpoint_halfGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ) (z : ℂ) :
    sourceAngularSelectedPolynomial hp hp1 ψ k z =
      (z-sourceStandardRootMidpoint hp hp1 ψ k)^2-(sourceStandardRootHalfGap hp hp1 ψ k)^2 := by
  unfold sourceAngularSelectedPolynomial quadraticRootPolynomial sourceStandardRootHalfGap
  ring

namespace SourceAbelianMomentErrorDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- The diagonal error retains the full squared gap, also at collapse.
The actual regular numerator, rather than an auxiliary model branch,
appears in the input error estimate. -/
theorem diagonal_error_bound
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (k : ℤ) (E F : ℝ) (hE : 0 ≤ E)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*E)
    (hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceMomentRegularNumerator hp hp1 k k (s k ψ : Coeff p) ψ z-Complex.I‖ ≤ F) :
    ‖(2*Real.pi:ℂ)⁻¹ * (A.moment k k 2 ψ -
      (Real.pi:ℂ)*(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2/4)‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*(E*(F+1)+F/4) := by
  let g : ℂ × CoeffPair p → ℂ := fun t => -Complex.I *
    ((t.1-sourceStandardRootMidpoint hp hp1 t.2 k)^2-(sourceStandardRootHalfGap hp hp1 t.2 k)^2)
  have hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k) := by
    dsimp only [g]
    fun_prop
  have hb := D.norm_model_error_le ψ hψ k k 1 g hg
    (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*(E*(F+1)+F/4)) (by
      intro z hz
      have hb := norm_square_regular_product_error_le
        (sourceFullAbelianSquare hp hp1 W k (z,ψ)) (sourceAngularSelectedPolynomial hp hp1 ψ k z)
        (sourceMomentRegularNumerator hp hp1 k k (s k ψ : Coeff p) ψ z)
        (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2) E F (sq_nonneg _) hE
        (hS z hz) (norm_sourceAngularSelectedPolynomial_le_gap_sq hp hp1 ψ k z hz) (hR z hz)
      dsimp only [g,sourceAbelianMomentEvenNumerator]
      rw [pow_one,one_mul,← sourceAngularSelectedPolynomial_eq_midpoint_halfGap]
      simpa only [neg_mul,sub_neg_eq_add] using hb)
  rw [one_mul,sourceGapCosineMean_diagonal_model] at hb
  exact hb

/-- The off-diagonal error retains three powers of the gap. The exact
leading term is quadratic in the gap and linear in the root offset. -/
theorem offDiagonal_error_bound
    (D : SourceAbelianMomentErrorDomain A) (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (n k : ℤ) (hkn : k ≠ n) (E F L : ℝ) (hE : 0 ≤ E) (hL : 0 ≤ L)
    (hS : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)+sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*E)
    (hR : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ F)
    (hLbound : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖displacedRoots (s n ψ : Coeff p) k-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*L) :
    ‖((n-k:ℤ):ℂ)*A.moment n k 2 ψ -
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2 *
        (displacedRoots (s n ψ : Coeff p) k-sourceStandardRootMidpoint hp hp1 ψ k)/4‖ ≤
      2*‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*L*(E*(F+1)+F/4) := by
  let sigma := displacedRoots (s n ψ : Coeff p) k
  let g : ℂ × CoeffPair p → ℂ := fun t => -Complex.I * ((sigma-t.1)*
    ((t.1-sourceStandardRootMidpoint hp hp1 t.2 k)^2-(sourceStandardRootHalfGap hp hp1 t.2 k)^2))
  have hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k) := by
    dsimp only [g]
    fun_prop
  have hb := D.norm_model_error_le ψ hψ n k ((Real.pi:ℂ)*((n-k:ℤ):ℂ)) g hg
    (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^3*L*(E*(F+1)+F/4)) (by
      intro z hz
      let S := sourceFullAbelianSquare hp hp1 W k (z,ψ)
      let P := sourceAngularSelectedPolynomial hp hp1 ψ k z
      let R := sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z
      have hprod := norm_square_regular_product_error_le S P R
        (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2) E F (sq_nonneg _) hE
        (hS z hz) (norm_sourceAngularSelectedPolynomial_le_gap_sq hp hp1 ψ k z hz) (hR z hz)
      have he : (Real.pi:ℂ)*((n-k:ℤ):ℂ)*
          sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (s n ψ : Coeff p) ψ z-g (z,ψ) =
            (sigma-z)*(S*R+Complex.I*P) := by
        have hf := sourceMomentRegularNumerator_eq_midpointFilledFactor hp hp1 n k hkn (s n ψ) ψ z
          (D.midpoint_sub_ne_zero ψ hψ n k hkn z hz)
        dsimp only [g,sourceAbelianMomentEvenNumerator]
        rw [pow_one,← sourceAngularSelectedPolynomial_eq_midpoint_halfGap]
        dsimp only [sigma,S,P,R] at *
        linear_combination (sourceFullAbelianSquare hp hp1 W k (z,ψ))*hf
      rw [he,norm_mul]
      calc
        _ ≤ (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖*L)*
            (‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2*(E*(F+1)+F/4)) :=
          mul_le_mul (hLbound z hz) hprod (norm_nonneg _) (mul_nonneg (norm_nonneg _) hL)
        _ = _ := by ring)
  rw [sourceGapCosineMean_shifted_model] at hb
  have he : (2*Real.pi:ℂ)⁻¹ * ((Real.pi:ℂ)*((n-k:ℤ):ℂ)*A.moment n k 2 ψ -
      (Real.pi:ℂ)*(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2*
        (sigma-sourceStandardRootMidpoint hp hp1 ψ k)/4) =
      (2:ℂ)⁻¹ * (((n-k:ℤ):ℂ)*A.moment n k 2 ψ -
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2*
          (sigma-sourceStandardRootMidpoint hp hp1 ψ k)/4) := by
    have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  rw [he,norm_mul,norm_inv,norm_ofNat] at hb
  dsimp only [sigma] at hb
  linarith

end SourceAbelianMomentErrorDomain
end NLS.ZakharovShabat
