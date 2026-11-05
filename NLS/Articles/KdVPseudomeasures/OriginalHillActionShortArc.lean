import NLS.Articles.KdVPseudomeasures.OriginalHillNativeTorusImage
import NLS.ComplexAnalysis.ShortArcRotation
import NLS.SequenceSpaces.FourierRealZeroReplacement
import NLS.FunctionalAnalysis.CompactInvariantCurveContinuity

/-! Actual indexed action flows match a coordinate by a short arc while
keeping their ENTIRE native output inside the prescribed target norm ball. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_originalHillNativeActionFlow (n : ℕ+) (p : HillRealMeanZeroSource) :
    Continuous (originalHillNativeActionFlow n p) :=
  (originalHillActionHamiltonianSystem n).continuous_globalCurve p

theorem hillRealSignedMap_actionFlow_apply (n : ℕ+) (p : HillRealMeanZeroSource) (t : ℝ) (k : ℤ) :
    (hillRealSignedMap (originalHillNativeActionFlow n p t)).val.val.val k=
      exp (hillActionRotationRate n k*t)*(hillRealSignedMap p).val.val.val k := by
  rw [hillRealSignedMap_coordinate,originalHillNativeActionFlow_coordinate,hillRealSignedMap_coordinate]

/-- Every actual target torus point has the same positive coordinate radii. -/
theorem norm_actionTorus_positive (q : HillRealMeanZeroSource) (z : HillRealSignedTarget)
    (hz : z ∈ hillRealNativeActionTorus q) (n : ℕ+) :
    ‖(hillRealSignedMap q).val.val.val (n:ℤ)‖=‖z.val.val.val (n:ℤ)‖ := by
  have ha := hillRealSignedMap_mem_actionTorus_of_discriminant_eq q q rfl n
  have he := ha.trans (hz n).symm
  rw [(hillRealSignedMap q).property,z.property] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := congrArg Complex.re he
  simpa only [mul_conj,ofReal_re,normSq_eq_norm_sq] using h

/-- ONE actual short action arc matches the selected target coordinate and
stays no farther from the fixed base output than the full final target.
All unselected modes keep their prior values; no global inverse is used. -/
theorem exists_short_action_output_path (n : ℕ+) (p : HillRealMeanZeroSource)
    (a z : HillRealSignedTarget)
    (ha : (hillRealSignedMap p).val.val.val (n:ℤ)=a.val.val.val (n:ℤ))
    (hnorm : ‖a.val.val.val (n:ℤ)‖=‖z.val.val.val (n:ℤ)‖)
    (hdom : ∀ k : ℤ, ‖(hillRealSignedMap p).val.val.val k-a.val.val.val k‖ ≤
      ‖z.val.val.val k-a.val.val.val k‖) :
    ∃ θ : ℝ, |θ| ≤ Real.pi ∧
      (hillRealSignedMap (originalHillNativeActionFlow n p θ)).val.val.val (n:ℤ)=z.val.val.val (n:ℤ) ∧
      ∀ u ∈ Icc (0:ℝ) 1,
        ‖hillRealSignedMap (originalHillNativeActionFlow n p (u*θ))-a‖ ≤ ‖z-a‖ := by
  obtain ⟨θ,hθ,hend,hpath⟩ := NLS.ComplexAnalysis.exists_short_rotation_of_norm_eq
    (a.val.val.val (n:ℤ)) (z.val.val.val (n:ℤ)) hnorm
  have hpositive (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      ‖(hillRealSignedMap (originalHillNativeActionFlow n p (u*θ))).val.val.val (n:ℤ)-a.val.val.val (n:ℤ)‖ ≤
        ‖z.val.val.val (n:ℤ)-a.val.val.val (n:ℤ)‖ := by
    rw [hillRealSignedMap_actionFlow_apply,hillActionRotationRate,if_pos rfl,ha]
    exact hpath u hu
  refine ⟨θ,hθ,?_,?_⟩
  · rw [hillRealSignedMap_actionFlow_apply,hillActionRotationRate,if_pos rfl,ha]
    exact hend
  · intro u hu
    apply WeightedCoeff.fourierRealZero_norm_le_of_coordinates
    intro k
    change ‖(hillRealSignedMap (originalHillNativeActionFlow n p (u*θ))).val.val.val k-a.val.val.val k‖ ≤
      ‖z.val.val.val k-a.val.val.val k‖
    by_cases hkp : k=(n:ℤ)
    · subst k
      exact hpositive u hu
    · by_cases hkn : k= -(n:ℤ)
      · subst k
        rw [(hillRealSignedMap (originalHillNativeActionFlow n p (u*θ))).property,a.property,z.property,
          ← map_sub,← map_sub,Complex.norm_conj,Complex.norm_conj]
        exact hpositive u hu
      · rw [hillRealSignedMap_actionFlow_apply,hillActionRotationRate,if_neg hkp,if_neg hkn,
          zero_mul,exp_zero,one_mul]
        exact hdom k

end NLS.Articles.KdVPseudomeasures
