import NLS.ZakharovShabat.DisplacedProductOrders
import NLS.SequenceSpaces.CoefficientDecay

/-! # Uniform separation of simple displaced-root sequences

Properness separates each fixed root from all the others. Outside a finite
head, vanishing displacements give the uniform half-pi lattice bound.
Taking a positive minimum over the remaining head finishes the source's
separation assertion preceding D.4.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed root of an injective displaced sequence is uniformly separated from every other root. -/
theorem exists_displacedRoot_separation (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) (n : ℤ) :
    ∃ r : ℝ, 0 < r ∧ ∀ k : ℤ, k ≠ n → r ≤ dist (displacedRoots a n) (displacedRoots a k) := by
  obtain ⟨r,hr,hiso⟩ := exists_displacedRoots_isolating_closedBall a (displacedRoots a n)
  refine ⟨r,hr,fun k hkn => ?_⟩
  by_contra hlt
  have hk : displacedRoots a k ∈ closedBall (displacedRoots a n) r := by
    rw [mem_closedBall, dist_comm]
    exact (lt_of_not_ge hlt).le
  exact hkn (ha (hiso k hk))

/-- The positive pairwise separation printed before Lemma D.4, without localization assumptions. -/
theorem exists_uniform_displacedRoots_separation (hp : p ≠ ⊤) (a : Coeff p)
    (ha : Function.Injective (displacedRoots a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j k : ℤ, j ≠ k → δ ≤ dist (displacedRoots a j) (displacedRoots a k) := by
  classical
  obtain ⟨N,hN⟩ := Coeff.exists_cutoff_norm_apply_lt hp a (by positivity : 0 < Real.pi/4)
  let S : Finset ℤ := Finset.Icc (-(N:ℤ)) N
  choose r hr hsep using exists_displacedRoot_separation a ha
  obtain ⟨δ,hδ,hbound⟩ := S.finite_toSet.isCompact.exists_forall_le'
    (continuous_of_discreteTopology.continuousOn : ContinuousOn r (S : Set ℤ))
    (fun n _ => hr n)
  refine ⟨min δ (Real.pi/2), lt_min hδ (by positivity), fun j k hjk => ?_⟩
  by_cases hj : j ∈ S
  · exact (min_le_left _ _).trans ((hbound j hj).trans (hsep j k hjk.symm))
  by_cases hk : k ∈ S
  · rw [dist_comm]
    exact (min_le_left _ _).trans ((hbound k hk).trans (hsep k j hjk))
  have hjN : N ≤ j.natAbs := by
    simp only [S, Finset.mem_Icc] at hj
    omega
  have hkN : N ≤ k.natAbs := by
    simp only [S, Finset.mem_Icc] at hk
    omega
  have hfree : Real.pi ≤ ‖(Real.pi:ℂ)*j-(Real.pi:ℂ)*k‖ := by
    rw [norm_free_center_sub]
    have hidx : (1:ℝ) ≤ |((j-k:ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjk)
    nlinarith [Real.pi_pos]
  have heq : (Real.pi:ℂ)*j-(Real.pi:ℂ)*k =
      (displacedRoots a j-displacedRoots a k)-a j+a k := by
    simp only [displacedRoots]
    ring
  have htri : ‖(Real.pi:ℂ)*j-(Real.pi:ℂ)*k‖ ≤
      ‖displacedRoots a j-displacedRoots a k‖+‖a j‖+‖a k‖ := by
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  apply (min_le_right _ _).trans
  rw [dist_eq_norm]
  nlinarith [hN j hjN, hN k hkN]

end NLS.ZakharovShabat
