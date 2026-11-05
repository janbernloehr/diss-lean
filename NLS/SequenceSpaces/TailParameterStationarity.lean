import NLS.SequenceSpaces.TailActionStationarity

/-! # Tail splitting without a head rotation hypothesis

The finite head is a linear parameter. Rotation stationarity outside it
suffices to merge the two squared tail components, also at zero entries.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- An analytic mixed-coordinate descent is stationary in every tail
splitting direction whenever its lift is stationary under rotations. -/
theorem fderiv_actionSplit_eq_zero_of_tail_stationarity (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (G : (Coeff q × Coeff q) → F)
    (U : Set (Coeff p × Coeff p)) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hG : AnalyticOnNhd ℂ G (pairMixedSquare S '' U))
    (he : ∀ z ∈ U, G (pairMixedSquare S z) = f z)
    (hrot : ∀ z ∈ U, ∀ k ∉ S, fderiv ℂ f z (actionRotationVectorCLM p k z) = 0)
    (b : Coeff q × Coeff q) (hb : b ∈ pairMixedSquare S '' U) (k : ℤ) (hk : k ∉ S) :
    fderiv ℂ G b (actionSplitDirection q k) = 0 := by
  have hopen := isOpenMap_pairMixedSquare (q := q) hp S U hU
  have hc : ContinuousOn (fun b => fderiv ℂ G b (actionSplitDirection q k)) (pairMixedSquare S '' U) :=
    hG.fderiv.continuousOn.clm_apply continuousOn_const
  apply eq_const_of_pair_coordinate_ne _ _ hopen hc k (0 : F) _ b hb
  intro w hw h1 h2
  obtain ⟨z,hz,rfl⟩ := hw
  have hx : z.1 k ≠ 0 := by
    intro heq
    apply h1
    simp [pairMixedSquare,hk,heq]
  have hy : z.2 k ≠ 0 := by
    intro heq
    apply h2
    simp [pairMixedSquare,hk,heq]
  have hnonzero : (2 : ℂ)*z.1 k*z.2 k ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  have hs := smul_fderiv_actionSplit_eq_zero_of_recovery S f G U hU hf hG.differentiableOn hopen he
    z hz k hk (hrot z hz k hk)
  exact (smul_eq_zero.mp hs).resolve_left hnonzero

end NLS.Coeff
