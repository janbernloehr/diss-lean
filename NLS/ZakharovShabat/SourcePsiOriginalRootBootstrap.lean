import NLS.ZakharovShabat.SourcePsiOriginalRootOffset
import NLS.SequenceSpaces.WeightQuotient

/-!
# The two substitutions concluding Lemma 12.12

Common analytic branch bounds first give O(1) offsets. The original
inequalities (2.34) then give a gap times an lp sequence; reinserting
that estimate gives a squared gap times an lp sequence. Both bounds
are uniform in the omitted index, locally at every complex source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Common local branch norms give the O(1) offset bound used before the two substitutions. -/
theorem SourceLemma12_11Data.original_root_offset_uniform_bound
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ χ ∈ U, ∀ n m : ℤ,
        ‖displacedRoots (s n χ:Coeff p) m-sourceStandardRootMidpoint hp hp1 χ m‖ ≤ A := by
  obtain ⟨A,hdom,hbranch⟩ := H.previous.atlas
  let B := A.toSourcePsiComplexRootAtlas
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hdom.symm ▸ hψ)
  obtain ⟨_,_,Vm,hVm,hψm,R,hR,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 ψ (by norm_num : (0:ℝ)<1)
  let T := (B.localBranch φ).rootRadius+
    ‖canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val)‖+
    ‖sourcePeriodicGapDisplacement hp hp1 φ.val‖
  have hT : 0 ≤ T := by
    have hh := (B.localBranch φ).rootRadius_pos
    dsimp only [T]; positivity
  refine ⟨B.sourceBall φ ∩ Vm,isOpen_ball.inter hVm,⟨hφ,hψm⟩,
    (fun χ hχ => hdom ▸ (subset_iUnion B.sourceBall φ hχ.1)),T+R,add_nonneg hT hR,?_⟩
  intro χ hχ n m
  have hb : ‖s n χ‖ ≤ T := by
    rw [← hbranch,B.eq_local n φ hχ.1]
    exact (B.localBranch φ).norm_branch_le n χ hχ.1
  have he : displacedRoots (s n χ:Coeff p) m-sourceStandardRootMidpoint hp hp1 χ m =
      (s n χ:Coeff p) m-sourcePeriodicMidpointDisplacement hp hp1 χ m := by
    simp only [displacedRoots,sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add
    ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (s n χ:Coeff p) m).trans hb)
    ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ m).trans (hmid χ hχ.2).1))

/-- Literal first-gap and squared-gap factorizations follow from the two source substitutions. -/
theorem SourceLemma12_11Data.original_two_stage_offsets
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ β α : Coeff p, β n = 0 ∧ α n = 0 ∧
        (∀ m, displacedRoots (sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n)) m =
          sourceStandardRootMidpoint hp hp1 χ m+sourcePeriodicGapDisplacement hp hp1 χ m*β m) ∧
        (∀ m, displacedRoots (sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n)) m =
          sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
        ‖β‖ ≤ C ∧ ‖α‖ ≤ C := by
  obtain ⟨V,hV,_,hψV,hVW,D,c,hD⟩ := H.previous.psi.previous.quotients.neighborhoods ψ (H.previous.subset hψ)
  obtain ⟨Ue,hUe,hψe,heW,L,hL,hineq⟩ :=
    H.original_root_offset_inequalities hW₀ hD.toSourceIsolatingNeighborhoods hV hVW ψ hψ hψV
  obtain ⟨Ua,hUa,hψa,_,A,hA,hoff⟩ := H.original_root_offset_uniform_bound ψ hψ
  obtain ⟨_,_,Ug,hUg,hψg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 ψ (by norm_num : (0:ℝ)<1)
  let T := A+G/2
  let K := T*L+1/2
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := max (T*L) (K*L)+1
  have hC : 0 < C := by
    have hh : 0 ≤ max (T*L) (K*L) := (mul_nonneg hT hL).trans (le_max_left _ _)
    dsimp only [C]; linarith
  refine ⟨(Ue ∩ Ua) ∩ Ug,(hUe.inter hUa).inter hUg,⟨⟨hψe,hψa⟩,hψg⟩,
    (fun χ hχ => (heW hχ.1.1).1),C,hC,?_⟩
  intro χ hχ n
  obtain ⟨B,hB,hb⟩ := hineq χ hχ.1.1 n
  let γ := sourcePeriodicGapDisplacement hp hp1 χ
  let d : ℤ → ℂ := fun m => if m = n then 0 else
    displacedRoots (s n χ:Coeff p) m-sourceStandardRootMidpoint hp hp1 χ m
  have hlinear (m : ℤ) : ‖d m‖ ≤ T*‖γ m‖*‖B m‖ := by
    by_cases hm : m = n
    · simp only [d,if_pos hm,norm_zero]; positivity
    · obtain ⟨ξ,_,_,hfirst,hsecond⟩ := hb m hm
      have hd := hfirst.trans hsecond
      have ha := hoff χ hχ.1.2 n m
      have hg : ‖γ m‖ ≤ G :=
        (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' γ m).trans (hgap χ hχ.2).1
      simp only [d,if_neg hm]
      exact hd.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add ha (div_le_div_of_nonneg_right hg (by norm_num)))
          (norm_nonneg _)) (norm_nonneg _))
  have hquad (m : ℤ) : ‖d m‖ ≤ K*‖γ m‖^2*‖B m‖ := by
    by_cases hm : m = n
    · simp only [d,if_pos hm,norm_zero]; positivity
    · obtain ⟨ξ,_,_,hfirst,hsecond⟩ := hb m hm
      have hd := hfirst.trans hsecond
      have hl := hlinear m
      simp only [d,if_neg hm] at hl ⊢
      have hBm : ‖B m‖ ≤ L := (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' B m).trans hB
      calc
        _ ≤ (T*‖γ m‖*‖B m‖+‖γ m‖/2)*‖γ m‖*‖B m‖ :=
          hd.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (add_le_add hl le_rfl) (norm_nonneg _)) (norm_nonneg _))
        _ = (T*‖B m‖+1/2)*‖γ m‖^2*‖B m‖ := by ring
        _ ≤ K*‖γ m‖^2*‖B m‖ := by
          dsimp only [K]
          gcongr
  obtain ⟨β,hβq,hβf,hβ⟩ := exists_coeff_weight_quotient γ d B T hT hlinear
  obtain ⟨α,hαq,hαf,hα⟩ := exists_coeff_squared_weight_quotient γ d B K hK hquad
  refine ⟨β,α,by rw [hβq n]; simp [d],by rw [hαq n]; simp [d],?_,?_,?_,?_⟩
  · intro m
    by_cases hm : m = n
    · subst m
      rw [displacedRoots_sourcePsiFillDeletedRoot_same,hβq n]
      simp [d]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hm]
      have hh := hβf m
      simp only [d,if_neg hm] at hh
      linear_combination hh
  · intro m
    by_cases hm : m = n
    · subst m
      rw [displacedRoots_sourcePsiFillDeletedRoot_same,hαq n]
      simp [d]
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n m hm]
      have hh := hαf m
      simp only [d,if_neg hm] at hh
      linear_combination hh
  · exact (hβ.trans (mul_le_mul_of_nonneg_left hB hT)).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right (by norm_num)))
  · exact (hα.trans (mul_le_mul_of_nonneg_left hB hK)).trans
      ((le_max_right _ _).trans (le_add_of_nonneg_right (by norm_num)))

end NLS.ZakharovShabat
