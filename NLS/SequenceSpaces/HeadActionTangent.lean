import NLS.SequenceSpaces.HeadRotationStationarity

/-! # Tangent vectors to head-action fibers

At a head with no zero pair, every action-preserving tangent is a finite
linear combination of coordinate rotations. Thus a continuous linear map
annihilating those rotations annihilates the entire tangent space.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A tangent to a nonzero quadratic pair is a multiple of its rotation. -/
theorem exists_rotation_scalar (x y u v : ℂ) (hxy : x ≠ 0 ∨ y ≠ 0)
    (ht : x*u+y*v = 0) : ∃ c : ℂ, c*(-y) = u ∧ c*x = v := by
  by_cases hx : x ≠ 0
  · refine ⟨v/x,?_,by field_simp⟩
    field_simp
    linear_combination -ht
  · have hy := hxy.resolve_left hx
    have hx0 : x = 0 := not_ne_iff.mp hx
    have hv : v = 0 := by simpa [hx0,hy] using ht
    refine ⟨-u/y,by field_simp,?_⟩
    simp [hx0,hv]

/-- Every action-preserving tangent is a finite sum of head rotations. -/
theorem exists_headRotation_decomposition (S : Finset ℤ) (w v : TailSumSpace q S)
    (hw : HeadNonzero S w) (htail : ∀ n ∉ S, v.2 n = 0)
    (hhead : ∀ k : S, w.1 k*v.1 k+w.2 k.val*v.2 k.val = 0) :
    ∃ c : S → ℂ, v = ∑ k : S, c k • headRotationVector S k w := by
  classical
  choose c hc using fun k => exists_rotation_scalar (w.1 k) (w.2 k.val)
    (v.1 k) (v.2 k.val) (hw k) (hhead k)
  refine ⟨c,?_⟩
  have hsum : (∑ k : S, c k • headRotationVector S k w) =
      (v.1,headInsertionCLM S (fun k => v.2 k.val)) := by
    have he (k : S) : c k • headRotationVector S k w =
        (Pi.single k (v.1 k),lp.single (E := fun _ : ℤ => ℂ) q k.val (v.2 k.val)) := by
      apply Prod.ext
      · funext j
        change c k * ((Pi.single k (-w.2 k.val) : S → ℂ) j) = (Pi.single k (v.1 k) : S → ℂ) j
        by_cases hj : j = k
        · subst j
          simpa using (hc k).1
        · simp [hj]
      · change c k • lp.single (E := fun _ : ℤ => ℂ) q k.val (w.1 k) = lp.single (E := fun _ : ℤ => ℂ) q k.val (v.2 k.val)
        rw [← lp.single_smul]
        exact congrArg (lp.single (E := fun _ : ℤ => ℂ) q k.val) (hc k).2
    simp_rw [he]
    apply Prod.ext
    · change (ContinuousLinearMap.fst ℂ (S → ℂ) (Coeff q)) _ = v.1
      rw [map_sum]
      funext j
      change (∑ k : S, Pi.single k (v.1 k)) j = v.1 j
      simp [Finset.sum_apply,Pi.single_apply]
    · change (ContinuousLinearMap.snd ℂ (S → ℂ) (Coeff q)) _ = _
      rw [map_sum]
      change (∑ k : S, lp.single (E := fun _ : ℤ => ℂ) q k.val (v.2 k.val)) = headInsertionCLM S (fun k => v.2 k.val)
      simp [headInsertionCLM,lp.singleContinuousLinearMap_apply]
  rw [hsum]
  apply Prod.ext
  · rfl
  · ext n
    by_cases hn : n ∈ S
    · simp [hn]
    · simp [hn,htail n hn]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Vanishing on head rotations implies vanishing on every head-action tangent. -/
theorem clm_headActionTangent_eq_zero (S : Finset ℤ) (w v : TailSumSpace q S)
    (L : TailSumSpace q S →L[ℂ] F) (hw : HeadNonzero S w)
    (hL : ∀ k : S, L (headRotationVector S k w) = 0)
    (htail : ∀ n ∉ S, v.2 n = 0)
    (hhead : ∀ k : S, w.1 k*v.1 k+w.2 k.val*v.2 k.val = 0) : L v = 0 := by
  obtain ⟨c,he⟩ := exists_headRotation_decomposition S w v hw htail hhead
  rw [he,map_sum]
  apply Finset.sum_eq_zero
  intro k _
  simp [map_smul,hL k]

end NLS.Coeff
