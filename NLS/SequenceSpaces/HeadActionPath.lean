import NLS.SequenceSpaces.HeadActionSection

/-! # Explicit paths to the head-action section

The free member of each retained pair moves linearly to its base value.
A normalized square root supplies the other member, keeping the quadratic
action fixed. The infinite tail is unchanged throughout the path.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The coordinate held fixed by the action section. -/
def headActionFree (S : Finset ℤ) (a w : TailSumSpace q S) (k : S) : ℂ :=
  if a.1 k ≠ 0 then w.2 k.val else w.1 k

/-- The complementary coordinate, which is nonzero at the base. -/
def headActionSolved (S : Finset ℤ) (a w : TailSumSpace q S) (k : S) : ℂ :=
  if a.1 k ≠ 0 then w.1 k else w.2 k.val

omit [Fact (1 ≤ q)] in
theorem headActionSolved_ne_zero (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (k : S) : headActionSolved S a a k ≠ 0 := by
  by_cases hx : a.1 k ≠ 0
  · simp [headActionSolved,hx]
  · simpa [headActionSolved,hx] using (ha k).resolve_left hx

/-- Interpolate the free coordinate, allowing a complex path parameter. -/
def headActionFreeLine (S : Finset ℤ) (a : TailSumSpace q S) (k : S)
    (u : TailSumSpace q S × ℂ) : ℂ :=
  headActionFree S a u.1 k+u.2*(headActionFree S a a k-headActionFree S a u.1 k)

/-- Radicand that preserves the original head action along the path. -/
def headActionPathRadicand (S : Finset ℤ) (a : TailSumSpace q S) (k : S)
    (u : TailSumSpace q S × ℂ) : ℂ :=
  u.1.1 k^2+u.1.2 k.val^2-headActionFreeLine S a k u^2

/-- The root is normalized by the chosen nonzero base coordinate. -/
def headActionPathRoot (S : Finset ℤ) (a : TailSumSpace q S) (k : S) :
    (TailSumSpace q S × ℂ) → ℂ :=
  ComplexAnalysis.prescribedSquareRoot (headActionPathRadicand S a k) (headActionSolved S a a k)

/-- The explicit action-preserving path, jointly parametrized by its
initial point and a complex time. -/
def headActionPath (S : Finset ℤ) (a : TailSumSpace q S)
    (u : TailSumSpace q S × ℂ) : TailSumSpace q S :=
  (fun k => if a.1 k ≠ 0 then headActionPathRoot S a k u else headActionFreeLine S a k u,
    u.1.2-truncate S u.1.2+headInsertionCLM S
      (fun k => if a.1 k ≠ 0 then headActionFreeLine S a k u else headActionPathRoot S a k u))

@[simp] theorem headActionPath_snd (S : Finset ℤ) (a : TailSumSpace q S)
    (u : TailSumSpace q S × ℂ) (n : ℤ) :
    (headActionPath S a u).2 n = if h : n ∈ S then
      (if a.1 ⟨n,h⟩ ≠ 0 then headActionFreeLine S a ⟨n,h⟩ u else headActionPathRoot S a ⟨n,h⟩ u)
      else u.1.2 n := by
  change u.1.2 n-truncate S u.1.2 n+headInsertionCLM S _ n = _
  by_cases hn : n ∈ S <;> simp [hn]

omit [Fact (1 ≤ q)] in
theorem headActionPathRadicand_base (S : Finset ℤ) (a : TailSumSpace q S) (k : S) (t : ℂ) :
    headActionPathRadicand S a k (a,t) = headActionSolved S a a k ^ 2 := by
  by_cases hx : a.1 k ≠ 0 <;>
    simp [headActionPathRadicand,headActionFreeLine,headActionFree,headActionSolved,hx]

omit [Fact (1 ≤ q)] in
theorem headActionPathRoot_base (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (k : S) (t : ℂ) :
    headActionPathRoot S a k (a,t) = headActionSolved S a a k :=
  ComplexAnalysis.prescribedSquareRoot_base _ _ (headActionSolved_ne_zero S a ha k) _
    (headActionPathRadicand_base S a k t)

@[simp] theorem headActionPath_base (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (t : ℂ) : headActionPath S a (a,t) = a := by
  apply Prod.ext
  · funext k
    change (if a.1 k ≠ 0 then headActionPathRoot S a k (a,t) else headActionFreeLine S a k (a,t)) = a.1 k
    rw [headActionPathRoot_base S a ha]
    by_cases hx : a.1 k ≠ 0 <;> simp [headActionFreeLine,headActionFree,headActionSolved,hx]
  · ext n
    rw [headActionPath_snd]
    by_cases hn : n ∈ S
    · rw [dif_pos hn,headActionPathRoot_base S a ha]
      by_cases hx : a.1 ⟨n,hn⟩ ≠ 0 <;> simp [headActionFreeLine,headActionFree,headActionSolved,hx]
    · simp [hn]

/-- All quadratic actions are preserved for every complex time. -/
theorem headActions_path (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a)
    (w : TailSumSpace q S) (t : ℂ) : headActions S (headActionPath S a (w,t)) = headActions S w := by
  ext n
  rw [headActions_apply,headActions_apply]
  by_cases hn : n ∈ S
  · simp only [dif_pos hn,headActionPath_snd]
    change ((if a.1 ⟨n,hn⟩ ≠ 0 then headActionPathRoot S a ⟨n,hn⟩ (w,t) else headActionFreeLine S a ⟨n,hn⟩ (w,t))^2+
      (if a.1 ⟨n,hn⟩ ≠ 0 then headActionFreeLine S a ⟨n,hn⟩ (w,t) else headActionPathRoot S a ⟨n,hn⟩ (w,t))^2)/2 = _
    have hs := ComplexAnalysis.prescribedSquareRoot_sq (headActionPathRadicand S a ⟨n,hn⟩)
      _ (headActionSolved_ne_zero S a ha ⟨n,hn⟩) (w,t)
    change headActionPathRoot S a ⟨n,hn⟩ (w,t)^2 = _ at hs
    by_cases hx : a.1 ⟨n,hn⟩ ≠ 0 <;>
      simp only [if_pos hx,if_neg hx,hs,headActionPathRadicand] <;> ring
  · simp [hn]

/-- At time one the path reaches the previously constructed action section. -/
theorem headActionPath_one (S : Finset ℤ) (a w : TailSumSpace q S) :
    headActionPath S a (w,1) = headActionSection S a (headActions S w) := by
  have hf (k : S) : headActionFreeLine S a k (w,1) = headActionFree S a a k := by
    simp [headActionFreeLine]
  have hr (k : S) : headActionPathRoot S a k (w,1) = headActionRoot S a k (headActions S w) := by
    have hsum : 2*headActions S w k.val = w.1 k^2+w.2 k.val^2 := by
      rw [headActions_apply,dif_pos k.property]
      ring
    by_cases hx : a.1 k ≠ 0 <;>
      simp only [headActionPathRoot,ComplexAnalysis.prescribedSquareRoot,headActionPathRadicand,
        hf,headActionSolved,headActionFree,headActionRoot,if_pos hx,if_neg hx,hsum]
  apply Prod.ext
  · funext k
    change (if a.1 k ≠ 0 then headActionPathRoot S a k (w,1) else headActionFreeLine S a k (w,1)) = _
    rw [hr,hf]
    by_cases hx : a.1 k ≠ 0 <;> simp [headActionSection,headActionFree,hx]
  · ext n
    rw [headActionPath_snd,headActionSection_snd]
    by_cases hn : n ∈ S
    · rw [dif_pos hn,dif_pos hn,hr,hf]
      by_cases hx : a.1 ⟨n,hn⟩ ≠ 0 <;> simp [headActionFree,hx]
    · simp only [dif_neg hn,headActions_apply]
      ring

end NLS.Coeff
