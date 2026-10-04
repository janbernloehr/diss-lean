import NLS.SequenceSpaces.TailSumCoordinates
import NLS.SequenceSpaces.QuadraticActionsExponent
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Analytic sections of the remaining head actions

In tail-sum coordinates only finitely many pairs still need squaring.
At a base point with no zero retained pair, solve for a nonzero member of
each pair using a normalized analytic square root. The infinite tail is
handled linearly, so zero tail actions require no root choices.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- Convert the retained head pairs and tail sums into quadratic actions. -/
def headActions (S : Finset ℤ) (w : TailSumSpace q S) : Coeff q :=
  (1/2 : ℂ) • (w.2-truncate S w.2 + headInsertionCLM S (fun k => w.1 k^2+w.2 k.val^2))

@[simp] theorem headActions_apply (S : Finset ℤ) (w : TailSumSpace q S) (k : ℤ) :
    headActions S w k = if h : k ∈ S then (w.1 ⟨k,h⟩^2+w.2 k^2)/2 else w.2 k/2 := by
  change (1/2 : ℂ) * (w.2 k-truncate S w.2 k+
    headInsertionCLM S (fun j => w.1 j^2+w.2 j.val^2) k) = _
  by_cases hk : k ∈ S <;> simp [hk,div_eq_mul_inv,mul_comm]

theorem analyticOnNhd_headActions (S : Finset ℤ) :
    AnalyticOnNhd ℂ (headActions (q := q) S) univ := by
  intro w _
  have hh : AnalyticAt ℂ (fun v : TailSumSpace q S => fun k : S => v.1 k^2+v.2 k.val^2) w := by
    apply analyticAt_pi_iff.mpr
    intro k
    have hx : AnalyticAt ℂ (fun v : TailSumSpace q S => v.1 k) w :=
      ((ContinuousLinearMap.proj k : (S → ℂ) →L[ℂ] ℂ).analyticAt w.1).comp analyticAt_fst
    have hy : AnalyticAt ℂ (fun v : TailSumSpace q S => v.2 k.val) w :=
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val).analyticAt w.2).comp analyticAt_snd
    exact (hx.pow 2).add (hy.pow 2)
  exact (analyticAt_snd.sub (((truncateCLM S).analyticAt _).comp analyticAt_snd) |>.add
    (((headInsertionCLM (q := q) S).analyticAt _).comp hh)).const_smul (c := (1/2 : ℂ))

/-- Solve for the first coordinate when it is nonzero, and otherwise
for the second coordinate. The other coordinate remains fixed. -/
def headActionRoot (S : Finset ℤ) (a : TailSumSpace q S) (k : S) (b : Coeff q) : ℂ :=
  if a.1 k ≠ 0 then
    ComplexAnalysis.prescribedSquareRoot (fun b : Coeff q => 2*b k.val-a.2 k.val^2) (a.1 k) b
  else
    ComplexAnalysis.prescribedSquareRoot (fun b : Coeff q => 2*b k.val-a.1 k^2) (a.2 k.val) b

/-- A global section formula; analyticity is asserted on a neighborhood
of the base action. All infinitely many tail coordinates are linear. -/
def headActionSection (S : Finset ℤ) (a : TailSumSpace q S) (b : Coeff q) : TailSumSpace q S :=
  (fun k => if a.1 k ≠ 0 then headActionRoot S a k b else a.1 k,
    (2 : ℂ) • (b-truncate S b) + headInsertionCLM S
      (fun k => if a.1 k ≠ 0 then a.2 k.val else headActionRoot S a k b))

@[simp] theorem headActionSection_snd (S : Finset ℤ) (a : TailSumSpace q S) (b : Coeff q) (k : ℤ) :
    (headActionSection S a b).2 k =
      if h : k ∈ S then (if a.1 ⟨k,h⟩ ≠ 0 then a.2 k else headActionRoot S a ⟨k,h⟩ b) else 2*b k := by
  change 2*(b k-truncate S b k)+headInsertionCLM S
    (fun j => if a.1 j ≠ 0 then a.2 j.val else headActionRoot S a j b) k = _
  by_cases hk : k ∈ S <;> simp [hk]

/-- Each retained pair must have a nonzero member; no tail restriction. -/
def HeadNonzero (S : Finset ℤ) (a : TailSumSpace q S) : Prop :=
  ∀ k : S, a.1 k ≠ 0 ∨ a.2 k.val ≠ 0

omit [Fact (1 ≤ q)] in
theorem headActionRoot_sq (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a)
    (k : S) (b : Coeff q) :
    headActionRoot S a k b ^ 2 = if a.1 k ≠ 0 then 2*b k.val-a.2 k.val^2 else 2*b k.val-a.1 k^2 := by
  classical
  by_cases hx : a.1 k ≠ 0
  · simp only [headActionRoot,if_pos hx]
    exact ComplexAnalysis.prescribedSquareRoot_sq _ _ hx b
  · simp only [headActionRoot,if_neg hx]
    exact ComplexAnalysis.prescribedSquareRoot_sq _ _ ((ha k).resolve_left hx) b

theorem headActionRoot_base (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a) (k : S) :
    headActionRoot S a k (headActions S a) = if a.1 k ≠ 0 then a.1 k else a.2 k.val := by
  classical
  have hbase : headActions S a k.val = (a.1 k^2+a.2 k.val^2)/2 := by simp [k.property]
  by_cases hx : a.1 k ≠ 0
  · simp only [headActionRoot,if_pos hx]
    apply ComplexAnalysis.prescribedSquareRoot_base _ _ hx
    rw [hbase]
    ring
  · simp only [headActionRoot,if_neg hx]
    apply ComplexAnalysis.prescribedSquareRoot_base _ _ ((ha k).resolve_left hx)
    rw [hbase]
    ring

@[simp] theorem headActionSection_base (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a) :
    headActionSection S a (headActions S a) = a := by
  classical
  apply Prod.ext
  · funext k
    change (if a.1 k ≠ 0 then headActionRoot S a k (headActions S a) else a.1 k) = a.1 k
    rw [headActionRoot_base S a ha k]
    split_ifs <;> rfl
  · ext k
    rw [headActionSection_snd]
    by_cases hk : k ∈ S
    · rw [dif_pos hk,headActionRoot_base S a ha]
      by_cases hx : a.1 ⟨k,hk⟩ ≠ 0 <;> simp only [if_pos hx,if_neg hx]
    · simp only [dif_neg hk,headActions_apply]
      ring

@[simp] theorem headActions_section (S : Finset ℤ) (a : TailSumSpace q S) (ha : HeadNonzero S a) (b : Coeff q) :
    headActions S (headActionSection S a b) = b := by
  classical
  ext k
  rw [headActions_apply,headActionSection_snd]
  by_cases hk : k ∈ S
  · simp only [dif_pos hk]
    change ((if a.1 ⟨k,hk⟩ ≠ 0 then headActionRoot S a ⟨k,hk⟩ b else a.1 ⟨k,hk⟩)^2+
      (if a.1 ⟨k,hk⟩ ≠ 0 then a.2 k else headActionRoot S a ⟨k,hk⟩ b)^2)/2 = b k
    by_cases hx : a.1 ⟨k,hk⟩ ≠ 0
    · simp only [if_pos hx,headActionRoot_sq S a ha]
      ring
    · simp only [if_neg hx,headActionRoot_sq S a ha]
      ring
  · simp [hk]

/-- The normalized root is analytic at the base action even when the
chosen coordinate lies on the principal square-root branch cut. -/
theorem analyticAt_headActionRoot (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (k : S) :
    AnalyticAt ℂ (headActionRoot S a k) (headActions S a) := by
  classical
  have hrad (c : ℂ) : AnalyticOnNhd ℂ (fun b : Coeff q => 2*b k.val-c^2) univ := by
    intro b _
    exact (analyticAt_const.mul ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val).analyticAt b)).sub analyticAt_const
  have hbase : headActions S a k.val = (a.1 k^2+a.2 k.val^2)/2 := by simp [k.property]
  by_cases hx : a.1 k ≠ 0
  · unfold headActionRoot
    simp only [if_pos hx]
    apply ComplexAnalysis.analyticOnNhd_prescribedSquareRoot _ _ (hrad (a.2 k.val))
    apply ComplexAnalysis.mem_prescribedSquareRootDomain _ _ hx
    rw [hbase]
    ring
  · unfold headActionRoot
    simp only [if_neg hx]
    apply ComplexAnalysis.analyticOnNhd_prescribedSquareRoot _ _ (hrad (a.1 k))
    apply ComplexAnalysis.mem_prescribedSquareRootDomain _ _ ((ha k).resolve_left hx)
    rw [hbase]
    ring

/-- Only a finite collection of root germs is used, so the section is
analytic in the full sequence norm at the base action. -/
theorem analyticAt_headActionSection (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) : AnalyticAt ℂ (headActionSection S a) (headActions S a) := by
  classical
  have hx : AnalyticAt ℂ (fun b : Coeff q => fun k : S =>
      if a.1 k ≠ 0 then headActionRoot S a k b else a.1 k) (headActions S a) := by
    apply AnalyticAt.pi
    intro k
    by_cases hk : a.1 k ≠ 0
    · simpa only [if_pos hk] using analyticAt_headActionRoot S a ha k
    · simpa only [if_neg hk] using (analyticAt_const : AnalyticAt ℂ (fun _ : Coeff q => a.1 k) (headActions S a))
  have hy : AnalyticAt ℂ (fun b : Coeff q => fun k : S =>
      if a.1 k ≠ 0 then a.2 k.val else headActionRoot S a k b) (headActions S a) := by
    apply AnalyticAt.pi
    intro k
    by_cases hk : a.1 k ≠ 0
    · simpa only [if_pos hk] using (analyticAt_const : AnalyticAt ℂ (fun _ : Coeff q => a.2 k.val) (headActions S a))
    · simpa only [if_neg hk] using analyticAt_headActionRoot S a ha k
  exact hx.prod (((analyticAt_id.sub ((truncateCLM (p := q) S).analyticAt _)).const_smul (c := (2 : ℂ))).add
    (((headInsertionCLM (q := q) S).analyticAt _).comp hy))

/-- Restrict the analytic section to any prescribed open neighborhood of
the base point. The neighborhood is independent of any frequency target. -/
theorem exists_headActionSection_neighborhood (S : Finset ℤ) (a : TailSumSpace q S)
    (ha : HeadNonzero S a) (U : Set (TailSumSpace q S)) (hU : IsOpen U) (haU : a ∈ U) :
    ∃ T : Set (Coeff q), IsOpen T ∧ headActions S a ∈ T ∧
      AnalyticOnNhd ℂ (headActionSection S a) T ∧ MapsTo (headActionSection S a) T U := by
  have hs := analyticAt_headActionSection S a ha
  have he : ∀ᶠ b in 𝓝 (headActions S a), headActionSection S a b ∈ U :=
    hs.continuousAt.preimage_mem_nhds (by simpa only [headActionSection_base S a ha] using hU.mem_nhds haU)
  obtain ⟨T,hTsub,hT,hbase⟩ := _root_.mem_nhds_iff.mp (hs.eventually_analyticAt.and he)
  exact ⟨T,hT,hbase,fun b hb => (hTsub hb).1,fun b hb => (hTsub hb).2⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderTriple p q]

/-- The action map in the reduced coordinates is exactly the original
quadratic action map, with its factor one half. -/
theorem headActions_tailSum_mixedSquare (S : Finset ℤ) (z : Coeff p × Coeff p) :
    headActions S (tailSumCLM S (pairMixedSquare (q := q) S z)) = quadraticActionsExponent z := by
  ext k
  rw [headActions_apply,quadraticActionsExponent_apply]
  by_cases hk : k ∈ S
  · simp only [dif_pos hk,tailSum_pairMixedSquare_fst,tailSum_pairMixedSquare_snd,if_pos hk]
  · simp only [dif_neg hk,tailSum_pairMixedSquare_snd,if_neg hk]

/-- Nonzero retained original pairs give exactly the hypothesis needed
for the analytic head-action section. -/
theorem headNonzero_tailSum_mixedSquare (S : Finset ℤ) (z : Coeff p × Coeff p)
    (hz : ∀ k ∈ S, z.1 k ≠ 0 ∨ z.2 k ≠ 0) :
    HeadNonzero S (tailSumCLM S (pairMixedSquare (q := q) S z)) := by
  intro k
  simpa only [tailSum_pairMixedSquare_fst,tailSum_pairMixedSquare_snd,if_pos k.property] using hz k.val k.property

end NLS.Coeff
