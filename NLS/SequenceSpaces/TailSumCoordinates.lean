import NLS.SequenceSpaces.TailActionInvariance

/-! # Linear coordinates for the retained head and tail sums

The finite first head and the sequence consisting of the second head and
the tail sums form a complemented quotient of the mixed-coordinate space.
The affine section through any base point preserves the original head and
all pairwise sums. No nonvanishing assumption is needed.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A finite first head together with the second head and the tail sums. -/
abbrev TailSumSpace (q : ℝ≥0∞) (S : Finset ℤ) := (S → ℂ) × Coeff q

/-- Restriction to a finite head. -/
def headRestrictionCLM (S : Finset ℤ) : Coeff q →L[ℂ] (S → ℂ) :=
  ContinuousLinearMap.pi fun k => lp.evalCLM ℂ (fun _ : ℤ => ℂ) q k.val

/-- Insert a finite head, with zero tail. -/
def headInsertionCLM (S : Finset ℤ) : (S → ℂ) →L[ℂ] Coeff q :=
  ∑ k : S, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) q k.val).comp
    (ContinuousLinearMap.proj k)

@[simp] theorem headRestrictionCLM_apply (S : Finset ℤ) (a : Coeff q) (k : S) :
    headRestrictionCLM S a k = a k.val := rfl

@[simp] theorem headInsertionCLM_apply (S : Finset ℤ) (a : S → ℂ) (n : ℤ) :
    headInsertionCLM (q := q) S a n = if h : n ∈ S then a ⟨n,h⟩ else 0 := by
  classical
  have he : headInsertionCLM (q := q) S a = ∑ k : S, lp.single q k.val (a k) := by
    simp [headInsertionCLM,lp.singleContinuousLinearMap_apply]
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n) (headInsertionCLM S a) = _
  rw [he,map_sum]
  simp only [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  by_cases hn : n ∈ S
  · rw [dif_pos hn]
    rw [Finset.sum_eq_single (⟨n,hn⟩ : S)]
    · simp
    · intro b _ hb
      have hb' : n ≠ b.val := fun h => hb (Subtype.ext h.symm)
      simp [hb']
    · simp
  · rw [dif_neg hn]
    apply Finset.sum_eq_zero
    intro k _
    have hk : n ≠ k.val := by intro heq; exact hn (heq ▸ k.property)
    simp [hk]

@[simp] theorem headInsertion_restriction (S : Finset ℤ) (a : Coeff q) :
    headInsertionCLM S (headRestrictionCLM S a) = truncate S a := by
  ext n
  simp

/-- Keep both head coordinates, and merge the two tail entries by addition. -/
def tailSumCLM (S : Finset ℤ) : (Coeff q × Coeff q) →L[ℂ] TailSumSpace q S :=
  ((headRestrictionCLM S).comp (ContinuousLinearMap.fst ℂ (Coeff q) (Coeff q))).prod
    (ContinuousLinearMap.snd ℂ (Coeff q) (Coeff q) +
      ((ContinuousLinearMap.id ℂ (Coeff q)-truncateCLM S).comp
        (ContinuousLinearMap.fst ℂ (Coeff q) (Coeff q))))

theorem tailSumCLM_apply (S : Finset ℤ) (b : Coeff q × Coeff q) :
    tailSumCLM S b = (headRestrictionCLM S b.1, b.2+(b.1-truncate S b.1)) := rfl

/-- A bounded linear right inverse to the tail-sum coordinates. -/
def tailSumRightInverseCLM (S : Finset ℤ) : TailSumSpace q S →L[ℂ] (Coeff q × Coeff q) :=
  (headInsertionCLM S).prodMap (ContinuousLinearMap.id ℂ (Coeff q))

@[simp] theorem tailSum_rightInverse (S : Finset ℤ) (w : TailSumSpace q S) :
    tailSumCLM S (tailSumRightInverseCLM S w) = w := by
  apply Prod.ext
  · funext k
    simp [tailSumRightInverseCLM,tailSumCLM_apply]
  · change w.2+(headInsertionCLM S w.1-truncate S (headInsertionCLM S w.1)) = w.2
    have he : truncate S (headInsertionCLM (q := q) S w.1) = headInsertionCLM S w.1 := by
      ext n
      by_cases hn : n ∈ S <;> simp [hn]
    rw [he,sub_self,add_zero]

/-- The affine section through a prescribed mixed-coordinate base point. -/
def tailSumSection (S : Finset ℤ) (a : Coeff q × Coeff q) (w : TailSumSpace q S) :
    Coeff q × Coeff q := a + tailSumRightInverseCLM S (w-tailSumCLM S a)

@[simp] theorem tailSumSection_base (S : Finset ℤ) (a : Coeff q × Coeff q) :
    tailSumSection S a (tailSumCLM S a) = a := by simp [tailSumSection]

@[simp] theorem tailSum_section (S : Finset ℤ) (a : Coeff q × Coeff q) (w : TailSumSpace q S) :
    tailSumCLM S (tailSumSection S a w) = w := by
  simp only [tailSumSection,map_add,tailSum_rightInverse]
  abel

theorem analyticAt_tailSumSection (S : Finset ℤ) (a : Coeff q × Coeff q) (w : TailSumSpace q S) :
    AnalyticAt ℂ (tailSumSection S a) w :=
  by
    have h : AnalyticAt ℂ (fun w : TailSumSpace q S => w-tailSumCLM S a) w :=
      analyticAt_id.sub analyticAt_const
    exact analyticAt_const.add (((tailSumRightInverseCLM (q := q) S).analyticAt _).comp h)

/-- The kernel is exactly the space of tail redistributions. -/
theorem tailSumCLM_eq_iff (S : Finset ℤ) (a b : Coeff q × Coeff q) :
    tailSumCLM S a = tailSumCLM S b ↔
      (∀ k ∈ S, b.2 k = a.2 k) ∧ a.1+a.2 = b.1+b.2 := by
  constructor
  · intro he
    have hh := congrArg Prod.fst he
    have ht : truncate S a.1 = truncate S b.1 := by
      simpa [tailSumCLM_apply] using congrArg (headInsertionCLM (q := q) S) hh
    have hs := congrArg Prod.snd he
    change a.2+(a.1-truncate S a.1) = b.2+(b.1-truncate S b.1) at hs
    have hsum : a.1+a.2 = b.1+b.2 := by
      rw [ht] at hs
      calc
        a.1+a.2 = (a.2+(a.1-truncate S b.1))+truncate S b.1 := by abel
        _ = (b.2+(b.1-truncate S b.1))+truncate S b.1 := by rw [hs]
        _ = b.1+b.2 := by abel
    refine ⟨?_,hsum⟩
    intro k hk
    have hc := congrArg (fun x : Coeff q => x k) hs
    simpa [hk] using hc.symm
  · rintro ⟨hh,hs⟩
    have hf : headRestrictionCLM S a.1 = headRestrictionCLM S b.1 := by
      funext k
      have hc := congrArg (fun x : Coeff q => x k.val) hs
      change a.1 k.val+a.2 k.val = b.1 k.val+b.2 k.val at hc
      rw [hh k.val k.property] at hc
      exact add_right_cancel hc
    have ht : truncate S a.1 = truncate S b.1 := by
      simpa using congrArg (headInsertionCLM (q := q) S) hf
    apply Prod.ext hf
    change a.2+(a.1-truncate S a.1) = b.2+(b.1-truncate S b.1)
    rw [ht]
    calc
      a.2+(a.1-truncate S b.1) = (a.1+a.2)-truncate S b.1 := by abel
      _ = (b.1+b.2)-truncate S b.1 := by rw [hs]
      _ = b.2+(b.1-truncate S b.1) := by abel

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] [p.HolderTriple p q]

/-- After mixed squaring, the first finite head is unchanged. -/
theorem tailSum_pairMixedSquare_fst (S : Finset ℤ) (z : Coeff p × Coeff p) (k : S) :
    (tailSumCLM S (pairMixedSquare (q := q) S z)).1 k = z.1 k.val := by
  simp [tailSumCLM_apply,pairMixedSquare,k.property]

/-- The sequence component retains the second head and contains twice
its quadratic action at every tail index. -/
theorem tailSum_pairMixedSquare_snd (S : Finset ℤ) (z : Coeff p × Coeff p) (k : ℤ) :
    (tailSumCLM S (pairMixedSquare (q := q) S z)).2 k =
      if k ∈ S then z.2 k else z.1 k^2+z.2 k^2 := by
  by_cases hk : k ∈ S <;> simp [tailSumCLM_apply,pairMixedSquare,hk,add_comm]

end NLS.Coeff
