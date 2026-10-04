import NLS.SequenceSpaces.SquareRootLifting
import NLS.SequenceSpaces.FiniteCenterBall

/-! # Squaring the tail while retaining a finite head

The finite coordinate block is retained linearly; its complement is
squared in the half-exponent space. This entire map is an open
surjection and supports descent through arbitrary tail square-root choices.
-/
noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A finite block can be transferred between any two Banach exponents. -/
def finiteBlockCLM (S : Finset ℤ) : Coeff p →L[ℂ] Coeff q :=
  ∑ n ∈ S, (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) q n).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)

@[simp] theorem finiteBlockCLM_apply (S : Finset ℤ) (a : Coeff p) (n : ℤ) :
    finiteBlockCLM (q := q) S a n = if n ∈ S then a n else 0 := by
  classical
  have he : finiteBlockCLM (q := q) S a = ∑ k ∈ S, lp.single q k (a k) := by
    simp [finiteBlockCLM,lp.singleContinuousLinearMap_apply]
    rfl
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n) (finiteBlockCLM S a) = _
  rw [he,map_sum]
  simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]


/-- Transfer the same finite block in both components. -/
def pairFiniteBlockCLM (S : Finset ℤ) : (Coeff p × Coeff p) →L[ℂ] (Coeff q × Coeff q) :=
  (finiteBlockCLM S).prodMap (finiteBlockCLM S)

variable [p.HolderTriple p q]

/-- Keep the finite head unchanged and square every remaining coordinate. -/
def mixedSquare (S : Finset ℤ) (a : Coeff p) : Coeff q :=
  finiteBlockCLM S a + square (a-truncate S a)

@[simp] theorem mixedSquare_apply (S : Finset ℤ) (a : Coeff p) (n : ℤ) :
    mixedSquare (q := q) S a n = if n ∈ S then a n else a n^2 := by
  classical
  by_cases hn : n ∈ S <;> simp [mixedSquare,hn]

/-- The mixed coordinate map is analytic in the full Banach norm. -/
theorem analyticOnNhd_mixedSquare (S : Finset ℤ) :
    AnalyticOnNhd ℂ (mixedSquare (p := p) (q := q) S) univ := by
  intro a _
  exact ((finiteBlockCLM S).analyticAt a).add
    ((analyticOnNhd_square _ (mem_univ _)).comp
      (analyticAt_id.sub ((truncateCLM S).analyticAt a)))

/-- Nearby mixed coordinates admit nearby lifts; the finite head has a
linear modulus and the squared tail has a square-root modulus. -/
theorem exists_nearby_mixedSquare (hp : p ≠ ⊤) (S : Finset ℤ) (a : Coeff p) (b : Coeff q) :
    ∃ w : Coeff p, mixedSquare S w = b ∧
      ‖w-a‖ ≤ Real.sqrt ‖b-mixedSquare S a‖ +
        ‖finiteBlockCLM (p := q) (q := p) S‖*‖b-mixedSquare S a‖ := by
  classical
  let delta := b-mixedSquare S a
  let b' := b-truncate S b+square (q := q) (truncate S a)
  obtain ⟨v,hv,hd⟩ := exists_nearby_squareRoot hp a b'
  let w := v-truncate S v+finiteBlockCLM (p := q) (q := p) S b
  have he : b'-square a = delta-truncate S delta := by
    ext n
    by_cases hn : n ∈ S <;> simp [b',delta,hn]
  have hs : ‖v-a‖^2 ≤ ‖delta‖ := by
    rw [he] at hd
    exact hd.trans (norm_sub_truncate_le
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ q))) S delta)
  have hvbound : ‖v-a‖ ≤ Real.sqrt ‖delta‖ := by
    nlinarith [Real.sq_sqrt (norm_nonneg delta),Real.sqrt_nonneg ‖delta‖,norm_nonneg (v-a)]
  refine ⟨w,?_,?_⟩
  · ext n
    have hnval := congrArg (fun c : Coeff q => c n) hv
    by_cases hn : n ∈ S
    · simp [w,hn]
    · simpa [w,b',hn] using hnval
  · have hw : w-a = (v-a)-truncate S (v-a)+finiteBlockCLM (p := q) (q := p) S delta := by
      ext n
      by_cases hn : n ∈ S <;> simp [w,delta,hn]
    rw [hw]
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_truncate_le (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) S (v-a)).trans hvbound)
      ((finiteBlockCLM (p := q) (q := p) S).le_opNorm delta))

/-- The mixed head-tail map reaches the full half-exponent space. -/
theorem mixedSquare_surjective (hp : p ≠ ⊤) (S : Finset ℤ) :
    Function.Surjective (mixedSquare (p := p) (q := q) S) := by
  intro b
  obtain ⟨w,hw,_⟩ := exists_nearby_mixedSquare hp S 0 b
  exact ⟨w,hw⟩

/-- Every open set of coordinates has open mixed-coordinate image. -/
theorem isOpenMap_mixedSquare (hp : p ≠ ⊤) (S : Finset ℤ) :
    IsOpenMap (mixedSquare (p := p) (q := q) S) := by
  intro U hU
  apply Metric.isOpen_iff.mpr
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU a ha
  let K := ‖finiteBlockCLM (p := q) (q := p) S‖
  have hK : 0 ≤ K := norm_nonneg _
  let delta := min (r/(2*(K+1))) (r^2/4)
  have hd : 0 < delta := by dsimp [delta]; positivity
  refine ⟨delta,hd,?_⟩
  intro b hb
  have hb' : ‖b-mixedSquare S a‖ < delta := by simpa only [mem_ball,dist_eq_norm] using hb
  have h1 : ‖b-mixedSquare S a‖ < r/(2*(K+1)) := hb'.trans_le (min_le_left _ _)
  have h2 : ‖b-mixedSquare S a‖ < r^2/4 := hb'.trans_le (min_le_right _ _)
  have hlin : K*‖b-mixedSquare S a‖ < r/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*(K+1))).mp h1
    nlinarith [norm_nonneg (b-mixedSquare S a)]
  have hroot : Real.sqrt ‖b-mixedSquare S a‖ < r/2 := by
    nlinarith [Real.sq_sqrt (norm_nonneg (b-mixedSquare S a)),
      Real.sqrt_nonneg ‖b-mixedSquare S a‖]
  obtain ⟨w,hw,hdist⟩ := exists_nearby_mixedSquare hp S a b
  refine ⟨w,hball ?_,hw⟩
  rw [mem_ball,dist_eq_norm]
  exact hdist.trans_lt (by change Real.sqrt ‖b-mixedSquare S a‖+K*‖b-mixedSquare S a‖ < r; linarith)

/-- Mixed coordinates for both Birkhoff components. -/
def pairMixedSquare (S : Finset ℤ) (z : Coeff p × Coeff p) : Coeff q × Coeff q :=
  (mixedSquare S z.1,mixedSquare S z.2)

theorem analyticOnNhd_pairMixedSquare (S : Finset ℤ) :
    AnalyticOnNhd ℂ (pairMixedSquare (p := p) (q := q) S) univ := by
  intro z _
  exact ((analyticOnNhd_mixedSquare S _ (mem_univ _)).comp analyticAt_fst).prod
    ((analyticOnNhd_mixedSquare S _ (mem_univ _)).comp analyticAt_snd)

theorem isOpenMap_pairMixedSquare (hp : p ≠ ⊤) (S : Finset ℤ) :
    IsOpenMap (pairMixedSquare (p := p) (q := q) S) :=
  (isOpenMap_mixedSquare hp S).prodMap (isOpenMap_mixedSquare hp S)

/-- A mixed-coordinate fiber fixes the finite head and the square of
all remaining coordinates in both components. -/
theorem pairMixedSquare_eq_iff (S : Finset ℤ) (z w : Coeff p × Coeff p) :
    pairMixedSquare (q := q) S z = pairMixedSquare S w ↔
      (∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n) ∧
      (∀ n, z.1 n^2 = w.1 n^2 ∧ z.2 n^2 = w.2 n^2) := by
  classical
  have hhead (he : pairMixedSquare (q := q) S z = pairMixedSquare S w)
      (n : ℤ) (hn : n ∈ S) : z.1 n = w.1 n ∧ z.2 n = w.2 n := by
    have h1 := congrArg (fun a : Coeff q × Coeff q => a.1 n) he
    have h2 := congrArg (fun a : Coeff q × Coeff q => a.2 n) he
    exact ⟨by simpa [pairMixedSquare,hn] using h1,by simpa [pairMixedSquare,hn] using h2⟩
  constructor
  · intro he
    refine ⟨hhead he,fun n => ?_⟩
    by_cases hn : n ∈ S
    · exact ⟨congrArg (fun a : ℂ => a^2) (hhead he n hn).1,
        congrArg (fun a : ℂ => a^2) (hhead he n hn).2⟩
    · have h1 := congrArg (fun a : Coeff q × Coeff q => a.1 n) he
      have h2 := congrArg (fun a : Coeff q × Coeff q => a.2 n) he
      exact ⟨by simpa [pairMixedSquare,hn] using h1,by simpa [pairMixedSquare,hn] using h2⟩
  · rintro ⟨hh,hs⟩
    apply Prod.ext <;> ext n
    · change mixedSquare S z.1 n = mixedSquare S w.1 n
      by_cases hn : n ∈ S <;> simp [hn,hh,hs]
    · change mixedSquare S z.2 n = mixedSquare S w.2 n
      by_cases hn : n ∈ S <;> simp [hn,hh,hs]

/-- Varying only the finite head is a linear lift of mixed-coordinate changes. -/
theorem pairMixedSquare_add_finiteBlock (S : Finset ℤ) (z : Coeff p × Coeff p)
    (b : Coeff q × Coeff q) :
    pairMixedSquare S (z+pairFiniteBlockCLM (p := q) (q := p) S b) =
      pairMixedSquare S z+truncatePair S b := by
  classical
  apply Prod.ext <;> ext n
  · change mixedSquare S (z.1+finiteBlockCLM S b.1) n = mixedSquare S z.1 n+truncate S b.1 n
    by_cases hn : n ∈ S <;> simp [hn]
  · change mixedSquare S (z.2+finiteBlockCLM S b.2) n = mixedSquare S z.2 n+truncate S b.2 n
    by_cases hn : n ∈ S <;> simp [hn]

end NLS.Coeff
