import NLS.SequenceSpaces.TailActionStationarity
import Mathlib.Analysis.Calculus.MeanValue

/-! # Invariance under arbitrary tail redistributions

Finite truncations show that annihilating each coordinate splitting
direction annihilates every tail direction `(-v,v)`. The mean-value theorem
then makes the descended map constant along any such segment in its domain.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded linear map annihilating each tail splitting direction
annihilates arbitrary, possibly infinite-support tail redistributions. -/
theorem clm_tailSplit_eq_zero (hq : q ≠ ⊤)
    (L : (Coeff q × Coeff q) →L[ℂ] F) (S : Finset ℤ)
    (hL : ∀ k ∉ S, L (actionSplitDirection q k) = 0)
    (v : Coeff q) (hv : ∀ k ∈ S, v k = 0) : L (-v,v) = 0 := by
  let J : Coeff q →L[ℂ] (Coeff q × Coeff q) :=
    (-(ContinuousLinearMap.id ℂ (Coeff q))).prod (ContinuousLinearMap.id ℂ (Coeff q))
  have hs (T : Finset ℤ) : (L.comp J) (truncate T v) = 0 := by
    rw [truncate,map_sum]
    apply Finset.sum_eq_zero
    intro k _
    have he : J (lp.single q k (v k)) = (v k) • actionSplitDirection q k := by
      have hs : lp.single q k (v k) = (v k) • (lp.single q k 1 : Coeff q) := by
        rw [← lp.single_smul]
        simp
      rw [hs,map_smul]
      rfl
    change L (J (lp.single q k (v k))) = 0
    rw [he,map_smul]
    by_cases hk : k ∈ S
    · simp [hv k hk]
    · simp [hL k hk]
  have ht := (L.comp J).continuous.continuousAt.tendsto.comp (tendsto_truncate hq v)
  exact tendsto_nhds_unique ht (tendsto_nhds_of_eventually_eq (Eventually.of_forall hs))

/-- If every tail splitting derivative vanishes, the map is constant on
any tail-redistribution segment lying inside its open domain. -/
theorem eq_of_tailSplit_segment (hq : q ≠ ⊤)
    (G : (Coeff q × Coeff q) → F) (U : Set (Coeff q × Coeff q)) (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) (S : Finset ℤ)
    (hD : ∀ b ∈ U, ∀ k ∉ S, fderiv ℂ G b (actionSplitDirection q k) = 0)
    (a : Coeff q × Coeff q) (v : Coeff q) (hv : ∀ k ∈ S, v k = 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a+t • (-v,v) ∈ U) : G (a+(-v,v)) = G a := by
  let γ : ℝ → Coeff q × Coeff q := fun t => a+t • (-v,v)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun t => G (γ t)) 0 t := by
    have hγ : HasDerivAt γ (-v,v) t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const ((-v,v) : Coeff q × Coeff q)).const_add a
    have hdf := ((hG _ (hseg t ht)).differentiableAt (hU.mem_nhds (hseg t ht))).hasFDerivAt.restrictScalars ℝ
    have hh := hdf.comp_hasDerivAt (f := γ) t hγ
    have he := clm_tailSplit_eq_zero hq (fderiv ℂ G (γ t)) S (hD _ (hseg t ht)) v hv
    change HasDerivAt (fun t => G (γ t)) (fderiv ℂ G (γ t) (-v,v)) t at hh
    simpa only [he] using hh
  have hm := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => by rw [(hd t ht).deriv]; simp : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (fun t => G (γ t)) t‖ ≤ (0 : ℝ))
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have he : G (γ 1)-G (γ 0) = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hm) (norm_nonneg _))
  have hzero : γ 0 = a := by dsimp only [γ]; rw [zero_smul,add_zero]
  have hone : γ 1 = a+(-v,v) := by dsimp only [γ]; rw [one_smul]
  simpa only [hzero,hone] using sub_eq_zero.mp he

/-- Two mixed-coordinate points with the same retained head and the same
pairwise sums have equal images whenever their joining segment stays in
the domain. In particular this gives local constancy on each tail-action fiber. -/
theorem eq_of_same_tailActions_of_segment (hq : q ≠ ⊤)
    (G : (Coeff q × Coeff q) → F) (U : Set (Coeff q × Coeff q)) (hU : IsOpen U)
    (hG : DifferentiableOn ℂ G U) (S : Finset ℤ)
    (hD : ∀ b ∈ U, ∀ k ∉ S, fderiv ℂ G b (actionSplitDirection q k) = 0)
    (a b : Coeff q × Coeff q) (hhead : ∀ k ∈ S, b.2 k = a.2 k)
    (hsum : a.1+a.2 = b.1+b.2) (hseg : segment ℝ a b ⊆ U) : G b = G a := by
  let v : Coeff q := b.2-a.2
  have hv : ∀ k ∈ S, v k = 0 := by
    intro k hk
    change b.2 k-a.2 k = 0
    rw [hhead k hk,sub_self]
  have hab : b = a+(-v,v) := by
    apply Prod.ext
    · change b.1 = a.1+ -(b.2-a.2)
      calc
        b.1 = (b.1+b.2)-b.2 := by abel
        _ = (a.1+a.2)-b.2 := by rw [← hsum]
        _ = a.1+ -(b.2-a.2) := by abel
    · change b.2 = a.2+(b.2-a.2)
      abel
  rw [hab]
  apply eq_of_tailSplit_segment hq G U hU hG S hD a v hv
  intro t ht
  apply hseg
  have hm := lineMap_mem_segment ℝ a b ht
  rw [hab] at hm
  rw [hab]
  simpa only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,add_sub_cancel_left,add_comm] using hm

end NLS.Coeff
