import NLS.SequenceSpaces.BoundedCoordinateHolomorphic
import NLS.ComplexAnalysis.BanachTaylorBounds

/-!
# Derivative sequences of bounded coordinatewise holomorphic maps

Finite truncations of a locally bounded `ℓq`-valued map have uniformly
bounded Fréchet derivatives. Their coordinatewise limit therefore belongs
to `ℓq`, with the same bound.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coordinate derivatives of a bounded coordinatewise holomorphic
`ℓq` map form an `ℓq` sequence, uniformly in the direction. -/
theorem exists_derivative_coeff_of_bounded_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M)
    (c : E) (hc : c ∈ V) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ V ∧
      ∀ h : E, ∃ D : Coeff q,
        (∀ n : ℤ, D n = (fderiv ℂ (fun x => f x n) c) h) ∧
        ‖D‖ ≤ (2*M/R)*‖h‖ := by
  classical
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hVopen c hc
  refine ⟨R,hR,hball,?_⟩
  intro h
  let g (s : Finset ℤ) : E → Coeff q := fun x => truncate s (f x)
  let A (s : Finset ℤ) : Coeff q := (fderiv ℂ (g s) c) h
  have hg (s : Finset ℤ) : DifferentiableOn ℂ (g s) (ball c R) :=
    (differentiableOn_truncate_of_coordinatewise f hVopen hcoord s).mono hball
  have hgnorm (s : Finset ℤ) (x : E) (hx : x ∈ ball c R) : ‖g s x‖ ≤ M :=
    (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) s (f x)).trans
      (hbound x (hball hx))
  have hder (s : Finset ℤ) : ‖fderiv ℂ (g s) c‖ ≤ 2*M/R := by
    have hmaps : MapsTo (g s) (ball c R) (closedBall (g s c) (2*M)) := by
      intro x hx
      rw [mem_closedBall,dist_eq_norm]
      calc
        ‖g s x-g s c‖ ≤ ‖g s x‖+‖g s c‖ := norm_sub_le _ _
        _ ≤ M+M := add_le_add (hgnorm s x hx) (hgnorm s c (mem_ball_self hR))
        _ = 2*M := by ring
    exact Complex.norm_fderiv_le_div_of_mapsTo_ball (hg s) hmaps hR
  have hAbound (s : Finset ℤ) : ‖A s‖ ≤ (2*M/R)*‖h‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hder s) (norm_nonneg h))
  have hcoordlim (n : ℤ) :
      Tendsto (fun s : Finset ℤ => A s n) atTop
        (𝓝 ((fderiv ℂ (fun x => f x n) c) h)) := by
    have heq (s : Finset ℤ) (hn : n ∈ s) :
        A s n = (fderiv ℂ (fun x => f x n) c) h := by
      have hdc : DifferentiableAt ℂ (g s) c :=
        (hg s c (mem_ball_self hR)).differentiableAt
          (isOpen_ball.mem_nhds (mem_ball_self hR))
      have hfun : (fun x : E => (g s x) n) = (fun x => f x n) := by
        funext x
        simp [g,hn]
      have hd : HasFDerivAt (fun x : E => (g s x) n)
          ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n).comp
            (fderiv ℂ (g s) c)) c :=
        (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n).hasFDerivAt.comp c
          hdc.hasFDerivAt
      rw [hfun] at hd
      have hdeq := hd.fderiv
      exact (congrArg (fun L : E →L[ℂ] ℂ => L h) hdeq).symm
    have hev : ∀ᶠ s : Finset ℤ in atTop,
        A s n = (fderiv ℂ (fun x => f x n) c) h := by
      filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with s hs
      exact heq s (hs (by simp))
    exact tendsto_nhds_of_eventually_eq hev
  have hlim : Tendsto (id fun s : Finset ℤ => A s : Finset ℤ → ∀ n : ℤ, ℂ)
      atTop (𝓝 (fun n : ℤ => (fderiv ℂ (fun x => f x n) c) h)) := by
    rw [tendsto_pi_nhds]
    exact hcoordlim
  have hbounded : Bornology.IsBounded (Set.range A) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨(2*M/R)*‖h‖,by rintro _ ⟨s,rfl⟩; exact hAbound s⟩
  have hmem : Memℓp (fun n : ℤ => (fderiv ℂ (fun x => f x n) c) h) q :=
    lp.memℓp_of_tendsto hbounded hlim
  let D : Coeff q := ⟨_,hmem⟩
  refine ⟨D,fun n => rfl,?_⟩
  exact lp.norm_le_of_tendsto (Filter.Eventually.of_forall hAbound) hlim

/-- The sequence of coordinate derivatives is a bounded complex-linear
operator from the source space into `ℓq`. -/
theorem exists_derivative_clm_of_bounded_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M)
    (c : E) (hc : c ∈ V) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ V ∧
      ∃ L : E →L[ℂ] Coeff q,
        (∀ h : E, ∀ n : ℤ,
          L h n = (fderiv ℂ (fun x => f x n) c) h) ∧
        ‖L‖ ≤ 2*M/R := by
  classical
  obtain ⟨R,hR,hball,hdir⟩ :=
    exists_derivative_coeff_of_bounded_coordinatewise f hVopen hcoord M hbound c hc
  let D (h : E) : Coeff q := Classical.choose (hdir h)
  have hDapply (h : E) (n : ℤ) :
      D h n = (fderiv ℂ (fun x => f x n) c) h :=
    (Classical.choose_spec (hdir h)).1 n
  have hDbound (h : E) : ‖D h‖ ≤ (2*M/R)*‖h‖ :=
    (Classical.choose_spec (hdir h)).2
  let L₀ : E →ₗ[ℂ] Coeff q := {
    toFun := D
    map_add' := by
      intro h k
      ext n
      change D (h+k) n = D h n + D k n
      rw [hDapply, hDapply, hDapply, map_add]
    map_smul' := by
      intro a h
      ext n
      change D (a • h) n = a • D h n
      rw [hDapply, hDapply, map_smul] }
  let L : E →L[ℂ] Coeff q := L₀.mkContinuous (2*M/R) hDbound
  refine ⟨R,hR,hball,L,?_,?_⟩
  · intro h n
    exact hDapply h n
  · have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
    have hC : 0 ≤ 2*M/R := div_nonneg (mul_nonneg (by norm_num) hM) hR.le
    exact LinearMap.mkContinuous_norm_le L₀ hC hDbound

end NLS.Coeff
