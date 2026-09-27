import NLS.SequenceSpaces.BoundedCoordinateDerivative

/-!
# Fréchet holomorphy from bounded holomorphic coordinates

The derivative sequence constructed from the scalar coordinates is the
Fréchet derivative of the full `ℓq`-valued map. A second-order Schwarz
estimate for finite truncations is uniform in the truncation, so it
passes to the sequence norm.
-/

noncomputable section
open Set Metric Filter Topology Asymptotics
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem differentiableOn_of_bounded_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, DifferentiableOn ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M) :
    DifferentiableOn ℂ f V := by
  classical
  intro c hc
  obtain ⟨R,hR,hball,L,hL,hLbound⟩ :=
    exists_derivative_clm_of_bounded_coordinatewise f hVopen hcoord M hbound c hc
  let g (s : Finset ℤ) : E → Coeff q := fun x => truncate s (f x)
  let A (s : Finset ℤ) : E →L[ℂ] Coeff q := fderiv ℂ (g s) c
  let r (s : Finset ℤ) (y : E) : Coeff q := g s y - g s c - A s (y-c)
  have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
  have hC : 0 ≤ 2*M/R := div_nonneg (mul_nonneg (by norm_num) hM) hR.le
  have hg (s : Finset ℤ) : DifferentiableOn ℂ (g s) (ball c R) :=
    (differentiableOn_truncate_of_coordinatewise f hVopen hcoord s).mono hball
  have hgnorm (s : Finset ℤ) (x : E) (hx : x ∈ ball c R) : ‖g s x‖ ≤ M :=
    (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) s (f x)).trans
      (hbound x (hball hx))
  have hA (s : Finset ℤ) : ‖A s‖ ≤ 2*M/R := by
    have hmaps : MapsTo (g s) (ball c R) (closedBall (g s c) (2*M)) := by
      intro x hx
      rw [mem_closedBall,dist_eq_norm]
      calc
        ‖g s x-g s c‖ ≤ ‖g s x‖+‖g s c‖ := norm_sub_le _ _
        _ ≤ M+M := add_le_add (hgnorm s x hx) (hgnorm s c (mem_ball_self hR))
        _ = 2*M := by ring
    exact Complex.norm_fderiv_le_div_of_mapsTo_ball (hg s) hmaps hR
  have hquad (s : Finset ℤ) (y : E) (hy : y ∈ ball c R) :
      ‖r s y‖ ≤ 4*M*(‖y-c‖/R)^2 := by
    have hlin : Differentiable ℂ (fun x : E => A s (x-c)) :=
      (A s).differentiable.comp (differentiable_id.sub_const c)
    have hrdiff : DifferentiableOn ℂ (r s) (ball c R) := by
      exact ((hg s).sub (differentiableOn_const (c := g s c))).sub hlin.differentiableOn
    have hzero : r s c = 0 := by simp [r]
    have hdc : DifferentiableAt ℂ (g s) c :=
      (hg s c (mem_ball_self hR)).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_self hR))
    have hlo : (fun x => r s x-r s c) =o[𝓝 c] (fun x => ‖x-c‖^1) := by
      simpa [r,hzero,pow_one] using hdc.hasFDerivAt.isLittleO.norm_right
    have hmaps : MapsTo (r s) (ball c R) (closedBall (r s c) (4*M)) := by
      intro x hx
      rw [mem_closedBall,dist_eq_norm,hzero,sub_zero]
      have hxR : ‖x-c‖ ≤ R := by
        simpa only [mem_ball,dist_eq_norm] using (show dist x c < R from hx).le
      have hlinbound : ‖A s (x-c)‖ ≤ 2*M := by
        calc
          ‖A s (x-c)‖ ≤ ‖A s‖*‖x-c‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (2*M/R)*‖x-c‖ := mul_le_mul_of_nonneg_right (hA s) (norm_nonneg _)
          _ ≤ (2*M/R)*R := mul_le_mul_of_nonneg_left hxR hC
          _ = 2*M := by field_simp
      calc
        ‖r s x‖ ≤ ‖g s x-g s c‖+‖A s (x-c)‖ := norm_sub_le _ _
        _ ≤ (‖g s x‖+‖g s c‖)+‖A s (x-c)‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (M+M)+2*M :=
          add_le_add (add_le_add (hgnorm s x hx) (hgnorm s c (mem_ball_self hR))) hlinbound
        _ = 4*M := by ring
    have hs := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      (n := 1) hrdiff hmaps hlo hy
    simpa only [hzero,dist_eq_norm,sub_zero,one_add_one_eq_two] using hs
  have hfull (y : E) (hy : y ∈ ball c R) :
      ‖f y-f c-L (y-c)‖ ≤ 4*M*(‖y-c‖/R)^2 := by
    have hAcoord (s : Finset ℤ) (n : ℤ) (hn : n ∈ s) (v : E) :
        A s v n = L v n := by
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
      rw [hL v n]
      exact (congrArg (fun T : E →L[ℂ] ℂ => T v) hdeq).symm
    have hcoordlim (n : ℤ) :
        Tendsto (fun s : Finset ℤ => r s y n) atTop
          (𝓝 ((f y-f c-L (y-c)) n)) := by
      have hev : ∀ᶠ s : Finset ℤ in atTop,
          r s y n = (f y-f c-L (y-c)) n := by
        filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with s hs
        have hn : n ∈ s := hs (by simp)
        change (g s y n - g s c n - A s (y-c) n) =
          (f y n - f c n - L (y-c) n)
        rw [show g s y n = f y n by simp [g,hn],
          show g s c n = f c n by simp [g,hn],hAcoord s n hn]
      exact tendsto_nhds_of_eventually_eq hev
    have hlim : Tendsto (id fun s : Finset ℤ => r s y : Finset ℤ → ∀ n : ℤ, ℂ)
        atTop (𝓝 (f y-f c-L (y-c))) := by
      rw [tendsto_pi_nhds]
      exact hcoordlim
    exact lp.norm_le_of_tendsto (Filter.Eventually.of_forall fun s => hquad s y hy) hlim
  have hsmall :
      (fun y => f y-f c-L (y-c)) =o[𝓝 c] (fun y => y-c) := by
    have hO :
        (fun y => f y-f c-L (y-c)) =O[𝓝 c] (fun y => ‖y-c‖^2) := by
      apply IsBigO.of_bound (4*M/R^2)
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with y hy
      have heq : 4*M*(‖y-c‖/R)^2 = (4*M/R^2)*‖y-c‖^2 := by
        field_simp
      simpa [Real.norm_eq_abs,abs_pow] using
        (hfull y hy).trans_eq heq
    exact hO.trans_isLittleO (isLittleO_pow_sub_sub c (by norm_num : 1 < 2))
  exact ((hasFDerivAt_iff_isLittleO).mpr hsmall).differentiableAt.differentiableWithinAt

/-- Evaluating the derivative of an `ℓq`-valued holomorphic map gives
the derivative of the corresponding scalar coordinate. -/
theorem fderiv_apply_of_differentiableAt (f : E → Coeff q) (c h : E) (n : ℤ)
    (hf : DifferentiableAt ℂ f c) :
    (fderiv ℂ f c) h n = (fderiv ℂ (fun x => f x n) c) h := by
  have hd : HasFDerivAt (fun x : E => f x n)
      ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n).comp (fderiv ℂ f c)) c :=
    (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n).hasFDerivAt.comp c hf.hasFDerivAt
  exact (congrArg (fun T : E →L[ℂ] ℂ => T h) hd.fderiv).symm

end NLS.Coeff
