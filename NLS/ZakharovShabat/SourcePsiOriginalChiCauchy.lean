import NLS.ZakharovShabat.SourcePsiOriginalChiMajorant
import NLS.ZakharovShabat.SourceActionContourFamily

/-!
# Uniform original contour collars and the Cauchy estimate in Lemma 12.12

The existing simultaneous circles have one positive collar width because
only finitely many differ from the exact free tail. Cauchy's estimate and
the convex mean-value inequality bound chi's divided difference on the
entire filled circles, uniformly in both spectral indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {D : ℤ → Set ℂ} {c : ℝ}

/-- The original circles have one positive width before the original disk boundaries. -/
theorem SourceActionContourFamily.uniform_outer_margin
    (C : SourceActionContourFamily hp hp1 V D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, C.radius m+δ ≤ C.outer m := by
  classical
  obtain ⟨K,hK⟩ := C.tail
  let S := Finset.Icc (-(K:ℤ)) (K:ℤ)
  have hS : S.Nonempty := ⟨0,by simp [S]⟩
  let δ := min (Real.pi/16) (S.inf' hS (fun m => C.outer m-C.radius m))
  have hδ : 0 < δ := lt_min (by positivity)
    ((Finset.lt_inf'_iff hS).mpr (fun m _ => sub_pos.mpr (C.radius_lt m)))
  refine ⟨δ,hδ,?_⟩
  intro m
  by_cases hm : m ∈ S
  · have hb : δ ≤ C.outer m-C.radius m :=
      (min_le_right _ _).trans (Finset.inf'_le _ hm)
    linarith
  · have hmK : K < m.natAbs := by simp only [S,Finset.mem_Icc] at hm; omega
    obtain ⟨_,_,hr,ho⟩ := hK m hmK
    have hb : δ ≤ Real.pi/16 := min_le_left _ _
    rw [hr,ho]
    linarith

/-- Cauchy's estimate on uniform collars also bounds the removable divided difference. -/
private theorem norm_dslope_le_of_collar (f : ℂ → ℂ) (a q : ℂ) (r R δ M : ℝ)
    (hδ : 0 < δ) (hmargin : r+δ ≤ R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hb : ∀ z ∈ ball a R, ‖f z-q‖ ≤ M)
    (u v : ℂ) (hu : u ∈ closedBall a r) (hv : v ∈ closedBall a r) :
    ‖dslope f u v‖ ≤ 2*M/δ := by
  have hsmall : closedBall a r ⊆ ball a R := closedBall_subset_ball (by linarith)
  have hinto (z : ℂ) (hz : z ∈ closedBall a r) : ball z δ ⊆ ball a R := by
    intro w hw
    apply mem_ball.mpr
    exact (dist_triangle w z a).trans_lt (by
      have hw' := mem_ball.mp hw
      have hz' := mem_closedBall.mp hz
      linarith)
  have hder (z : ℂ) (hz : z ∈ closedBall a r) : ‖deriv f z‖ ≤ 2*M/δ := by
    have hmaps : MapsTo f (ball z δ) (closedBall (f z) (2*M)) := by
      intro w hw
      rw [mem_closedBall,dist_eq_norm]
      have ht := norm_sub_le_norm_sub_add_norm_sub (f w) q (f z)
      rw [norm_sub_rev q] at ht
      linarith [hb w (hinto z hz hw),hb z (hsmall hz)]
    exact Complex.norm_deriv_le_div_of_mapsTo_ball
      (hf.mono (hinto z hz)).differentiableOn hmaps hδ
  by_cases he : v = u
  · subst v
    rw [dslope_same]
    exact hder u hu
  · rw [dslope_of_ne _ he,slope_def_module,norm_smul,norm_inv,← div_eq_inv_mul]
    apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr
    exact (convex_closedBall a r).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hf z (hsmall hz)).differentiableAt) hder hu hv

/-- Uniform divided-difference lp bounds on all original filled contour disks. -/
theorem SourceLemma12_11Data.original_chi_dslope_errorBound
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (C : SourceActionContourFamily hp hp1 V D)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ L ∧
        ∀ m : ℤ, m ≠ n → ∀ z ∈ closedBall (C.center m:ℂ) (C.radius m),
          ‖dslope (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n χ) χ)
            (sourceStandardRootMidpoint hp hp1 χ m) z‖ ≤ ‖E m‖ := by
  obtain ⟨U,hU,hψU,hUV,L,hL,hb⟩ := H.original_allDisk_chi_errorBound hD hV ψ hψ hψV
  obtain ⟨δ,hδ,hmargin⟩ := C.uniform_outer_margin
  refine ⟨U,hU,hψU,hUV,(2/δ)*L,by positivity,?_⟩
  intro χ hχ n
  obtain ⟨B,hB,hBpoint⟩ := hb χ hχ n
  let E : Coeff p := ((2/δ:ℝ):ℂ) • B
  have hEpoint (m : ℤ) : ‖E m‖ = (2/δ)*‖B m‖ := by
    simp only [E,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 2/δ)]
  refine ⟨E,?_,?_⟩
  · simpa only [E,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 2/δ)] using
      mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2/δ)
  · intro m hmn z hz
    have hχV := (hUV hχ).2
    have ho : 0 < C.outer m := (C.inner_pos m).trans ((C.inner_lt m).trans (C.radius_lt m))
    let P := hD.periodCircle χ hχV m (C.center m) (C.outer m) ho (C.original m)
    have hf := (H.original_chi_analytic χ (hUV hχ).1 n m hmn P).mono ball_subset_closedBall
    have hτ : sourceStandardRootMidpoint hp hp1 χ m ∈ closedBall (C.center m:ℂ) (C.radius m) :=
      ball_subset_closedBall ((ball_subset_ball (C.inner_lt m).le)
        (C.gap χ hχV m (sourcePeriodicMidpoint_mem_segment hp hp1 χ m)))
    have hd := norm_dslope_le_of_collar _ (C.center m:ℂ) I (C.radius m) (C.outer m) δ ‖B m‖
      hδ (hmargin m) hf (fun w hw => hBpoint m hmn w ((C.original m).symm ▸ hw))
      _ z hτ hz
    rw [hEpoint]
    convert hd using 1
    ring

end NLS.ZakharovShabat
