import NLS.ZakharovShabat.SourcePsiOriginalChiCauchy
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError

/-!
# The original root inequalities (2.34)

The exact original dslope identity and the standard-root maximum bound
give the first gap factor, with a single positive midpoint lower bound.
The gap's half-length gives the second displayed inequality. The result
uses actual complex gaps and includes collapsed gaps without division.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Both inequalities in (2.34), with an attained gap maximum and explicit constants. -/
theorem SourceLemma12_11Data.original_root_offset_gap_bound
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (R : ℝ) (hPR : P.radius < R)
    (hf : AnalyticOnNhd ℂ (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ)
      (ball (P.center:ℂ) R))
    (B c₀ : ℝ) (hB : 0 ≤ B) (hc₀ : 0 < c₀)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m,
      ‖dslope (sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ)
        (sourceStandardRootMidpoint hp hp1 ψ m) z‖ ≤ B)
    (hlow : c₀ ≤ ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ
      (sourceStandardRootMidpoint hp hp1 ψ m)‖) :
    ∃ ξ ∈ sourcePeriodicSegment hp hp1 ψ m,
      IsMaxOn (fun z => ‖displacedRoots (s n ψ:Coeff p) m-z‖) (sourcePeriodicSegment hp hp1 ψ m) ξ ∧
      ‖displacedRoots (s n ψ:Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
        ‖displacedRoots (s n ψ:Coeff p) m-ξ‖*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖*(B/(2*c₀)) ∧
      ‖displacedRoots (s n ψ:Coeff p) m-ξ‖*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖*(B/(2*c₀)) ≤
        (‖displacedRoots (s n ψ:Coeff p) m-sourceStandardRootMidpoint hp hp1 ψ m‖+
          ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖/2)*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖*(B/(2*c₀)) := by
  let σ := displacedRoots (s n ψ:Coeff p) m
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ m
  let f := sourcePsiMidpointFilledRegularFactor hp hp1 n m (s n ψ) ψ
  let b := dslope f τ
  let F : ℂ → ℂ := fun z => (σ-z)*(z-τ)*b z
  have hτ : τ ∈ ball (P.center:ℂ) R :=
    (ball_subset_ball hPR.le) (P.gap (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m))
  have hbana : AnalyticOnNhd ℂ b (ball (P.center:ℂ) R) :=
    ((differentiableOn_dslope (isOpen_ball.mem_nhds hτ)).mpr hf.differentiableOn).analyticOnNhd isOpen_ball
  have hF : AnalyticOnNhd ℂ F (closedBall (P.center:ℂ) P.radius) := by
    intro z hz
    exact ((analyticAt_const.sub analyticAt_id).mul (analyticAt_id.sub analyticAt_const)).mul
      (hbana z (closedBall_subset_ball hPR hz))
  obtain ⟨z,hz,_,hbound,_⟩ := P.lemma12_3_circle F hF
  rw [PiecewiseC1Loop.integral_circle] at hbound
  have hπ : (2*Real.pi:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have he : (2*Real.pi:ℂ)⁻¹*(∮ w in C((P.center:ℂ),P.radius), F w/sourceStandardRoot hp hp1 ψ m w) =
      I*(σ-τ)*f τ := by
    have hi := H.original_chi_dslope_identity hW₀ ψ hψ n m hmn P
    have heq : (∮ w in C((P.center:ℂ),P.radius), F w/sourceStandardRoot hp hp1 ψ m w) =
        (2*Real.pi*I:ℂ)*(σ-τ)*f τ := by
      rw [hi]
      apply circleIntegral.integral_congr P.radius_pos.le
      intro w _
      dsimp only [F,b,σ,τ,f]
      ring
    rw [heq]
    field_simp
  rw [he,norm_mul,norm_mul,norm_I,one_mul] at hbound
  have hgap : ‖z-τ‖ ≤ ‖γ‖/2 := by
    simpa only [norm_sub_rev] using norm_sourceMidpoint_sub_le_halfGap hp hp1 ψ m z hz
  have hmain : ‖σ-τ‖*c₀ ≤ ‖σ-z‖*(‖γ‖/2)*B := by
    calc
      ‖σ-τ‖*c₀ ≤ ‖σ-τ‖*‖f τ‖ := mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
      _ ≤ ‖F z‖ := hbound
      _ = ‖σ-z‖*‖z-τ‖*‖b z‖ := by simp only [F,norm_mul]
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hgap (norm_nonneg _)) (hb z hz)
        (norm_nonneg _) (by positivity)
  have hcompact : IsCompact (sourcePeriodicSegment hp hp1 ψ m) := by
    rw [← sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact standardRootGapSegment_compact _ _
  obtain ⟨ξ,hξ,hmax⟩ := hcompact.exists_isMaxOn
    ⟨τ,sourcePeriodicMidpoint_mem_segment hp hp1 ψ m⟩ (continuous_const.sub continuous_id).norm.continuousOn
  have hξgap : ‖τ-ξ‖ ≤ ‖γ‖/2 := norm_sourceMidpoint_sub_le_halfGap hp hp1 ψ m ξ hξ
  have htri : ‖σ-ξ‖ ≤ ‖σ-τ‖+‖γ‖/2 :=
    (norm_sub_le_norm_sub_add_norm_sub σ τ ξ).trans (add_le_add le_rfl hξgap)
  refine ⟨ξ,hξ,hmax,?_,?_⟩
  · have hh : ‖σ-τ‖*c₀ ≤ (‖σ-ξ‖*‖γ‖*(B/(2*c₀)))*c₀ := by
      calc
        ‖σ-τ‖*c₀ ≤ ‖σ-z‖*(‖γ‖/2)*B := hmain
        _ ≤ ‖σ-ξ‖*(‖γ‖/2)*B := by gcongr; exact hmax hz
        _ = (‖σ-ξ‖*‖γ‖*(B/(2*c₀)))*c₀ := by field_simp
    nlinarith [hh]
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htri (norm_nonneg _))
      (by positivity)

/-- Equations (2.34) have one lp bound on a neighborhood of every complex source. -/
theorem SourceLemma12_11Data.original_root_offset_inequalities
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V) (hVW : V ⊆ W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ L ∧
        ∀ m : ℤ, m ≠ n → ∃ ξ ∈ sourcePeriodicSegment hp hp1 χ m,
          IsMaxOn (fun z => ‖displacedRoots (s n χ:Coeff p) m-z‖) (sourcePeriodicSegment hp hp1 χ m) ξ ∧
          ‖displacedRoots (s n χ:Coeff p) m-sourceStandardRootMidpoint hp hp1 χ m‖ ≤
            ‖displacedRoots (s n χ:Coeff p) m-ξ‖*‖sourcePeriodicGapDisplacement hp hp1 χ m‖*‖E m‖ ∧
          ‖displacedRoots (s n χ:Coeff p) m-ξ‖*‖sourcePeriodicGapDisplacement hp hp1 χ m‖*‖E m‖ ≤
            (‖displacedRoots (s n χ:Coeff p) m-sourceStandardRootMidpoint hp hp1 χ m‖+
              ‖sourcePeriodicGapDisplacement hp hp1 χ m‖/2)*‖sourcePeriodicGapDisplacement hp hp1 χ m‖*‖E m‖ := by
  have HC : SourceSection11ContourData hp hp1 W₀ :=
    H.previous.psi.previous.previous.previous.previous.previous.previous
  obtain ⟨Vc,hVc,_,hψc,hcV,C,_⟩ := HC.contours hV hVW hD ψ hψV
  have hDc := hD.mono hcV
  obtain ⟨Ub,hUb,hψb,hbc,L,hL,hb⟩ := H.original_chi_dslope_errorBound hDc hVc C ψ hψ hψc
  obtain ⟨Ul,hUl,hψl,_,c₀,hc₀,hl⟩ := H.original_midpoint_lower_bound ψ hψ
  refine ⟨Ub ∩ Ul,hUb.inter hUl,⟨hψb,hψl⟩,
    (fun χ hχ => ⟨(hbc hχ.1).1,hcV (hbc hχ.1).2⟩),L/(2*c₀),by positivity,?_⟩
  intro χ hχ n
  obtain ⟨B,hB,hBpoint⟩ := hb χ hχ.1 n
  let E : Coeff p := ((1/(2*c₀):ℝ):ℂ) • B
  have hEpoint (m : ℤ) : ‖E m‖ = ‖B m‖/(2*c₀) := by
    simp only [E,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (by positivity : 0 ≤ 1/(2*c₀))]
    ring
  refine ⟨E,?_,?_⟩
  · simp only [E,norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0 ≤ 1/(2*c₀))]
    rw [one_div,mul_comm,← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right hB (by positivity)
  · intro m hmn
    have hχc := (hbc hχ.1).2
    have hχW := (hbc hχ.1).1
    have ho : 0 < C.outer m := (C.inner_pos m).trans ((C.inner_lt m).trans (C.radius_lt m))
    let P₀ := hDc.periodCircle χ hχc m (C.center m) (C.outer m) ho (C.original m)
    let P : SourceCriticalRootPeriodCircle hp hp1 χ m := {
      center := C.center m
      radius := C.radius m
      radius_pos := (C.inner_pos m).trans (C.inner_lt m)
      gap := (C.gap χ hχc m).trans (ball_subset_ball (C.inner_lt m).le)
      other := by
        intro k hkm z hz
        rcases P₀.other k hkm z hz with h | h
        · left; change z.re < C.center m-C.outer m at h; linarith [C.radius_lt m]
        · right; change C.center m+C.outer m < z.re at h; linarith [C.radius_lt m]
    }
    have hf := (H.original_chi_analytic χ hχW n m hmn P₀).mono ball_subset_closedBall
    obtain ⟨ξ,hξ,hmax,hfirst,hsecond⟩ := H.original_root_offset_gap_bound hW₀ χ hχW n m hmn P
      (C.outer m) (C.radius_lt m) hf ‖B m‖ c₀ (norm_nonneg _) hc₀
      (fun z hz => hBpoint m hmn z (ball_subset_closedBall (P.gap hz)))
      (hl χ hχ.2 n m hmn)
    exact ⟨ξ,hξ,hmax,by simpa only [hEpoint] using hfirst,by simpa only [hEpoint] using hsecond⟩

end NLS.ZakharovShabat
