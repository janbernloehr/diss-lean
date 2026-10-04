import NLS.SequenceSpaces.HeadActionTangent

/-! # Constancy along differentiable head-action curves

Differentiating the quadratic action identities gives the tangent
constraints. Rotation stationarity therefore makes the function constant
along any differentiable action-preserving curve in its domain, provided
no retained pair vanishes along the curve.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- A zero action derivative gives the full head-action tangent constraints. -/
theorem headActionTangent_of_hasDerivAt (S : Finset ℤ)
    (γ : ℝ → TailSumSpace q S) (v : TailSumSpace q S) (t : ℝ)
    (hγ : HasDerivAt γ v t) (ha : HasDerivAt (fun s => headActions S (γ s)) 0 t) :
    (∀ n ∉ S, v.2 n = 0) ∧
      ∀ k : S, (γ t).1 k*v.1 k+(γ t).2 k.val*v.2 k.val = 0 := by
  have hy (n : ℤ) : HasDerivAt (fun s => (γ s).2 n) (v.2 n) t := by
    let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).comp
      (ContinuousLinearMap.snd ℂ (S → ℂ) (Coeff q))
    exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hγ
  have hb (n : ℤ) : HasDerivAt (fun s => headActions S (γ s) n) 0 t := by
    have hh := ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t ha
    change HasDerivAt (fun s => headActions S (γ s) n) ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n) (0 : Coeff q)) t at hh
    simpa only [map_zero] using hh
  constructor
  · intro n hn
    have hd : HasDerivAt (fun s => headActions S (γ s) n) (v.2 n/2) t := by
      simpa only [headActions_apply,dif_neg hn] using (hy n).div_const (2 : ℂ)
    have he := hd.unique (hb n)
    exact (div_eq_zero_iff.mp he).resolve_right (by norm_num)
  · intro k
    have hx : HasDerivAt (fun s => (γ s).1 k) (v.1 k) t := by
      let L := (ContinuousLinearMap.proj k : (S → ℂ) →L[ℂ] ℂ).comp
        (ContinuousLinearMap.fst ℂ (S → ℂ) (Coeff q))
      exact (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hγ
    have hd := ((hx.pow 2).add ((hy k.val).pow 2)).div_const (2 : ℂ)
    simp only [Pi.add_def] at hd
    have hd' : HasDerivAt (fun s => headActions S (γ s) k.val)
        ((γ t).1 k*v.1 k+(γ t).2 k.val*v.2 k.val) t := by
      simpa only [headActions_apply,dif_pos k.property,Pi.add_def] using
        (show HasDerivAt (fun s => ((γ s).1 k^2+(γ s).2 k.val^2)/2)
          ((γ t).1 k*v.1 k+(γ t).2 k.val*v.2 k.val) t from by
            convert hd using 1 <;> first | rfl | ring)
    exact hd'.unique (hb k.val)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A function stationary under head rotations is constant along a
head-action curve on the unit interval. The action identity is global in
the curve parameter; differentiability and domain membership are local
conditions only at points of the interval. -/
theorem eq_of_headAction_curve (S : Finset ℤ) (G : TailSumSpace q S → F)
    (U : Set (TailSumSpace q S)) (hU : IsOpen U) (hG : DifferentiableOn ℂ G U)
    (hrot : ∀ w ∈ U, ∀ k : S, fderiv ℂ G w (headRotationVector S k w) = 0)
    (γ dγ : ℝ → TailSumSpace q S)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (dγ t) t)
    (hinto : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hnonzero : ∀ t ∈ Icc (0 : ℝ) 1, HeadNonzero S (γ t))
    (ha : ∀ t : ℝ, headActions S (γ t) = headActions S (γ 0)) : G (γ 1) = G (γ 0) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt (fun s => G (γ s)) 0 t := by
    have hact : HasDerivAt (fun s => headActions S (γ s)) 0 t := by
      simpa only [ha] using hasDerivAt_const t (headActions S (γ 0))
    obtain ⟨htail,hhead⟩ := headActionTangent_of_hasDerivAt S γ (dγ t) t (hγ t ht) hact
    have hzero := clm_headActionTangent_eq_zero S (γ t) (dγ t) (fderiv ℂ G (γ t))
      (hnonzero t ht) (hrot _ (hinto t ht)) htail hhead
    have hdf := ((hG _ (hinto t ht)).differentiableAt (hU.mem_nhds (hinto t ht))).hasFDerivAt.restrictScalars ℝ
    have hc := hdf.comp_hasDerivAt (f := γ) t (hγ t ht)
    change HasDerivAt (fun s => G (γ s)) (fderiv ℂ G (γ t) (dγ t)) t at hc
    simpa only [hzero] using hc
  have hm := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (hd t ht).differentiableAt)
    (fun t ht => by rw [(hd t ht).deriv]; simp : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (fun s => G (γ s)) t‖ ≤ (0 : ℝ))
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hm) (norm_nonneg _)))

end NLS.Coeff
