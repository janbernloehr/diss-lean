import NLS.ZakharovShabat.L2PeriodicEquation

/-! # Uniqueness and full-time regularity of the periodic L2 fundamental solution -/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

@[simp] theorem l2PeriodicColumn_nat (u : IntervalPairL2) (z : ℂ) (j : Fin 2) (n : ℕ) :
    l2PeriodicColumn u z j n = ((l2Monodromy u z ^ n) 0 j,(l2Monodromy u z ^ n) 1 j) := by
  simp only [l2PeriodicColumn,max_eq_left (Nat.cast_nonneg n),l2PeriodicFundamentalMatrix_nat]

/-- Each real-variable column is continuous, including all joins and its value at zero. -/
theorem continuous_l2PeriodicColumn (u : IntervalPairL2) (z : ℂ) (j : Fin 2) :
    Continuous (l2PeriodicColumn u z j) := by
  have hc : Continuous (fun x : ℝ => ((z,u),
      (⟨max x 0,by change 0 ≤ max x 0; exact le_max_right _ _⟩ : Ici (0 : ℝ)))) :=
    continuous_const.prodMk ((continuous_id.max continuous_const).subtype_mk _)
  have hM := continuous_l2PeriodicFundamentalMatrix_joint.comp hc
  exact (hM.matrix_elem 0 j).prodMk (hM.matrix_elem 1 j)

/-- The continuous solution of the actual integral equation on successive periods is unique.
The integral hypothesis supplies the absolute-continuity information that an a.e. ODE alone lacks. -/
theorem l2PeriodicColumn_unique (u : IntervalPairL2) (z : ℂ) (j : Fin 2)
    (w : ℝ → ℂ × ℂ) (hw : Continuous w)
    (h0 : w 0 = l2PeriodicColumn u z j 0)
    (he : ∀ (n : ℕ) (s : Icc (0 : ℝ) 1),
      w (n+s.val) = w n+∫ r in (0 : ℝ)..s.val,
        classicalODECoefficient (intervalL2Representative u r) z (w (n+r))) :
    EqOn w (l2PeriodicColumn u z j) (Ici (0 : ℝ)) := by
  have hperiod (n : ℕ) (hn : w n = l2PeriodicColumn u z j n) :
      ∀ s : Icc (0 : ℝ) 1, w (n+s.val) = l2PeriodicColumn u z j (n+s.val) := by
    let W : Curve (ℂ × ℂ) := ⟨fun s => w (n+s.val),
      hw.comp (continuous_const.add continuous_subtype_val)⟩
    let v := ((l2Monodromy u z ^ n) 0 j,(l2Monodromy u z ^ n) 1 j)
    have hi : w n = v := hn.trans (l2PeriodicColumn_nat u z j n)
    have hW : ∀ s, W s = v+l2ODEIntegral u z W s := by
      intro s
      change w (n+s.val) = _
      rw [he n s,hi]
      congr 1
      apply intervalIntegral.integral_congr
      intro r hr
      have hr' : r ∈ Icc (0 : ℝ) 1 := by
        rw [uIcc_of_le s.property.1] at hr
        exact ⟨hr.1,hr.2.trans s.property.2⟩
      have hwr : extend W r = w (n+r) := extend_coe W ⟨r,hr'⟩
      dsimp only
      rw [hwr]
    have hunique := l2SolutionCurve_unique_integral u z v W hW
    intro s
    have hcol := l2PeriodicColumn_on_period u z j n (n+s.val)
      (by constructor <;> linarith [s.property.1,s.property.2])
    rw [add_sub_cancel_left,extend_coe _ s] at hcol
    exact (congrArg (fun f : Curve (ℂ × ℂ) => f s) hunique).trans hcol.symm
  have hnat (n : ℕ) : w n = l2PeriodicColumn u z j n := by
    induction n with
    | zero => simpa only [Nat.cast_zero] using h0
    | succ n ih =>
      have h := hperiod n ih ⟨1,by constructor <;> norm_num⟩
      simpa only [Nat.cast_add,Nat.cast_one] using h
  intro x hx
  let n := ⌊x⌋₊
  have hs : x-(n : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le hx),by have h := Nat.lt_floor_add_one x; dsimp [n]; linarith⟩
  simpa only [add_sub_cancel] using hperiod n (hnat n) ⟨x-n,hs⟩

/-- The full-domain regularity recalled in the introduction of Appendix G.
The matrix is the periodic continuation identified with the actual integral equation,
not the endpoint-clamped continuation of a continuous coefficient curve. -/
theorem sourceFundamentalSolution_regularity :
    Continuous (fun p : Ici (0 : ℝ) × (ℂ × IntervalPairL2) =>
      l2PeriodicFundamentalMatrix p.2.2 p.2.1 p.1) ∧
    ∀ t : Ici (0 : ℝ), AnalyticOnNhd ℂ
      (fun q : ℂ × IntervalPairL2 => l2PeriodicFundamentalMatrix q.2 q.1 t) univ := by
  have hc : Continuous (fun p : Ici (0 : ℝ) × (ℂ × IntervalPairL2) => (p.2,p.1)) := continuous_swap
  have h := continuous_l2PeriodicFundamentalMatrix_joint.comp hc
  exact ⟨h,analyticOnNhd_l2PeriodicFundamentalMatrix_joint⟩

end NLS.ZakharovShabat
