import NLS.SequenceSpaces.BoundedCoordinateTaylor

/-!
# Assembling Taylor coefficients from finite Fourier truncations

The uniformly bounded finite-truncation Taylor coefficients stabilize at
each Fourier coordinate. This permits their assembly into multilinear
maps with values in `ℓq`.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal ContDiff
namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A retained coordinate of a finite truncation has the same Taylor
coefficient as the scalar coordinate of the original map. -/
theorem complexTaylorSeries_truncate_apply_of_mem
    (f : E → Coeff q) (c : E) (s : Finset ℤ) (n : ℤ) (hn : n ∈ s)
    (k : ℕ) (hs : ContDiffAt ℂ k (fun x : E => truncate s (f x)) c)
    (v : Fin k → E) :
    (NLS.ComplexAnalysis.complexTaylorSeries
      (fun x : E => truncate s (f x)) c k v) n =
    NLS.ComplexAnalysis.complexTaylorSeries (fun x : E => f x n) c k v := by
  let ev : Coeff q →L[ℂ] ℂ := lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n
  have hfun : ev ∘ (fun x : E => truncate s (f x)) = (fun x : E => f x n) := by
    funext x
    change (truncate s (f x)) n = f x n
    simp [hn]
  have hder := ev.iteratedFDeriv_comp_left (i := k) hs (by exact_mod_cast (le_refl k))
  rw [hfun] at hder
  have hbase : ((iteratedFDeriv ℂ k (fun x : E => truncate s (f x)) c) v) n =
      (iteratedFDeriv ℂ k (fun x : E => f x n) c) v := by
    rw [hder]
    rfl
  simp only [NLS.ComplexAnalysis.complexTaylorSeries, smul_apply]
  rw [lp.coeFn_smul, Pi.smul_apply]
  rw [hbase]

/-- Every Taylor order of a locally bounded coordinatewise analytic map
has an `ℓq`-valued continuous multilinear coefficient. Its norm bound
is inherited from the finite truncations. -/
theorem exists_taylor_coefficient_of_bounded_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M)
    (c : E) (hc : c ∈ V) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ V ∧
      ∀ k : ℕ, ∃ A : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) (Coeff q),
        (∀ v : Fin k → E, ∀ n : ℤ,
          A v n = NLS.ComplexAnalysis.complexTaylorSeries
            (fun x : E => f x n) c k v) ∧
        ‖A‖ ≤ (4*Real.exp 1/R)^k*M := by
  classical
  obtain ⟨R,hR,hball,huniform⟩ :=
    exists_uniform_truncate_taylor_bound f hVopen hcoord M hbound c hc
  refine ⟨R,hR,hball,?_⟩
  intro k
  let C : ℝ := (4*Real.exp 1/R)^k*M
  have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
  have hC : 0 ≤ C := mul_nonneg (by positivity) hM
  let g (s : Finset ℤ) : E → Coeff q := fun x => truncate s (f x)
  let A (s : Finset ℤ) : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) (Coeff q) :=
    NLS.ComplexAnalysis.complexTaylorSeries (g s) c k
  have hsmooth (s : Finset ℤ) : ContDiffAt ℂ k (g s) c := by
    have hs : ContDiffOn ℂ ∞ (g s) V :=
      (analyticOnNhd_truncate_of_coordinatewise f hcoord s).contDiffOn_of_completeSpace
    exact (hs.contDiffAt (hVopen.mem_nhds hc)).of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have hAnorm (s : Finset ℤ) : ‖A s‖ ≤ C := huniform s k
  have hpoint (v : Fin k → E) (s : Finset ℤ) :
      ‖A s v‖ ≤ C * ∏ i, ‖v i‖ :=
    ((A s).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hAnorm s) (by positivity))
  have hdir (v : Fin k → E) : ∃ D : Coeff q,
      (∀ n : ℤ, D n = NLS.ComplexAnalysis.complexTaylorSeries
        (fun x : E => f x n) c k v) ∧
      ‖D‖ ≤ C * ∏ i, ‖v i‖ := by
    have hcoordlim (n : ℤ) :
        Tendsto (fun s : Finset ℤ => A s v n) atTop
          (𝓝 (NLS.ComplexAnalysis.complexTaylorSeries
            (fun x : E => f x n) c k v)) := by
      have hev : ∀ᶠ s : Finset ℤ in atTop,
          A s v n = NLS.ComplexAnalysis.complexTaylorSeries
            (fun x : E => f x n) c k v := by
        filter_upwards [eventually_ge_atTop ({n} : Finset ℤ)] with s hs
        exact complexTaylorSeries_truncate_apply_of_mem f c s n (hs (by simp)) k
          (hsmooth s) v
      exact tendsto_nhds_of_eventually_eq hev
    have hlim : Tendsto (id fun s : Finset ℤ => A s v :
        Finset ℤ → ∀ n : ℤ, ℂ) atTop
        (𝓝 (fun n : ℤ => NLS.ComplexAnalysis.complexTaylorSeries
          (fun x : E => f x n) c k v)) := by
      rw [tendsto_pi_nhds]
      exact hcoordlim
    have hbounded : Bornology.IsBounded (Set.range (fun s : Finset ℤ => A s v)) := by
      apply isBounded_iff_forall_norm_le.mpr
      exact ⟨C * ∏ i, ‖v i‖, by rintro _ ⟨s,rfl⟩; exact hpoint v s⟩
    have hmem : Memℓp (fun n : ℤ => NLS.ComplexAnalysis.complexTaylorSeries
        (fun x : E => f x n) c k v) q :=
      lp.memℓp_of_tendsto hbounded hlim
    let D : Coeff q := ⟨_,hmem⟩
    refine ⟨D,fun n => rfl,?_⟩
    exact lp.norm_le_of_tendsto (Filter.Eventually.of_forall (hpoint v)) hlim
  let D (v : Fin k → E) : Coeff q := Classical.choose (hdir v)
  have hDapply (v : Fin k → E) (n : ℤ) :
      D v n = NLS.ComplexAnalysis.complexTaylorSeries
        (fun x : E => f x n) c k v :=
    (Classical.choose_spec (hdir v)).1 n
  have hDbound (v : Fin k → E) : ‖D v‖ ≤ C * ∏ i, ‖v i‖ :=
    (Classical.choose_spec (hdir v)).2
  let L₀ : MultilinearMap ℂ (fun _ : Fin k => E) (Coeff q) := {
    toFun := D
    map_update_add' := by
      intro _ v i x y
      ext n
      change D (Function.update v i (x+y)) n =
        D (Function.update v i x) n + D (Function.update v i y) n
      rw [hDapply, hDapply, hDapply]
      exact (NLS.ComplexAnalysis.complexTaylorSeries
        (fun z : E => f z n) c k).map_update_add v i x y
    map_update_smul' := by
      intro _ v i a x
      ext n
      change D (Function.update v i (a • x)) n = a • D (Function.update v i x) n
      rw [hDapply, hDapply]
      exact (NLS.ComplexAnalysis.complexTaylorSeries
        (fun z : E => f z n) c k).map_update_smul v i a x }
  let L : ContinuousMultilinearMap ℂ (fun _ : Fin k => E) (Coeff q) :=
    L₀.mkContinuous C hDbound
  refine ⟨L,?_,?_⟩
  · intro v n
    exact hDapply v n
  · exact L₀.mkContinuous_norm_le hC hDbound

end NLS.Coeff
