import NLS.KdV.HillHminusOneRootRegions

/-! # Exact central characteristic counts in H^-1

Uniform exterior confinement gives actual zero-free source separators.
Reality excludes the nonreal part of the diameter circle. Homotopy then
retains the exact free count 2*N-1, including multiple central roots.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- Actual source-path control, supplied by the proved H^-1 exterior
estimates rather than by an assumed list of central eigenvalues. -/
structure HillHminusCentralControl (q : PeriodOneHminusOne) (N : ℕ) : Prop where
  index_ge_two : 2 ≤ N
  roots_lower : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ,
    hillHminusRadicand ((s : ℂ) • q) z = 0 → -(N : ℝ)^2 < z.re
  separator_free : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, z.re = hillCentralSeparator N →
    hillHminusRadicand ((s : ℂ) • q) z ≠ 0

theorem analyticOnNhd_hillHminusRadicand (q : PeriodOneHminusOne) :
    AnalyticOnNhd ℂ (hillHminusRadicand q) univ := by
  intro z _
  exact (analyticOnNhd_hillHminusRadicand_joint (z,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

theorem HillHminusCentralControl.root_lower
    {q : PeriodOneHminusOne} {N : ℕ} (h : HillHminusCentralControl q N)
    (z : ℂ) (hz : hillHminusRadicand q z = 0) : -(N : ℝ)^2 < z.re := by
  simpa only [ofReal_one,one_smul] using h.roots_lower 1 (by norm_num) z (by simpa using hz)

theorem HillHminusCentralControl.separator_ne_zero
    {q : PeriodOneHminusOne} {N : ℕ} (h : HillHminusCentralControl q N)
    (z : ℂ) (hz : z.re = hillCentralSeparator N) : hillHminusRadicand q z ≠ 0 := by
  simpa only [ofReal_one,one_smul] using h.separator_free 1 (by norm_num) z hz

theorem exists_hillHminus_central_controls (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ J : ℕ, N ≤ J → ∀ a ∈ V, HillHminusCentralControl a J := by
  obtain ⟨N,V,hN,hV,hq,hsep⟩ := exists_hillHminus_zero_free_source_separators q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro J hJ a ha
  refine ⟨hN.trans hJ,?_,?_⟩
  · intro s hs z hz
    by_contra! h
    exact hsep J hJ a ha s hs z (Or.inl h) hz
  · intro s hs z hz
    exact hsep J hJ a ha s hs z (Or.inr hz)

theorem hillHminusRadicand_free_central_count (N : ℕ) (hN : 2 ≤ N) :
    analyticZeroCount (hillHminusRadicand 0) (hillCentralDisc N) = 2*N-1 := by
  have he : hillHminusRadicand 0 = hillL2Radicand 0 := by
    funext z
    simpa only [map_zero] using hillHminusRadicand_eq_hillL2 (0 : Coeff 2) z
  rw [he]
  exact hillL2Radicand_free_central_count N hN

theorem HillHminusCentralControl.ne_zero_on_central_sphere
    {q : PeriodOneHminusOne} {N : ℕ} (h : HillHminusCentralControl q N)
    (hq : IsRealPeriodOneHminusOne q) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (z : ℂ) (hz : z ∈ sphere (hillCentralCenter N) (hillCentralRadius N)) :
    hillHminusRadicand ((s : ℂ) • q) z ≠ 0 := by
  apply ne_zero_on_realDiameter_sphere (hillHminusRadicand ((s : ℂ) • q))
    (-(N : ℝ)^2) (hillCentralSeparator N)
    (by linarith [hillCentralSeparator_pos N h.index_ge_two,sq_nonneg (N : ℝ)])
    (fun w hw => hillHminusRadicand_root_im_zero _ (hq.smul_real s) w hw) ?_ ?_ z hz
  · intro he
    have hh := h.roots_lower s hs _ he
    simp only [ofReal_re] at hh
    exact (lt_irrefl _ hh)
  · exact h.separator_free s hs _ rfl

/-- Exact physical central count, with one simple free lowest root and
N-1 free double roots continued along the actual H^-1 source path. -/
theorem HillHminusCentralControl.central_count
    {q : PeriodOneHminusOne} {N : ℕ} (h : HillHminusCentralControl q N)
    (hq : IsRealPeriodOneHminusOne q) :
    analyticZeroCount (hillHminusRadicand q) (hillCentralDisc N) = 2*N-1 := by
  let F : Icc (0 : ℝ) 1 → ℂ → ℂ := fun t z => hillHminusRadicand ((t.val : ℂ) • q) z
  have hcont : Continuous F.uncurry := by
    have hc : Continuous (fun p : ℂ × PeriodOneHminusOne => hillHminusRadicand p.2 p.1) :=
      analyticOnNhd_hillHminusRadicand_joint.continuous
    have hm : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ => (p.2,(p.1.val : ℂ) • q)) := by
      have ht : Continuous (fun p : Icc (0 : ℝ) 1 × ℂ => (p.1.val : ℂ)) :=
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
      exact continuous_snd.prodMk (ht.smul continuous_const)
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusRadicand p.2 p.1)
      (f := fun p : Icc (0 : ℝ) 1 × ℂ => (p.2,(p.1.val : ℂ) • q)) hc hm
  have hana (t : Icc (0 : ℝ) 1) : AnalyticOnNhd ℂ (F t) (hillCentralDisc N) := by
    intro z _
    exact (analyticOnNhd_hillHminusRadicand_joint (z,(t.val : ℂ) • q) (mem_univ _)).comp
      (f := fun z : ℂ => (z,(t.val : ℂ) • q)) (analyticAt_id.prod analyticAt_const)
  have he := analyticZeroCount_eq_of_homotopy F (hillCentralCenter N) (hillCentralRadius N)
    (hillCentralRadius_pos N h.index_ge_two) hcont.continuousOn hana
    (fun t z hz => h.ne_zero_on_central_sphere hq t.val t.property z hz)
    (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1) (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)
  have he' : analyticZeroCount (hillHminusRadicand q) (hillCentralDisc N) =
      analyticZeroCount (hillHminusRadicand 0) (hillCentralDisc N) := by
    simpa only [hillCentralDisc,F,ofReal_one,one_smul,ofReal_zero,zero_smul] using he
  exact he'.trans (hillHminusRadicand_free_central_count N h.index_ge_two)

theorem HillHminusCentralControl.central_interval_count
    {q : PeriodOneHminusOne} {N : ℕ} (h : HillHminusCentralControl q N)
    (hq : IsRealPeriodOneHminusOne q) :
    analyticZeroCount (hillHminusRadicand q)
      {z : ℂ | z.im = 0 ∧ z.re ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N)} = 2*N-1 := by
  rw [← h.central_count hq]
  apply analyticZeroCount_congr_set
  intro z hz
  have him := hillHminusRadicand_root_im_zero q hq z hz
  have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  have hlo : -(N : ℝ)^2 < z.re := by
    simpa only [ofReal_one,one_smul] using h.roots_lower 1 (by norm_num) z (by simpa using hz)
  have hne : z.re ≠ hillCentralSeparator N := by
    intro hc
    exact h.separator_free 1 (by norm_num) z hc (by simpa using hz)
  rw [← he,ofReal_mem_hillCentralDisc_iff]
  simp only [ofReal_re,ofReal_im,mem_ofPred_eq,true_and,mem_Ioo,mem_Icc]
  exact ⟨fun hh => ⟨hh.1.le,hh.2.le⟩,fun hh => ⟨hlo,lt_of_le_of_ne hh.2 hne⟩⟩

end NLS.KdV
