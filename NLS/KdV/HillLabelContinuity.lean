import NLS.KdV.HillCumulativeCounts

/-! # Continuity of the intrinsic real Hill labels

Cumulative characteristic counts stabilize on every diameter circle
whose limiting real endpoint is not a root. Finite ordered count
stability then proves continuity of each label in the actual L2 topology,
including at a closed gap.
-/

noncomputable section
open Set Metric Filter Topology
open scoped Classical
namespace NLS.KdV

theorem HillRealCharacteristicLabeling.ne_zero_of_not_central_value
    {q : WeightedCoeff SpectralWeight.one.toWeight 2} {N : ℕ} {lambda : ℕ → ℝ}
    (h : HillRealCharacteristicLabeling q N lambda)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (c : ℝ) (hc : c < hillCentralSeparator N)
    (hnot : c ∉ (Finset.range (2*N-1)).image lambda) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) c ≠ 0 := by
  intro hd
  obtain ⟨j,hj⟩ := (h.roots c).mp hd
  have he : lambda j = c := (Complex.ofReal_injective hj).symm
  by_cases hjl : j < 2*N-1
  · exact hnot (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hjl,he⟩)
  · have hh := h.tail_above_separator hq j (by omega)
    rw [he] at hh
    linarith

/-- Continuous real L2 potential families have continuous ordered
characteristic labels. No simplicity or open-gap hypothesis is required. -/
theorem continuousAt_hillRealLabels_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hreal : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t))) (t0 : T) (j : ℕ) :
    ContinuousAt (fun t => hillRealLabels (Q t) (hq t) (hreal t) j) t0 := by
  let N := max (j+2) (2+⌈8*‖Q t0‖⌉₊)
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hj : j < 2*N-1 := by dsimp [N]; omega
  have hcut0 : 8*‖Q t0‖ < (N : ℝ) := by
    have hc := Nat.le_ceil (8*‖Q t0‖)
    have hn : (2+⌈8*‖Q t0‖⌉₊ : ℕ) ≤ N := le_max_right _ _
    have hn' : (2 : ℝ)+(⌈8*‖Q t0‖⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    linarith
  have hevent : ∀ᶠ t in 𝓝 t0, 8*‖Q t‖ < (N : ℝ) :=
    (continuous_const.mul hQ.norm).continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds hcut0)
  let labels (t : T) := hillRealLabels (Q t) (hq t) (hreal t)
  have hs0 := hillRealLabels_spec_at (Q t0) (hq t0) (hreal t0) N hN hcut0.le
  let F : T → ℂ → ℂ := fun t z => hillL2Radicand (SpectralWeight.one.toCoeff (Q t)) z
  have hF : Continuous F.uncurry := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Radicand p.2 p.1) :=
      continuous_iff_continuousAt.mpr
        (fun p => (analyticOnNhd_hillL2Radicand_joint p (mem_univ _)).continuousAt)
    have hm : Continuous (fun p : T × ℂ => (p.2,SpectralWeight.one.toCoeff (Q p.1))) :=
      continuous_snd.prodMk ((SpectralWeight.one.toCoeff.continuous.comp hQ).comp continuous_fst)
    dsimp only [F, Function.uncurry]
    convert! hc.comp hm using 1
  apply NLS.tendsto_ordered_finite_of_counts (2*N-1) labels (labels t0)
    (-(N : ℝ)^2) (hillCentralSeparator N)
    (fun t i _ k _ hik => monotone_hillRealLabels (Q t) (hq t) (hreal t) hik)
    (fun i _ k _ hik => hs0.monotone hik) hs0.central_mem ?_ j hj
  intro c hc hnot
  have hnc := hs0.ne_zero_of_not_central_value (hq t0) c hc.2 hnot
  have hr : 0 < (c-(-(N : ℝ)^2))/2 := by linarith [hc.1]
  have hb : ∀ z ∈ sphere (((-(N : ℝ)^2+c)/2 : ℝ) : ℂ) ((c-(-(N : ℝ)^2))/2), F t0 z ≠ 0 := by
    apply ComplexAnalysis.ne_zero_on_realDiameter_sphere
      (hillL2Radicand (SpectralWeight.one.toCoeff (Q t0))) (-(N : ℝ)^2) c hc.1.le
      (fun z hz => hillL2Discriminant_root_im_zero _ (hq t0) (hreal t0) z (sub_eq_zero.mp hz))
      ?_ hnc
    intro hd
    have hh := hillL2Radicand_re_lower_bound (Q t0) (hq t0) N (by omega)
      (by linarith [norm_nonneg (Q t0)]) _ hd
    exact lt_irrefl _ hh
  have hstable := ComplexAnalysis.eventually_analyticZeroCount_eq_of_continuous_family F
    (((-(N : ℝ)^2+c)/2 : ℝ) : ℂ) ((c-(-(N : ℝ)^2))/2) hr hF.continuousOn
    (fun t => (analyticOnNhd_hillL2Radicand _).mono (subset_univ _)) t0 hb
  filter_upwards [hstable,hevent] with t ht hct
  have hs := hillRealLabels_spec_at (Q t) (hq t) (hreal t) N hN hct.le
  have hc0 := hs0.cumulative_count (hq t0) (hreal t0) c hc.2.le
  have hct' := hs.cumulative_count (hq t) (hreal t) c hc.2.le
  exact hct'.symm.trans (ht.trans hc0)

theorem continuous_hillRealLabels_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t) ∈ Coeff.paritySubspace 0)
    (hreal : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t))) (j : ℕ) :
    Continuous (fun t => hillRealLabels (Q t) (hq t) (hreal t) j) :=
  continuous_iff_continuousAt.mpr (fun t => continuousAt_hillRealLabels_family Q hQ hq hreal t j)

/-- The real period-one coefficient domain, with its inherited L2 norm topology. -/
abbrev RealPeriodOneHillPotential := {q : WeightedCoeff SpectralWeight.one.toWeight 2 //
  SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0 ∧
    IsRealHillPotential (SpectralWeight.one.toCoeff q)}

theorem continuous_hillRealLabels (j : ℕ) :
    Continuous (fun q : RealPeriodOneHillPotential => hillRealLabels q.val q.property.1 q.property.2 j) :=
  continuous_hillRealLabels_family Subtype.val continuous_subtype_val
    (fun q => q.property.1) (fun q => q.property.2) j

end NLS.KdV
