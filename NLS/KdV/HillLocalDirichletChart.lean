import NLS.KdV.HillUniformComplexDirichlet
import NLS.KdV.HillComplexLowGapPairs

/-! # Fixed-gap analytic Dirichlet charts near the free potential

Compact boundary stability preserves the free simple Dirichlet zero count.
The existing logarithmic-moment root is thereby analytic on a genuine
complex source neighborhood, with its complete uniqueness statement.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillScaledDirichlet_local_zero_count
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧ ∀ p ∈ V,
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)), hillL2DirichletCharacteristic p E ≠ 0) ∧
      analyticZeroCount (hillL2DirichletCharacteristic p) (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))) = 1 := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  have hR : 0 < R := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1)
  have hcont : Continuous (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticOnNhd_hillL2DirichletCharacteristic_joint t (mem_univ _)).continuousAt)
  have hbase (E : ℂ) (hE : E ∈ sphere c R) : hillL2DirichletCharacteristic 0 E ≠ 0 := by
    intro hz
    have he := hillScaledFreeGapContour_zero_unique h0q h0r ρ hρ1 k hk E
      (sphere_subset_closedBall hE) (hillL2DirichletCharacteristic_free_zero_imp_radicand E hz)
    have hd := mem_sphere.mp hE
    rw [he,dist_self] at hd
    linarith
  let D : Set (ℂ × Coeff 2) := {t | hillL2DirichletCharacteristic t.2 t.1 ≠ 0}
  have hD : IsOpen D := isOpen_ne_fun hcont continuous_const
  have hb : sphere c R ×ˢ {(0 : Coeff 2)} ⊆ D := by
    rintro ⟨E,p⟩ ⟨hE,hp⟩
    have hp0 : p = 0 := hp
    subst p
    exact hbase E hE
  obtain ⟨U,V,_,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma (isCompact_sphere c R) isCompact_singleton hD hb
  have hc : Continuous (Function.uncurry (fun p : Coeff 2 => hillL2DirichletCharacteristic p)) := by
    apply (hcont.comp (continuous_swap : Continuous (Prod.swap : Coeff 2 × ℂ → ℂ × Coeff 2))).congr
    intro t
    rfl
  have hcount := eventually_analyticZeroCount_eq_of_continuous_family
    (fun p : Coeff 2 => hillL2DirichletCharacteristic p) c R hR hc.continuousOn
    (fun p => (analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _)) 0 hbase
  obtain ⟨W,hWsub,hW,h0W⟩ := _root_.mem_nhds_iff.mp hcount
  refine ⟨V ∩ W,hV.inter hW,⟨h0V (mem_singleton _),h0W⟩,?_⟩
  intro p hp
  refine ⟨?_,(hWsub hp.2).trans (hillScaledFreeGapContour_zero_counts h0q h0r ρ hρ hρ1 k hk).2⟩
  intro E hE
  have hEP : (E,p) ∈ U ×ˢ V := ⟨hKU hE,hp.1⟩
  have hDP : (E,p) ∈ D := hUV hEP
  exact hDP

theorem exists_hillScaledDirichlet_local_roots
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧ ∀ p ∈ V,
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)), hillL2DirichletCharacteristic p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
        hillL2DirichletCharacteristic p a = 0 ∧
        analyticOrderAt (hillL2DirichletCharacteristic p) a = 1 ∧
        (∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          analyticOrderNatAt (hillL2DirichletCharacteristic p) E = if E=a then 1 else 0) ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          hillL2DirichletCharacteristic p E = 0 ↔ E=a := by
  obtain ⟨V,hV,h0V,hcount⟩ := exists_hillScaledDirichlet_local_zero_count h0q h0r k hk ρ hρ hρ1
  refine ⟨V,hV,h0V,?_⟩
  intro p hp
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  have hR : 0 < R := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1)
  obtain ⟨hb,hc⟩ := hcount p hp
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have ha := (analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ (closedBall c R))
  have hfinite (E : ℂ) (hE : E ∈ closedBall c R) : analyticOrderAt (hillL2DirichletCharacteristic p) E ≠ ⊤ :=
    analyticOrderAt_ne_top_on_connected (isConnected_closedBall hR.le).isPreconnected ha
      (sphere_subset_closedBall hw) (hb w hw) hE
  obtain ⟨a,haK,haz,hm⟩ := exists_one_analytic_zero
    (analyticZeroCount_hasFiniteSupport (isCompact_closedBall c R) (isConnected_closedBall hR.le) ha
      (sphere_subset_closedBall hw) (hb w hw)) hc
  have haB : a ∈ ball c R := lt_of_le_of_ne haK (fun he => hb a he haz)
  have horder : analyticOrderAt (hillL2DirichletCharacteristic p) a = 1 := by
    have hh : analyticOrderNatAt (hillL2DirichletCharacteristic p) a = 1 := by simpa only [if_pos haK,ite_true] using hm a
    have ht := congrArg (fun n : ℕ => (n : ℕ∞)) hh
    simpa only [Nat.cast_analyticOrderNatAt (hfinite a haK),Nat.cast_one] using ht
  refine ⟨hb,a,haB,haz,horder,fun E hE => by
    have hE' : E ∈ closedBall c R := hE
    simpa only [if_pos hE'] using hm E,?_⟩
  intro E hE
  constructor
  · intro hz
    have hpos := analyticOrderNatAt_pos_of_zero (ha E hE) (hfinite E hE) hz
    have hh := hm E
    rw [if_pos hE] at hh
    by_contra he
    rw [if_neg he] at hh
    omega
  · rintro rfl
    exact haz


theorem exists_hillScaledDirichletRoot_local_analytic_chart
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧
      AnalyticOnNhd ℂ (hillScaledDirichletRoot h0q h0r ρ k) (V) ∧
      ∀ p ∈ V,
        hillScaledDirichletRoot h0q h0r ρ k p ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) ∧
        hillL2DirichletCharacteristic p (hillScaledDirichletRoot h0q h0r ρ k p)=0 ∧
        analyticOrderAt (hillL2DirichletCharacteristic p) (hillScaledDirichletRoot h0q h0r ρ k p)=1 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          hillL2DirichletCharacteristic p E=0 ↔ E=hillScaledDirichletRoot h0q h0r ρ k p := by
  obtain ⟨V,hV,h0V,hroots⟩ := exists_hillScaledDirichlet_local_roots h0q h0r k hk ρ hρ hρ1
  have hR := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1)
  have han := analyticOnNhd_logarithmicCircleMoment
    (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) analyticOnNhd_hillL2DirichletCharacteristic_joint
    (hillRealGapCenter 0 h0q h0r k : ℂ)
    (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) hR.le 1 hV
    (fun p hp => (hroots p hp).1)
  refine ⟨V,hV,h0V,han,?_⟩
  intro p hp
  obtain ⟨hb,a,ha,haz,horder,hm,hunique⟩ := hroots p hp
  have he : hillScaledDirichletRoot h0q h0r ρ k p=a := by
    exact (logarithmicCircleMoment_eq_single_root_power
      (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) p hR 1
      ((analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _)) hb ha hm).trans (pow_one a)
  rw [he]
  exact ⟨ha,haz,horder,hunique⟩


end NLS.KdV
