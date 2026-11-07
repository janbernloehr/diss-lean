import NLS.Articles.DNLSEstimates.SpectralConnectedness
import NLS.ZakharovShabat.PeriodicDiscriminantSpectralData
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.TotallyDisconnected
import NLS.ZakharovShabat.SourceIsolatingDomainCounterexample

/-!
# A double spectral point has no surface chart

The topology is the original subspace topology. A punctured complex disc
is connected, whereas the two branches at a node have the continuous,
discrete-valued label `w / b(z)`. Both labels occur in every neighborhood
of the node, ruling out even a topological surface chart there.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat
open scoped ENNReal Manifold ContDiff
namespace NLS.Articles.DNLSEstimates

/-- A punctured complex disc is connected, by transporting the punctured
plane through the explicit radial homeomorphism onto a disc. -/
theorem complex_punctured_ball_preconnected (c : ℂ) (r : ℝ) (hr : 0 < r) :
    IsPreconnected (ball c r \ {c}) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall c r
  have hinj : Function.Injective e := fun x y h =>
    e.injOn (by simp [e]) (by simp [e]) h
  have he : e '' ({0}ᶜ : Set ℂ) = ball c r \ {c} := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · simpa only [e, OpenPartialHomeomorph.univBall_target c hr] using e.map_source (by simp [e] : x ∈ e.source)
      · intro hy
        have heq : e x = e 0 := by simpa only [mem_singleton_iff,e,OpenPartialHomeomorph.univBall_apply_zero] using hy
        exact hx (hinj heq)
    · intro hy
      have hyt : y ∈ e.target := by simpa only [e, OpenPartialHomeomorph.univBall_target c hr] using hy.1
      refine ⟨e.symm y,?_,e.right_inv hyt⟩
      intro hzero
      have hz : e.symm y = 0 := hzero
      have h := e.right_inv hyt
      rw [hz] at h
      exact hy.2 (by simpa [e] using h.symm)
  rw [← he]
  have hdim : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank]
    norm_num
  exact (isConnected_compl_singleton_of_one_lt_rank hdim (0 : ℂ)).isPreconnected.image e
    (OpenPartialHomeomorph.continuous_univBall c r).continuousOn

/-- Two local branches meeting only at the base preclude a complex chart.
The assertion concerns arbitrary homeomorphic charts, without imposing
analyticity on their coordinate maps. -/
theorem doubleCover_no_chart_of_crossing (f b : ℂ → ℂ) (z : ℂ) (hz : f z = 0)
    (V : Set ℂ) (hV : IsOpen V) (hzV : z ∈ V) (hb : ContinuousOn b V) (hbz : b z = 0)
    (hzero : ∀ x ∈ V, b x = 0 → x = z)
    (hbranches : ∀ x ∈ V, ∀ w : ℂ, (x,w) ∈ doubleCover f ↔ w = b x ∨ w = -b x)
    (e : OpenPartialHomeomorph (doubleCover f) ℂ) :
    (⟨(z,0),by change (0 : ℂ)^2 = f z; simp [hz]⟩ : doubleCover f) ∉ e.source := by
  classical
  let q : doubleCover f := ⟨(z,0),by change (0 : ℂ)^2 = f z; simp [hz]⟩
  intro hq
  change q ∈ e.source at hq
  let O : Set (doubleCover f) := {x | x.val.1 ∈ V}
  have hO : IsOpen O := hV.preimage (continuous_fst.comp continuous_subtype_val)
  have hqO : q ∈ O := hzV
  have hnb : e.target ∩ e.symm ⁻¹' O ∈ 𝓝 (e q) :=
    inter_mem (e.open_target.mem_nhds (e.map_source hq))
      ((e.continuousAt_symm (e.map_source hq)).preimage_mem_nhds
        (by simpa only [e.left_inv hq] using hO.mem_nhds hqO))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnb
  let S : Set ℂ := ball (e q) r \ {e q}
  have hSt (u : ℂ) (hu : u ∈ S) : u ∈ e.target := (hball hu.1).1
  have hSV (u : ℂ) (hu : u ∈ S) : (e.symm u).val.1 ∈ V := (hball hu.1).2
  have hnonzero (u : ℂ) (hu : u ∈ S) : b (e.symm u).val.1 ≠ 0 := by
    intro hzero'
    have hx := hzero _ (hSV u hu) hzero'
    have hw := (hbranches _ (hSV u hu) _).mp (e.symm u).property
    have heq : e.symm u = q := by
      apply Subtype.ext
      refine Prod.ext hx ?_
      rcases hw with hw | hw <;> simpa only [hzero',neg_zero] using hw
    have h := e.right_inv (hSt u hu)
    rw [heq] at h
    exact hu.2 h.symm
  let L : ℂ → ℂ := fun u => (e.symm u).val.2 / b (e.symm u).val.1
  have hinv : ContinuousOn (fun u => (e.symm u).val) S :=
    continuous_subtype_val.comp_continuousOn (e.symm.continuousOn.mono hSt)
  have hL : ContinuousOn L S :=
    (continuous_snd.comp_continuousOn hinv).div
      (hb.comp (continuous_fst.comp_continuousOn hinv) hSV) hnonzero
  have hmap : MapsTo L S ({(1 : ℂ),-1} : Set ℂ) := by
    intro u hu
    rcases (hbranches _ (hSV u hu) _).mp (e.symm u).property with h | h
    · change (e.symm u).val.2 / b (e.symm u).val.1 ∈ _
      rw [h,div_self (hnonzero u hu)]
      simp
    · change (e.symm u).val.2 / b (e.symm u).val.1 ∈ _
      rw [h,neg_div,div_self (hnonzero u hu)]
      simp
  have hconst {u v : ℂ} (hu : u ∈ S) (hv : v ∈ S) : L u = L v :=
    (complex_punctured_ball_preconnected (e q) r hr).constant_of_mapsTo
      (Set.toFinite ({(1 : ℂ),-1} : Set ℂ)).isDiscrete hL hmap hu hv
  let B : Bool → ℂ → doubleCover f := fun σ x =>
    if hx : x ∈ V then ⟨(x,if σ then b x else -b x),
      (hbranches x hx _).mpr (by cases σ <;> simp)⟩ else q
  have hBval (σ : Bool) (x : ℂ) (hx : x ∈ V) :
      (B σ x).val = (x,if σ then b x else -b x) := by simp [B,hx]
  have hBbase (σ : Bool) : B σ z = q := by
    apply Subtype.ext
    rw [hBval σ z hzV,hbz]
    cases σ <;> simp [q]
  have hBc (σ : Bool) : ContinuousAt (B σ) z := by
    apply Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
    have hc : ContinuousAt (fun x : ℂ => (x,if σ then b x else -b x)) z := by
      cases σ
      · exact continuousAt_id.prodMk (hb.continuousAt (hV.mem_nhds hzV)).neg
      · exact continuousAt_id.prodMk (hb.continuousAt (hV.mem_nhds hzV))
    apply hc.congr
    filter_upwards [hV.mem_nhds hzV] with x hx
    exact (hBval σ x hx).symm
  have hBnb (σ : Bool) : ∀ᶠ x in 𝓝 z, B σ x ∈ e.source ∧ e (B σ x) ∈ ball (e q) r := by
    have hc0 : ContinuousAt e (B σ z) := by rw [hBbase σ]; exact e.continuousAt hq
    have hc := hc0.comp (f := B σ) (hBc σ)
    have he : e (B σ z) = e q := congrArg e (hBbase σ)
    have h1 : ∀ᶠ x in 𝓝 z, B σ x ∈ e.source := (hBc σ).preimage_mem_nhds (by simpa only [hBbase σ] using e.open_source.mem_nhds hq)
    have h2 : ∀ᶠ x in 𝓝 z, e (B σ x) ∈ ball (e q) r := hc.preimage_mem_nhds
      (by change ball (e q) r ∈ 𝓝 (e (B σ z)); rw [he]; exact isOpen_ball.mem_nhds (mem_ball_self hr))
    exact h1.and h2
  have hfreq : ∃ x : ℂ, x ≠ z ∧ x ∈ V ∧
      (B true x ∈ e.source ∧ e (B true x) ∈ ball (e q) r) ∧
      (B false x ∈ e.source ∧ e (B false x) ∈ ball (e q) r) := by
    have hv : ∀ᶠ x in 𝓝 z, x ∈ V := hV.mem_nhds hzV
    have hh := (hv.and ((hBnb true).and (hBnb false))).filter_mono (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
    obtain ⟨x,hx,hdata⟩ := (eventually_mem_nhdsWithin.and hh).exists
    exact ⟨x,hx,hdata⟩
  obtain ⟨x,hxz,hxV,hplus,hminus⟩ := hfreq
  have hbn : b x ≠ 0 := fun h => hxz (hzero x hxV h)
  have hBS (σ : Bool) (hσ : B σ x ∈ e.source ∧ e (B σ x) ∈ ball (e q) r) :
      e (B σ x) ∈ S := by
    refine ⟨hσ.2,?_⟩
    intro heq
    have hh := e.injOn hσ.1 hq heq
    have hhx := congrArg (fun u : doubleCover f => u.val.1) hh
    rw [hBval σ x hxV] at hhx
    exact hxz hhx
  have hp : L (e (B true x)) = 1 := by
    change (e.symm (e (B true x))).val.2 / b (e.symm (e (B true x))).val.1 = 1
    rw [e.left_inv hplus.1,hBval true x hxV]
    simp [hbn]
  have hm : L (e (B false x)) = -1 := by
    change (e.symm (e (B false x))).val.2 / b (e.symm (e (B false x))).val.1 = -1
    rw [e.left_inv hminus.1,hBval false x hxV]
    simp [hbn]
  have hh := hconst (hBS true hplus) (hBS false hminus)
  rw [hp,hm] at hh
  norm_num at hh

/-- A genuine analytic double zero is not locally homeomorphic to C. -/
theorem doubleCover_double_zero_no_chart (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) (hz : f z = 0) (ho : analyticOrderAt f z = 2)
    (e : OpenPartialHomeomorph (doubleCover f) ℂ) :
    (⟨(z,0),by change (0 : ℂ)^2 = f z; simp [hz]⟩ : doubleCover f) ∉ e.source := by
  obtain ⟨b,hb,hbz,hbd,_,hbranches⟩ := doubleCover_double_branches f z hf ho
  let g := hb.hasStrictDerivAt.localInverse b (deriv b z) z hbd
  have hl : ∀ᶠ x in 𝓝 z, g (b x) = x := HasStrictDerivAt.eventually_left_inverse ..
  have hzero : ∀ᶠ x in 𝓝 z, b x = 0 → x = z := by
    filter_upwards [hl] with x hx hbx
    calc
      x = g (b x) := hx.symm
      _ = g (b z) := by rw [hbx,hbz]
      _ = z := hl.self_of_nhds
  obtain ⟨V,hdata,hV,hzV⟩ := _root_.eventually_nhds_iff.mp
    (hbranches.and (hzero.and hb.eventually_analyticAt))
  exact doubleCover_no_chart_of_crossing f b z hz V hV hzV
    (fun x hx => (hdata x hx).2.2.continuousAt.continuousWithinAt) hbz
    (fun x hx => (hdata x hx).2.1) (fun x hx => (hdata x hx).1) e

/-- In particular no charted-space structure on the inherited topology
can contain an analytic double zero. -/
theorem doubleCover_double_zero_not_charted (f : ℂ → ℂ) (z : ℂ)
    (hf : AnalyticAt ℂ f z) (hz : f z = 0) (ho : analyticOrderAt f z = 2) :
    ¬ Nonempty (ChartedSpace ℂ (doubleCover f)) := by
  rintro ⟨c⟩
  let := c
  let q : doubleCover f := ⟨(z,0),by change (0 : ℂ)^2 = f z; simp [hz]⟩
  exact doubleCover_double_zero_no_chart f z hf hz ho (chartAt ℂ q) (mem_chart_source ℂ q)

/-- The actual affine spectral curve cannot carry a charted complex
surface structure in its inherited topology at a double periodic point. -/
theorem spectralCurve_double_point_not_charted {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) (z : ℂ)
    (hm : periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 2) :
    ¬ Nonempty (ChartedSpace ℂ (spectralCurve hp a)) := by
  let f : ℂ → ℂ := fun x => (canonicalDiscriminant hp (periodOnePotential a) x)^2-4
  apply doubleCover_double_zero_not_charted f z
  · exact ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a) z (mem_univ _)).pow 2).sub analyticAt_const
  · apply sub_eq_zero.mpr
    apply (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem a) z).mpr
    apply (periodicAlgebraicMultiplicity_pos_iff hp _ z).mp
    omega
  · rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem a),hm]
    rfl

/-- Disjoint isolating sets for the actual endpoint segments bound
algebraic multiplicity by two; no boundary-spectrum hypothesis is needed. -/
theorem periodicMultiplicity_le_two_of_disjoint_segments {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (D : ℤ → Set ℂ)
    (hcluster : ∀ n, sourcePeriodicSegment hp hp1 ψ n ⊆ D n)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j))
    (z : ℂ) (hspec : z ∈ periodicSpectrum hp (periodOnePotential ψ)) :
    periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z ≤ 2 := by
  classical
  obtain ⟨n,hn⟩ := (canonicalPeriodicEndpoints_exhaustive hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) z).mp hspec
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let C := canonicalPeriodicCutoff hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let K := max C n.natAbs
  have hlabel := (canonicalPeriodicEndpoints_spec hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)).1
  have hcentral := hlabel.central_at_larger_cutoff K (le_max_left _ _)
  have hnK : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    simp only [Finset.mem_Icc]
    have hnat : n.natAbs ≤ K := le_max_right C n.natAbs
    omega
  have hzD : z ∈ D n := by
    rcases hn with hL | hR
    · exact hL ▸ hcluster n (left_mem_segment ℝ _ _)
    · exact hR ▸ hcluster n (right_mem_segment ℝ _ _)
  have hzcentral : z ∈ centralPeriodicSpectrum hp (periodOnePotential ψ) K :=
    (hcentral.root_iff z).mp ⟨n,le_max_right C n.natAbs,
      by simpa only [eq_comm] using hn⟩
  have hzero (m : ℤ) (hmn : m ≠ n) : ({L m,R m} : Multiset ℂ).count z = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hz
    have hz' : z = L m ∨ z = R m := by
      simpa only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] using hz
    have hzM : z ∈ D m := by
      rcases hz' with hL | hR
      · rw [hL]; exact hcluster m (left_mem_segment ℝ _ _)
      · rw [hR]; exact hcluster m (right_mem_segment ℝ _ _)
    exact Set.disjoint_left.mp (hdisjoint n m hmn.symm) hzD hzM
  have hsum : (∑ m ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ({L m,R m} : Multiset ℂ).count z) =
      ({L n,R n} : Multiset ℂ).count z := by
    apply Finset.sum_eq_single n
    · intro m hm hmn
      exact hzero m hmn
    · intro hnot
      exact False.elim (hnot hnK)
  have hcount := hcentral.count_eq z
  rw [hsum,if_pos hzcentral] at hcount
  rw [← hcount]
  simpa using Multiset.count_le_card z ({L n,R n} : Multiset ℂ)

/-- On the paper's constructed almost-real domains, a complex surface
structure exists exactly when every periodic spectral point is simple.
The reverse implication rules out any charted-space structure at a node. -/
theorem spectralCurve_surface_iff_simple {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}
    (Q : SourceSection19Data hp hp1 W U) (a : CoeffPair p) (ha : a ∈ U) :
    (∃ c : ChartedSpace ℂ (spectralCurve hp a),
      @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ,ℂ) ω (spectralCurve hp a) _ c) ↔
    ∀ z ∈ periodicSpectrum hp (periodOnePotential a),
      periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 1 := by
  constructor
  · rintro ⟨c,_⟩ z hz
    obtain ⟨D⟩ := Q.charts a ha
    have hle := periodicMultiplicity_le_two_of_disjoint_segments hp hp1 a
      (fun n => ball (D.discs.center n) (D.discs.outer n))
      (fun n => (D.discs.segment_subset a D.source_mem n).trans (ball_subset_ball (D.discs.inner_lt n).le))
      D.discs.disjoint z hz
    have hpos := (periodicAlgebraicMultiplicity_pos_iff hp _ z).mpr hz
    by_contra hne
    have hm : periodicAlgebraicMultiplicity hp (periodOnePotential a) z = 2 := by omega
    exact spectralCurve_double_point_not_charted hp hp1 a z hm ⟨c⟩
  · exact spectralCurve_complex_surface hp hp1 a

/-- The actual affine curve depends only on the original periodic
spectrum with algebraic multiplicities, including complex sources. -/
theorem spectralCurve_eq_of_periodic_spectral_data {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (a b : CoeffPair p)
    (hs : periodicSpectrum hp (periodOnePotential a) = periodicSpectrum hp (periodOnePotential b))
    (hm : ∀ z : ℂ, periodicAlgebraicMultiplicity hp (periodOnePotential a) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential b) z) :
    spectralCurve hp a = spectralCurve hp b := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential a) (periodOnePotential b) (periodOnePotential_mem a) (periodOnePotential_mem b) hs hm
  have he : canonicalPeriodicProduct hp (periodOnePotential a) = canonicalPeriodicProduct hp (periodOnePotential b) := by
    rw [← canonicalPeriodicEndpoints_product hp hp1 _ (periodOnePotential_mem a),
      ← canonicalPeriodicEndpoints_product hp hp1 _ (periodOnePotential_mem b),hl,hr]
  have heq (z : ℂ) : (canonicalDiscriminant hp (periodOnePotential a) z)^2-4 =
      (canonicalDiscriminant hp (periodOnePotential b) z)^2-4 := by
    have hh := congrFun he z
    simpa only [canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 _ (periodOnePotential_mem a),
      canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 _ (periodOnePotential_mem b)] using hh
  ext q
  change q.2^2 = (canonicalDiscriminant hp (periodOnePotential a) q.1)^2-4 ↔
    q.2^2 = (canonicalDiscriminant hp (periodOnePotential b) q.1)^2-4
  rw [heq]
end NLS.Articles.DNLSEstimates
