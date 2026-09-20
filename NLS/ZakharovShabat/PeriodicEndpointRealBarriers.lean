import NLS.ZakharovShabat.CanonicalPeriodicStability
import NLS.ComplexAnalysis.RealDiameterDiscs
import NLS.SequenceSpaces.OrderedCountBounds

/-!
# Stable real barriers for ordered periodic endpoints

Real-diameter circles avoiding the original spectrum preserve exact slot
counts. Prefix and suffix counts bound the nearby canonical real parts,
without assuming simple roots or distinct endpoint values.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Avoiding the real values of all central slots gives a spectral-free real-diameter circle. -/
theorem PeriodicEndpointLabeling.realDiameterSphere_avoids_spectrum
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hreal : IsRealType φ) (a b : ℝ)
    (ha : -centralCircleRadius N ≤ a) (hb : b ≤ centralCircleRadius N)
    (hneA : ∀ k ∈ centralPeriodicSlots N, (periodicEndpointSlot ξ η k).re ≠ a)
    (hneB : ∀ k ∈ centralPeriodicSlots N, (periodicEndpointSlot ξ η k).re ≠ b) :
    ∀ z ∈ sphere (((a+b)/2 : ℝ) : ℂ) ((b-a)/2), z ∉ periodicSpectrum hp φ := by
  intro z hz hs
  have hd := realDiameterDisc_subset_closedBall a b (centralCircleRadius N) ha hb
    (sphere_subset_closedBall hz)
  have hr : |z.re| ≤ centralCircleRadius N :=
    (Complex.abs_re_le_norm z).trans (by simpa only [mem_closedBall,dist_zero_right] using hd)
  have hm := h.spectrum_mem_central_of_abs_re_le z hs hr
  obtain ⟨n,hn,he⟩ := (h.central.root_iff z).mpr hm
  have hslot : ∃ k ∈ centralPeriodicSlots N, periodicEndpointSlot ξ η k = z := by
    rcases he with he | he
    · exact ⟨toLex (n,0),by simpa using hn,by simpa using he⟩
    · exact ⟨toLex (n,1),by simpa using hn,by simpa using he⟩
  obtain ⟨k,hk,rfl⟩ := hslot
  have him := periodicSpectrum_im_eq_zero_of_realType hp φ hreal _ hs
  rcases re_eq_endpoints_of_mem_realDiameterSphere a b _ him hz with he | he
  · exact hneA k hk he
  · exact hneB k hk he

/-- A stable left prefix count bounds the nearby canonical slot from above. -/
theorem eventually_canonicalPeriodicSlot_re_le_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (N : ℕ)
    (hN : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      PeriodicEndpointLabeling hp ψ.val N
        (canonicalPeriodicLeft hp hp1 ψ.val ψ.property) (canonicalPeriodicRight hp hp1 ψ.val ψ.property))
    (k : ℤ ×ₗ Fin 2) (hk : k ∈ centralPeriodicSlots N) (a : ℝ)
    (ha : -centralCircleRadius N < a) (haR : a ≤ centralCircleRadius N)
    (hxa : (canonicalPeriodicSlot hp hp1 φ.val φ.property k).re ≤ a)
    (hne : ∀ z ∈ sphere (((-centralCircleRadius N+a)/2 : ℝ) : ℂ)
      ((a+centralCircleRadius N)/2), z ∉ periodicSpectrum hp φ.val) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      (canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).re ≤ a := by
  let R := centralCircleRadius N
  let D := closedBall (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2)
  let s := centralPeriodicSlots N
  let ξ := fun ψ : pairParitySubspace (p := p) 0 => canonicalPeriodicSlot hp hp1 ψ.val ψ.property
  have hφ := hN.self_of_nhds
  have hsub : D ⊆ closedBall 0 R := by
    simpa only [sub_neg_eq_add] using realDiameterDisc_subset_closedBall (-R) a R le_rfl haR
  have hS : ∀ z ∈ D, |z.re| ≤ R := fun z hz => (Complex.abs_re_le_norm z).trans
    (by simpa only [mem_closedBall,dist_zero_right] using hsub hz)
  have hpref : s.filter (fun j => j ≤ k) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hjk⟩ := Finset.mem_filter.mp hj
    have hjN := (mem_centralPeriodicSlots N j).mp hjs
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_lt.mp (hφ.abs_re_central_lt (ofLex j).1 hjN _ (periodicEndpointSlot_mem_pair _ _ j))).1.le
    have hm := re_le_of_complexLexLE (canonicalPeriodicSlot_ordered hp hp1 φ.val φ.property j k hjk)
    have him := canonicalPeriodicSlot_im_eq_zero_of_realType hp hp1 φ.val φ.property hreal j
    apply (show ξ φ j ∈ D ↔ -R ≤ (ξ φ j).re ∧ (ξ φ j).re ≤ a from by
      simpa only [sub_neg_eq_add] using mem_realDiameterDisc_iff (-R) a (ξ φ j) him).mpr
    exact ⟨hr,hm.trans hxa⟩
  have he := continuous_subtype_val.continuousAt.eventually
    (eventually_periodicProduct_count_eq hp hp1 φ.val (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2)
      (by dsimp [R]; linarith) hne)
  filter_upwards [hN,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter_slots hp1 D hS,
      hφ.analyticZeroCount_eq_card_filter_slots hp1 D hS] at hc
    exact hc
  apply NLS.le_of_prefix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun i _ j _ hij => re_le_of_complexLexLE (canonicalPeriodicSlot_ordered hp hp1 ψ.val ψ.property i j hij))
    k hk a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    exact (re_mem_Icc_of_mem_realDiameterDisc (-R) a (ξ ψ j)
      (by simpa only [sub_neg_eq_add] using (Finset.mem_filter.mp hj).2)).2
  · rw [heq]
    exact Finset.card_le_card hpref

/-- A stable right suffix count bounds the nearby canonical slot from below. -/
theorem eventually_le_canonicalPeriodicSlot_re_of_barrier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (N : ℕ)
    (hN : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      PeriodicEndpointLabeling hp ψ.val N
        (canonicalPeriodicLeft hp hp1 ψ.val ψ.property) (canonicalPeriodicRight hp hp1 ψ.val ψ.property))
    (k : ℤ ×ₗ Fin 2) (hk : k ∈ centralPeriodicSlots N) (a : ℝ)
    (ha : -centralCircleRadius N ≤ a) (haR : a < centralCircleRadius N)
    (hax : a ≤ (canonicalPeriodicSlot hp hp1 φ.val φ.property k).re)
    (hne : ∀ z ∈ sphere (((a+centralCircleRadius N)/2 : ℝ) : ℂ)
      ((centralCircleRadius N-a)/2), z ∉ periodicSpectrum hp φ.val) :
    ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      a ≤ (canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).re := by
  let R := centralCircleRadius N
  let D := closedBall (((a+R)/2 : ℝ) : ℂ) ((R-a)/2)
  let s := centralPeriodicSlots N
  let ξ := fun ψ : pairParitySubspace (p := p) 0 => canonicalPeriodicSlot hp hp1 ψ.val ψ.property
  have hφ := hN.self_of_nhds
  have hsub : D ⊆ closedBall 0 R := realDiameterDisc_subset_closedBall a R R ha le_rfl
  have hS : ∀ z ∈ D, |z.re| ≤ R := fun z hz => (Complex.abs_re_le_norm z).trans
    (by simpa only [mem_closedBall,dist_zero_right] using hsub hz)
  have hsuff : s.filter (fun j => k ≤ j) ⊆ s.filter (fun j => ξ φ j ∈ D) := by
    intro j hj
    obtain ⟨hjs,hkj⟩ := Finset.mem_filter.mp hj
    have hjN := (mem_centralPeriodicSlots N j).mp hjs
    refine Finset.mem_filter.mpr ⟨hjs,?_⟩
    have hr := (abs_lt.mp (hφ.abs_re_central_lt (ofLex j).1 hjN _ (periodicEndpointSlot_mem_pair _ _ j))).2.le
    have hm := re_le_of_complexLexLE (canonicalPeriodicSlot_ordered hp hp1 φ.val φ.property k j hkj)
    have him := canonicalPeriodicSlot_im_eq_zero_of_realType hp hp1 φ.val φ.property hreal j
    exact (mem_realDiameterDisc_iff a R (ξ φ j) him).mpr ⟨hax.trans hm,hr⟩
  have he := continuous_subtype_val.continuousAt.eventually
    (eventually_periodicProduct_count_eq hp hp1 φ.val (((a+R)/2 : ℝ) : ℂ) ((R-a)/2)
      (by dsimp [R]; linarith) hne)
  filter_upwards [hN,he] with ψ hψ hc
  have heq : (s.filter (fun j => ξ ψ j ∈ D)).card = (s.filter (fun j => ξ φ j ∈ D)).card := by
    rw [hψ.analyticZeroCount_eq_card_filter_slots hp1 D hS,
      hφ.analyticZeroCount_eq_card_filter_slots hp1 D hS] at hc
    exact hc
  apply NLS.le_of_suffix_card_le s (s.filter (fun j => ξ ψ j ∈ D)) (fun j => (ξ ψ j).re)
    (fun i _ j _ hij => re_le_of_complexLexLE (canonicalPeriodicSlot_ordered hp hp1 ψ.val ψ.property i j hij))
    k hk a (Finset.filter_subset _ _) ?_ ?_
  · intro j hj
    exact (re_mem_Icc_of_mem_realDiameterDisc a R (ξ ψ j) (Finset.mem_filter.mp hj).2).1
  · rw [heq]
    exact Finset.card_le_card hsuff

end NLS.ZakharovShabat
