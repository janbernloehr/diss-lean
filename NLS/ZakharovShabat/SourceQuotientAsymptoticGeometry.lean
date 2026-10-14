import NLS.ZakharovShabat.SourceQuotientClosedDiscs
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup

/-!
# Quotient asymptotic geometry at every source in the common domain

The original isolating family supplies separation at every index. A free
auxiliary family with empty central disks lets the existing tail estimates
apply without imposing a real-source assumption on the base point.
The actual disks, including their nonempty central part, are retained.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.midpoint_separation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (i j : ℤ) (hij : i ≠ j)
    (z : ℂ) (hz : z ∈ D i) :
    |((i-j : ℤ) : ℝ)| ≤ c *
      ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖ := by
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one hD.one_le
  have hd := (hD.pointwise_distance i j hij z hz _
    (hD.gap ψ hψ j (sourcePeriodicMidpoint_mem_segment hp hp1 ψ j))).1
  rw [dist_comm,dist_eq_norm] at hd
  have hm := mul_le_mul_of_nonneg_left hd hc.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] using hm

/-- The auxiliary family discards only the finite head, not any actual selected disk. -/
theorem sourceIsolatingDisc_zero_margin (hp : p ≠ ⊤) (hp1 : 1 < p) (N : ℕ) (n : ℤ) :
    sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 n =
      if n.natAbs ≤ N then ∅ else refinedResonantDisk n := by
  unfold sourceIsolatingDisc
  split_ifs
  · simp [sourceClusterDisc,map_zero,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero]
  · rfl

theorem SourceIsolatingNeighborhoods.auxiliary_subset
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (_hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (N : ℕ) (hN : ∀ n : ℤ, N < n.natAbs → D n = refinedResonantDisk n) (n : ℤ) :
    sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 n ⊆ D n := by
  rw [sourceIsolatingDisc_zero_margin]
  split_ifs with hn
  · exact empty_subset _
  · rw [hN n (lt_of_not_ge hn)]

/-- Geometry and finite-head bounds on one joint neighborhood, independent of the target exponent. -/
structure SourceQuotientDiscEstimates (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (Coeff p × CoeffPair p)) (D : ℤ → Set ℂ)
    (c R H M : ℝ) (N K : ℕ) : Prop where
  one_le : 1 ≤ c
  midpoint_nonneg : 0 ≤ R
  gap_nonneg : 0 ≤ H
  head_nonneg : 0 ≤ M
  threshold : N < K
  tail : ∀ n : ℤ, N < n.natAbs → D n = refinedResonantDisk n
  nonempty : ∀ n : ℤ, (D n).Nonempty
  midpoint : ∀ t ∈ U, ‖sourcePeriodicMidpointDisplacement hp hp1 t.2‖ ≤ R
  squared_gap : ∀ t ∈ U, ‖sourcePeriodicSquaredGapCoeff hp hp1 t.2‖ ≤ H^2
  separation : ∀ t ∈ U, ∀ i j : ℤ, i ≠ j →
    ∀ z ∈ sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N 0 i,
      |((i-j : ℤ) : ℝ)| ≤ c *
        ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) j-z‖
  small : ∀ t ∈ U, ∀ n : ℤ, K ≤ n.natAbs →
    (c^2/4)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 t.2 n m) ≤ 1/2
  domain : ∀ t ∈ U, ∀ n : ℤ, ∀ z ∈ D n,
    z ∈ sourceStandardRootOmittedDomain hp hp1 t.2 n
  head : ∀ t ∈ U, ∀ n : ℤ, n.natAbs ≤ K → ∀ z ∈ closure (D n),
    ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,t)-1‖ ≤ M

/-- All disks and the original distance constant are retained near an arbitrary source in W. -/
theorem SourceCorollary10_6Data.quotientDiscEstimates
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceCorollary10_6Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧ U ⊆ univ ×ˢ V ∧
      ∃ R H M : ℝ, ∃ N K : ℕ, SourceQuotientDiscEstimates hp hp1 U D c R H M N K := by
  obtain ⟨N,hN⟩ := hD.tail
  obtain ⟨_,_,Vm,hVm,hφm,R,hR,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  obtain ⟨Vg,hVg,hφg,H,hH,hg⟩ := exists_local_sourcePeriodicSquaredGapCoeff_bound hp hp1 φ
  obtain ⟨Vs,hVs,hφs,Ks,hs⟩ := exists_uniform_sourceSquaredGapPhysicalRows_half_unit hp hp1 φ c hD.one_le
  let K := max Ks (N+1)
  let s : Finset ℤ := Finset.Icc (-(K:ℤ)) K
  obtain ⟨Uh,hUh,hbase,M,hM,hh⟩ := h.finiteClosedDiscBound hD φ hφW hφV a s
  let U := Uh ∩ (univ ×ˢ (V ∩ (Vm ∩ (Vg ∩ Vs))))
  have ho : IsOpen U := hUh.inter (isOpen_univ.prod (hV.inter (hVm.inter (hVg.inter hVs))))
  refine ⟨U,ho,⟨hbase,mem_univ _,hφV,hφm,hφg,hφs⟩,
    (fun t ht => ⟨mem_univ _,ht.2.2.1⟩),R,H,M,N,K,
    hD.one_le,hR,hH,hM,by dsimp [K]; omega,hN,?_,?_,?_,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨b,r,hr,he⟩ := hD.discs n
    rw [he]
    exact nonempty_ball.mpr hr
  · intro t ht
    exact (hm t.2 ht.2.2.2.1).1
  · intro t ht
    exact hg t.2 ht.2.2.2.2.1
  · intro t ht i j hij z hz
    exact hD.midpoint_separation t.2 ht.2.2.1 i j hij z (hD.auxiliary_subset N hN i hz)
  · intro t ht n hn
    exact hs t.2 ht.2.2.2.2.2 n (by dsimp [K] at hn; omega)
  · intro t ht n z hz
    exact hD.disk_subset_omittedDomain t.2 ht.2.2.1 n hz
  · intro t ht n hn z hz
    exact hh t ht.1 n (by simp only [s,Finset.mem_Icc]; omega) z hz

end NLS.ZakharovShabat
