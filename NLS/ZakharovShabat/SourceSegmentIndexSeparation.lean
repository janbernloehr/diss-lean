import NLS.ZakharovShabat.SourceDiscIndexSeparation
import NLS.ZakharovShabat.SourceClusterDiscsLocal
import NLS.ZakharovShabat.SourceTailIsolation

/-! # Index-scale separation of actual periodic segments

Every real source has a complex neighborhood on which one constant controls
all pairs of points on distinct periodic segments. The proof places whole
segments in convex central half-margin discs or refined tail discs.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Segment localization supplies a common separation constant for every distinct index pair. -/
theorem exists_source_segment_index_separation_of_disc_data
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hεmax : ε ≤ Real.pi/4)
    (houterL : canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (-(N : ℤ)) ∈ refinedResonantDisk (-(N : ℤ)))
    (houterR : canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) (N : ℤ) ∈ refinedResonantDisk (N : ℤ))
    (hgap : ∀ i j : ℤ, i.natAbs ≤ N → j.natAbs ≤ N → i < j →
      2*ε ≤
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re)
    (V : Set (CoeffPair p))
    (hmidCentral : ∀ ψ ∈ V, ∀ j : ℤ, j.natAbs ≤ N →
      sourcePeriodicSegment hp hp1 ψ j ⊆
          sourceClusterDisc hp hp1 φ (fun _ => ε/2) j)
    (hmidTail : ∀ ψ ∈ V, ∀ j : ℤ, N < j.natAbs →
      sourcePeriodicSegment hp hp1 ψ j ⊆ refinedResonantDisk j) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ ψ ∈ V, ∀ i j : ℤ, i ≠ j →
        ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i, ∀ w ∈ sourcePeriodicSegment hp hp1 ψ j,
          |((i-j : ℤ) : ℝ)| ≤ C *
            ‖w-z‖ := by
  obtain ⟨C,hC,hsep⟩ := exists_source_disc_point_index_separation
    hp hp1 φ hφ N ε hε hεmax houterL houterR hgap
  refine ⟨C,hC,?_⟩
  intro ψ hψ i j hij z hz w hw
  apply hsep i j hij z hz w
  split_ifs with hj
  · exact hmidCentral ψ hψ j hj hw
  · exact hmidTail ψ hψ j (by omega) hw

/-- All periodic segments have a common index-scale separation near every real source. -/
theorem exists_local_source_segment_index_separation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ ψ ∈ V, ∀ i j : ℤ, i ≠ j →
            ∀ z ∈ sourcePeriodicSegment hp hp1 ψ i, ∀ w ∈ sourcePeriodicSegment hp hp1 ψ j,
              |((i-j : ℤ) : ℝ)| ≤ C *
                ‖w-z‖ := by
  obtain ⟨N₀,Ut,hUtopen,hφUt,htail⟩ :=
    exists_uniform_source_tail_isolation hp hp1 φ
  let N := N₀+1
  have hN₀ : N₀ < N := by dsimp [N]; omega
  have hpos : N₀ < (N:ℤ).natAbs := by simpa using hN₀
  have hneg : N₀ < (-(N:ℤ)).natAbs := by simpa using hN₀
  have houterR := (htail φ hφUt (N:ℤ) hpos).2.1
  have houterL := (htail φ hφUt (-(N:ℤ)) hneg).1
  let s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  obtain ⟨ε,hε,hεmax,hgap⟩ :=
    exists_bounded_positive_margin_for_finite_pairs s
      (fun i j =>
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re)
      (by
        intro i hi j hj hij
        exact sub_pos.mpr (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
          (periodOnePotential φ) (periodOnePotential_mem φ)
          (isRealType_periodOnePotential φ hφ) hij))
      (by positivity : 0 < Real.pi/4)
  have hgap' : ∀ i j : ℤ, i.natAbs ≤ N → j.natAbs ≤ N → i < j →
      2*ε ≤
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) j).re -
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
          (periodOnePotential_mem φ) i).re := by
    intro i j hi hj hij
    have hiS : i ∈ s := by simp only [s, Finset.mem_Icc]; omega
    have hjS : j ∈ s := by simp only [s, Finset.mem_Icc]; omega
    exact hgap i hiS j hjS hij
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ j ∈ s,
      sourceSpectralCluster hp hp1 ψ j ⊆
        sourceClusterDisc hp hp1 φ (fun _ => ε/2) j := by
    rw [Finset.eventually_all]
    intro j hj
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ j _
      Metric.isOpen_ball (sourceSpectralCluster_subset_disc hp hp1 φ hφ
        (fun _ => ε/2) j (by linarith))
  obtain ⟨Uc,hUcsub,hUcopen,hφUc⟩ := _root_.mem_nhds_iff.mp hevent
  let U := Uc ∩ Ut
  have hUopen : IsOpen U := hUcopen.inter hUtopen
  have hφU : φ ∈ U := ⟨hφUc,hφUt⟩
  have hmidCentral : ∀ ψ ∈ U, ∀ j : ℤ, j.natAbs ≤ N →
      sourcePeriodicSegment hp hp1 ψ j ⊆
          sourceClusterDisc hp hp1 φ (fun _ => ε/2) j := by
    intro ψ hψ j hj
    have hjS : j ∈ s := by simp only [s, Finset.mem_Icc]; omega
    have hc := (hUcsub hψ.1) j hjS
    have hconv : Convex ℝ (sourceClusterDisc hp hp1 φ (fun _ => ε/2) j) := by
      unfold sourceClusterDisc
      exact convex_ball _ _
    exact hconv.segment_subset (hc (Or.inl rfl))
      (hc (Or.inr (Or.inl rfl)))
  have hmidTail : ∀ ψ ∈ U, ∀ j : ℤ, N < j.natAbs →
      sourcePeriodicSegment hp hp1 ψ j ⊆ refinedResonantDisk j := by
    intro ψ hψ j hj
    have hc := htail ψ hψ.2 j (hN₀.trans hj)
    have hconv : Convex ℝ (refinedResonantDisk j) := by
      unfold refinedResonantDisk
      exact convex_ball _ _
    exact hconv.segment_subset hc.1 hc.2.1
  obtain ⟨C,hC,hsep⟩ := exists_source_segment_index_separation_of_disc_data
    hp hp1 φ hφ N ε hε hεmax houterL houterR hgap' U
      hmidCentral hmidTail
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hφU)
  refine ⟨ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,hC,?_⟩
  intro ψ hψ i j hij z hz w hw
  have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε i := by
    unfold sourceIsolatingDisc
    split_ifs with hi
    · exact sourceClusterDisc_mono_constant_margin hp hp1 φ (ε/2) ε (by linarith) i
        (hmidCentral ψ (hrU hψ) i hi hz)
    · exact hmidTail ψ (hrU hψ) i (by omega) hz
  exact hsep ψ (hrU hψ) i j hij z hzdisc w hw


end NLS.ZakharovShabat
