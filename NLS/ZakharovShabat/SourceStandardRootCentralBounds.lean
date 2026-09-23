import NLS.ZakharovShabat.SourceStandardRootCentralSeparation

/-!
# Equation (2.10) on finite central source blocks

Finitely many central midpoint discs form a bounded union. The exact root
norm identity gives a common upper bound, while positive half-margin
separation gives a common lower bound. The finite index span turns both
into bounds proportional to the distance between signed indices.
-/

noncomputable section
open Set Metric Complex
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A finite family of central discs gives a common upper bound for
nonzero standard roots whose endpoints stay in those discs. -/
theorem exists_source_central_disc_uniform_root_upper
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (ε : ℝ) (s : Finset ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : CoeffPair p),
      (∀ n ∈ s, sourceSpectralCluster hp hp1 ψ n ⊆
        sourceClusterDisc hp hp1 φ (fun _ => ε) n) →
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
          sourceStandardRoot hp hp1 ψ j z ≠ 0 →
          ‖sourceStandardRoot hp hp1 ψ j z‖ ≤ C := by
  let S : Set ℂ := ⋃ n ∈ s, sourceClusterDisc hp hp1 φ (fun _ => ε) n
  have hS : Bornology.IsBounded S := by
    exact (Bornology.isBounded_biUnion_finset s).2 (by
      intro n hn
      exact Metric.isBounded_ball)
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS
  let C : ℝ := 2*(max R 0+1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ψ hcluster i hi j hj hij z hz hroot
  have hzS : z ∈ S := mem_iUnion_of_mem i (mem_iUnion_of_mem hi hz)
  have hLS : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ S :=
    mem_iUnion_of_mem j (mem_iUnion_of_mem hj (hcluster j hj (Or.inl rfl)))
  have hRS : canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j ∈ S :=
    mem_iUnion_of_mem j (mem_iUnion_of_mem hj (hcluster j hj (Or.inr (Or.inl rfl))))
  have hzB : ‖z‖ ≤ max R 0+1 := by
    have h := hR z hzS
    linarith [le_max_left R 0]
  have hLB : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j‖ ≤ max R 0+1 := by
    have h := hR _ hLS
    linarith [le_max_left R 0]
  have hRB : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j‖ ≤ max R 0+1 := by
    have h := hR _ hRS
    linarith [le_max_left R 0]
  have hLdist : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j-z‖ ≤ C := by
    calc
      _ ≤ ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j‖+‖z‖ := norm_sub_le _ _
      _ ≤ C := by change _ ≤ 2*(max R 0+1); linarith [hLB, hzB]
  have hRdist : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j-z‖ ≤ C := by
    calc
      _ ≤ ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j‖+‖z‖ := norm_sub_le _ _
      _ ≤ C := by change _ ≤ 2*(max R 0+1); linarith [hRB, hzB]
  have hmid : z ≠ canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) j := by
    intro he
    apply hroot
    unfold sourceStandardRoot normalizedStandardRoot
    rw [he]
    simp
  have hsq := sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ j z hmid
  have hnorm : ‖sourceStandardRoot hp hp1 ψ j z‖^2 =
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) j-z‖ := by
    rw [← norm_pow, hsq, norm_mul]
  have hmul :
      ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) j-z‖ *
        ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) j-z‖ ≤ C*C :=
    mul_le_mul hLdist hRdist (norm_nonneg _) hC
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ j z)]

/-- A shared source neighborhood carries two-sided constant bounds for
all distinct indices in one finite central block. -/
theorem exists_local_source_central_root_two_sided
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) i,
            ε/2 ≤ ‖sourceStandardRoot hp hp1 ψ j z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ j z‖ ≤ C := by
  obtain ⟨ε, hε, V₁, hV₁open, hφV₁, hlower⟩ :=
    exists_local_source_central_root_lower hp hp1 φ hφ s
  obtain ⟨C, hC, hupper⟩ :=
    exists_source_central_disc_uniform_root_upper hp hp1 φ ε s
  have hevent : ∀ᶠ ψ : CoeffPair p in 𝓝 φ, ∀ n ∈ s,
      sourceSpectralCluster hp hp1 ψ n ⊆
        sourceClusterDisc hp hp1 φ (fun _ => ε) n := by
    rw [Finset.eventually_all]
    intro n hn
    exact eventually_sourceSpectralCluster_subset_open hp hp1 φ hφ n _
      Metric.isOpen_ball
      (sourceSpectralCluster_subset_disc hp hp1 φ hφ (fun _ => ε) n hε)
  obtain ⟨V₂, hV₂sub, hV₂open, hφV₂⟩ := _root_.mem_nhds_iff.mp hevent
  refine ⟨ε, hε, C, hC, V₁ ∩ V₂, hV₁open.inter hV₂open, ⟨hφV₁,hφV₂⟩, ?_⟩
  intro ψ hψ i hi j hj hij z hz
  have hlo := hlower ψ hψ.1 i hi j hj hij z hz
  have hroot : sourceStandardRoot hp hp1 ψ j z ≠ 0 := by
    apply norm_pos_iff.mp
    linarith
  exact ⟨hlo, hupper ψ (hV₂sub hψ.2) i hi j hj hij z hz hroot⟩

/-- Equation (2.10) for all distinct indices in the central block
`[-N,N]`, with one constant and one connected local source neighborhood. -/
theorem exists_local_source_central_root_index_bounds
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (N : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 1 ≤ c ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∀ ψ ∈ V, ∀ m n : ℤ, m.natAbs ≤ N → n.natAbs ≤ N → m ≠ n →
          ∀ z ∈ sourceClusterDisc hp hp1 φ (fun _ => ε) m,
            c⁻¹ * |((m-n : ℤ) : ℝ)| ≤ ‖sourceStandardRoot hp hp1 ψ n z‖ ∧
              ‖sourceStandardRoot hp hp1 ψ n z‖ ≤
                c * |((m-n : ℤ) : ℝ)| := by
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨ε, hε, C, hC, V, hVopen, hφV, hroot⟩ :=
    exists_local_source_central_root_two_sided hp hp1 φ hφ s
  let c : ℝ := max 1 (max C ((4*(N:ℝ)+2)/ε))
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcC : C ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcScale : (4*(N:ℝ)+2)/ε ≤ c :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hcpos : 0 < c := by linarith
  have hscale : 4*(N:ℝ)+2 ≤ c*ε := (div_le_iff₀ hε).mp hcScale
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hφV)
  refine ⟨ε, hε, c, hc1, ball φ r, Metric.isOpen_ball,
    isConnected_ball hr, mem_ball_self hr, ?_⟩
  intro ψ hψ m n hm hn hmn z hz
  have hmS : m ∈ s := by
    simp only [s, Finset.mem_Icc]
    omega
  have hnS : n ∈ s := by
    simp only [s, Finset.mem_Icc]
    omega
  obtain ⟨hlower,hupper⟩ := hroot ψ (hrV hψ) m hmS n hnS hmn z hz
  let d : ℝ := |((m-n : ℤ) : ℝ)|
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmn)
  have hdN : d ≤ 2*(N:ℝ) := by
    have hmi : -(N:ℤ) ≤ m ∧ m ≤ (N:ℤ) := by omega
    have hni : -(N:ℤ) ≤ n ∧ n ≤ (N:ℤ) := by omega
    have hdi : |m-n| ≤ 2*(N:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    have hreal : (|(m-n : ℤ)| : ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hdi
    simpa only [d, Int.cast_abs] using hreal
  have hl : c⁻¹*d ≤ ε/2 := by
    rw [show c⁻¹*d = d/c by ring]
    exact (div_le_iff₀ hcpos).2 (by nlinarith [hdN, hscale])
  have hu : C ≤ c*d := by nlinarith [hcC, hd1, hc1]
  exact ⟨hl.trans hlower, hupper.trans hu⟩

end NLS.ZakharovShabat
