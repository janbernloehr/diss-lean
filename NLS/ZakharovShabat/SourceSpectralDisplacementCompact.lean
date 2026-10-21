import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement

/-! # Uniform displacement envelopes on compact real source sets

Local L2 spectral estimates and a fixed physical H1 budget give common all-index bounds on compact real source sets.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem displacement_envelope (δ : Coeff 2) (D B : ℝ) (N : ℕ)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hN : 0 < N) (hδ : ‖δ‖ ≤ D)
    (ht : ∀ n : ℤ, N ≤ n.natAbs → ‖δ n‖ ≤ B/(n.natAbs:ℝ)) :
    ∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ (1+(N:ℝ))*D+2*B := by
  intro n
  have hnabs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
  rw [hnabs]
  by_cases hn : N ≤ n.natAbs
  · have hn1 : 1 ≤ (n.natAbs:ℝ) := by exact_mod_cast hN.trans_le hn
    have ht' := ht n hn
    have hm := (le_div_iff₀ (by linarith : (0:ℝ) < n.natAbs)).mp ht'
    have hdB : ‖δ n‖ ≤ B := ht'.trans (div_le_self hB hn1)
    nlinarith [mul_nonneg (show 0 ≤ 1+(N:ℝ) by positivity) hD]
  · have hnN : (n.natAbs:ℝ) ≤ N := by exact_mod_cast (show n.natAbs ≤ N by omega)
    have hnD := (lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) δ n).trans hδ
    have h := mul_le_mul (by linarith : 1+(n.natAbs:ℝ) ≤ 1+(N:ℝ)) hnD
      (norm_nonneg _) (by positivity : (0:ℝ) ≤ 1+(N:ℝ))
    linarith

/-- On one L2 neighborhood of a real source, a fixed physical H1 budget
controls all three canonical displacement sequences and their inverse-index
norms, including every central index. -/
theorem exists_local_source_all_displacement_envelopes
    (φ₀ : realTypeSourceLocus 2) (R : ℝ) (hR : 0 ≤ R) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ₀.val ∈ U ∧
      ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧ ∀ φ ∈ U,
      ∀ a : Domain 2, ‖a‖ ≤ R → periodOnePotential φ = domainInclusion a →
      (∀ θ : BoundaryCondition,
        ‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ φ‖ ≤ D ∧
        ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ φ n‖ ≤ M) ∧
      ‖sourceCriticalDisplacement (by norm_num) (by norm_num) φ‖ ≤ D ∧
      ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceCriticalDisplacement (by norm_num) (by norm_num) φ n‖ ≤ M := by
  let δ (θ : BoundaryCondition) (φ : CoeffPair 2) := sourceBoundaryDisplacement (by norm_num) (by norm_num) θ φ
  let κ (φ : CoeffPair 2) := sourceCriticalDisplacement (by norm_num) (by norm_num) φ
  let g (φ : CoeffPair 2) := ‖δ .dirichlet φ‖+‖δ .neumann φ‖+‖κ φ‖
  obtain ⟨W,hW,hrealW,haW⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain (p := 2) (by norm_num) (by norm_num)
  have hg : ContinuousAt g φ₀.val :=
    (((haW .dirichlet φ₀.val (hrealW φ₀.property)).continuousAt.norm).add
      ((haW .neumann φ₀.val (hrealW φ₀.property)).continuousAt.norm)).add
        ((continuousAt_sourceCriticalDisplacement_of_realType (by norm_num) (by norm_num) φ₀.val φ₀.property).norm)
  let D := g φ₀.val+1
  have hD : 0 ≤ D := by dsimp [D,g]; positivity
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp (hg.eventually (gt_mem_nhds (show g φ₀.val < D by dsimp only [D]; linarith)))
  obtain ⟨Uμ,hUμ,hφμ,Nμ,hNμ,Bμ,hBμ,hμ⟩ :=
    exists_local_source_boundary_sobolev_inverse_index_bound (p := 2) (by norm_num) (by norm_num) le_rfl φ₀.val R hR
  obtain ⟨Uκ,hUκ,hφκ,Nκ,_,Bκ,hBκ,hκ⟩ :=
    exists_local_source_critical_sobolev_inverse_index_bound φ₀.val R hR
  let N := max Nμ Nκ
  let B := Bμ+Bκ
  let M := (1+(N:ℝ))*D+2*B
  refine ⟨V ∩ (Uμ ∩ Uκ),hV.inter (hUμ.inter hUκ),⟨hφV,hφμ,hφκ⟩,
    D,M,hD,by dsimp [M,B]; positivity,?_⟩
  intro φ hφ a ha hcompat
  have hgD : g φ ≤ D := (hVsub hφ.1).le
  have hδD (θ : BoundaryCondition) : ‖δ θ φ‖ ≤ D := by
    dsimp only [g] at hgD
    cases θ <;> linarith [norm_nonneg (δ .dirichlet φ),norm_nonneg (δ .neumann φ),norm_nonneg (κ φ)]
  have hκD : ‖κ φ‖ ≤ D := by
    dsimp only [g] at hgD
    linarith [norm_nonneg (δ .dirichlet φ),norm_nonneg (δ .neumann φ)]
  have hδtail (θ : BoundaryCondition) (n : ℤ) (hn : N ≤ n.natAbs) :
      ‖δ θ φ n‖ ≤ B/(n.natAbs:ℝ) := by
    have h := hμ φ (by simpa only [CoeffPair.exponentInclusion_refl] using hφ.2.1)
      a ha hcompat θ n ((le_max_left _ _).trans hn)
    simp only [CoeffPair.exponentInclusion_refl] at h
    change ‖δ θ φ n‖ ≤ _ at h
    exact h.trans (div_le_div_of_nonneg_right (by dsimp [B]; linarith) (Nat.cast_nonneg _))
  have hκtail (n : ℤ) (hn : N ≤ n.natAbs) : ‖κ φ n‖ ≤ B/(n.natAbs:ℝ) := by
    have h := hκ φ hφ.2.2 a ha hcompat n ((le_max_right _ _).trans hn)
    change ‖κ φ n‖ ≤ _ at h
    exact h.trans (div_le_div_of_nonneg_right (by dsimp [B]; linarith) (Nat.cast_nonneg _))
  exact ⟨fun θ => ⟨hδD θ,displacement_envelope (δ θ φ) D B N hD (by dsimp [B]; positivity)
    (hNμ.trans_le (le_max_left _ _)) (hδD θ) (hδtail θ)⟩,
    hκD,displacement_envelope (κ φ) D B N hD (by dsimp [B]; positivity)
      (hNμ.trans_le (le_max_left _ _)) hκD hκtail⟩

/-- A compact set of real L2 sources has common all-index displacement
bounds for all its members obeying a fixed physical H1 budget. -/
theorem exists_source_all_displacement_envelopes_on_compact
    (K : Set (CoeffPair 2)) (hK : IsCompact K) (hKreal : K ⊆ realTypeSourceLocus 2)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ D M : ℝ, 0 ≤ D ∧ 0 ≤ M ∧ ∀ φ ∈ K,
      ∀ a : Domain 2, ‖a‖ ≤ R → periodOnePotential φ = domainInclusion a →
      (∀ θ : BoundaryCondition,
        ‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ φ‖ ≤ D ∧
        ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceBoundaryDisplacement (by norm_num) (by norm_num) θ φ n‖ ≤ M) ∧
      ‖sourceCriticalDisplacement (by norm_num) (by norm_num) φ‖ ≤ D ∧
      ∀ n : ℤ, (1+|(n:ℝ)|)*‖sourceCriticalDisplacement (by norm_num) (by norm_num) φ n‖ ≤ M := by
  classical
  have hl (φ : K) := exists_local_source_all_displacement_envelopes ⟨φ.val,hKreal φ.property⟩ R hR
  choose U hU hφU D M hD hM hb using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover U hU
    (fun φ hφ => mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩⟩)
  refine ⟨∑ φ ∈ S, D φ,∑ φ ∈ S, M φ,
    Finset.sum_nonneg (fun φ _ => hD φ),Finset.sum_nonneg (fun φ _ => hM φ),?_⟩
  intro φ hφ a ha hcompat
  obtain ⟨ψ,hψ⟩ := mem_iUnion.mp (hS hφ)
  obtain ⟨hψS,hφU⟩ := mem_iUnion.mp hψ
  have h := hb ψ φ hφU a ha hcompat
  have hDs : D ψ ≤ ∑ φ ∈ S, D φ := Finset.single_le_sum (fun φ _ => hD φ) hψS
  have hMs : M ψ ≤ ∑ φ ∈ S, M φ := Finset.single_le_sum (fun φ _ => hM φ) hψS
  exact ⟨fun θ => ⟨(h.1 θ).1.trans hDs,fun n => ((h.1 θ).2 n).trans hMs⟩,
    h.2.1.trans hDs,fun n => (h.2.2 n).trans hMs⟩

end NLS.ZakharovShabat
