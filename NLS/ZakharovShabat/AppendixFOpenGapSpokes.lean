import NLS.ComplexAnalysis.AppendixFSpokeGeometry
import NLS.ZakharovShabat.AppendixFOpenGapBranches
import NLS.ZakharovShabat.AppendixFSourceSpokes
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Hull

/-! # Common original-boundary endpoint spokes for the open-gap argument in F.2 -/

noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- An outward ray from an interior point reaches the original disc boundary. -/
theorem appendixF_exists_boundary_ray (l g c : ℂ) (R : ℝ)
    (hl : l ∈ ball c R) (hg : g ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ l-(σ:ℂ)*g ∈ sphere c R := by
  have hR : 0 < R := (dist_nonneg : 0 ≤ dist l c).trans_lt (mem_ball.mp hl)
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  let T := (R+‖l-c‖+1)/‖g‖
  have hT : 0 < T := by dsimp [T]; positivity
  let f : ℝ → ℝ := fun t => ‖l-(t:ℂ)*g-c‖
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hzero : f 0 < R := by
    simpa only [f,Complex.ofReal_zero,zero_mul,sub_zero,dist_eq_norm] using mem_ball.mp hl
  have hnorm : ‖(T:ℂ)*g‖ = R+‖l-c‖+1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hT]
    exact div_mul_cancel₀ _ hgpos.ne'
  have hbound : R ≤ f T := by
    have htriangle : ‖(T:ℂ)*g‖ ≤ ‖l-c‖+‖l-(T:ℂ)*g-c‖ := by
      calc
        ‖(T:ℂ)*g‖ = ‖(l-c)-(l-(T:ℂ)*g-c)‖ := by congr 1; ring
        _ ≤ ‖l-c‖+‖l-(T:ℂ)*g-c‖ := norm_sub_le _ _
    rw [hnorm] at htriangle
    dsimp only [f]
    linarith
  obtain ⟨σ,hσ,hσeq⟩ := intermediate_value_Icc hT.le hf.continuousOn ⟨hzero.le,hbound⟩
  have hσpos : 0 < σ := by
    by_contra hn
    have he : σ = 0 := le_antisymm (not_lt.mp hn) hσ.1
    rw [he] at hσeq
    exact (ne_of_lt hzero) hσeq
  refine ⟨σ,hσpos,?_⟩
  simpa only [mem_sphere,dist_eq_norm,f] using hσeq

end NLS.ComplexAnalysis

namespace NLS.ZakharovShabat
open NLS.ComplexAnalysis
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable {D : ℤ → Set ℂ} {c : ℝ}

/-- Both endpoint rays and analytic branches share one source neighborhood, retain the
printed quarter-distance margins, and avoid every gap in the original closed disc. -/
theorem SourceLemma10_2Data.appendixF_common_open_gap_spokes
    (H : SourceLemma10_2Data hp hp1 W) (hV : IsOpen V) (hVW : V ⊆ W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n
    ∃ σ₁ σ₂ : ℝ, ∃ ν₁ ν₂ : ℂ,
      0 < σ₁ ∧ 0 < σ₂ ∧ ν₁ = l-(σ₁:ℂ)*(r-l) ∧ ν₂ = r+(σ₂:ℂ)*(r-l) ∧
      ν₁ ∈ frontier (D n) ∧ ν₂ ∈ frontier (D n) ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
        ∃ ρ₁ ρ₂ : CoeffPair p → ℂ,
          AnalyticOnNhd ℂ ρ₁ U ∧ AnalyticOnNhd ℂ ρ₂ U ∧ ρ₁ φ = l ∧ ρ₂ φ = r ∧
          ∀ ψ ∈ U,
            ({ρ₁ ψ,ρ₂ ψ} : Set ℂ) =
              {canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n,
               canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n} ∧
            ρ₁ ψ ≠ ρ₂ ψ ∧
            ‖ρ₁ ψ-l‖ < (1/4)*min (infDist l (frontier (D n))) ‖r-l‖ ∧
            ‖ρ₂ ψ-r‖ < (1/4)*min (infDist r (frontier (D n))) ‖r-l‖ ∧
            segment ℝ (ρ₁ ψ) ν₁ \ {ρ₁ ψ} ⊆ closure (D n) ∩ sourceCanonicalRootDomain hp hp1 ψ ∧
            segment ℝ (ρ₂ ψ) ν₂ \ {ρ₂ ψ} ⊆ closure (D n) ∩ sourceCanonicalRootDomain hp hp1 ψ := by
  dsimp only
  let l := fun ψ : CoeffPair p => canonicalPeriodicLeft hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := fun ψ : CoeffPair p => canonicalPeriodicRight hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  have hg : r φ-l φ ≠ 0 := hgap
  have hgpos : 0 < ‖r φ-l φ‖ := norm_pos_iff.mpr hg
  obtain ⟨a,R,hR,hDb⟩ := hD.discs n
  have hlD : l φ ∈ D n := hD.gap φ hφ n (left_mem_segment ℝ _ _)
  have hrD : r φ ∈ D n := hD.gap φ hφ n (right_mem_segment ℝ _ _)
  obtain ⟨σ₁,hσ₁,hν₁sphere⟩ := appendixF_exists_boundary_ray (l φ) (r φ-l φ) (a:ℂ) R
    (by rwa [← hDb]) hg
  obtain ⟨σ₂,hσ₂,hν₂sphere⟩ := appendixF_exists_boundary_ray (r φ) (l φ-r φ) (a:ℂ) R
    (by rwa [← hDb]) (sub_ne_zero.mpr (sub_ne_zero.mp hg).symm)
  let ν₁ := l φ-(σ₁:ℂ)*(r φ-l φ)
  let ν₂ := r φ-(σ₂:ℂ)*(l φ-r φ)
  have hν₁ : ν₁ ∈ frontier (D n) := by
    rw [hDb,frontier_ball _ hR.ne']
    exact hν₁sphere
  have hν₂ : ν₂ ∈ frontier (D n) := by
    rw [hDb,frontier_ball _ hR.ne']
    exact hν₂sphere
  have hopen : IsOpen (D n) := by rw [hDb]; exact isOpen_ball
  have hdistpos (z : ℂ) (hz : z ∈ D n) : 0 < infDist z (frontier (D n)) := by
    apply (infDist_pos_iff_notMem_closure ⟨ν₁,hν₁⟩).mp
    rw [isClosed_frontier.closure_eq]
    intro hf
    have hn : z ∉ D n := by simpa only [hopen.interior_eq] using hf.2
    exact hn hz
  let d₁ := infDist (l φ) (frontier (D n))
  let d₂ := infDist (r φ) (frontier (D n))
  have hd₁ : 0 < d₁ := hdistpos _ hlD
  have hd₂ : 0 < d₂ := hdistpos _ hrD
  have hd₁ray : d₁ ≤ σ₁*‖r φ-l φ‖ := by
    calc
      d₁ ≤ dist (l φ) ν₁ := infDist_le_dist_of_mem hν₁
      _ = σ₁*‖r φ-l φ‖ := by
        rw [dist_eq_norm]
        have he : l φ-ν₁ = (σ₁:ℂ)*(r φ-l φ) := by dsimp [ν₁]; ring
        rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ₁]
  have hd₂ray : d₂ ≤ σ₂*‖r φ-l φ‖ := by
    calc
      d₂ ≤ dist (r φ) ν₂ := infDist_le_dist_of_mem hν₂
      _ = σ₂*‖r φ-l φ‖ := by
        rw [dist_eq_norm]
        have he : r φ-ν₂ = (σ₂:ℂ)*(l φ-r φ) := by dsimp [ν₂]; ring
        rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hσ₂,norm_sub_rev]
  let ε := min (min d₁ d₂) ‖r φ-l φ‖/4
  have hε : 0 < ε := div_pos (lt_min (lt_min hd₁ hd₂) hgpos) (by norm_num)
  have hε₁ : ε ≤ d₁/4 := div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hε₂ : ε ≤ d₂/4 := div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hεg : ε ≤ ‖r φ-l φ‖/4 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  obtain ⟨U,hU,hφU,hUV,ρ₁,ρ₂,hA₁,hA₂,hbase₁,hbase₂,hbranches⟩ :=
    exists_local_analytic_pair_branches l r V hV φ hφ
      (H.midpoint n φ (hVW hφ)) (H.squared_gap n φ (hVW hφ))
      (sub_ne_zero.mp hg).symm ε hε
  refine ⟨σ₁,σ₂,ν₁,ν₂,hσ₁,hσ₂,rfl,?_,hν₁,hν₂,U,hU,hφU,hUV,
    ρ₁,ρ₂,hA₁,hA₂,hbase₁,hbase₂,?_⟩
  · change r φ-(σ₂:ℂ)*(l φ-r φ) = r φ+(σ₂:ℂ)*(r φ-l φ)
    ring
  intro ψ hψ
  obtain ⟨hpair,hdistinct,hlnear,hrnear⟩ := hbranches ψ hψ
  have hψV := hUV hψ
  have hseg : segment ℝ (ρ₁ ψ) (ρ₂ ψ) = sourcePeriodicSegment hp hp1 ψ n := by
    rw [sourcePeriodicSegment,← convexHull_pair,← convexHull_pair,hpair]
  have hρ₁D : ρ₁ ψ ∈ D n := hD.gap ψ hψV n (by rw [← hseg]; exact left_mem_segment ℝ _ _)
  have hρ₂D : ρ₂ ψ ∈ D n := hD.gap ψ hψV n (by rw [← hseg]; exact right_mem_segment ℝ _ _)
  have hlquarter : ‖(ρ₁ ψ-l φ)/(r φ-l φ)‖ < 1/4 := by
    rw [norm_div]
    apply (div_lt_iff₀ hgpos).mpr
    linarith [hlnear.trans_le hεg]
  have hrquarter : ‖(ρ₂ ψ-r φ)/(r φ-l φ)‖ < 1/4 := by
    rw [norm_div]
    apply (div_lt_iff₀ hgpos).mpr
    linarith [hrnear.trans_le hεg]
  have hlσ : ‖(ρ₁ ψ-l φ)/(r φ-l φ)‖ < σ₁/4 := by
    rw [norm_div]
    apply (div_lt_iff₀ hgpos).mpr
    nlinarith [hlnear.trans_le hε₁]
  have hrσ : ‖(ρ₂ ψ-r φ)/(r φ-l φ)‖ < σ₂/4 := by
    rw [norm_div]
    apply (div_lt_iff₀ hgpos).mpr
    nlinarith [hrnear.trans_le hε₂]
  have hεbound₁ : ε ≤ (1/4)*min d₁ ‖r φ-l φ‖ := by
    rw [mul_comm,mul_one_div]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact le_min ((min_le_left _ _).trans (min_le_left _ _)) (min_le_right _ _)
  have hεbound₂ : ε ≤ (1/4)*min d₂ ‖r φ-l φ‖ := by
    rw [mul_comm,mul_one_div]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact le_min ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
  refine ⟨hpair,hdistinct,hlnear.trans_le hεbound₁,hrnear.trans_le hεbound₂,?_,?_⟩
  · intro z hz
    have hz' := appendixF_perturbed_spoke_in_disc (l φ) (r φ) (ρ₁ ψ) (ρ₂ ψ) (a:ℂ) R σ₁
      hσ₁ hg (lt_min hlquarter hlσ) hrquarter
      (ball_subset_closedBall (by rwa [← hDb])) (sphere_subset_closedBall hν₁sphere) hz
    have hcl : z ∈ closure (D n) := by rw [hDb,closure_ball _ hR.ne']; exact hz'.1
    exact ⟨hcl,hD.closedCutDisk_subset_rootDomain ψ hψV n ⟨hcl,by rw [← hseg]; exact hz'.2⟩⟩
  · intro z hz
    have hrev : ‖l φ-r φ‖ = ‖r φ-l φ‖ := norm_sub_rev _ _
    have hrrev : ‖(ρ₂ ψ-r φ)/(l φ-r φ)‖ < min (1/4) (σ₂/4) := by
      simpa only [norm_div,hrev] using lt_min hrquarter hrσ
    have hlrev : ‖(ρ₁ ψ-l φ)/(l φ-r φ)‖ < 1/4 := by
      simpa only [norm_div,hrev] using hlquarter
    have hz' := appendixF_perturbed_spoke_in_disc (r φ) (l φ) (ρ₂ ψ) (ρ₁ ψ) (a:ℂ) R σ₂
      hσ₂ (sub_ne_zero.mpr (sub_ne_zero.mp hg).symm) hrrev hlrev
      (ball_subset_closedBall (by rwa [← hDb])) (sphere_subset_closedBall hν₂sphere) hz
    have hcl : z ∈ closure (D n) := by rw [hDb,closure_ball _ hR.ne']; exact hz'.1
    exact ⟨hcl,hD.closedCutDisk_subset_rootDomain ψ hψV n
      ⟨hcl,by rw [← hseg,segment_symm]; exact hz'.2⟩⟩

end NLS.ZakharovShabat
