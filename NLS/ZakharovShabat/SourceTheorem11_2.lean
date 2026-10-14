import NLS.ZakharovShabat.SourceActionGapZeroLocus
import NLS.ZakharovShabat.SourceNormalizedIndexedActionLocal

/-!
# Theorem 11.2: analytic normalized actions on one common domain

One open neighborhood W inside the preceding W₀ supports every normalized
indexed action and its principal root. Positive lower bounds and genuine
ℓ^(p/2)+ℓ^(1+) decompositions hold locally uniformly at every complex point
of W, on one neighborhood independent of the index and the one-plus exponent.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complete normalized-action assertions on W, retaining Lemma 11.1 on W₀. -/
structure SourceTheorem11_2Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma11_1Data hp hp1 W₀
  subset : W ⊆ W₀
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) W
  root_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionRoot hp hp1 n) W
  factorization : ∀ ψ ∈ W, ∀ n : ℤ, sourceIndexedAction hp hp1 n ψ =
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
      sourceNormalizedActionComplexExtension hp hp1 n ψ
  agreement : ∀ ψ ∈ W, ∀ n : ℤ, ψ ∈ sourceComplexActionDomain hp hp1 n ∧
    sourceIndexedAction hp hp1 n ψ = sourceComplexAction hp hp1 n ψ
  locally_uniform : ∀ φ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
    SourceNormalizedActionUniformBounds hp hp1 U

/-- The only source-domain shrink in Theorem 11.2 preserves the entire real locus. -/
theorem SourceLemma11_1Data.normalizedActions
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W₀) (hreal : realTypeSourceLocus p ⊆ W₀) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceTheorem11_2Data hp hp1 W₀ W := by
  let W : Set (CoeffPair p) := {ψ | ∃ V : Set (CoeffPair p), IsOpen V ∧ ψ ∈ V ∧
    V ⊆ W₀ ∧ SourceNormalizedIndexedActionLocalData hp hp1 V}
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    rintro ψ ⟨V,hV,hψV,hVW,Hv⟩
    exact mem_of_superset (hV.mem_nhds hψV) (fun χ hχ => ⟨V,hV,hχ,hVW,Hv⟩)
  refine ⟨W,hW,?_,H,?_,?_,?_,?_,?_,?_⟩
  · intro φ hφ
    obtain ⟨V,hV,hφV,hVW,Hv⟩ :=
      H.previous.previous.normalizedActions_near_real φ hφ (hreal hφ)
    exact ⟨V,hV,hφV,hVW,Hv⟩
  · rintro ψ ⟨V,_,hψV,hVW,_⟩
    exact hVW hψV
  · rintro n ψ ⟨V,_,hψV,_,Hv⟩
    exact Hv.analytic n ψ hψV
  · rintro n ψ ⟨V,_,hψV,_,Hv⟩
    exact Hv.root_analytic n ψ hψV
  · rintro ψ ⟨V,_,hψV,_,Hv⟩ n
    exact Hv.factorization ψ hψV n
  · rintro ψ ⟨V,_,hψV,_,Hv⟩ n
    exact Hv.agreement ψ hψV n
  · rintro φ ⟨V,hV,hφV,hVW,Hv⟩
    exact ⟨V,hV,hφV,(fun ψ hψ => ⟨V,hV,hψ,hVW,Hv⟩),Hv.uniform⟩

namespace SourceTheorem11_2Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}

/-- In particular both functions are real analytic on the complex source domain. -/
theorem real_analytic (H : SourceTheorem11_2Data hp hp1 W₀ W) (n : ℤ) :
    AnalyticOnNhd ℝ (sourceNormalizedActionComplexExtension hp hp1 n) W ∧
      AnalyticOnNhd ℝ (sourceNormalizedActionRoot hp hp1 n) W :=
  ⟨(H.analytic n).restrictScalars, (H.root_analytic n).restrictScalars⟩

/-- Off Z_n, the analytic factor is exactly the quotient in the dissertation. -/
theorem normalized_eq_quotient (H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    sourceNormalizedActionComplexExtension hp hp1 n ψ = sourceIndexedAction hp hp1 n ψ /
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 := by
  apply (eq_div_iff (pow_ne_zero 2 hg)).mpr
  simpa only [mul_comm] using (H.factorization ψ hψ n).symm

/-- The normalized action has positive real part, including at collapsed gaps. -/
theorem re_pos (H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    0 < (sourceNormalizedActionComplexExtension hp hp1 n ψ).re := by
  obtain ⟨U,_,hψU,_,Hu⟩ := H.locally_uniform ψ hψ
  obtain ⟨c,hc,hbound⟩ := Hu.positive
  exact hc.trans_le (hbound ψ hψU n)

/-- The root is the existing principal square root, with its exact normalization. -/
theorem root_sq (_H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (n : ℤ) :
    (sourceNormalizedActionRoot hp hp1 n ψ)^2 =
      4*sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  have h := Complex.cpow_nat_inv_pow
    (4*sourceNormalizedActionComplexExtension hp hp1 n ψ) (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [sourceNormalizedActionRoot,Complex.sqrt,one_div] using h

/-- The principal roots never vanish on the common domain. -/
theorem root_ne_zero (H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceNormalizedActionRoot hp hp1 n ψ ≠ 0 := by
  intro hz
  have he : 4*sourceNormalizedActionComplexExtension hp hp1 n ψ = 0 := by
    rw [← H.root_sq ψ n,hz]
    norm_num
  have hf := (mul_eq_zero.mp he).resolve_left (by norm_num : (4 : ℂ) ≠ 0)
  have hpos := H.re_pos ψ hψ n
  rw [hf] at hpos
  exact (lt_irrefl 0) hpos

/-- On W the complex action vanishes exactly on the actual collapsed-gap locus. -/
theorem action_eq_zero_iff_gap_zero (H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = 0 ↔
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 := by
  have hf : sourceNormalizedActionComplexExtension hp hp1 n ψ ≠ 0 := by
    intro he
    have hpos := H.re_pos ψ hψ n
    rw [he] at hpos
    exact (lt_irrefl 0) hpos
  rw [H.factorization ψ hψ n]
  simp [hf]

/-- On real sources the chosen branch is the positive real square root. -/
theorem root_real_positive (H : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    (sourceNormalizedActionRoot hp hp1 n ψ).im = 0 ∧
      0 < (sourceNormalizedActionRoot hp hp1 n ψ).re := by
  have him := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType hp hp1 n ψ hreal
  have hpos := H.re_pos ψ hψ n
  have heq : sourceNormalizedActionComplexExtension hp hp1 n ψ =
      ((sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [sourceNormalizedActionRoot,heq]
  have hcast : (4 : ℂ)*((sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℂ) =
      ((4*(sourceNormalizedActionComplexExtension hp hp1 n ψ).re : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast]
  have hr : 0 < 4*(sourceNormalizedActionComplexExtension hp hp1 n ψ).re := by positivity
  open scoped ComplexOrder in
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast hr.le)]
  exact ⟨rfl,Real.sqrt_pos.mpr hr⟩

/-- The free value of every principal root is one, also at the central gap. -/
theorem root_zero (_H : SourceTheorem11_2Data hp hp1 W₀ W) (n : ℤ) :
    sourceNormalizedActionRoot hp hp1 n (0 : CoeffPair p) = 1 := by
  simp [sourceNormalizedActionRoot,sourceNormalizedActionComplexExtension_zero_source]

end SourceTheorem11_2Data

/-- Theorem 11.2 for every finite p>1, with one open W for every signed index. -/
theorem sourceTheorem11_2 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ SourceTheorem11_2Data hp hp1 W₀ W := by
  obtain ⟨W₀,hW₀,hconn,hr,H⟩ := sourceLemma11_1 hp hp1
  obtain ⟨W,hW,hrW,Hn⟩ := H.normalizedActions hr
  exact ⟨W₀,W,hW₀,hconn,hr,hW,hrW,Hn⟩

end NLS.ZakharovShabat
