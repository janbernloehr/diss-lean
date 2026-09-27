import NLS.ZakharovShabat.SourceNormalizedActionComplexUniformSequenceMajorants
import NLS.SequenceSpaces.TwoExponentMajorant
import NLS.ZakharovShabat.CompleteParityDisplacementBounds

/-!
# Sequence-space values of the complex normalized action

The complex-source `ℓq + ℓ^(p/2)` majorants imply that the normalized
action deviation is an actual `ℓq` sequence whenever `q ≥ p/2`.
The finitely many central indices do not affect membership. The
distant tail has a locally uniform `ℓq` norm bound, including the
quasi-Banach range `p/2 < 1`.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar deviation of the chart-independent normalized action
from its free value at each signed index. -/
def sourceNormalizedActionDeviation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1

/-- Near every real-type source, the entire complex normalized-action
deviation belongs to `ℓq` whenever `q ≥ p/2`; its distant tail has
one uniform norm bound on the same neighborhood. -/
theorem exists_local_sourceNormalizedActionDeviation_coeff
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ L : ℝ, ∀ ψ ∈ V,
        ∃ A T : Coeff q,
          (∀ n : ℤ, A n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          (∀ n : ℤ, T n = if K ≤ n.natAbs then
            sourceNormalizedActionDeviation hp hp1 ψ n else 0) ∧
          ‖T‖ ≤ L := by
  obtain ⟨V,hVopen,hφV,K,Lq,Lg,hmajor⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_complex_uniformSequenceMajorants
      hp hp1 hq1 hq hhalf φ hreal
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hr : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (half_pos hpr)
  refine ⟨V,hVopen,hφV,K,Lq+Lg,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,hCq,hCg⟩ := hmajor ψ hψ
  let a : ℤ → ℂ := sourceNormalizedActionDeviation hp hp1 ψ
  obtain ⟨T,hTapply,hTnorm,hmem⟩ :=
    Coeff.exists_tailCoeff_of_twoSequenceMajorants
      hr hq1 hq hhalf a K Cq Cg (by
        intro n hn
        exact hpoint n hn)
  let A : Coeff q := ⟨a,hmem⟩
  refine ⟨A,T,fun n => rfl,?_,?_⟩
  · exact hTapply
  · exact hTnorm.trans (add_le_add hCq hCg)

/-- The complex normalized-action deviation takes values in `ℓq`
with a locally uniform full sequence norm bound near every real-type
source. -/
theorem exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ M : ℝ, ∀ ψ ∈ V,
        ∃ A : Coeff q,
          (∀ n : ℤ, A n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          ‖A‖ ≤ M := by
  obtain ⟨V₀,hV₀open,hφV₀,K,L,hdata⟩ :=
    exists_local_sourceNormalizedActionDeviation_coeff
      hp hp1 hq1 hq hhalf φ hreal
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let a (ψ : CoeffPair p) (n : ℤ) :=
    sourceNormalizedActionDeviation hp hp1 ψ n
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ s, ‖a ψ n‖ ≤ ‖a φ n‖+1 := by
    rw [Finset.eventually_all]
    intro n hn
    have hdiff := differentiableAt_sourceNormalizedActionComplexExtension_of_realType
      hp hp1 φ hreal n
    have hcont : ContinuousAt (fun ψ : CoeffPair p => ‖a ψ n‖) φ := by
      have hda : DifferentiableAt ℂ (fun ψ : CoeffPair p => a ψ n) φ := by
        change DifferentiableAt ℂ (fun ψ : CoeffPair p =>
          4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1) φ
        exact (hdiff.const_mul 4).sub_const 1
      exact hda.continuousAt.norm
    have hlt : ‖a φ n‖ < ‖a φ n‖+1 := by linarith
    filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with ψ hψ
    exact hψ.le
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  let V := V₀ ∩ U
  let B : ℝ := ∑ n ∈ s, (‖a φ n‖+1)
  let M : ℝ := s.card*B+L
  refine ⟨V,hV₀open.inter hUopen,⟨hφV₀,hφU⟩,M,?_⟩
  intro ψ hψ
  obtain ⟨A,T,hA,hT,hTnorm⟩ := hdata ψ hψ.1
  have hcenter (n : ℤ) (hn : n ∈ s) : ‖A n‖ ≤ B := by
    calc
      ‖A n‖ = ‖a ψ n‖ := by rw [hA n]
      _ ≤ ‖a φ n‖+1 := hUsub hψ.2 n hn
      _ ≤ B := Finset.single_le_sum (f := fun k => ‖a φ k‖+1)
        (fun k _ => by positivity) hn
  have hout (n : ℤ) (hn : n ∉ s) : A n = T n := by
    have hKn : K ≤ n.natAbs := by
      simp only [s,Finset.mem_Icc] at hn
      omega
    rw [hA n,hT n,if_pos hKn]
  refine ⟨A,hA,?_⟩
  exact (Coeff.norm_le_of_eq_outside_finset A T s B hcenter hout).trans
    (add_le_add_right hTnorm _)

end NLS.ZakharovShabat
