import NLS.ZakharovShabat.SourcePsiOriginalRootFamily
import NLS.ZakharovShabat.SourcePsiOriginalQuotientError

/-!
# Quotient errors uniformly over the original analytic root family

At any complex base source, compactness of the filled root family and
uniform graph continuity turn the local joint quotient bounds into one
lp bound for every deleted index on all supplied original disks.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {D : ℤ → Set ℂ} {c : ℝ}

/-- The full original quotient disk errors have one lp bound for all actual branches. -/
theorem SourceLemma12_11Data.original_allDisk_quotient_errorBound
    (H : SourceLemma12_11Data hp hp1 W₀ W s)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hψV : ψ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∩ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D
          (sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n),χ) m : ℂ)) ∧
        ∀ m : ℤ, ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n),χ))-1‖ ≤ ‖E m‖ := by
  obtain ⟨K,hK,hroots⟩ := H.original_filled_rootFamily_compact ψ hψ
  let g : Coeff p × (Coeff p × CoeffPair p) → Coeff p × CoeffPair p :=
    fun q => (q.1+q.2.1,q.2.2)
  have hg : Continuous g := by fun_prop
  let P := fun (q : Coeff p × (Coeff p × CoeffPair p)) (C : ℝ) =>
    ∃ E : Coeff p, ‖E‖ ≤ C ∧
      (∀ m : ℤ, E m = (sourceQuotientDiscSup hp hp1 D (g q) m : ℂ)) ∧
      ∀ m : ℤ, ∀ z ∈ D m, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,g q)-1‖ ≤ ‖E m‖
  obtain ⟨O,hO,hbase,C,hC,hbound⟩ := NLS.ComplexAnalysis.exists_uniform_property_near_compact_slice
    K hK ((0:Coeff p),ψ) P (by
      rintro q C L hCL ⟨E,hE,he,hb⟩
      exact ⟨E,hE.trans hCL,he,hb⟩) (by
      intro a _
      obtain ⟨T,hT,hbase,L,hL,hb⟩ := H.previous.psi.previous.quotients.local_allDisk_quotient_errorBound
        hD hV ψ (H.previous.subset hψ) hψV a
      refine ⟨g ⁻¹' T,hT.preimage hg,?_,L,hL,fun q hq => hb (g q) hq⟩
      simpa only [mem_preimage,g,add_zero] using hbase)
  obtain ⟨ε,hε,hεball⟩ := Metric.isOpen_iff.mp hO (0,ψ) hbase
  obtain ⟨r,hr,hrW,hclose⟩ := H.original_filled_graph_radius ψ hψ ε hε
  refine ⟨ball ψ r ∩ V,isOpen_ball.inter hV,⟨mem_ball_self hr,hψV⟩,
    (fun χ hχ => ⟨hrW hχ.1,hχ.2⟩),C,hC,?_⟩
  intro χ hχ n
  let a := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  let b := sourcePsiFillDeletedRoot n (s n χ) (sourceStandardRootMidpoint hp hp1 χ n)
  have ht : (b-a,χ) ∈ O := by
    apply hεball
    rw [mem_ball,Prod.dist_eq,dist_zero_right]
    have hh : max (dist b a) (dist χ ψ) < ε := hclose χ hχ.1 n
    simpa only [dist_eq_norm] using hh
  have hb := hbound (b-a,χ) ht a (hroots n)
  simpa only [P,g,add_sub_cancel] using hb

end NLS.ZakharovShabat
