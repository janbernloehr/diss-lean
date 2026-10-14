import NLS.ZakharovShabat.SourcePsiOriginalZetaAsymptotic
import NLS.ZakharovShabat.SourceLemma12_4
import NLS.SequenceSpaces.CoordinateNormSup

/-!
# Equation (2.26) with literal disk suprema

The lp error is represented by its actual disk-supremum sequence, with
zero at the omitted row. One neighborhood and both constants precede the
choice of omitted index. The original source domain and disks are retained.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiZetaSequenceDiscSup (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (D : ℤ → Set ℂ) (n : ℤ) (a : Coeff p) (ψ : CoeffPair p) (m : ℤ) : ℝ :=
  sSup ((fun z => ‖if m = n then 0 else sourcePsiZetaSequenceTerm hp hp1 φ n m a ψ z‖) '' D m)

theorem SourceCorollary10_6Data.zeta_originalAsymptotic_sup
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ t ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        (∀ m : ℤ, E m = (sourcePsiZetaSequenceDiscSup hp hp1 φ D n t.1 t.2 m : ℂ)) ∧
        E n = 0 ∧ ∀ m : ℤ, m ≠ n → ∀ z ∈ D m,
          ‖sourcePsiZetaReciprocalTerm hp hp1 φ n m z‖ ≤ K/‖((n-m:ℤ):ℂ)‖ ∧
          ‖sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 z‖ ≤ ‖E m‖ := by
  obtain ⟨U,hU,hbase,hUV,K,C,hK,hC,hb⟩ := H.zeta_originalAsymptotic hW hD hV φ hφW hφV a₀
  have hne (m : ℤ) : (D m).Nonempty := by
    obtain ⟨d,r,hr,he⟩ := hD.discs m
    rw [he]
    exact nonempty_ball.mpr hr
  refine ⟨U,hU,hbase,hUV,K,C,hK,hC,?_⟩
  intro t ht n
  obtain ⟨E,hE,hpoint⟩ := hb t ht n
  let f : ℤ → ℂ → ℂ := fun m z => if m = n then 0 else sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 z
  obtain ⟨B,hB,hBpoint,hBn⟩ := NLS.exists_coordinateNormSup (zero_lt_one.trans hp1).ne' D hne f E (by
    intro m z hz
    by_cases hm : m = n
    · simp only [f,if_pos hm,norm_zero]
      exact norm_nonneg _
    · simpa only [f,if_neg hm] using (hpoint m hm z hz).2)
  refine ⟨B,hBn.trans hE,hB,?_,?_⟩
  · rw [hB n]
    simp [f,(hne n).image_const (0:ℝ)]
  · intro m hm z hz
    exact ⟨(hpoint m hm z hz).1,by simpa only [f,if_neg hm] using hBpoint m z hz⟩

/-- Equation (2.26) at every complex base in the same original W from
Lemma 12.4, for every arbitrary full root-input sequence. -/
theorem SourceLemma12_4Data.equation2_26
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ D : ℤ → Set ℂ, ∃ c : ℝ, SourceIsolatingNeighborhoods hp hp1 V D c ∧
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
        ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ t ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
          (∀ m : ℤ, E m = (sourcePsiZetaSequenceDiscSup hp hp1 φ D n t.1 t.2 m : ℂ)) ∧
          E n = 0 ∧ ∀ m : ℤ, m ≠ n → ∀ z ∈ D m,
            ‖sourcePsiZetaReciprocalTerm hp hp1 φ n m z‖ ≤ K/‖((n-m:ℤ):ℂ)‖ ∧
            ‖sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 z‖ ≤ ‖E m‖ := by
  obtain ⟨V,hV,_,hφV,hVW,D,c,hD⟩ := H.previous.quotients.neighborhoods φ hφ
  exact ⟨V,hV,hφV,hVW,D,c,hD.toSourceIsolatingNeighborhoods,
    H.previous.quotients.zeta_originalAsymptotic_sup hW hD.toSourceIsolatingNeighborhoods hV φ hφ hφV a₀⟩

end NLS.ZakharovShabat
