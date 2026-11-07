import NLS.KdV.HillL2AbelianHilbertWeights
import NLS.KdV.HillAbelianUniformValueBound
import NLS.SequenceSpaces.WeightedPositiveReciprocalSumBound

/-! The ENTIRE original physical off-index correction, and its full
absolute series, decay by one index order on complex L2 neighborhoods.
One retained patch and its original family estimates precede ALL indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

private theorem common_preimage_witness_bound {X Y Z I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (L : X → Y) (hL : Continuous L) (q : X)
    (S : Set Y) (V : Set Y) (hV : IsOpen V) (hqV : L q ∈ V) (hVS : V ⊆ S)
    (Uw : Set X) (hUw : IsOpen Uw) (hqUw : q ∈ Uw) (D : Y → Z → Prop)
    (F G : Y → I → ℝ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ x ∈ Uw, ∃ z, D (L x) z)
    (hb : ∀ y ∈ V, ∀ z, D y z → ∀ i, F y i ≤ R ∧ G y i ≤ R) :
    ∃ U : Set X, IsOpen U ∧ q ∈ U ∧ (∀ x ∈ U, L x ∈ S) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, F (L x) i ≤ R ∧ G (L x) i ≤ R := by
  refine ⟨Uw ∩ L ⁻¹' V,hUw.inter (hV.preimage hL),⟨hqUw,hqV⟩,
    (fun x hx => hVS hx.2),R,hR,?_⟩
  intro x hx i
  obtain ⟨z,hz⟩ := hw x hx.1
  exact hb (L x) hx.2 z hz i

private theorem weighted_physical_series_of_majorants (P : HillProductEquationPatch)
    (a : PeriodOneHminusOne) (G D : Coeff 2) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ m : ℕ+, (1+(m:ℝ))*(
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤ ‖G ((m:ℕ):ℤ)‖+‖D ((m:ℕ):ℤ)‖)
    (n : ℕ+)
    (hvalue : ∀ m : ℕ+, m ≠ n → ‖P.physicalOffIndexAbelianValue n m a‖ ≤ C*
      (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
          (1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ)))) :
    (1+(n:ℝ))*(∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n a m‖) ≤
        C*(‖G‖+‖D‖)*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖) ∧
      (1+(n:ℝ))*‖P.physicalOffIndexAbelianCorrection n a‖ ≤
        C*(‖G‖+‖D‖)*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖) := by
  let g : ℕ+ → ℝ := fun m =>
    ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
      ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖
  have hu (m : ℕ+) (hmn : m ≠ n) : ‖P.physicalOffIndexAbelianTerm n a m‖ ≤
      C*g m*(1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ))) := by
    simpa only [physicalOffIndexAbelianTerm,if_neg hmn,g,P.physicalAbelianMidpointDisplacement_apply] using hvalue m hmn
  obtain ⟨_,habs,hnorm⟩ := Coeff.weighted_norm_positive_sum_le_of_reciprocal_bound G D g
    (fun m => by dsimp [g]; positivity) hw n (P.physicalOffIndexAbelianTerm n a)
      (by simp [physicalOffIndexAbelianTerm]) C hC hu
  exact ⟨habs,hnorm⟩

private theorem weighted_constant_bound (C M : ℝ) (hC : 0 ≤ C) (G D : Coeff 2)
    (hGD : ‖G‖+‖D‖ ≤ M) :
    C*(‖G‖+‖D‖)*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖) ≤
      C*M*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖)+1 := by
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGD hC)
    (show 0 ≤ 3*‖Coeff.puncturedLattice 2 (by norm_num)‖ by positivity)
  linarith

private theorem assemble_weighted_point (P : HillProductEquationPatch) (a : PeriodOneHminusOne)
    (C M : ℝ) (hC : 0 ≤ C)
    (hvalue : ∀ n m : ℕ+, m ≠ n → ‖P.physicalOffIndexAbelianValue n m a‖ ≤ C*
      (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
          (1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ))))
    (hwit : ∃ G D : Coeff 2, ‖G‖+‖D‖ ≤ M ∧ ∀ m : ℕ+,
      (1+(m:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤ ‖G ((m:ℕ):ℤ)‖+‖D ((m:ℕ):ℤ)‖) :
    ∀ n : ℕ+,
      (1+(n:ℝ))*(∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n a m‖) ≤ C*M*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖)+1 ∧
      (1+(n:ℝ))*‖P.physicalOffIndexAbelianCorrection n a‖ ≤ C*M*(3*‖Coeff.puncturedLattice 2 (by norm_num)‖)+1 := by
  obtain ⟨G,D,hGD,hw⟩ := hwit
  intro n
  have hb := P.weighted_physical_series_of_majorants a G D C hC hw n (hvalue n)
  have hc := weighted_constant_bound C M hC G D hGD
  exact ⟨hb.1.trans hc,hb.2.trans hc⟩

private theorem assemble_weighted_neighborhood (P : HillProductEquationPatch) (q : Coeff 2)
    (hv : ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ periodOneL2Inclusion q ∈ V ∧ V ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ V, ∀ n m : ℕ+, m ≠ n →
        ‖P.physicalOffIndexAbelianValue n m a‖ ≤ C*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
              (1/|(n:ℝ)-(m:ℝ)|+1/((n:ℝ)+(m:ℝ))))
    (hw : ∃ Uw : Set (Coeff 2), IsOpen Uw ∧ q ∈ Uw ∧ (∀ r ∈ Uw, periodOneL2Inclusion r ∈ P.source) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ r ∈ Uw, ∃ G D : Coeff 2, ‖G‖+‖D‖ ≤ M ∧ ∀ m : ℕ+,
        (1+(m:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi (periodOneL2Inclusion r)) ((m:ℕ):ℤ)‖+
          ‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((m:ℕ):ℤ)‖) ≤ ‖G ((m:ℕ):ℤ)‖+‖D ((m:ℕ):ℤ)‖) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r ∈ U, ∀ n : ℕ+,
        (1+(n:ℝ))*(∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n (periodOneL2Inclusion r) m‖) ≤ R ∧
        (1+(n:ℝ))*‖P.physicalOffIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ R := by
  obtain ⟨V,hV,hqV,hVP,C,hC,hvalue⟩ := hv
  obtain ⟨Uw,hUw,hqUw,_,M,hM,hweights⟩ := hw
  let κ := Coeff.puncturedLattice 2 (by norm_num : 1 < (2:ℝ≥0∞))
  let R := C*M*(3*‖κ‖)+1
  let D : PeriodOneHminusOne → (Coeff 2 × Coeff 2) → Prop := fun a z =>
    ‖z.1‖+‖z.2‖ ≤ M ∧ ∀ m : ℕ+,
      (1+(m:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤ ‖z.1 ((m:ℕ):ℤ)‖+‖z.2 ((m:ℕ):ℤ)‖
  apply common_preimage_witness_bound periodOneL2Inclusion periodOneL2Inclusion.continuous q
    P.physicalDirichletSource V hV hqV hVP Uw hUw hqUw D
    (fun (a : PeriodOneHminusOne) (n : ℕ+) => (1+(n:ℝ))*(∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n a m‖))
    (fun (a : PeriodOneHminusOne) (n : ℕ+) => (1+(n:ℝ))*‖P.physicalOffIndexAbelianCorrection n a‖) R (by dsimp [R]; positivity)
  · intro r hr
    obtain ⟨G,D,hGD,hb⟩ := hweights r hr
    exact ⟨(G,D),hGD,hb⟩
  · intro a ha z hz
    exact P.assemble_weighted_point a C M hC.le (hvalue a ha) ⟨z.1,z.2,hz⟩

theorem exists_local_l2OffIndex_weighted_correction_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r ∈ U, ∀ n : ℕ+,
        (1+(n:ℝ))*(∑' m : ℕ+, ‖P.physicalOffIndexAbelianTerm n (periodOneL2Inclusion r) m‖) ≤ R ∧
        (1+(n:ℝ))*‖P.physicalOffIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ R :=
  P.assemble_weighted_neighborhood q
    (P.exists_local_uniform_physicalOffIndexAbelianValue_bound H _ hq hr)
    (P.exists_local_l2Abelian_Hilbert_weight_majorants q hq hr)

end NLS.KdV.HillProductEquationPatch
