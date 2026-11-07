import NLS.KdV.HillL2AbelianHilbertWeights
import NLS.KdV.HillMomentWeightedSeriesBounds
import NLS.SequenceSpaces.BoundedPositiveMomentSeries

/-! The full original second-moment series is UNIFORMLY BOUNDED
before all positive frequency indices on one complex L2 neighborhood.
The original spectral patch and primitive neighborhood are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

private theorem common_preimage_witness_bound {X Y Z I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (L : X → Y) (hL : Continuous L)
    (q : X) (S : Set Y) (hS : IsOpen S) (hqS : L q ∈ S)
    (V : Set X) (hV : IsOpen V) (hqV : q ∈ V)
    (E : Y → Z → Prop) (F : Y → I → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hw : ∀ x ∈ V, ∃ z, E (L x) z)
    (hb : ∀ y ∈ S, ∀ z, E y z → ∀ i, F y i ≤ R) :
    ∃ U : Set X, IsOpen U ∧ q ∈ U ∧ (∀ x ∈ U, L x ∈ S) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ U, ∀ i, F (L x) i ≤ R := by
  refine ⟨V ∩ L ⁻¹' S,hV.inter (hS.preimage hL),⟨hqV,hqS⟩,
    (fun _ hx => hx.2),R,hR,?_⟩
  intro x hx i
  obtain ⟨z,hz⟩ := hw x hx.1
  exact hb (L x) hx.2 z hz i

private theorem moment_bound_of_majorants (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (a : PeriodOneHminusOne)
    (hfull : ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (G E : Coeff 2) (M : ℝ) (hGE : ‖G‖+‖E‖ ≤ M)
    (hw : ∀ m : ℕ+, (1+(m:ℝ))*(
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤
          ‖G ((m:ℕ):ℤ)‖+‖E ((m:ℕ):ℤ)‖) (n : ℕ+) :
    ‖P.centeredSecondMomentSeries D.ambient n a‖ ≤
      (2*Real.pi*D.constant)*(1+‖Coeff.puncturedLattice 2 (by norm_num)‖)*M^2 := by
  let H : Coeff 2 := Coeff.magnitude G+Coeff.magnitude E
  have hH (k : ℤ) : ‖H k‖=‖G k‖+‖E k‖ := by
    have he : H k=((‖G k‖+‖E k‖:ℝ):ℂ) := by
      simp only [H,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,ofReal_add]
    rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hnorm : ‖H‖ ≤ M := (norm_add_le _ _).trans (by
    simpa only [Coeff.norm_magnitude] using hGE)
  let g : ℕ+ → ℝ := fun m =>
    ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖
  have hweight (m : ℕ+) : (1+(m:ℝ))*g m ≤ ‖H ((m:ℕ):ℤ)‖ := by
    rw [hH]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
      (by positivity : 0 ≤ 1+(m:ℝ))).trans (hw m)
  have hC := D.constant_pos
  have hu (i m : ℕ+) : ‖P.centeredMoment D.ambient i m 1 a‖ ≤
      (2*Real.pi*D.constant)*(g m)^2*
        (if m=i then 1 else 1/|((i:ℕ):ℝ)-(m:ℕ)|+1/((i:ℕ)+(m:ℕ):ℝ)) := by
    have he (z : ℂ) : ‖z‖=2*Real.pi*‖(2*Real.pi:ℂ)⁻¹*z‖ := by
      simp only [norm_mul,norm_inv,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      field_simp
    rw [he (P.centeredMoment D.ambient i m 1 a)]
    simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left (hfull i m) (by positivity : 0 ≤ 2*Real.pi)
  have hb := (Coeff.norm_positive_moment_series_le_of_Hilbert_majorant H g
    (fun _ => norm_nonneg _) hweight (fun i m => P.centeredMoment D.ambient i m 1 a)
      (2*Real.pi*D.constant) (by positivity) hu n).2
  exact hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg H) hnorm 2) (by positivity))

theorem exists_local_l2CenteredSecondMomentSeries_bound (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood)
    (hfull : ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧ (∀ r ∈ U, periodOneL2Inclusion r ∈ D.source) ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ U, ∀ n : ℕ+,
        ‖P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)‖ ≤ R := by
  obtain ⟨V,hV,hqV,_,M,_,hweights⟩ :=
    P.exists_local_l2Abelian_Hilbert_weight_majorants q (D.subset hq).1 hr
  have hC := D.constant_pos
  let E : PeriodOneHminusOne → (Coeff 2 × Coeff 2) → Prop := fun a z =>
    ‖z.1‖+‖z.2‖ ≤ M ∧ ∀ m : ℕ+, (1+(m:ℝ))*(
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤
          ‖z.1 ((m:ℕ):ℤ)‖+‖z.2 ((m:ℕ):ℤ)‖
  apply common_preimage_witness_bound periodOneL2Inclusion periodOneL2Inclusion.continuous
    q D.source D.source_open hq V hV hqV E
    (fun (a : PeriodOneHminusOne) (n : ℕ+) => ‖P.centeredSecondMomentSeries D.ambient n a‖)
    ((2*Real.pi*D.constant)*(1+‖Coeff.puncturedLattice 2 (by norm_num)‖)*M^2) (by positivity)
  · intro r hrV
    obtain ⟨G,E,hGE,hw⟩ := hweights r hrV
    exact ⟨(G,E),hGE,hw⟩
  · intro a ha z hz n
    exact P.moment_bound_of_majorants D a (hfull a ha) z.1 z.2 M hz.1 hz.2 n

end NLS.KdV.HillProductEquationPatch
