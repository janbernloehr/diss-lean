import NLS.KdV.HillProductCoordinateBounds
import NLS.KdV.HillProductJointPeriods

/-! The actual retained weighted Hill periods form an inverse-index
l2 sequence under the proved original quotient bound. The l2 majorant
retains root, midpoint and gap displacements and ONE bound BEFORE ALL n. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

def hillProductFrequencyMajorant (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) :
    lp (fun _ : ℕ+ => ℂ) 2 :=
  LpSequence.positiveRestriction (Coeff.magnitude (hillIndependentFrequencyDisplacement (c,d))+
    Coeff.magnitude (sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ)+
    Coeff.magnitude (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ))

theorem norm_hillProductFrequencyMajorant_apply (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (ψ : CoeffPair 2) (m : ℕ+) :
    ‖hillProductFrequencyMajorant c d ψ m‖ =
      ‖hillIndependentFrequencyDisplacement (c,d) ((m:ℕ):ℤ)‖+
      ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖+
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖ := by
  change ‖(‖hillIndependentFrequencyDisplacement (c,d) ((m:ℕ):ℤ)‖:ℂ)+
    (‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖:ℂ)+
    (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖:ℂ)‖ = _
  rw [← Complex.ofReal_add,← Complex.ofReal_add,Complex.norm_real,Real.norm_of_nonneg (by positivity)]

theorem norm_hillProductFrequencyMajorant_le (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (ψ : CoeffPair 2) :
    ‖hillProductFrequencyMajorant c d ψ‖ ≤ ‖hillIndependentFrequencyDisplacement (c,d)‖+
      ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖+
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ‖ := by
  have h := LpSequence.norm_positiveRestriction_le
    (Coeff.magnitude (hillIndependentFrequencyDisplacement (c,d))+
      Coeff.magnitude (sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ)+
      Coeff.magnitude (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ))
  exact h.trans ((norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans_eq (by
    simp only [Coeff.norm_magnitude])))

def hillRetainedProductPeriodRow (n m : ℕ+) (a R : ℤ → ℝ)
    (t : lp (fun _ : ℕ+ => ℂ) 2 × (ℂ × CoeffPair 2)) : ℂ :=
  if m = n then 0 else hillPeriodEquationWeight n m*
    hillEnergyProductJointPeriod n (a ((m:ℕ):ℤ):ℂ) (R ((m:ℕ):ℤ)) t

theorem norm_hillRetainedProductPeriodRow_le
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (a R : ℤ → ℝ) (hR : ∀ k, 0 < R k) (he : ∀ k, D k = Metric.ball (a k:ℂ) (R k))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hquot : ∀ k : ℤ, ∀ z ∈ D k,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q)
    (n m : ℕ+) :
    ‖hillRetainedProductPeriodRow n m a R (d,(c,ψ))‖ ≤
      (2*Real.pi*(Real.pi^2*C*(C*Q)))*‖hillProductFrequencyMajorant c d ψ m‖ := by
  have hc : 0 ≤ C := zero_le_one.trans hD.one_le
  by_cases hmn : m = n
  · simp only [hillRetainedProductPeriodRow,if_pos hmn,norm_zero]
    positivity
  have hrow : hillRetainedProductPeriodRow n m a R (d,(c,ψ)) =
      hillPeriodEquationWeight n m*hillEnergyProductFixedPeriod n c ψ
        (hD.periodCircle ψ hψV ((m:ℕ):ℤ) (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ)) (hR _) (he _)) d := by
    rw [hillRetainedProductPeriodRow,if_neg hmn]
    rfl
  have hb := hillWeightedProductPeriod_coordinate_bound H hD ψ hψW hψV c d hplace n m hmn
    (a ((m:ℕ):ℤ)) (R ((m:ℕ):ℤ)) (hR _) (he _) Q (hquot ((m:ℕ):ℤ))
  have hscale : ‖hillRetainedProductPeriodRow n m a R (d,(c,ψ))‖ =
      (2*Real.pi)*‖(2*Real.pi:ℂ)⁻¹*hillRetainedProductPeriodRow n m a R (d,(c,ψ))‖ := by
    rw [norm_mul,norm_inv,norm_mul]
    simp only [Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    field_simp
  rw [hscale,hrow]
  calc
    _ ≤ (2*Real.pi)*((‖hillIndependentFrequencyDisplacement (c,d) ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ ((m:ℕ):ℤ)‖)*(Real.pi^2*C*(C*Q))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [norm_hillProductFrequencyMajorant_apply]; ring

theorem exists_hillRetainedProductPeriodSequence_of_quotient_bound
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (a R : ℤ → ℝ) (hR : ∀ k, 0 < R k) (he : ∀ k, D k = Metric.ball (a k:ℂ) (R k))
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hquot : ∀ k : ℤ, ∀ z ∈ D k,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) k
        (z,(hillIndependentFrequencyDisplacement (c,d),ψ))‖ ≤ Q)
    (n : ℕ+) :
    ∃ F : lp (fun _ : ℕ+ => ℂ) 2,
      (∀ m, F m = hillRetainedProductPeriodRow n m a R (d,(c,ψ))) ∧
      ‖F‖ ≤ (2*Real.pi*(Real.pi^2*C*(C*Q)))*
        (‖hillIndependentFrequencyDisplacement (c,d)‖+
          ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖+
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ‖) := by
  let K := 2*Real.pi*(Real.pi^2*C*(C*Q))
  have hK : 0 ≤ K := by have hc := hD.one_le; dsimp only [K]; positivity
  let B : lp (fun _ : ℕ+ => ℂ) 2 := (K:ℂ) • hillProductFrequencyMajorant c d ψ
  have hB (m : ℕ+) : ‖B m‖ = K*‖hillProductFrequencyMajorant c d ψ m‖ := by
    change ‖(K:ℂ)*hillProductFrequencyMajorant c d ψ m‖ = _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hK]
  have hbound (m : ℕ+) : ‖hillRetainedProductPeriodRow n m a R (d,(c,ψ))‖ ≤ ‖B m‖ := by
    rw [hB]
    exact norm_hillRetainedProductPeriodRow_le H hD ψ hψW hψV c d hplace a R hR he Q hQ hquot n m
  let F : lp (fun _ : ℕ+ => ℂ) 2 := ⟨_,(lp.memℓp B).mono' hbound⟩
  refine ⟨F,fun _ => rfl,?_⟩
  calc
    ‖F‖ ≤ ‖B‖ := lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0) hbound
    _ = K*‖hillProductFrequencyMajorant c d ψ‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hK]
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_hillProductFrequencyMajorant_le c d ψ) hK

theorem exists_hillRetainedProductPeriodSequence
    {W V : Set (CoeffPair 2)} (H : SourceCorollary10_6Data (by norm_num) (by norm_num) W)
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (hV : IsOpen V) (ψ : CoeffPair 2) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency (c,d) k ∈ D k)
    (a R : ℤ → ℝ) (hR : ∀ k, 0 < R k) (he : ∀ k, D k = Metric.ball (a k:ℂ) (R k)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ+, ∃ F : lp (fun _ : ℕ+ => ℂ) 2,
      (∀ m, F m = hillRetainedProductPeriodRow n m a R (d,(c,ψ))) ∧
      ‖F‖ ≤ K*(‖hillIndependentFrequencyDisplacement (c,d)‖+
        ‖sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) ψ‖+
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) ψ‖) := by
  obtain ⟨U,_,hbase,Q,hQ,hquot⟩ := H.local_allDisk_quotient_bound hD hV ψ hψW hψV
    (hillIndependentFrequencyDisplacement (c,d))
  refine ⟨2*Real.pi*(Real.pi^2*C*(C*Q)),?_,?_⟩
  · have hc := hD.one_le
    positivity
  · intro n
    exact exists_hillRetainedProductPeriodSequence_of_quotient_bound H hD ψ hψW hψV c d hplace
      a R hR he Q hQ (fun k z hz => hquot _ hbase k z hz) n

end NLS.KdV
