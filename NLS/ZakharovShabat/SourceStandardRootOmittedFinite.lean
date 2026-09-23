import NLS.ZakharovShabat.SourceStandardRootPairedProductJointAnalytic
import NLS.ZakharovShabat.SingleSpectralProducts

/-!
# Finite standard-root products with an arbitrary omitted index

Lemma 10.5 uses the normalization `π₀ = 1` and `πₙ = nπ` for `n ≠ 0`.
This file defines its literal symmetric finite cutoffs, proves their joint
analyticity, and constructs their common open moving-gap domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The spectral domain of the product whose `n`th standard root is omitted. -/
def sourceStandardRootOmittedDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : Set ℂ :=
  {z | ∀ m : ℤ, m ≠ n → z ∉ sourcePeriodicSegment hp hp1 ψ m}

/-- The corresponding domain in the joint spectral/source space. -/
def sourceStandardRootOmittedJointDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) : Set (ℂ × CoeffPair p) :=
  {t | t.2 ∈ W ∧ t.1 ∈ sourceStandardRootOmittedDomain hp hp1 t.2 n}

@[simp] theorem sourceStandardRootOmittedDomain_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    sourceStandardRootOmittedDomain hp hp1 ψ 0 =
      sourceStandardRootPairedDomain hp hp1 ψ := rfl

@[simp] theorem sourceStandardRootOmittedJointDomain_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) :
    sourceStandardRootOmittedJointDomain hp hp1 W 0 =
      sourceStandardRootPairedJointDomain hp hp1 W := rfl

/-- The literal symmetric cutoff of the product in Lemma 10.5. -/
def sourceStandardRootOmittedPartialProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (N : ℕ) : ℂ × CoeffPair p → ℂ :=
  fun t => (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
    sourceStandardRoot hp hp1 t.2 m t.1 / singleSpectralDenominator m) /
    singleSpectralDenominator n

/-- The arbitrary-index cutoff specializes exactly to the paired cutoff
when the omitted index is zero. -/
theorem sourceStandardRootOmittedPartialProduct_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (N : ℕ) :
    sourceStandardRootOmittedPartialProduct hp hp1 0 N (z,ψ) =
      sourceStandardRootPairedPartialProduct hp hp1 ψ z N := by
  let f (m : ℤ) := sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m
  let g (m : ℤ) := if m = 0 then (1 : ℂ) else f m
  let s : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hprod : (∏ m ∈ s.erase 0, f m) = ∏ m ∈ s, g m := by
    calc
      _ = ∏ m ∈ s.erase 0, g m := Finset.prod_congr rfl (by
        intro m hm
        simp [g, (Finset.mem_erase.mp hm).1])
      _ = ∏ m ∈ s, g m := Finset.prod_erase s (by simp [g])
  unfold sourceStandardRootOmittedPartialProduct sourceStandardRootPairedPartialProduct
  simp only [singleSpectralDenominator, if_pos, div_one]
  change (∏ m ∈ s.erase 0, f m) = _
  rw [hprod, prod_symmetric_interval]
  simp only [g, if_pos, one_mul]
  apply Finset.prod_congr rfl
  intro j hj
  have hjpos : (j : ℤ)+1 ≠ 0 := by omega
  have hjneg : -1 + -(j : ℤ) ≠ 0 := by omega
  simp [f, singleSpectralDenominator, sourceStandardRootPairedFactor, hjpos, hjneg]
  left
  congr 1
  ring

/-- Every finite cutoff is nonzero on its arbitrary-index gap complement. -/
theorem sourceStandardRootOmittedPartialProduct_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (t : ℂ × CoeffPair p)
    (ht : t.1 ∈ sourceStandardRootOmittedDomain hp hp1 t.2 n) :
    sourceStandardRootOmittedPartialProduct hp hp1 n N t ≠ 0 := by
  unfold sourceStandardRootOmittedPartialProduct
  apply div_ne_zero _ (singleSpectralDenominator_ne_zero n)
  apply Finset.prod_ne_zero_iff.mpr
  intro m hm
  exact div_ne_zero
    (sourceStandardRoot_ne_zero_off_segment hp hp1 t.2 m t.1
      (ht m (Finset.mem_erase.mp hm).1))
    (singleSpectralDenominator_ne_zero m)

/-- A fixed omitted index does not obstruct openness of the moving-gap
complement. Only finitely many gap incidences matter near each point. -/
theorem isOpen_sourceStandardRootOmittedJointDomain_of_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (hWopen : IsOpen W)
    (hA : ∀ ψ ∈ W, ∀ m : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) m) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) m)^2) ψ)
    (n : ℤ) :
    IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨z,φ⟩ ⟨hφ, hz⟩
  obtain ⟨N, V, hVopen, hφV, htail⟩ :=
    exists_uniform_sourcePeriodicSegment_tail_avoids_ball hp hp1 φ z
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) N).erase n
  let A (k : ℤ) : Set (ℂ × CoeffPair p) :=
    {t | t.1 ∉ sourcePeriodicSegment hp hp1 t.2 k}
  have hfinite (k : ℤ) (hk : k ∈ s) : A k ∈ 𝓝 (z,φ) := by
    have hkn : k ≠ n := (Finset.mem_erase.mp hk).1
    obtain ⟨U, hUopen, hbaseU, hUsub⟩ :=
      exists_joint_neighborhood_avoids_sourcePeriodicSegment hp hp1 φ z k
        (hA φ hφ k).1 (hA φ hφ k).2 (hz k hkn)
    exact Filter.mem_of_superset (hUopen.mem_nhds hbaseU) hUsub
  have hfinnear : (⋂ k ∈ s, A k) ∈ 𝓝 (z,φ) :=
    (Filter.biInter_finset_mem s).mpr hfinite
  have hWnear : {t : ℂ × CoeffPair p | t.2 ∈ W} ∈ 𝓝 (z,φ) :=
    (hWopen.preimage continuous_snd).mem_nhds hφ
  have hVnear : {t : ℂ × CoeffPair p | t.2 ∈ V} ∈ 𝓝 (z,φ) :=
    (hVopen.preimage continuous_snd).mem_nhds hφV
  have hballnear : {t : ℂ × CoeffPair p | t.1 ∈ Metric.ball z 1} ∈ 𝓝 (z,φ) :=
    (isOpen_ball.preimage continuous_fst).mem_nhds
      (mem_ball_self (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hWnear, hVnear, hballnear, hfinnear] with t htW htV htball htfin
  refine ⟨htW, ?_⟩
  intro k hkn
  by_cases hk : k ∈ s
  · exact (Set.mem_iInter.mp (Set.mem_iInter.mp htfin k) hk)
  · have hlarge : N < k.natAbs := by
      have hnotIcc : k ∉ Finset.Icc (-(N : ℤ)) N := by
        intro hIcc
        exact hk (Finset.mem_erase.mpr ⟨hkn, hIcc⟩)
      simp only [Finset.mem_Icc] at hnotIcc
      omega
    exact (htail t.2 htV k hlarge) htball

/-- On the arbitrary-index domain, every literal finite cutoff is jointly
analytic. This includes points on the omitted gap itself. -/
theorem sourceStandardRootOmittedPartialProduct_analyticAt_of_symmetric
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hA : ∀ ψ ∈ W, ∀ m : ℤ,
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) m) ψ ∧
      AnalyticAt ℂ (fun χ : CoeffPair p =>
        (canonicalPeriodicGap hp hp1 (periodOnePotential χ)
          (periodOnePotential_mem χ) m)^2) ψ)
    (n : ℤ) (N : ℕ) (t : ℂ × CoeffPair p)
    (ht : t ∈ sourceStandardRootOmittedJointDomain hp hp1 W n) :
    AnalyticAt ℂ (sourceStandardRootOmittedPartialProduct hp hp1 n N) t := by
  have hroot (m : ℤ) (hm : m ≠ n) :
      AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
        sourceStandardRoot hp hp1 q.2 m q.1) t :=
    sourceStandardRoot_joint_analyticAt_of_symmetric hp hp1 t.2 m t.1
      (hA t.2 ht.1 m).1 (hA t.2 ht.1 m).2 (ht.2 m hm)
  change AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
    (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      sourceStandardRoot hp hp1 q.2 m q.1 / singleSpectralDenominator m) /
    singleSpectralDenominator n) t
  exact ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n).analyticAt_fun_prod
    (fun m hm => (hroot m (Finset.mem_erase.mp hm).1).div_const) |>.div_const

/-- One connected almost-real source neighborhood supports all arbitrary
omissions, with open joint domains and analytic literal finite cutoffs. -/
theorem exists_global_source_open_analytic_omittedPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ n : ℤ, IsOpen (sourceStandardRootOmittedJointDomain hp hp1 W n) ∧
        ∀ N : ℕ,
        AnalyticOnNhd ℂ (sourceStandardRootOmittedPartialProduct hp hp1 n N)
          (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  obtain ⟨W, hWopen, hWconnected, hreal, hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W, hWopen, hWconnected, hreal, ?_⟩
  intro n
  refine ⟨isOpen_sourceStandardRootOmittedJointDomain_of_analytic hp hp1 W hWopen hA n,
    ?_⟩
  intro N t ht
  exact sourceStandardRootOmittedPartialProduct_analyticAt_of_symmetric
      hp hp1 W hA n N t ht

end NLS.ZakharovShabat
