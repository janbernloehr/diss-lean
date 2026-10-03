import NLS.ZakharovShabat.SourceMidpointPhysicalFourierBound

/-! # Summability of actual midpoint derivatives at real H¹ sources

The physical H¹ coefficients now supply the source operator majorant;
no derivative bound or contour premise is assumed. G.7's midpoint
summability follows from the actual canonical source contour identity.
-/

noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equality of physical coefficients supplies the continuous H¹ representative. -/
theorem physicalBase_source_sobolev_compatibility (φ : CoeffPair 2) (a : Domain 2)
    (ha : periodOnePotential φ = domainInclusion a) :
    physicalBase (periodOnePotential φ) =ᵐ[volume.restrict (Ioc 0 1)]
      extend (classicalSobolevPotential a) := by
  rw [ha]
  exact physicalBase_eq_extend_physicalDomainCurve a

/-- On one open neighborhood of the entire real source locus, every H¹
potential has an outer ℓp sequence of actual midpoint derivatives for finite
p ≥ 2. All contour geometry and integrand bounds are supplied by proofs. -/
theorem exists_global_source_midpoint_fderiv_sobolev_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ a : Domain 2, periodOnePotential φ = domainInclusion a →
      Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion h2p φ)) p := by
  classical
  let R := {φ : CoeffPair p // φ ∈ realTypeSourceLocus p}
  have hloc := fun φ : R => exists_local_source_midpoint_fderiv_tail_contour_bound hp hp1 φ.val φ.property
  choose U hU hmem N hlocal using hloc
  refine ⟨⋃ φ : R, U φ,isOpen_iUnion hU,?_,?_⟩
  · intro φ hφ
    exact mem_iUnion_of_mem (⟨φ,hφ⟩ : R) (hmem ⟨φ,hφ⟩)
  intro φ hφ a ha
  obtain ⟨ι,hι⟩ := mem_iUnion.mp hφ
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let q := ENNReal.ofReal (p.toReal/(p.toReal-1))
  have hq : ENNReal.ofReal (1+1/p.toReal) < q :=
    conjugate_exponent_ennreal_gt_gradient_threshold p.toReal hs
  have hq1 : 1 < q := lt_of_le_of_lt
    (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let : q.HolderConjugate p := by
    have hc := (Real.HolderConjugate.conjExponent hs).symm.ennrealOfReal
    simpa only [Real.conjExponent,q,ENNReal.ofReal_toReal hp] using hc
  obtain ⟨N₀,_,b,hb,h⟩ := exists_sourceMidpointContourIntegrand_sobolev_uniform_memlp
    hp hp1 h2p p.toReal hs hq ‖a‖ (norm_nonneg _)
  let F (n : ℤ) := fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion h2p φ)
  have hm : Memℓp F (ENNReal.ofReal p.toReal) := by
    apply memlp_of_natAbs_eventual_bound p.toReal (by linarith) F
      (fun n => (Real.pi/4)*b n) (hb.const_mul (Real.pi/4)) (max (N ι+1) N₀)
    intro n hn
    have hn₁ : N ι < n.natAbs := by omega
    have hn₂ : N₀ ≤ n.natAbs := le_trans (le_max_right _ _) hn
    exact (hlocal ι _ hι n hn₁).2.2 (b n)
      (h a le_rfl φ (physicalBase_source_sobolev_compatibility φ a ha) n hn₂)
  simpa only [ENNReal.ofReal_toReal hp] using hm

/-- In particular, every real H¹ source has the midpoint derivative estimate. -/
theorem memlp_real_source_midpoint_fderiv_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (hφ : φ ∈ realTypeSourceLocus 2) (a : Domain 2)
    (ha : periodOnePotential φ = domainInclusion a) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) (CoeffPair.exponentInclusion h2p φ)) p := by
  obtain ⟨W,_,hreal,h⟩ := exists_global_source_midpoint_fderiv_sobolev_memlp hp hp1 h2p
  exact h φ (hreal (fun n => hφ n)) a ha

end NLS.ZakharovShabat
