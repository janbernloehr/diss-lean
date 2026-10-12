import NLS.ZakharovShabat.L2SourceMidpointGradient
import NLS.ZakharovShabat.L2SourceG7Gradients

/-! # All-index physical midpoint contours and their G.7 coefficients

The existing isolating discs supply actual circles, including the finite
central block and collapsed gaps. The source midpoint coefficient vectors
realize the physical contour gradients and retain the H1 summability estimate.
-/
noncomputable section
open Set Metric Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every signed periodic pair admits an isolating circle on one complex
neighborhood of the real source locus; no endpoint separation is required. -/
theorem exists_global_source_midpoint_isolating_circles (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ, ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r ∧
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r ∧
        closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  obtain ⟨W,hW,_,hreal,hdata⟩ := exists_global_source_isolating_neighborhood hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro ψ hψ n
  obtain ⟨V,_,_,hψV,_,φ,N,ε,_,_,hcluster,_,hdisjoint⟩ := hdata ψ hψ
  have hd : ∃ c : ℂ, ∃ r : ℝ, sourceIsolatingDisc hp hp1 φ N ε n = ball c r := by
    unfold sourceIsolatingDisc
    split <;> exact ⟨_,_,rfl⟩
  obtain ⟨c,r,hd⟩ := hd
  have ha := hcluster ψ hψV n (Or.inl rfl)
  have hb := hcluster ψ hψV n (Or.inr (Or.inl rfl))
  rw [hd] at ha hb
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp ha)
  have hi := closure_sourceIsolatingDisc_subset_omittedDomain hp hp1 φ ψ N ε
    (hcluster ψ hψV) hdisjoint n
  rw [hd,closure_ball _ hr.ne'] at hi
  exact ⟨c,r,hr,ha,hb,hi⟩

/-- The physical gradient contours exist at every index and represent the
full source differential in every included Hilbert direction. -/
theorem exists_global_source_midpoint_l2_gradient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ h : CoeffPair 2,
          (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
            (periodOnePotential χ) (periodOnePotential_mem χ) n) (CoeffPair.exponentInclusion h2p φ))
            (CoeffPair.exponentInclusion h2p h) =
            ∫ s in (0 : ℝ)..1, (l2MidpointGradient (sourcePhysicalL2 φ) c r s).1*
              (physicalBase (periodOnePotential h) s).1+
              (l2MidpointGradient (sourcePhysicalL2 φ) c r s).2*(physicalBase (periodOnePotential h) s).2 := by
  obtain ⟨U,hU,hUr,hu⟩ := exists_global_source_midpoint_l2_gradient_contour hp hp1 h2p
  obtain ⟨V,hV,hVr,hv⟩ := exists_global_source_midpoint_isolating_circles hp hp1
  refine ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hUr hφ,hVr hφ⟩,?_⟩
  intro φ hφ n
  obtain ⟨c,r,hr,ha,hb,hi⟩ := hv _ hφ.2 n
  exact ⟨c,r,hr,hu φ hφ.1 n c r hr ha hb hi⟩

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The signed G.7 midpoint vector is the actual Fourier vector of the
physical contour gradient on one domain, with no supplied contour family. -/
theorem exists_global_sourceG7_l2_midpoint_realization
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W → ∀ n : ℤ,
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
          L2RootGradientFourierRealizes (l2MidpointGradient (sourcePhysicalL2 φ) c r)
            (sourceG7MidpointGradient (q := q) hp hp1 (CoeffPair.exponentInclusion h2p φ) n) := by
  obtain ⟨W,hW,hreal,hgradient⟩ := exists_global_source_midpoint_l2_gradient hp hp1 h2p
  refine ⟨W,hW,hreal,?_⟩
  have hcoeff (f : ℝ → ℂ) (k : ℤ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
    rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
  intro φ hφ n
  obtain ⟨c,r,hr,hint⟩ := hgradient φ hφ n
  refine ⟨c,r,hr,fun k => ?_⟩
  rw [(sourceG7MidpointGradient_coefficients (q := q) hp hp1 _ n k).1,
    (sourceG7MidpointGradient_coefficients (q := q) hp hp1 _ n k).2]
  constructor
  · have hdir : CoeffPair.inlCLM (lp.single p k (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (Finsupp.single k 1,0)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint,source_physical_gradient_pairing_single_fst,hcoeff]
  · have hdir : CoeffPair.inrCLM (lp.single p (-k) (1 : ℂ)) =
        CoeffPair.exponentInclusion h2p (CoeffPair.ofFinsupp (p := 2) (0,Finsupp.single (-k) 1)) := by
      rw [CoeffPair.exponentInclusion_ofFinsupp]
      apply (CoeffPair.toMax p).injective
      apply Prod.ext <;> ext m <;> simp [lp.single_apply,Pi.single_apply,Finsupp.single_apply,eq_comm]
    rw [hdir,hint,source_physical_gradient_pairing_single_snd,neg_neg,hcoeff]

/-- On the original H1 source, the whole realized midpoint sequence satisfies
G.7 in its exact finite conjugate coefficient norm. -/
theorem exists_global_sourceG7_l2_midpoint_memlp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ a : ScalarDomain 2 × ScalarDomain 2,
        CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a) ∈ W →
        Memℓp (fun n : ℤ => sourceG7MidpointGradient (q := q) hp hp1
          (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) p ∧
        ∀ n : ℤ, ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧
          L2RootGradientFourierRealizes (l2MidpointGradient (sourcePhysicalL2 (sobolevSourceInclusion a)) c r)
            (sourceG7MidpointGradient (q := q) hp hp1 (CoeffPair.exponentInclusion h2p (sobolevSourceInclusion a)) n) := by
  obtain ⟨U,hU,hUr,hu⟩ := exists_global_sourceG7_l2_midpoint_realization (q := q) hp hp1 h2p
  obtain ⟨V,hV,hVr,hv⟩ := sourceLemmaG7_corrected (q := q) hp hp1 h2p
  refine ⟨U ∩ V,hU.inter hV,fun φ hφ => ⟨hUr hφ,hVr hφ⟩,?_⟩
  intro a ha
  exact ⟨(hv a ha.2).1,fun n => hu _ ha.1 n⟩

end NLS.ZakharovShabat
