import NLS.KdV.HillFullEndpointPhase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Every finite collection of full physical endpoint phases has genuine
infinite H1 cotangents and zero pairwise Gardner brackets. The complete
physical correction series is retained in every phase; other gaps may
be collapsed. -/
theorem exists_hillFullPhysicalPhases_endpoint_Gardner_family
    (q : RealPeriodOneHillPotential) (s : Finset ℕ)
    (hgap : ∀ j∈s, hillRealGapHalfLength q.val q.property.1 q.property.2 (j+1)≠0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0) :
    ∃ Θ ε : ℕ → Coeff 2 → ℂ, ∃ c : ℕ → ℕ → ℂ,
      (∀ j∈s, AnalyticAt ℂ (Θ j) (SpectralWeight.one.toCoeff q.val) ∧
        AnalyticAt ℂ (ε j) (SpectralWeight.one.toCoeff q.val) ∧
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
          hillRealGapHalfLength p.val p.property.1 p.property.2 (j+1)≠0 ∧
          (ε j (SpectralWeight.one.toCoeff p.val)).im=0 ∧
          cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 (j+1))
            (hillRealGapHalfLength p.val p.property.1 p.property.2 (j+1)) (ε j (SpectralWeight.one.toCoeff p.val))=
              (hillDirichletEnergy p.val p.property.1 p.property.2 (j+1) (by omega) : ℂ) ∧
          Complex.sin (ε j (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine
            p.val p.property.1 p.property.2 (j+1) (by omega) ∧
          Θ j (SpectralWeight.one.toCoeff p.val)=hillSummedRegularAbelianCorrection
            p.val p.property.1 p.property.2 (j+1) (by omega)+ε j (SpectralWeight.one.toCoeff p.val)-(Real.pi : ℂ)) ∧
        Summable (fun k : ℕ => ‖c j k‖) ∧
        ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
          SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
          (fderiv ℂ (Θ j) (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
            hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillInfiniteNormingGradient q (c j))) ∧
      (∀ j∈s,
        AbsolutelyContinuousOnInterval (extend (hillInfiniteNormingGradient q (c j))) 0 1 ∧
        MemLp (extend (hillInfiniteNormingGradient q (c j))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
        MemLp (deriv (extend (hillInfiniteNormingGradient q (c j)))) 2 (volume.restrict (Ioc (0 : ℝ) 1))) ∧
      ∀ j∈s, ∀ k∈s,
        (∫ x in (0 : ℝ)..1,extend (hillInfiniteNormingGradient q (c j)) x*
          deriv (extend (hillInfiniteNormingGradient q (c k))) x)=0 := by
  have hex (j : ℕ) (hj : j∈s) := exists_hillFullPhysicalPhase_endpoint_cotangent h0q h0r
    q (j+1) (by omega) (hgap j hj) hterminal
  choose T E c hT hE hphysical hc hD using hex
  let TT : ℕ → Coeff 2 → ℂ := fun j => if hj : j∈s then T j hj else 0
  let EE : ℕ → Coeff 2 → ℂ := fun j => if hj : j∈s then E j hj else 0
  let CC : ℕ → ℕ → ℂ := fun j => if hj : j∈s then c j hj else 0
  have hCC (j : ℕ) (hj : j∈s) : Summable (fun k : ℕ => ‖CC j k‖) := by
    simpa only [CC,dif_pos hj] using hc j hj
  refine ⟨TT,EE,CC,?_,fun j hj => hillInfiniteNormingGradient_H1 h0q h0r q (CC j) (hCC j hj),
    fun j hj k hk => hillInfiniteNormingGradient_GardnerBracket_eq_zero h0q h0r q (CC j) (CC k) (hCC j hj) (hCC k hk)⟩
  intro j hj
  simpa only [TT,EE,CC,dif_pos hj] using ⟨hT j hj,hE j hj,hphysical j hj,hc j hj,hD j hj⟩

end NLS.KdV
