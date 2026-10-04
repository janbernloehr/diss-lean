import NLS.SequenceSpaces.HeadRotationStationarity

/-! # Head rotations of the local tail-sum factor

Every point of the local tail-sum target lifts to the original domain.
The rotation identity therefore holds on the whole target, not merely at
the image of a particular chosen original point.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Rotation stationarity of the original lift passes to the local
analytic factor at every target point. -/
theorem fderiv_tailSumFactor_headRotation_eq_zero (hq : q ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (g : (Coeff q × Coeff q) → F)
    (V : Set (Coeff p × Coeff p)) (hV : IsOpen V)
    (hQ : IsOpen (pairMixedSquare (q := q) S '' V))
    (hf : DifferentiableOn ℂ f V) (hg : AnalyticOnNhd ℂ g (pairMixedSquare S '' V))
    (he : ∀ z ∈ V, g (pairMixedSquare S z) = f z)
    (hsplit : ∀ b ∈ pairMixedSquare S '' V, ∀ k ∉ S, fderiv ℂ g b (actionSplitDirection q k) = 0)
    (hrot : ∀ z ∈ V, ∀ k, fderiv ℂ f z (actionRotationVectorCLM p k z) = 0)
    (a : Coeff q × Coeff q) (C : TailSumChart S (pairMixedSquare S '' V) a)
    (w : TailSumSpace q S) (hw : w ∈ C.target) (k : S) :
    fderiv ℂ (C.factor g) w (headRotationVector S k w) = 0 := by
  let Z := V ∩ pairMixedSquare (q := q) S ⁻¹' C.source
  have hcont : Continuous (pairMixedSquare (p := p) (q := q) S) :=
    continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  have hZ : IsOpen Z := hV.inter (C.source_open.preimage hcont)
  have himage := tailSum_mixed_image_chart_source S V a C
  obtain ⟨z,hz,hwz⟩ := (himage.symm ▸ hw)
  have hzZ : z ∈ Z := hz
  have hrec : ∀ z ∈ Z, C.factor g (tailSumCLM S (pairMixedSquare S z)) = f z := by
    intro z hz
    exact (C.factor_apply hq hQ g hg.differentiableOn hsplit _ hz.2).trans (he z hz.1)
  have hd := fderiv_headRotation_eq_zero_of_recovery S f (C.factor g) Z hZ C.target C.target_open
    (hf.mono inter_subset_left) (C.analyticOnNhd_factor g hg).differentiableOn
    (fun z hz => C.map_mem _ hz.2) hrec z hzZ k (hrot z hz.1 k.val)
  simpa only [hwz] using hd

end NLS.Coeff
