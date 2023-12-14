import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

import Mathlib.Tactic.LibrarySearch

open Complex Topology

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

/-- The wedge integral from z to w of a function f -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-- diff of wedges -/
lemma diff_of_wedges {c : ℂ} {r : ℝ} (h0 : 0 < r) (z : ℂ)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∀ᶠ h in 𝓝 0,
      WedgeInt c (z+h) f - WedgeInt c z f = WedgeInt z (z+h) f := by
    sorry

lemma wedgeInt_of_const (z w c : ℂ) :
    WedgeInt z w (fun x => c) = c*(w-z) := by
  dsimp [WedgeInt]
  simp only [intervalIntegral.integral_const c]
  have : w-z=w.re+I*w.im-z.re-I*z.im := by
    conv =>
      lhs
      rw [(Complex.re_add_im w).symm]
      rw [(Complex.re_add_im z).symm]
    ring
  rw [this]

  simp [smul_eq_mul]
  ring


lemma deriv_of_wedgeInt {f: ℂ → ℂ} {U : Set ℂ} {hU: IsOpen U} (hf: ContinuousOn f U)
    {z₀ : ℂ} (hz₀ : z₀∈U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h ↦ ((WedgeInt z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by
  have : Asymptotics.IsLittleO (𝓝 0) (fun h ↦ f (z₀+h) - f z₀) (fun h ↦ (1:ℂ)) := by
    have := ContinuousOn.continuousAt hf (IsOpen.mem_nhds hU hz₀)
    have f_tendsto := ContinuousAt.tendsto this
    simp only [Asymptotics.isLittleO_one_iff]
    rw [tendsto_sub_nhds_zero_iff]

    -- shift the origin of the filter
    -- this can probably be done better
    let g := fun h ↦ z₀+h
    have g_tendsto : Filter.Tendsto g (𝓝 0) (𝓝 z₀) := by
      dsimp [g]
      rw [tendsto_sub_nhds_zero_iff.symm]
      simp only [add_sub_cancel']
      rw [Filter.tendsto_def]
      intros s hs
      simp only [Set.preimage_id']
      exact hs
    have := Filter.Tendsto.comp f_tendsto g_tendsto
    rw [Function.comp] at this
    exact this

  dsimp [WedgeInt]

  sorry




    
    

-- trivial case: empty set
theorem hasPrimitivesOfEmpty : hasPrimitives ∅ := by
  dsimp [hasPrimitives]
  simp only [Set.eqOn_empty, and_true]
  dsimp [DifferentiableOn]
  dsimp [DifferentiableWithinAt]
  dsimp [HasFDerivWithinAt]
  dsimp [HasFDerivAtFilter]
  simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
  forall_true_left]


-- To prove the main theorem, we first prove it on a disc
-- not sure what happens if U is empty
theorem hasPrimitivesOfConvex (U: Set ℂ) (hU: Convex ℝ U) : hasPrimitives U := by
  by_cases hne : U = ∅
  · convert hasPrimitivesOfEmpty

  · intros f hf_diff
    -- get z₀
    have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
    obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
    use fun z ↦ linint z₀ z f
    constructor
    · sorry

    · intro z  hz
      have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
        intros h hinU
        refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

        exact Subtype.mem z₀
      sorry


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
