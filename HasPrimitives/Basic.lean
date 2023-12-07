import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral

import Mathlib.Tactic.LibrarySearch

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

-- From V. Beffara https://github.com/vbeffara/RMT4
-- integral along a curve
noncomputable def curvint (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  ∫ t in t₁..t₂, deriv γ t • f (γ t)

namespace Real
-- A useful function: goes from z₁ to z₂ with a speed that vanishes at the endpoints
-- Having a vanishing speed at the endpoints allows paths that are differentiable by parts to be
--  parametrized in a differentiable way
noncomputable def straightSeg (t₁ t₂ : ℝ ) (z₁ z₂ : ℂ) : ℝ → ℂ :=
  fun t => z₁ * (1 - cos (t * π / (t₂ - t₁))) + z₂ * cos (t * π / (t₂ - t₁))

-- straight line integral between two complex points
noncomputable def linint (z₁ z₂ : ℂ) (f : ℂ → ℂ) : ℂ :=
  curvint 0 1 f (straightSeg 0 1 z₁ z₂)

lemma diffOfIntegrals (z₀ z₁ z₂ : Complex.UnitDisc) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1)) :
    linint z₀ z₁ f - linint z₀ z₂ f = linint z₂ z₁ f := by
  sorry

lemma derivOfLinint (z₀ : ℂ) (f: ℂ → ℂ) (hf: Continuous f) (l: Filter ℂ):
    ∀ᶠh in l, (linint z₀ (z₀+h) f)/h = f z₀ := by
  sorry

-- To prove the main theorem, we first prove it on a disk
theorem hasPrimitivesOfDisk : hasPrimitives (Metric.ball 0 1) := by
  intros f hf_diff
  use fun z ↦ linint 0 z f
  constructor
  · sorry

  · intro z  hz
    let z_ondisc := (Complex.UnitDisc.mk z ?_)
    have : ∀ h : Complex.UnitDisc, Complex.abs (z_ondisc+h) < 1 → linint 0 (z+h) f - linint 0 z f = linint z (z+h) f:= by
      intros h ondisc
      let zph_ondisc := (Complex.UnitDisc.mk (z+h) ?_)
      have := diffOfIntegrals 0 zph_ondisc z_ondisc f hf_diff
      rw [Complex.UnitDisc.coe_mk] at this
      rw [Complex.UnitDisc.coe_mk] at this
      exact this

      sorry
      sorry

    sorry

  

-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
