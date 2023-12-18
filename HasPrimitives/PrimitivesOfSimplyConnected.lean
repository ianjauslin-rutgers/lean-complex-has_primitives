import HasPrimitives.Basic



open scoped Interval

noncomputable def CurvInt (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
   ∫ t in t₁..t₂, deriv γ t • f (γ t)

theorem curvInt_eval_of_primitive {t₁ t₂ : ℝ} {γ : ℝ → ℂ} {f F : ℂ → ℂ} {U : Set ℂ}
    (U_open : IsOpen U) (γ_in_U : ∀ t, t ∈ [[t₁, t₂]] → γ t ∈ U)
    (F_holo : DifferentiableOn ℂ F U)
    (F_prim : Set.EqOn (deriv F) f U) (hγ : DifferentiableOn ℝ γ ([[t₁, t₂]])) :
    CurvInt t₁ t₂ f γ = F (γ t₂) - F (γ t₁) := by
  dsimp [CurvInt]
  convert @intervalIntegral.integral_deriv_eq_sub ℂ _ _ _ (F ∘ γ) t₁ t₂ ?_ ?_
  · -- apply deriv_comp
--

#exit
  · ext1 t
    have := @deriv.comp ℝ _ t ℂ _ _ γ F --(F_holo (γ t) (γ_in_U t (hγ t).1 (hγ t).2)) --(hγ t).1 (F_holo (γ t) (γ_in_U t (hγ t).1 (hγ t).2))
    --ext1 t

    -- chain rule for derivatives
    have h₁ : deriv (F ∘ γ) t = deriv F (γ t) * deriv γ t := deriv.comp_deriv_eq_deriv_comp _ _ _
  sorry

-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem HasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    HasPrimitives U := by
  sorry
