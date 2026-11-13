/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Bipartite Reflection Diagrams and Theorem 1.4

Formalization of Section 2.4 and Theorem 1.4 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `bipartiteConjugator_mul_self`: `P * P = 1` (so `P ∈ 𝒪`).
* `bipartite_conjugation_theorem` (Theorem 1.4): For a bipartite reflection diagram `Γ`,
  `Pᵀ * B(Γ) * P = - B(Γ_-)`.
* `bipartite_conjugates_reflections`: `Pᵀ * s_i(Γ) * P = s_i(Γ_-)`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-- Negate all diagonal node weights of `B` to form `B(Γ_-)` (Definition 2.43). -/
def negateDiag (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i = j then -B i j else B i j

@[simp]
lemma negateDiag_apply (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    negateDiag B i j = if i = j then -B i j else B i j := rfl

/-- A bipartite reflection system: nodes are partitioned by `part : Fin n → Bool`
into `N₁` (`true`) and `N₂` (`false`) with no edges within `N₁` or `N₂` (Definition 2.40). -/
structure BipartiteReflectionSystem (n : ℕ) extends ReflectionSystem n where
  part : Fin n → Bool
  bipartite_edges : ∀ i j : Fin n, part i = part j → i ≠ j → B i j = 0

/-- The orthogonal conjugator `P ∈ 𝒪` from the proof of Theorem 1.4:
`P = diag(±1)` with `-1` on `N₁` (`part i = true`) and `+1` on `N₂` (`part i = false`). -/
def bipartiteConjugator (part : Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => if part i then -1 else 1

@[simp]
lemma bipartiteConjugator_apply (part : Fin n → Bool) (i j : Fin n) :
    bipartiteConjugator part i j = if i = j then (if part i then -1 else 1) else 0 :=
  diagonal_apply _ i j

lemma bipartiteConjugator_transpose (part : Fin n → Bool) :
    (bipartiteConjugator part)ᵀ = bipartiteConjugator part :=
  diagonal_transpose _

lemma bipartiteConjugator_mul_self (part : Fin n → Bool) :
    bipartiteConjugator part * bipartiteConjugator part = 1 := by
  ext i j
  simp only [bipartiteConjugator, diagonal_mul_diagonal, one_apply]
  by_cases hij : i = j
  · subst hij
    cases h : part i <;> simp [h]
  · simp [hij]

/-- **Theorem 1.4**: If `Γ` is a bipartite reflection diagram, then
`Pᵀ * B(Γ) * P = - B(Γ_-)` where `P ∈ 𝒪` is `bipartiteConjugator`. -/
theorem bipartite_conjugation_theorem (G : BipartiteReflectionSystem n) :
    (bipartiteConjugator G.part)ᵀ * G.B * bipartiteConjugator G.part =
      -negateDiag G.B := by
  rw [bipartiteConjugator_transpose]
  ext i j
  simp only [bipartiteConjugator, diagonal_mul, mul_diagonal, neg_apply, negateDiag_apply]
  by_cases hij : i = j
  · subst hij
    cases h : G.part i <;> simp [h]
  · have hdiff : G.part i ≠ G.part j ∨ G.B i j = 0 := by
      by_cases hp : G.part i = G.part j
      · exact Or.inr (G.bipartite_edges i j hp hij)
      · exact Or.inl hp
    rcases hdiff with hp | h0
    · cases hi : G.part i <;> cases hj : G.part j <;> simp_all [hij] <;> ring
    · simp [hij, h0]

/-- Conjugating each generating reflection `s_i(Γ)` by `P` yields `s_i(Γ_-)`. -/
theorem bipartite_conjugates_reflections (G : BipartiteReflectionSystem n) (i : Fin n) :
    (bipartiteConjugator G.part)ᵀ * reflectionMatrix G.B i * bipartiteConjugator G.part =
      reflectionMatrix (negateDiag G.B) i := by
  rw [bipartiteConjugator_transpose]
  ext r c
  simp only [bipartiteConjugator, diagonal_mul, mul_diagonal, reflectionMatrix_apply,
    negateDiag_apply]
  by_cases hrc : r = c
  · subst hrc
    by_cases hri : r = i
    · subst hri
      cases h : G.part r <;> simp [h, G.B_diag_ne_zero r] <;> ring
    · cases h : G.part r <;> simp [h, hri]
  · by_cases hri : r = i
    · subst hri
      have hne : r ≠ c := hrc
      by_cases hp : G.part r = G.part c
      · have h0 := G.bipartite_edges r c hp hne
        simp [hne, h0]
      · cases hr : G.part r <;> cases hc : G.part c <;> simp_all [hne] <;> ring
    · cases hr : G.part r <;> cases hc : G.part c <;> simp [hrc, hri, hr, hc]

end ReflectionSystem

