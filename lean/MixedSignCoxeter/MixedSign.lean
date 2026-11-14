/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import MixedSignCoxeter.Bipartite

/-!
# Mixed-Sign Coxeter Systems

Formalization of Chapter 3 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `Sign`: Node sign `+` (`pos`) or `-` (`neg`).
* `MixedSignCoxeterGraph n`: Undirected weighted graph with node signs and edge weights
  `m(i, j) ∈ {2, 3, ..., ∞}` (Definition 3.1, 3.2).
* `toReflectionSystem`: The induced `ReflectionSystem n` with `B(e_i, e_i) = ±2` and
  `B(e_i, e_j) = -2 cos(π / m(i, j))` (or `-2` for `∞`).
* `tildeAminus2`: The 3-node negative cycle `~A_{-2}` from Lemma 3.21.

## Main results
* `bipartite_mixed_sign_conjugation` (Corollary 1.5): For a bipartite mixed-sign Coxeter
  graph `Γ`, `Pᵀ * B(Γ) * P = -B(Γ_-)`.
* `tildeAminus2_principal_order_four`: `(s_0 * s_1 * s_2)^4 = 1` in `W(~A_{-2})` (Eq. 3.21.2).
-/

open Matrix

namespace MixedSignCoxeter

/-- Sign label `+` or `-` on a node of a mixed-sign Coxeter graph (Definition 3.1). -/
inductive Sign : Type
  | pos : Sign
  | neg : Sign
  deriving DecidableEq, Repr

namespace Sign

def toReal : Sign → ℝ
  | pos => 1
  | neg => -1

def flip : Sign → Sign
  | pos => neg
  | neg => pos

@[simp]
lemma toReal_ne_zero (s : Sign) : s.toReal ≠ 0 := by
  cases s <;> norm_num [toReal]

@[simp]
lemma flip_toReal (s : Sign) : s.flip.toReal = -s.toReal := by
  cases s <;> norm_num [flip, toReal]

end Sign

/-- Edge weight `m(i, j) ∈ {2, 3, ..., ∞}`, where `none` denotes `∞`. -/
noncomputable def edgeEntry : Option ℕ → ℝ
  | none => -2
  | some m => -2 * Real.cos (Real.pi / (m : ℝ))

/-- A mixed-sign Coxeter graph `Γ` on `n` nodes (Definitions 3.1 & 3.2). -/
structure MixedSignCoxeterGraph (n : ℕ) where
  sign : Fin n → Sign
  weight : Fin n → Fin n → Option ℕ
  weight_symm : ∀ i j, weight i j = weight j i
  weight_ge_two : ∀ i j m, weight i j = some m → 2 ≤ m

namespace MixedSignCoxeterGraph

variable {n : ℕ}

/-- Symmetric bilinear form `B(Γ)` defined by `Γ` (Definition 3.1). -/
noncomputable def toBilinearForm (Γ : MixedSignCoxeterGraph n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then 2 * (Γ.sign i).toReal
    else edgeEntry (Γ.weight i j)

lemma toBilinearForm_symm (Γ : MixedSignCoxeterGraph n) :
    Γ.toBilinearForm.IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, toBilinearForm, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji, Γ.weight_symm j i]

lemma toBilinearForm_diag_ne_zero (Γ : MixedSignCoxeterGraph n) (i : Fin n) :
    Γ.toBilinearForm i i ≠ 0 := by
  simp [toBilinearForm, Sign.toReal_ne_zero]

/-- Every mixed-sign Coxeter system is a reflection system (Section 1.3). -/
noncomputable def toReflectionSystem (Γ : MixedSignCoxeterGraph n) :
    ReflectionSystem n where
  B := Γ.toBilinearForm
  B_symm := Γ.toBilinearForm_symm
  B_diag_ne_zero := Γ.toBilinearForm_diag_ne_zero

/-- Negate all node signs to obtain `Γ_-` (Definition 2.43). -/
def negateSigns (Γ : MixedSignCoxeterGraph n) : MixedSignCoxeterGraph n where
  sign i := (Γ.sign i).flip
  weight := Γ.weight
  weight_symm := Γ.weight_symm
  weight_ge_two := Γ.weight_ge_two

lemma negateSigns_toBilinearForm (Γ : MixedSignCoxeterGraph n) :
    Γ.negateSigns.toBilinearForm = ReflectionSystem.negateDiag Γ.toBilinearForm := by
  ext i j
  simp only [toBilinearForm, negateSigns, ReflectionSystem.negateDiag_apply, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp [Sign.flip_toReal]
  · simp [hij]

/-- A mixed-sign Coxeter system is classical iff all nodes are positive (Proposition 3.5). -/
def isClassical (Γ : MixedSignCoxeterGraph n) : Prop :=
  ∀ i : Fin n, Γ.sign i = Sign.pos

/-- **Corollary 1.5**: If `Γ` is a bipartite mixed-sign Coxeter diagram with bipartition `part`,
then `Pᵀ * B(Γ) * P = -B(Γ_-)` for `P ∈ 𝒪`. -/
theorem bipartite_mixed_sign_conjugation (Γ : MixedSignCoxeterGraph n)
    (part : Fin n → Bool)
    (hbp : ∀ i j : Fin n, part i = part j → i ≠ j → Γ.toBilinearForm i j = 0) :
    (ReflectionSystem.bipartiteConjugator part)ᵀ * Γ.toBilinearForm *
        ReflectionSystem.bipartiteConjugator part =
      -Γ.negateSigns.toBilinearForm := by
  let G : ReflectionSystem.BipartiteReflectionSystem n :=
    { toReflectionSystem := Γ.toReflectionSystem
      part := part
      bipartite_edges := hbp }
  rw [negateSigns_toBilinearForm]
  exact ReflectionSystem.bipartite_conjugation_theorem G

end MixedSignCoxeterGraph

/-! ### Lemma 3.21: The `~A_{-2}` Counterexample -/

/-- Explicit generating reflections `s₁, s₂, s₃` for `W(~A_{-2})` from Lemma 3.21. -/
def s1TildeAminus2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, -1, -1;
      0,  1,  0;
      0,  0,  1]

def s2TildeAminus2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 1,  0,  0;
     -1, -1, -1;
      0,  0,  1]

def s3TildeAminus2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ 1,  0,  0;
      0,  1,  0;
     -1, -1, -1]

/-- Equation (3.21.2): `(s₁ s₂ s₃)⁴ = 1` in `W(~A_{-2})`. -/
theorem tildeAminus2_principal_order_four :
    (s1TildeAminus2 * s2TildeAminus2 * s3TildeAminus2) ^ 4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1TildeAminus2, s2TildeAminus2, s3TildeAminus2, Matrix.mul_apply,
      pow_succ, Fin.sum_univ_three]

/-- Equation (3.21.3): `(s₁ s₂ s₃)² s₁ = (s₃ s₂ s₁) s₃ s₂` in `W(~A_{-2})`. -/
theorem tildeAminus2_eq_3_21_3 :
    (s1TildeAminus2 * s2TildeAminus2 * s3TildeAminus2) ^ 2 * s1TildeAminus2 =
      (s3TildeAminus2 * s2TildeAminus2 * s1TildeAminus2) * s3TildeAminus2 * s2TildeAminus2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1TildeAminus2, s2TildeAminus2, s3TildeAminus2, Matrix.mul_apply,
      pow_succ, Fin.sum_univ_three]

/-! ### Proposition 3.5: Classical Coxeter Systems as All-Positive Mixed-Sign Systems -/

/-- **Definition 3.4 / Proposition 3.5**: A `MixedSignCoxeterGraph n` is a classical
Coxeter graph if every node has positive sign (`+`). -/
def MixedSignCoxeterGraph.IsClassical {n : ℕ} (Γ : MixedSignCoxeterGraph n) : Prop :=
  ∀ i : Fin n, Γ.sign i = Sign.pos

/-- **Proposition 3.5**: Every classical Coxeter graph (`∀ i, Γ.sign i = Sign.pos`)
induces a classical Coxeter bilinear form with `B(e_i, e_i) = 2` and
`B(e_i, e_j) = edgeEntry (Γ.weight i j)` for `i ≠ j`. -/
theorem proposition_3_5_classical_form {n : ℕ} (Γ : MixedSignCoxeterGraph n)
    (hpos : Γ.IsClassical) :
    (∀ i : Fin n, Γ.toBilinearForm i i = 2) ∧
    (∀ i j : Fin n, i ≠ j → Γ.toBilinearForm i j = edgeEntry (Γ.weight i j)) := by
  constructor
  · intro i
    simp [MixedSignCoxeterGraph.toBilinearForm, hpos i, Sign.toReal]
  · intro i j hij
    simp [MixedSignCoxeterGraph.toBilinearForm, hij]

end MixedSignCoxeter

