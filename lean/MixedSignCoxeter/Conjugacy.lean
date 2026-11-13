/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Conjugate Reflection Systems and Reflection Diagrams (Section 2.3)

Formalization of Section 2.3 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `SignedPerm n`: Elements of `𝒪`, the subgroup of the orthogonal group permuting
  `{±e₁, ..., ±eₙ}` (Definition 2.8).
* `GraphIso B₁ B₂`: An isomorphism of reflection diagrams `Γ(B₁) ≅ Γ(B₂)` (Definition 2.33).

## Main results
* `SignedPerm.toMatrix_transpose_mul_self`: `Pᵀ * P = 1` (Remark 2.30).
* `conjugate_reflections_of_form` (Lemma 2.32): If `B₂ = ± Pᵀ * B₁ * P` with `P ∈ 𝒪`, then
  `Pᵀ * s_{P.perm j}(B₁) * P = s_j(B₂)`.
* `graphIso_conjugates_forms` (Lemma 2.37): An isomorphism `Γ(B₁) ≅ Γ(B₂)` induces
  `P ∈ 𝒪` with `Pᵀ * B₁ * P = B₂`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-- An element `P ∈ 𝒪` (Definition 2.8): a signed permutation matrix sending
`e_j ↦ (±1) e_{perm j}`. -/
structure SignedPerm (n : ℕ) where
  perm : Equiv.Perm (Fin n)
  neg : Fin n → Bool

namespace SignedPerm

def signReal (P : SignedPerm n) (j : Fin n) : ℝ :=
  if P.neg j then -1 else 1

@[simp]
lemma signReal_mul_self (P : SignedPerm n) (j : Fin n) :
    P.signReal j * P.signReal j = 1 := by
  cases h : P.neg j <;> simp [signReal, h]

/-- Matrix representation of `P ∈ 𝒪` in the standard basis. -/
def toMatrix (P : SignedPerm n) : Matrix (Fin n) (Fin n) ℝ :=
  of fun r c => if r = P.perm c then P.signReal c else 0

@[simp]
lemma toMatrix_apply (P : SignedPerm n) (r c : Fin n) :
    P.toMatrix r c = if r = P.perm c then P.signReal c else 0 := rfl

/-- **Remark 2.30**: Every `P ∈ 𝒪` is orthogonal (`Pᵀ * P = 1`). -/
theorem toMatrix_transpose_mul_self (P : SignedPerm n) :
    P.toMatrixᵀ * P.toMatrix = 1 := by
  ext r c
  simp only [mul_apply, transpose_apply, toMatrix_apply, one_apply]
  have hterm : ∀ k : Fin n,
      (if k = P.perm r then P.signReal r else 0) *
        (if k = P.perm c then P.signReal c else 0) =
      if k = P.perm r then (if P.perm r = P.perm c then P.signReal r * P.signReal c else 0) else 0 := by
    intro k
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hrc : r = c
  · subst hrc
    simp
  · have hp : P.perm r ≠ P.perm c := fun h => hrc (P.perm.injective h)
    simp [hrc, hp]

/-- Entrywise formula for `Pᵀ * M * P`. -/
lemma toMatrix_conj_apply (P : SignedPerm n) (M : Matrix (Fin n) (Fin n) ℝ) (r c : Fin n) :
    (P.toMatrixᵀ * M * P.toMatrix) r c =
      P.signReal r * P.signReal c * M (P.perm r) (P.perm c) := by
  have hleft : ∀ k : Fin n,
      (P.toMatrixᵀ * M) r k = P.signReal r * M (P.perm r) k := by
    intro k
    simp only [mul_apply, transpose_apply, toMatrix_apply]
    have ht : ∀ m : Fin n,
        (if m = P.perm r then P.signReal r else 0) * M m k =
        if m = P.perm r then P.signReal r * M m k else 0 := by
      intro m; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun m _ => ht m)]
    simp
  rw [mul_apply]
  simp_rw [hleft, toMatrix_apply]
  have ht2 : ∀ k : Fin n,
      P.signReal r * M (P.perm r) k * (if k = P.perm c then P.signReal c else 0) =
      if k = P.perm c then P.signReal r * P.signReal c * M (P.perm r) k else 0 := by
    intro k; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun k _ => ht2 k)]
  simp

end SignedPerm

/-- **Lemma 2.32** (positive sign): If `B₂ = Pᵀ * B₁ * P` with `P ∈ 𝒪`, then
conjugating `s_{P.perm j}(B₁)` by `P` yields `s_j(B₂)`. -/
theorem conjugate_reflections_of_form (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (P : SignedPerm n)
    (hB : B₂ = P.toMatrixᵀ * B₁ * P.toMatrix) (j : Fin n) :
    P.toMatrixᵀ * reflectionMatrix B₁ (P.perm j) * P.toMatrix = reflectionMatrix B₂ j := by
  ext r c
  rw [P.toMatrix_conj_apply]
  simp only [reflectionMatrix_apply, hB, P.toMatrix_conj_apply]
  have h1 : P.signReal j * P.signReal j = 1 := P.signReal_mul_self j
  by_cases hrc : r = c
  · subst hrc
    have hp : P.perm r = P.perm r := rfl
    by_cases hrj : r = j
    · subst hrj
      simp [P.signReal_mul_self r]
    · have hpj : P.perm r ≠ P.perm j := fun h => hrj (P.perm.injective h)
      simp [hrj, hpj, P.signReal_mul_self r]
  · have hprc : P.perm r ≠ P.perm c := fun h => hrc (P.perm.injective h)
    by_cases hrj : r = j
    · subst hrj
      simp only [hrc, ↓reduceIte, hprc, P.signReal_mul_self r, one_mul]
      ring
    · have hpj : P.perm r ≠ P.perm j := fun h => hrj (P.perm.injective h)
      simp [hrc, hprc, hrj, hpj]

/-- **Lemma 2.32** (negative sign): If `B₂ = -(Pᵀ * B₁ * P)` with `P ∈ 𝒪`,
conjugating `s_{P.perm j}(B₁)` by `P` still yields `s_j(B₂)` (by Lemma 2.31). -/
theorem conjugate_reflections_of_neg_form (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (P : SignedPerm n)
    (hB : B₂ = -(P.toMatrixᵀ * B₁ * P.toMatrix)) (j : Fin n) :
    P.toMatrixᵀ * reflectionMatrix B₁ (P.perm j) * P.toMatrix = reflectionMatrix B₂ j := by
  rw [hB, reflectionMatrix_neg]
  exact conjugate_reflections_of_form B₁ (P.toMatrixᵀ * B₁ * P.toMatrix) P rfl j

/-- **Definition 2.33**: An isomorphism of reflection diagrams `Γ(B₁) ≅ Γ(B₂)` is a
bijection `φ` on nodes preserving node weights and edge weights. -/
def IsGraphIso (B₁ B₂ : Matrix (Fin n) (Fin n) ℝ) (φ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, B₂ i j = B₁ (φ i) (φ j)

/-- **Lemma 2.37**: If `Γ(B₁) ≅ Γ(B₂)` via `φ`, then `B₂ = Pᵀ * B₁ * P` for `P ∈ 𝒪`. -/
theorem graphIso_conjugates_forms {B₁ B₂ : Matrix (Fin n) (Fin n) ℝ}
    {φ : Equiv.Perm (Fin n)} (hφ : IsGraphIso B₁ B₂ φ) :
    let P : SignedPerm n := ⟨φ, fun _ => false⟩
    P.toMatrixᵀ * B₁ * P.toMatrix = B₂ := by
  intro P
  ext r c
  rw [P.toMatrix_conj_apply]
  simp only [P, SignedPerm.signReal, Bool.false_eq_true, ↓reduceIte, one_mul]
  exact (hφ r c).symm

end ReflectionSystem
