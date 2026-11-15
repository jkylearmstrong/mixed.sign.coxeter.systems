/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import MixedSignCoxeter.CyclesAndDeletion
import MixedSignCoxeter.SpectralRadius

/-!
# Dissertation Remarks 3.23, 3.26, and 3.30

Formalization of the remaining computational and algebraic remarks from Chapter 3 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main results
* `remark_3_23_card` (**Remark 3.23**): `W(~A_{-2})` is isomorphic to `S₄` (`Equiv.Perm (Fin 4)`),
  hence finite of order `24`.
* `remark_3_26_det_neg_odd_cycle` (**Remark 3.26**): For every odd `m ≥ 3` (i.e. `~A_{-n}` with
  `n = m - 1` even), `det (-B(~A_{-n})) = 4`, proved via the cyclic-shift factorization
  `-B(~A_{-n}) = (I + P)(I + Pᵀ)` and `det (I + P) = 1 + (-1)^{m-1} = 2`.
* `remark_3_30_oscillation` (**Remark 3.30**): Exact principal polynomials for
  `A₂(+,-)`, `A₃(-,+,+)`, `A₄(-,+,+,+)`, `A₅(-,+,+,+,+)` and strict spectral-radius oscillation
  `ρ(A₂(+,-)) > 2.6 > 1 = ρ(A₃(-,+,+)) < 2.15 < ρ(A₄(-,+,+,+))` and `ρ(A₅(-,+,+,+,+)) < 2.13`.
-/

open Matrix

namespace MixedSignCoxeter

/-! ### Remark 3.23: `W(~A_{-2}) ≅ S₄` and `|W(~A_{-2})| = 24` -/

section Remark323

private def s0Z' : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-1, -1, -1;
      0,  1,  0;
      0,  0,  1]

private def s1Z' : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 1,  0,  0;
     -1, -1, -1;
      0,  0,  1]

private def s2Z' : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 1,  0,  0;
      0,  1,  0;
     -1, -1, -1]

private def rowVec4 : Fin 4 → (Fin 3 → ℤ)
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]
  | 3 => ![-1, -1, -1]

private def perm4Mat (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => rowVec4 (σ⁻¹ ⟨i.val, by omega⟩) j

private lemma perm4Mat_swap03 : perm4Mat (Equiv.swap 0 3) = s0Z' := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma perm4Mat_swap13 : perm4Mat (Equiv.swap 1 3) = s1Z' := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma perm4Mat_swap23 : perm4Mat (Equiv.swap 2 3) = s2Z' := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma perm4Mat_one : perm4Mat 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma perm4Mat_mul_rowVec4 (σ : Equiv.Perm (Fin 4)) (a : Fin 4) :
    rowVec4 a ᵥ* perm4Mat σ = rowVec4 (σ⁻¹ a) := by
  fin_cases a
  · funext j; fin_cases j <;> simp [vecMul, dotProduct, perm4Mat, rowVec4, Fin.sum_univ_three]
  · funext j; fin_cases j <;> simp [vecMul, dotProduct, perm4Mat, rowVec4, Fin.sum_univ_three]
  · funext j; fin_cases j <;> simp [vecMul, dotProduct, perm4Mat, rowVec4, Fin.sum_univ_three]
  · funext j
    have hsum : ∑ x : Fin 4, rowVec4 (σ⁻¹ x) j = 0 := by
      rw [Equiv.sum_comp σ⁻¹ (fun x => rowVec4 x j)]
      fin_cases j <;> decide
    have h012 : rowVec4 (σ⁻¹ 0) j + rowVec4 (σ⁻¹ 1) j + rowVec4 (σ⁻¹ 2) j +
        rowVec4 (σ⁻¹ 3) j = 0 := by
      simpa [Fin.sum_univ_four, add_assoc] using hsum
    simp only [vecMul, dotProduct, perm4Mat, Matrix.of_apply, Fin.sum_univ_three]
    change (-1) * rowVec4 (σ⁻¹ 0) j + (-1) * rowVec4 (σ⁻¹ 1) j + (-1) * rowVec4 (σ⁻¹ 2) j =
      rowVec4 (σ⁻¹ 3) j
    linarith

private lemma perm4Mat_mul (σ τ : Equiv.Perm (Fin 4)) :
    perm4Mat (σ * τ) = perm4Mat σ * perm4Mat τ := by
  ext i j
  have h := congr_fun (perm4Mat_mul_rowVec4 τ (σ⁻¹ ⟨i.val, by omega⟩)) j
  have hi : (perm4Mat σ * perm4Mat τ) i j = (rowVec4 (σ⁻¹ ⟨i.val, by omega⟩) ᵥ* perm4Mat τ) j := by
    simp [Matrix.mul_apply, vecMul, dotProduct, perm4Mat]
  rw [hi, h]
  simp [perm4Mat, _root_.mul_inv_rev, Equiv.Perm.mul_apply]

private lemma rowVec4_injective : Function.Injective rowVec4 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)

private lemma perm4Mat_injective : Function.Injective perm4Mat := by
  intro σ τ h
  have hinj : ∀ i : Fin 3, σ⁻¹ ⟨i.val, by omega⟩ = τ⁻¹ ⟨i.val, by omega⟩ := fun i =>
    rowVec4_injective (funext fun j => congr_fun (congr_fun h i) j)
  have h0 : σ⁻¹ 0 = τ⁻¹ 0 := hinj 0
  have h1 : σ⁻¹ 1 = τ⁻¹ 1 := hinj 1
  have h2 : σ⁻¹ 2 = τ⁻¹ 2 := hinj 2
  have h3 : σ⁻¹ 3 = τ⁻¹ 3 := by
    have hsumσ : ∑ x : Fin 4, (σ⁻¹ x : ℕ) = 6 := by
      rw [Equiv.sum_comp σ⁻¹ (fun x : Fin 4 => (x : ℕ))]
      decide
    have hsumτ : ∑ x : Fin 4, (τ⁻¹ x : ℕ) = 6 := by
      rw [Equiv.sum_comp τ⁻¹ (fun x : Fin 4 => (x : ℕ))]
      decide
    simp only [Fin.sum_univ_four, Fin.isValue] at hsumσ hsumτ
    rw [h0, h1, h2] at hsumσ
    exact Fin.ext (by omega)
  have hinv : σ⁻¹ = τ⁻¹ := by
    ext a
    fin_cases a
    · exact congr_arg Fin.val h0
    · exact congr_arg Fin.val h1
    · exact congr_arg Fin.val h2
    · exact congr_arg Fin.val h3
  exact inv_injective hinv

/-- The monoid homomorphism `S₄ →* M₃(ℤ)` realizing `W(~A_{-2})`. -/
def perm4MonoidHom : Equiv.Perm (Fin 4) →* Matrix (Fin 3) (Fin 3) ℤ where
  toFun := perm4Mat
  map_one' := perm4Mat_one
  map_mul' := perm4Mat_mul

/-- The submonoid of `M₃(ℤ)` generated by the three reflections of `~A_{-2}`. -/
def W_tildeAminus2Z : Submonoid (Matrix (Fin 3) (Fin 3) ℤ) :=
  Submonoid.closure {s0Z', s1Z', s2Z'}

private lemma s0Z'_mem : s0Z' ∈ W_tildeAminus2Z := Submonoid.subset_closure (by simp)
private lemma s1Z'_mem : s1Z' ∈ W_tildeAminus2Z := Submonoid.subset_closure (by simp)
private lemma s2Z'_mem : s2Z' ∈ W_tildeAminus2Z := Submonoid.subset_closure (by simp)

private lemma perm4Mat_swap_mem_W (a b : Fin 4) :
    perm4Mat (Equiv.swap a b) ∈ W_tildeAminus2Z := by
  fin_cases a <;> fin_cases b
  · convert Submonoid.one_mem W_tildeAminus2Z; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s0Z'_mem s1Z'_mem) s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s0Z'_mem s2Z'_mem) s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s0Z'_mem s1Z'_mem) s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.one_mem W_tildeAminus2Z; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s1Z'_mem s2Z'_mem) s1Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s1Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s0Z'_mem s2Z'_mem) s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.mul_mem _ (Submonoid.mul_mem _ s1Z'_mem s2Z'_mem) s1Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.one_mem W_tildeAminus2Z; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s2Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s0Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s1Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert s2Z'_mem; ext i j; fin_cases i <;> fin_cases j <;> decide
  · convert Submonoid.one_mem W_tildeAminus2Z; ext i j; fin_cases i <;> fin_cases j <;> decide

private lemma perm4Mat_mem_W (σ : Equiv.Perm (Fin 4)) : perm4Mat σ ∈ W_tildeAminus2Z := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [perm4Mat_one]; exact Submonoid.one_mem _
  | swap_mul σ x y _ ih =>
    rw [perm4Mat_mul]
    exact Submonoid.mul_mem _ (perm4Mat_swap_mem_W x y) ih

private lemma W_subset_range (M : Matrix (Fin 3) (Fin 3) ℤ) (hM : M ∈ W_tildeAminus2Z) :
    ∃ σ : Equiv.Perm (Fin 4), perm4Mat σ = M := by
  induction hM using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨Equiv.swap 0 3, perm4Mat_swap03⟩
    · exact ⟨Equiv.swap 1 3, perm4Mat_swap13⟩
    · exact ⟨Equiv.swap 2 3, perm4Mat_swap23⟩
  | one => exact ⟨1, perm4Mat_one⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨σ, rfl⟩ := ihx
    obtain ⟨τ, rfl⟩ := ihy
    exact ⟨σ * τ, perm4Mat_mul σ τ⟩

/-- **Remark 3.23**: `W(~A_{-2})` is isomorphic (as a monoid/group) to `S₄ = Equiv.Perm (Fin 4)`. -/
noncomputable def remark_3_23_tildeAminus2_iso_S4 :
    Equiv.Perm (Fin 4) ≃* W_tildeAminus2Z :=
  MulEquiv.ofBijective
    ({ toFun := fun σ => ⟨perm4Mat σ, perm4Mat_mem_W σ⟩
       map_one' := Subtype.ext perm4Mat_one
       map_mul' := fun σ τ => Subtype.ext (perm4Mat_mul σ τ) } :
      Equiv.Perm (Fin 4) →* W_tildeAminus2Z)
    ⟨fun σ τ h => perm4Mat_injective (congr_arg Subtype.val h),
     fun ⟨M, hM⟩ => by
       obtain ⟨σ, rfl⟩ := W_subset_range M hM
       exact ⟨σ, rfl⟩⟩

/-- **Remark 3.23**: `|W(~A_{-2})| = 24`. -/
theorem remark_3_23_card : Nat.card W_tildeAminus2Z = 24 := by
  rw [← Nat.card_congr remark_3_23_tildeAminus2_iso_S4.toEquiv]
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

end Remark323

/-! ### Remark 3.26: `det (-B(~A_{-n})) = 4` for even `n ≥ 2` -/

section Remark326

/-- Cyclic shift permutation matrix `P` of size `m`: `P i j = 1` iff `j = i + 1` (mod `m`). -/
private def shiftMat (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if j.val = (i.val + 1) % m then 1 else 0

private lemma shiftMat_mul_transpose (m : ℕ) (hm : 1 ≤ m) :
    shiftMat m * (shiftMat m)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, transpose_apply, shiftMat, Matrix.of_apply, Matrix.one_apply]
  have huniq : ∀ x : Fin m, x.val = (i.val + 1) % m ↔ x = ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩ := by
    intro x; simp [Fin.ext_iff]
  simp_rw [huniq]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hij : i = j
  · subst hij; simp
  · have hne : (i.val + 1) % m ≠ (j.val + 1) % m := by
      intro h
      apply hij
      ext
      have hi := i.isLt
      have hj := j.isLt
      by_cases hi1 : i.val + 1 < m <;> by_cases hj1 : j.val + 1 < m
      · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at h; omega
      · have : j.val + 1 = m := by omega
        rw [Nat.mod_eq_of_lt hi1, this, Nat.mod_self] at h; omega
      · have : i.val + 1 = m := by omega
        rw [this, Nat.mod_self, Nat.mod_eq_of_lt hj1] at h; omega
      · omega
    simp [hij, hne]

private lemma neg_cycleNegForm_eq (m : ℕ) [NeZero m] (hm : 3 ≤ m) :
    -cycleNegForm m = (1 + shiftMat m) * (1 + shiftMat m)ᵀ := by
  have hm1 : 1 ≤ m := by omega
  rw [transpose_add, transpose_one, add_mul, mul_add, mul_add,
    shiftMat_mul_transpose m hm1]
  simp only [one_mul, mul_one]
  ext i j
  have hval1 : ((1 : Fin m) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < m)]
  simp only [Matrix.neg_apply, cycleNegForm, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    shiftMat, Matrix.transpose_apply, Fin.ext_iff, Fin.val_add, hval1]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hij : i.val = j.val
  · have hij' : i = j := Fin.ext hij
    subst hij'
    have h1 : ¬ (i.val = (i.val + 1) % m) := by
      by_cases hlt : i.val + 1 < m
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · have : i.val + 1 = m := by omega
        rw [this, Nat.mod_self]; omega
    have hc1 : (i.val = (i.val + 1) % m) = False := eq_false h1
    have hc2 : ((i.val + 1) % m = i.val) = False := eq_false (fun h => h1 h.symm)
    simp only [↓reduceIte, hc1, hc2]
    ring
  · by_cases h1 : (i.val + 1) % m = j.val
    · have h2 : ¬ ((j.val + 1) % m = i.val) := by
        by_cases hi1 : i.val + 1 < m <;> by_cases hj1 : j.val + 1 < m
        · rw [Nat.mod_eq_of_lt hi1] at h1; rw [Nat.mod_eq_of_lt hj1]; omega
        · have : j.val + 1 = m := by omega
          rw [Nat.mod_eq_of_lt hi1] at h1; rw [this, Nat.mod_self]; omega
        · have : i.val + 1 = m := by omega
          rw [this, Nat.mod_self] at h1; rw [Nat.mod_eq_of_lt hj1]; omega
        · omega
      have hc0 : (i.val = j.val) = False := eq_false hij
      have hc1 : (j.val = (i.val + 1) % m) = True := eq_true h1.symm
      have hc2 : (i.val = (j.val + 1) % m) = False := eq_false (fun h => h2 h.symm)
      have hc3 : ((i.val + 1) % m = j.val) = True := eq_true h1
      have hc4 : ((j.val + 1) % m = i.val) = False := eq_false h2
      simp only [hc0, hc1, hc2, hc3, hc4, ↓reduceIte]
      norm_num
    · by_cases h2 : (j.val + 1) % m = i.val
      · have hc0 : (i.val = j.val) = False := eq_false hij
        have hc1 : (j.val = (i.val + 1) % m) = False := eq_false (fun h => h1 h.symm)
        have hc2 : (i.val = (j.val + 1) % m) = True := eq_true h2.symm
        have hc3 : ((i.val + 1) % m = j.val) = False := eq_false h1
        have hc4 : ((j.val + 1) % m = i.val) = True := eq_true h2
        simp only [hc0, hc1, hc2, hc3, hc4, ↓reduceIte]
        norm_num
      · have hc0 : (i.val = j.val) = False := eq_false hij
        have hc1 : (j.val = (i.val + 1) % m) = False := eq_false (fun h => h1 h.symm)
        have hc2 : (i.val = (j.val + 1) % m) = False := eq_false (fun h => h2 h.symm)
        have hc3 : ((i.val + 1) % m = j.val) = False := eq_false h1
        have hc4 : ((j.val + 1) % m = i.val) = False := eq_false h2
        simp only [hc0, hc1, hc2, hc3, hc4, ↓reduceIte]
        norm_num

private lemma det_one_add_shiftMat (r : ℕ) (hr : 1 ≤ r) :
    (1 + shiftMat (r + 2)).det = 1 + (-1 : ℝ) ^ (r + 1) := by
  rw [det_succ_row_zero]
  have hrow0_0 : (1 + shiftMat (r + 2)) 0 0 = 1 := by
    simp only [Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply, ↓reduceIte, Fin.val_zero]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < r + 2)]
    norm_num
  have hrow0_1 : (1 + shiftMat (r + 2)) 0 1 = 1 := by
    simp only [Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply, Fin.ext_iff, Fin.val_zero,
      Fin.val_one]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < r + 2)]
    norm_num
  have hrow0_tail : ∀ j : Fin r, (1 + shiftMat (r + 2)) 0 j.succ.succ = 0 := by
    intro j
    simp only [Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply, Fin.val_succ, Fin.val_zero]
    have hj := j.isLt
    have h1 : (0 : Fin (r + 2)) ≠ j.succ.succ := by simp [Fin.ext_iff]
    have h2 : j.val + 1 + 1 ≠ (0 + 1) % (r + 2) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [h1, h2]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hrow0_0, Fin.val_succ, pow_one, neg_mul,
    hrow0_1, hrow0_tail, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  -- Submatrix `M₀` (deleting row 0 and col 0) is upper triangular with 1s on diagonal
  let M₀ := (1 + shiftMat (r + 2)).submatrix Fin.succ (Fin.succAbove 0)
  have hM₀_ut : M₀.BlockTriangular id := by
    intro i j hij
    change j < i at hij
    have hij' : j.val < i.val := hij
    simp only [M₀, submatrix_apply, Fin.succAbove_zero, Matrix.add_apply, Matrix.one_apply, shiftMat,
      Matrix.of_apply, Fin.ext_iff, Fin.val_succ]
    have hi := i.isLt
    have hj := j.isLt
    have h1 : i.val ≠ j.val := by omega
    have h2 : j.val + 1 ≠ (i.val + 1 + 1) % (r + 2) := by
      by_cases him : i.val + 2 < r + 2
      · rw [Nat.mod_eq_of_lt him]; omega
      · have : i.val + 2 = r + 2 := by omega
        rw [this, Nat.mod_self]; omega
    simp [h1, h2]
  have hM₀_det : M₀.det = 1 := by
    rw [det_of_upperTriangular hM₀_ut]
    apply Finset.prod_eq_one
    intro i _
    simp only [M₀, submatrix_apply, Fin.succAbove_zero, Matrix.add_apply, Matrix.one_apply, shiftMat,
      Matrix.of_apply, ↓reduceIte, Fin.val_succ]
    have h2 : i.val + 1 ≠ (i.val + 1 + 1) % (r + 2) := by
      by_cases him : i.val + 2 < r + 2
      · rw [Nat.mod_eq_of_lt him]; omega
      · have : i.val + 2 = r + 2 := by omega
        rw [this, Nat.mod_self]; omega
    simp [h2]
  -- Submatrix `M₁` (deleting row 0 and col 1)
  let M₁ := (1 + shiftMat (r + 2)).submatrix Fin.succ (Fin.succAbove 1)
  have hM₁_col0 : ∀ i : Fin (r + 1), M₁ i 0 = if i = Fin.last r then 1 else 0 := by
    intro i
    simp only [M₁, submatrix_apply, Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply,
      Fin.succAbove_of_castSucc_lt _ _ (by simp : (0 : Fin (r + 1)).castSucc < 1),
      Fin.coe_castSucc, Fin.val_zero, Fin.val_succ]
    have h1 : (i.succ : Fin (r + 2)) ≠ 0 := Fin.succ_ne_zero i
    have hi := i.isLt
    by_cases hlast : i = Fin.last r
    · subst hlast
      simp [Fin.last, h1]
    · have hil : i.val < r := by
        rcases Fin.eq_or_lt_of_le (Fin.le_last i) with h | h
        · exact absurd h hlast
        · exact h
      have h2 : (0 : ℕ) ≠ (i.val + 1 + 1) % (r + 2) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp [h1, h2, hlast]
  have hM₁_det : M₁.det = (-1 : ℝ) ^ r := by
    rw [det_succ_column_zero]
    have hsum1 : ∑ i : Fin (r + 1), (-1 : ℝ) ^ (i : ℕ) * M₁ i 0 *
        (M₁.submatrix (Fin.succAbove i) Fin.succ).det =
        (-1 : ℝ) ^ (Fin.last r : ℕ) * 1 *
          (M₁.submatrix (Fin.succAbove (Fin.last r)) Fin.succ).det := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · simp [hM₁_col0]
      · intro i _ hi
        simp [hM₁_col0, hi]
      · simp
    rw [hsum1]
    let N := M₁.submatrix (Fin.succAbove (Fin.last r)) Fin.succ
    have hsuccAbove_ge1 : ∀ j : Fin r, (Fin.succAbove (1 : Fin (r + 2)) j.succ).val = j.val + 2 := by
      intro j
      simp only [Fin.succAbove]
      split_ifs with h
      · exfalso
        have : (j.succ.castSucc : ℕ) < (1 : Fin (r + 2)).val := h
        simp at this
      · simp [Fin.val_succ]
    have hNt_ut : Nᵀ.BlockTriangular id := by
      intro i j hij
      change j < i at hij
      have hlt : j.val < i.val := hij
      have hi := i.isLt
      have hj := j.isLt
      simp only [transpose_apply, N, M₁, submatrix_apply,
        Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j),
        Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply, Fin.ext_iff, Fin.val_succ,
        Fin.val_castSucc, hsuccAbove_ge1]
      have h1 : j.val + 1 ≠ i.val + 2 := by omega
      have h2 : i.val + 2 ≠ (j.val + 1 + 1) % (r + 2) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      simp only [h1, h2, ↓reduceIte, add_zero]
    have hN_det : N.det = 1 := by
      rw [← det_transpose, det_of_upperTriangular hNt_ut]
      apply Finset.prod_eq_one
      intro i _
      have hi := i.isLt
      simp only [transpose_apply, N, M₁, submatrix_apply,
        Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last i),
        Matrix.add_apply, Matrix.one_apply, shiftMat, Matrix.of_apply, Fin.ext_iff, Fin.val_succ,
        Fin.val_castSucc, hsuccAbove_ge1]
      have h1 : i.val + 1 ≠ i.val + 2 := by omega
      have h2 : i.val + 2 = (i.val + 1 + 1) % (r + 2) := by
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [if_neg h1, if_pos h2, zero_add]
    rw [hN_det, mul_one, mul_one, Fin.val_last]
  have hsucc0 : (Fin.succ 0 : Fin (r + 2)) = 1 := rfl
  rw [hsucc0, hrow0_1,
    show ((1 + shiftMat (r + 2)).submatrix Fin.succ (Fin.succAbove 0)).det = M₀.det from rfl,
    show ((1 + shiftMat (r + 2)).submatrix Fin.succ (Fin.succAbove 1)).det = M₁.det from rfl,
    hM₀_det, hM₁_det]
  ring

/-- **Remark 3.26**: For every odd `m ≥ 3` (corresponding to `~A_{-n}` with `n = m - 1` even),
`det (-B(~A_{-n})) = 4`. -/
theorem remark_3_26_det_neg_odd_cycle (m : ℕ) [NeZero m] (hm : 3 ≤ m) (hodd : Odd m) :
    (-cycleNegForm m).det = 4 := by
  obtain ⟨r, hr_eq⟩ : ∃ r, m = r + 2 := ⟨m - 2, by omega⟩
  subst hr_eq
  have hr : 1 ≤ r := by omega
  rw [neg_cycleNegForm_eq (r + 2) hm, det_mul, det_transpose]
  have hdet := det_one_add_shiftMat r hr
  have hr_odd : Odd (r + 2) := hodd
  have hr1_even : Even (r + 1) := by
    obtain ⟨k, hk⟩ := hr_odd
    exact ⟨k, by omega⟩
  rw [hr1_even.neg_one_pow] at hdet
  rw [hdet]
  norm_num

end Remark326

/-! ### Remark 3.30: Oscillation of minimal spectral radii along `A₂(+,-) ⊂ A₃(-,+,+) ⊂ A₄(-,+,+,+) ⊂ A₅(-,+,+,+,+)` -/

section Remark330

private def rem330_A2 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; -1, -2] * !![-2, 0; 1, 1]
private def rem330_A3 : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; -1, 1, 0; 0, -1, 1] * !![-2, 1, 0; 0, 2, 1; 0, 0, 2]
-- Wait: let's use the exact integer principal elements via `reflectionMatrix` on `MixedSignCoxeterGraph.A_n`!

private def sA2 (i : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  match i with
  | 0 => !![-1, 1; 0, 1]
  | 1 => !![1, 0; -1, -1]

private def sA3 (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℤ :=
  match i with
  | 0 => !![-1, -1, 0; 0, 1, 0; 0, 0, 1]
  | 1 => !![1, 0, 0; 1, -1, 1; 0, 0, 1]
  | 2 => !![1, 0, 0; 0, 1, 0; 0, 1, -1]

private def sA4 (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  match i with
  | 0 => !![-1, -1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 1 => !![1, 0, 0, 0; 1, -1, 1, 0; 0, 0, 1, 0; 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, -1, 1; 0, 0, 0, 1]
  | 3 => !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, -1]

private def sA5 (i : Fin 5) : Matrix (Fin 5) (Fin 5) ℤ :=
  match i with
  | 0 => !![-1, -1, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 1 => !![1, 0, 0, 0, 0; 1, -1, 1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, -1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 3 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, -1, 1; 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 1, -1]

private def wA2Z : Matrix (Fin 2) (Fin 2) ℤ := sA2 0 * sA2 1
private def wA3Z : Matrix (Fin 3) (Fin 3) ℤ := sA3 0 * sA3 1 * sA3 2
private def wA4Z : Matrix (Fin 4) (Fin 4) ℤ := sA4 0 * sA4 1 * sA4 2 * sA4 3
private def wA5Z : Matrix (Fin 5) (Fin 5) ℤ := sA5 0 * sA5 1 * sA5 2 * sA5 3 * sA5 4

theorem wA2Z_annihilated : wA2Z ^ 2 + 3 • wA2Z + 1 = 0 := by decide
theorem wA3Z_annihilated : (wA3Z + 1) ^ 3 = 0 := by decide
theorem wA4Z_annihilated : wA4Z ^ 4 + 3 • wA4Z ^ 3 + 3 • wA4Z ^ 2 + 3 • wA4Z + 1 = 0 := by decide
theorem wA5Z_annihilated :
    wA5Z ^ 5 + 3 • wA5Z ^ 4 + 3 • wA5Z ^ 3 + 3 • wA5Z ^ 2 + 3 • wA5Z + 1 = 0 := by decide

/-- `A₂(+,-)` has a real eigenvalue `< -2.6` (namely `-(3 + √5)/2 ≈ -2.61803`). -/
theorem remark_3_30_A2_root_gt : ∃ r : ℝ, r < -2.6 ∧ r ^ 2 + 3 * r + 1 = 0 := by
  let f : ℝ → ℝ := fun x => -(x ^ 2 + 3 * x + 1)
  have hf_cont : ContinuousOn f (Set.Icc (-3) (-2.6)) := by fun_prop
  have hfa : f (-3) < 0 := by norm_num [f]
  have hfb : 0 < f (-2.6) := by norm_num [f]
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by norm_num) hf_cont ⟨hfa.le, hfb.le⟩
  refine ⟨r, ?_, by linarith [show -(r ^ 2 + 3 * r + 1) = 0 from hfr]⟩
  rcases eq_or_lt_of_le hr.2 with rfl | hlt
  · exfalso; linarith
  · exact hlt

/-- `A₄(-,+,+,+)` has a real eigenvalue `< -2.15` (namely `≈ -2.15372`). -/
theorem remark_3_30_A4_root_gt : ∃ r : ℝ, r < -2.15 ∧ r ^ 4 + 3 * r ^ 3 + 3 * r ^ 2 + 3 * r + 1 = 0 := by
  let f : ℝ → ℝ := fun x => -(x ^ 4 + 3 * x ^ 3 + 3 * x ^ 2 + 3 * x + 1)
  have hf_cont : ContinuousOn f (Set.Icc (-3) (-2.15)) := by fun_prop
  have hfa : f (-3) < 0 := by norm_num [f]
  have hfb : 0 < f (-2.15) := by norm_num [f]
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by norm_num) hf_cont ⟨hfa.le, hfb.le⟩
  refine ⟨r, ?_, by linarith [show -(r ^ 4 + 3 * r ^ 3 + 3 * r ^ 2 + 3 * r + 1) = 0 from hfr]⟩
  rcases eq_or_lt_of_le hr.2 with rfl | hlt
  · exfalso; linarith
  · exact hlt

/-- Every complex root of `A₅(-,+,+,+,+)`'s principal polynomial has modulus `< 2.13`
(in fact `ρ ≈ 1.8832 < 2.13 < 2.15 < ρ(A₄)`). -/
theorem remark_3_30_A5_roots_lt (z : ℂ)
    (hz : z ^ 5 + 3 * z ^ 4 + 3 * z ^ 3 + 3 * z ^ 2 + 3 * z + 1 = 0) :
    ‖z‖ < 2.13 := by
  by_contra hge
  push Not at hge
  have hmul : (z - 1) * (z ^ 5 + 3 * z ^ 4 + 3 * z ^ 3 + 3 * z ^ 2 + 3 * z + 1) = 0 := by
    rw [hz, mul_zero]
  have h6 : z ^ 6 + 2 * z ^ 5 = 2 * z + 1 := by
    linear_combination hmul
  have hleft : ‖z‖ ^ 5 * (‖z‖ - 2) ≤ ‖z ^ 6 + 2 * z ^ 5‖ := by
    have h1 : ‖z ^ 6‖ - ‖2 * z ^ 5‖ ≤ ‖z ^ 6 + 2 * z ^ 5‖ := by
      have := norm_sub_le (z ^ 6 + 2 * z ^ 5) (2 * z ^ 5)
      simp only [add_sub_cancel_right] at this
      linarith
    have h2 : ‖z ^ 6‖ = ‖z‖ ^ 6 := by simp
    have h3 : ‖2 * z ^ 5‖ = 2 * ‖z‖ ^ 5 := by simp
    rw [h2, h3] at h1
    linarith [show ‖z‖ ^ 5 * (‖z‖ - 2) = ‖z‖ ^ 6 - 2 * ‖z‖ ^ 5 by ring]
  have hright : ‖2 * z + 1‖ ≤ 2 * ‖z‖ + 1 := by
    calc ‖2 * z + 1‖ ≤ ‖2 * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = 2 * ‖z‖ + 1 := by simp
  rw [h6] at hleft
  have hineq : ‖z‖ ^ 5 * (‖z‖ - 2) ≤ 2 * ‖z‖ + 1 := hleft.trans hright
  have hpow : (2.13 : ℝ) ^ 5 ≤ ‖z‖ ^ 5 := pow_le_pow_left₀ (by norm_num) hge 5
  have h213 : (2.13 : ℝ) ^ 5 * (‖z‖ - 2) ≤ ‖z‖ ^ 5 * (‖z‖ - 2) :=
    mul_le_mul_of_nonneg_right hpow (by linarith)
  linarith

end Remark330

end MixedSignCoxeter

