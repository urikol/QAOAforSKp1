import Mathlib

----------------------------------------------------------------
--------------------------Lemmas--------------------------------
----------------------------------------------------------------

/--
`2` is nonzero in `ℂ`.
Used to justify inverses such as `(2 : ℂ)⁻¹` in normalization proofs.
-/
lemma two_ne_zero_complex : (2 : ℂ) ≠ 0 := by
  norm_num


/--
In `ℂ`, squaring `√2` gives `2`.
This is the algebraic identity needed to simplify the `1 / √2` factors
when proving normalization of `|+⟩` and `|s⟩`.
-/
lemma sqrt2_sq_complex : ((Real.sqrt 2 : ℂ) ^ 2) = (2 : ℂ) := by
  have hR : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  exact_mod_cast hR



----------------------------------------------------------------
--------------------------Bra State-----------------------------
----------------------------------------------------------------
/-- Bra associated to `ψ` in any finite-dimensional computational basis. -/
noncomputable def bra {n : ℕ} (ψ : Fin n → ℂ) : (Fin n → ℂ) → ℂ :=
  fun φ => ∑ i : Fin n, star (ψ i) * φ i



----------------------------------------------------------------
--------------------------Single Qubit--------------------------
----------------------------------------------------------------

/-- A single-qubit pure state represented as amplitudes on basis indices `0,1`. -/
abbrev Qubit := Fin 2 → ℂ

/-- Computational basis state `|0⟩`. -/
def ket0 : Qubit :=
  ![1, 0]

/-- Computational basis state `|1⟩`. -/
def ket1 : Qubit :=
  ![0, 1]

/-- Hadamard gate on a single qubit. -/
noncomputable def hadamard (ψ : Qubit) : Qubit :=
  ![
    (ψ 0 + ψ 1) / Real.sqrt 2,
    (ψ 0 - ψ 1) / Real.sqrt 2
  ]

/-- `|+⟩ = H|0⟩` for a single qubit. -/
noncomputable def ketPlus : Qubit :=
  hadamard ket0


/-- Single qubit state normalization and orthogonalization. -/
theorem bra_ket0_ket0 : bra ket0 ket0 = 1 := by
  simp [bra, ket0]

theorem bra_ket1_ket1 : bra ket1 ket1 = 1 := by
  simp [bra, ket1]

theorem bra_ket0_ket1 : bra ket0 ket1 = 0 := by
  simp [bra, ket0, ket1]

theorem bra_ket1_ket0 : bra ket1 ket0 = 0 := by
  simp [bra, ket0, ket1]

/-- The `|+⟩` state is normalized: `⟨+|+⟩ = 1`. -/
theorem bra_ketPlus_ketPlus : bra ketPlus ketPlus = 1 := by
  simp [bra, ketPlus, hadamard, ket0]
  ring_nf
  simp [sqrt2_sq_complex]



----------------------------------------------------------------
--------------------------n-Qubits State------------------------
----------------------------------------------------------------

/-- State space for `(n+1)` qubits in computational basis indexing. -/
abbrev State (n : ℕ) := Fin (2 ^ (n + 1)) → ℂ


/--
Split an index of `2^(n+1)` basis states into:
1 qubit index (`Fin 2`) and the remaining `n`-qubit index (`Fin (2^n)`).
-/
def splitQubitIndex {n : ℕ} (i : Fin (2 ^ (n + 1))) : Fin 2 × Fin (2 ^ n) :=
  ( ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩
  , ⟨i.1 / 2, by
      have hi : i.1 < 2 ^ n * 2 := by
        simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using i.2
      exact (Nat.div_lt_iff_lt_mul (by decide : 0 < (2 : ℕ))).2 <| by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi
    ⟩ )

/--
Initial QAOA state on `n+1` qubits, defined as `|s⟩ = |+⟩^{⊗ (n+1)}`.
This encoding avoids the `n=0` scalar base case.
-/
noncomputable def s : (n : ℕ) → State n
  | 0 => ketPlus
  | n + 1 => fun i =>
      let p := splitQubitIndex (n := n + 1) i
      ketPlus p.1 * s n p.2


/-- The initial state is normalized: `⟨s|s⟩ = 1`. -/
theorem bra_s_s (n : ℕ) : bra (s n) (s n) = 1 := by
  let c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hketPlus : ∀ i : Fin 2, ketPlus i = c := by
    intro i
    fin_cases i <;> simp [ketPlus, hadamard, ket0, c]
  have hs_const : ∀ n : ℕ, ∀ i : Fin (2 ^ (n + 1)), s n i = c ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro i
        fin_cases i <;> simp [s, hketPlus, c]
    | succ n ih =>
        intro i
        simp [s, hketPlus, ih, pow_succ, mul_comm]
  have hc2 : c * c = (2 : ℂ)⁻¹ := by
    dsimp [c]
    ring_nf
    simp [sqrt2_sq_complex]
  calc
    bra (s n) (s n)
        = ∑ i : Fin (2 ^ (n + 1)), star (s n i) * s n i := rfl
    _ = ∑ _i : Fin (2 ^ (n + 1)), star (c ^ (n + 1)) * (c ^ (n + 1)) := by
          simp [hs_const]
    _ = (2 ^ (n + 1) : ℂ) * (star (c ^ (n + 1)) * c ^ (n + 1)) := by
          simp
    _ = (2 ^ (n + 1) : ℂ) * (c ^ (n + 1) * c ^ (n + 1)) := by
          simp [c]
    _ = (2 ^ (n + 1) : ℂ) * ((c * c) ^ (n + 1)) := by
          rw [← mul_pow]
    _ = (2 ^ (n + 1) : ℂ) * (((2 : ℂ)⁻¹) ^ (n + 1)) := by
          simp [hc2]
    _ = (2 : ℂ) ^ (n + 1) * ((2 : ℂ)⁻¹ ^ (n + 1)) := by
          norm_num
    _ = ((2 : ℂ) * (2 : ℂ)⁻¹) ^ (n + 1) := by
          rw [(mul_pow (2 : ℂ) ((2 : ℂ)⁻¹) (n + 1)).symm]
    _ = 1 := by
          simp



----------------------------------------------------------------
--------------------------The Mixer Operator--------------------
----------------------------------------------------------------

/-- Linear operators acting on `State n`. -/
abbrev Operator (n : ℕ) := State n → State n


/-- Hamming distance between computational-basis indices (`(n+1)`-bit strings). -/
def basisHammingDist (n : ℕ) (x y : Fin (2 ^ (n + 1))) : ℕ :=
  ((Finset.range (n + 1)).filter (fun j => Nat.testBit x.1 j ≠ Nat.testBit y.1 j)).card

/-- Computational-basis matrix element of `U_B(β) = exp(-i β ∑_j X_j)`. -/
noncomputable def mixerEntry (n : ℕ) (β : ℝ) (x y : Fin (2 ^ (n + 1))) : ℂ :=
  let d := basisHammingDist n x y
  (Real.cos β : ℂ) ^ ((n + 1) - d) * ((-Complex.I) * (Real.sin β : ℂ)) ^ d

/-- Explicit mixer unitary action in the computational basis. -/
noncomputable def U_B (n : ℕ) (β : ℝ) : Operator n :=
  fun ψ x => ∑ y : Fin (2 ^ (n + 1)), mixerEntry n β x y * ψ y
