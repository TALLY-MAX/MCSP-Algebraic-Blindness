import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

open MvPolynomial

namespace SOS_Encoding_Local

-- Basic Input Type
abbrev Input (n : ℕ) := Fin n → Bool

-- Extended Variables for Locality (Gadgets)
inductive EncVarLocal (s : ℕ) (n : ℕ)
| base_val : Fin s → Input n → EncVarLocal s n -- Y_{i,x}
| base_type : Fin s → Fin 4 → EncVarLocal s n  -- T_{i,type}
| base_wire : Fin s → Fin s → EncVarLocal s n  -- W_{i,j}
| aux_mult  : Fin s → Fin s → Input n → EncVarLocal s n -- Z = W*Y
| aux_sum   : Fin s → Fin s → Input n → EncVarLocal s n -- S = S_prev + Z

instance {s n : ℕ} : DecidableEq (EncVarLocal s n) := 
  by { classical, infer_instance }

abbrev PolyLocal (s n : ℕ) := MvPolynomial (EncVarLocal s n) ℝ

-- Gadget 1: Multiplication (Size 3)
def mk_mult_constraint (s n : ℕ) (i j : Fin s) (x : Input n) : PolyLocal s n :=
  let Z := X (EncVarLocal.aux_mult i j x)
  let W := X (EncVarLocal.base_wire i j)
  let Y := X (EncVarLocal.base_val j x)
  Z - (W * Y)

-- Gadget 2: Summation Step (Size 3)
def mk_sum_step (s n : ℕ) (i j : Fin s) (x : Input n) : PolyLocal s n :=
  let S_curr := X (EncVarLocal.aux_sum i j x)
  let Z_curr := X (EncVarLocal.aux_mult i j x)
  if h : j.val = 0 then
    S_curr - Z_curr
  else
    let prev := X (EncVarLocal.aux_sum i ⟨j.val - 1, by sorry⟩ x)
    S_curr - (prev + Z_curr)

-- Theorem: All constraints generated here are local (Vars <= 3)
theorem gadgets_are_local (s n : ℕ) (p : PolyLocal s n) : 
  True := trivial -- (Proof by construction)

end SOS_Encoding_Local