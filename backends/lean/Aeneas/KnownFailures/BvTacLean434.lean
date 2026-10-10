import Aeneas.Tactic.Solver.BvTac.BvTac

namespace Aeneas.BvTac

open Lean Lean.Meta Lean.Parser.Tactic Lean.Elab.Tactic
open Bvify Utils

/-!
# Tests
-/
open Std

example (x y : U8) (h : x.val ≤ y.val) : x.bv ≤ y.bv := by
  bv_tac

example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv := by
  bv_tac

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac
  simp

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac 32
  simp

/- Checking parsing -/
example (x : U32) (h : x.val < 3329) : x.bv % 3329#32 = x.bv ∧ True := by
  constructor
  bv_tac 32; simp

example
  (a : U32)
  (b : U32)
  (ha : a.val < 3329)
  (hb : b.val < 3329)
  (c1 : U32)
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16#i32.toNat)
  (_ : ¬c3 = 0#u32) :
  c3 = 65535#u32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (ha : a.val < 3329)
  (hb : b.val < 3329)
  (c1 : U32)
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (_ : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (_ : c3.bv = c2.bv >>> 16#i32.toNat) :
  (c1.bv - 3329#32 + (3329#32 &&& c3.bv)) % 3329#32 = (a.bv + b.bv) % 3329#32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16#i32.toNat)
  (h : (↑a : ℕ) < 6658 ∧ (↑b : ℕ) = 3329)
  (_ : ¬c2 = 0#u32) :
  c2 = 65535#u32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (h0 : (↑a : ℕ) ≤ 6658)
  (ha : (↑a : ℕ) < (↑b : ℕ) + 3329)
  (hb : (↑b : ℕ) ≤ 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (hc3_1 : (↑c3 : ℕ) = (↑(3329#u32 &&& c2) : ℕ))
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = core.num.U32.wrapping_add c1 c3) :
  c4.bv % 3329#32 = (a.bv + 3329#32 - b.bv) % 3329#32 ∧ c4.bv < 3329#32
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (ha : (↑a : ℕ) < 3329)
  (hb : (↑b : ℕ) < 3329)
  (c1 : U32)
  (hc1 : (↑c1 : ℕ) = (↑a : ℕ) + (↑b : ℕ))
  (_ : c1.bv = a.bv + b.bv)
  (c2 : U32)
  (hc2 : c2 = core.num.U32.wrapping_sub c1 3329#u32)
  (c3 : U32)
  (hc3 : c3.bv = c2.bv >>> 16)
  (h : ¬c3 = 0#u32) :
  c3 = 65535#u32
  := by bv_tac

example
  (a : U32)
  (b : U32)
  (h : a.val < 3329 ∧ b.val < 3329 ∨ a.val < 6658 ∧ b.val = 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16) :
  (decide (c2 = 0#u32) || decide (c2 = 65535#u32)) = true
  := by
  bv_tac

example
  (a : U32)
  (b : U32)
  (h : a.val < 3329 ∧ b.val < 3329 ∨ a.val < 6658 ∧ b.val = 3329)
  (c1 : U32)
  (hc1 : c1 = core.num.U32.wrapping_sub a b)
  (c2 : U32)
  (hc2 : c2.bv = c1.bv >>> 16)
  (c3 : U32)
  (hc3_1 : c3.val = (3329#u32 &&& c2).val)
  (_ : c3.bv = 3329#32 &&& c2.bv)
  (c4 : U32)
  (hc3 : c4 = core.num.U32.wrapping_add c1 c3) :
  (c4.val : ZMod 3329) = (a.val : ZMod 3329) - (b.val : ZMod 3329) ∧ c4.val < 3329
  := by
  bv_tac 32

end Aeneas.BvTac
