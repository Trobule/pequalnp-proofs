import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20192

def witness : Circuit :=
  ⟨[⟨.or, [4, 15]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [5, 21]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [23, 20]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [8, 19]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [31, 11]⟩, ⟨.or, [32, 17]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [34, 18]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [36, 14]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [26, 29]⟩, ⟨.and, [30, 33]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [43, 41]⟩], 44⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_20192

open PEqualNP.Outside.L_meta_20192 in
theorem PEqualNP.Outside.L_meta_20192 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
