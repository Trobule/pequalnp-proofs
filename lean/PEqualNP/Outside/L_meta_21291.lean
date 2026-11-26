import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21291

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [13, 9]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [17, 18]⟩], 19⟩

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

end PEqualNP.Outside.L_meta_21291

open PEqualNP.Outside.L_meta_21291 in
theorem PEqualNP.Outside.L_meta_21291 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40409 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
