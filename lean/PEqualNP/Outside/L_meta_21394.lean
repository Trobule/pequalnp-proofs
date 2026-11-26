import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_21394

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩

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

end PEqualNP.Outside.L_meta_21394

open PEqualNP.Outside.L_meta_21394 in
theorem PEqualNP.Outside.L_meta_21394 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112093 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
