import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22407

def witness : Circuit :=
  ⟨[⟨.or, [3, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [14, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [18, 11]⟩, ⟨.and, [13, 15]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22407

open PEqualNP.Outside.L_meta_22407 in
theorem PEqualNP.Outside.L_meta_22407 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904061 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
