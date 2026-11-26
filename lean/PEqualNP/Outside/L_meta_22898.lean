import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22898

def witness : Circuit :=
  ⟨[⟨.or, [7, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [23, 22]⟩], 24⟩

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

end PEqualNP.Outside.L_meta_22898

open PEqualNP.Outside.L_meta_22898 in
theorem PEqualNP.Outside.L_meta_22898 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947512 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
