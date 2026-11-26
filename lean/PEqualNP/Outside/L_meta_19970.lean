import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19970

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.or, [8, 16]⟩, ⟨GateOp.or, [4, 21]⟩, ⟨GateOp.or, [0, 21]⟩, ⟨GateOp.or, [6, 15]⟩, ⟨GateOp.or, [9, 22]⟩, ⟨GateOp.or, [3, 25]⟩, ⟨GateOp.or, [24, 25]⟩, ⟨GateOp.or, [19, 23]⟩, ⟨GateOp.or, [10, 22]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [30, 33]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [20, 28]⟩, ⟨GateOp.and, [18, 31]⟩, ⟨GateOp.and, [26, 29]⟩, ⟨GateOp.or, [34, 37]⟩, ⟨GateOp.or, [7, 35]⟩, ⟨GateOp.or, [38, 39]⟩, ⟨GateOp.and, [27, 40]⟩, ⟨GateOp.or, [36, 41]⟩, ⟨GateOp.and, [3, 32]⟩, ⟨GateOp.or, [43, 44]⟩, ⟨GateOp.or, [42, 45]⟩], 46⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19970

theorem PEqualNP.Outside.L_meta_19970 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15581543385461502840 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19970.circ, PEqualNP.Outside.L_meta_19970.mono, by decide, PEqualNP.Outside.L_meta_19970.rep⟩
