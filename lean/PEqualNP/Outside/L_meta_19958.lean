import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19958

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [0, 17]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 18]⟩, ⟨GateOp.and, [20, 21]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [1, 18]⟩, ⟨GateOp.or, [16, 24]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [1, 12]⟩, ⟨GateOp.or, [3, 17]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [10, 29]⟩, ⟨GateOp.or, [3, 27]⟩, ⟨GateOp.or, [20, 21]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.and, [25, 28]⟩, ⟨GateOp.and, [31, 32]⟩, ⟨GateOp.and, [23, 30]⟩, ⟨GateOp.or, [31, 33]⟩, ⟨GateOp.or, [23, 33]⟩, ⟨GateOp.or, [35, 36]⟩, ⟨GateOp.or, [16, 37]⟩, ⟨GateOp.or, [34, 39]⟩, ⟨GateOp.and, [26, 40]⟩, ⟨GateOp.or, [22, 41]⟩, ⟨GateOp.and, [11, 38]⟩, ⟨GateOp.or, [42, 43]⟩, ⟨GateOp.or, [44, 45]⟩], 46⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19958

theorem PEqualNP.Outside.L_meta_19958 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19958.circ, PEqualNP.Outside.L_meta_19958.mono, by decide, PEqualNP.Outside.L_meta_19958.rep⟩
